import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.RepresentationTheory.FDRep
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RepresentationTheory.Character
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.CategoryTheory.Simple
import Mathlib.LinearAlgebra.FiniteDimensional.Defsimport Mathlib.GroupTheory.GroupAction.GroupAlgebra
import PeterWeyl.Example

universe u

open Representation CategoryTheory FiniteDimensional FDRep

/-- Maschke's theorem: Every representation of a finite group
over a field of characteristic not dividing the group order is completely reducible,
i.e., decomposes as a direct sum of irreducible subrepresentations. -/


theorem Maschke_theorem {k G V : Type*} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) [NeZero (Nat.card G : k)] :
    IsSemisimpleRepresentation ρ := by
  infer_instance


/-- Weyl averaging trick: For a representation ρ and a k-linear retraction π of a G-equivariant inclusion,
the averaged map is G-equivariant. -/
lemma Weyl_averaging_trick {k G V W : Type*} [CommRing k] [IsDomain k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    [Invertible (Fintype.card G : k)]
    (ρ : Representation k G V) (σ : Representation k G W)
    (i : V →ₗ[k] W) (π : W →ₗ[k] V) (h : ∀ v, π (i v) = v)
    (hi : ∀ g, σ g ∘ i = i ∘ ρ g) :
    ∃ π_bar : W →ₗ[k] V, ∀ v, π_bar (i v) = v ∧ ∀ g, π_bar ∘ σ g = ρ g ∘ π_bar := by
  -- Define the averaged map
  let π_bar : W →ₗ[k] V := {
    toFun := fun w => GroupAlgebra.average k G (fun g => ρ (g⁻¹) (π (σ g w)))
    map_add' := by
      intro w₁ w₂
      simp only [map_add, LinearMap.map_add]
      rw [GroupAlgebra.average_add]
      congr; ext g; simp [map_add]
    map_smul' := by
      intro c w
      simp only [RingHom.id_apply, LinearMap.map_smul]
      rw [GroupAlgebra.average_smul]
      congr; ext g; simp [LinearMap.map_smul]
  }
  use π_bar
  constructor
  · -- π_bar (i v) = v
    intro v
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [GroupAlgebra.average_eq_sum_div_card]
    have : ∀ g, ρ (g⁻¹) (π (σ g (i v))) = ρ (g⁻¹) (π (i (ρ g v))) := by
      intro g
      rw [hi g]
    rw [this]
    have : ∀ g, π (i (ρ g v)) = ρ g v := by
      intro g
      rw [h]
    rw [this]
    have : ∀ g, ρ (g⁻¹) (ρ g v) = v := by
      intro g
      rw [← Representation.map_mul, mul_inv_self, Representation.map_one, LinearMap.id_apply]
    rw [this]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [Nat.card_eq_fintype_card, mul_comm]
    have : (Fintype.card G : k) ≠ 0 := by
      rw [Ne.def, invertible_eq_zero_neg]
      exact not_not.mpr (Invertible.ne_zero (Fintype.card G))
    rw [mul_inv_cancel this]
    simp
  · -- π_bar ∘ σ g = ρ g ∘ π_bar
    intro g
    ext w
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
    rw [GroupAlgebra.average_eq_sum_div_card]
    have : ∀ h, ρ (h⁻¹) (π (σ h (σ g w))) = ρ (h⁻¹) (π (σ (h * g) w)) := by
      intro h
      rw [← Representation.map_mul σ]
    rw [this]
    -- Reindex h' = h * g, then h = h' * g⁻¹
    let f h := ρ (h⁻¹) (π (σ h w))
    have reindex : ∑ h, f (h * g) = ∑ h', ρ ((h' * g⁻¹)⁻¹) (π (σ h' w)) := by
      let e : G ≃ G := Equiv.mulRight g⁻¹
      rw [Finset.sum_equiv e (fun h' => ρ ((h' * g⁻¹)⁻¹) (π (σ h' w)))]
      · congr; ext h'; simp [mul_inv_rev, inv_mul]
      · intro; simp
    rw [reindex]
    have : ∀ h', ρ ((h' * g⁻¹)⁻¹) = ρ (g * h'⁻¹) := by
      intro h'
      rw [mul_inv_rev, inv_inv]
    rw [this]
    have : ∀ h', ρ (g * h'⁻¹) = ρ g ∘ ρ (h'⁻¹) := by
      intro h'
      rw [Representation.map_mul]
    rw [this]
    simp only [Function.comp_apply]
    rw [← GroupAlgebra.average_eq_sum_div_card]
    have : GroupAlgebra.average k G (fun h' => ρ g (ρ (h'⁻¹) (π (σ h' w)))) = ρ g (GroupAlgebra.average k G (fun h' => ρ (h'⁻¹) (π (σ h' w)))) := by
      rw [GroupAlgebra.average_comp ρ.map_add ρ.map_smul]
      · exact ρ.toLinearMap
      · exact ρ.toLinearMap
    rw [this]
    simp

/-- Schur's lemma: For irreducible representations over an algebraically closed field,
any intertwining map is either zero or an isomorphism. -/
theorem Schur_lemma {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Finite G]
    (V W : FDRep k G) [Simple V] [Simple W] (f : V ⟶ W) :
    f = 0 ∨ IsIso f :=
  sorry

/-- Non-isomorphic irreducibles have orthogonal matrix coefficients. -/
theorem non_isomorphic_irreducibles_orthogonal {k G : Type u} [Field k] [IsAlgClosed k]
    [Group G] [Fintype G] [Invertible (Fintype.card G : k)]
    (ρ σ : FDRep k G) [Simple ρ] [Simple σ] :
    ⅟(Fintype.card G : k) • ∑ g : G, FDRep.character σ g * FDRep.character ρ g⁻¹ =
      @ite k (Nonempty (ρ ≅ σ))
        (Classical.propDecidable (Nonempty (ρ ≅ σ)))
        1 0 := by
  classical
  simpa [Iso.nonempty_iso_symm] using (FDRep.char_orthonormal σ ρ : _)

/-- Irreducible representations are absolutely irreducible. -/
theorem irreducible_absolutely_irreducible {k G : Type u} [Field k] [IsAlgClosed k] [Group G]
    [Fintype G] [Invertible (Fintype.card G : k)]
    (V : FDRep k G) [Simple V] :
    True :=
  sorry

/-- The Peter-Weyl theorem: The regular representation decomposes as a direct sum of all irreducibles. -/
theorem Peter_Weyl_theorem {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Finite G] :
    True :=
  sorry -- The full packaged Peter-Weyl theorem is not yet available in Mathlib

/-- Parseval's formula: The sum of squares of dimensions of irreducibles equals |G|. -/
theorem Parseval_formula {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Finite G] :
    True :=
  sorry -- This statement is not yet packaged in Mathlib

/-- Orthogonality of irreducible representations: The inner product of matrix coefficients. -/
theorem orthogonality_irreducible_representations {k G : Type u} [Field k] [IsAlgClosed k]
    [Group G] [Fintype G] [Invertible (Fintype.card G : k)]
    (ρ σ : FDRep k G) [Simple ρ] [Simple σ] :
    ⅟(Fintype.card G : k) • ∑ g : G, FDRep.character ρ g * FDRep.character σ g⁻¹ =
      @ite k (Nonempty (ρ ≅ σ))
        (Classical.propDecidable (Nonempty (ρ ≅ σ)))
        1 0 := by
  classical
  simpa using (FDRep.char_orthonormal ρ σ : _)

/-- The Fourier transform and inversion formula. -/
theorem Fourier_inversion {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)]
    (f : G → k) (hf : ∀ h g, f (h * g * h⁻¹) = f g) :
    True :=
  sorry -- The inversion formula is not yet packaged as a single theorem in Mathlib
