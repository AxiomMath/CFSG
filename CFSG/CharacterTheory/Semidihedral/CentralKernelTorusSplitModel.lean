module

public import CFSG.LinearAlgebra.LinearGroups.PSL2NineCoverKernelAction
public import CFSG.CharacterTheory.Semidihedral.ActualFourGroupCentralizer

public section

namespace CFSG.Semidihedral.CentralKernelTorusSplit

noncomputable section

open Matrix CFSG.Semidihedral.MatrixTorus CFSG.Semidihedral.MatrixCoverData
open CFSG.Semidihedral.ActualFourGroupCentralizer (originalOddInclusion OriginalWProduct
  originalOddInclusion_coordinates)

universe u

variable (F : Type u) [Field F] (a : Fˣ) (A : Subgroup (F ≃+* F))
  (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)

@[expose] def modelProjection : OriginalH F a A hfix →* C2 × A where
  toFun x := (x.left.right, x.right)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem mem_originalSlInH_range_iff (x : OriginalH F a A hfix) :
    x ∈ (originalSlInH F a A hfix).range ↔ x.left.right = 1 ∧ x.right = 1 := by
  constructor
  · rintro ⟨X, rfl⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨x.left.left, ?_⟩
    apply SemidirectProduct.ext
    · apply SemidirectProduct.ext
      · rfl
      · exact h1.symm
    · exact h2.symm

theorem modelProjection_ker :
    (modelProjection F a A hfix).ker = (originalSlInH F a A hfix).range := by
  ext x
  rw [MonoidHom.mem_ker, mem_originalSlInH_range_iff]
  exact Prod.mk_eq_one

theorem commutator_le_originalSlInH_range (hA : ∀ σ τ : A, σ * τ = τ * σ) :
    commutator (OriginalH F a A hfix) ≤ (originalSlInH F a A hfix).range := by
  rw [← modelProjection_ker, commutator_def, Subgroup.commutator_le]
  intro g _ h _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact Prod.ext (mul_comm _ _) (hA _ _)

theorem originalSlInH_commute_originalU_iff (X : SL F) :
    originalSlInH F a A hfix X * originalU F a A hfix =
        originalU F a A hfix * originalSlInH F a A hfix X ↔ X ∈ Torus F a := by
  have hM : ∀ m : M F a, (SemidirectProduct.inl m : OriginalH F a A hfix) *
      originalU F a A hfix = originalU F a A hfix * SemidirectProduct.inl m ↔
        m * u F a = u F a * m := by
    intro m
    change SemidirectProduct.inl m * SemidirectProduct.inl (u F a) =
      SemidirectProduct.inl (u F a) * SemidirectProduct.inl m ↔ _
    rw [← map_mul, ← map_mul]
    exact SemidirectProduct.inl_injective.eq_iff
  rw [show originalSlInH F a A hfix X = SemidirectProduct.inl (inclusion F a X) from rfl, hM,
    ← Subgroup.mem_centralizer_singleton_iff, matrix_centralizer_u_iff]
  rfl

theorem originalU_conj_originalSlInH (X : SL F) :
    originalU F a A hfix * originalSlInH F a A hfix X * (originalU F a A hfix)⁻¹ =
      originalSlInH F a A hfix (beta F a X) := by
  have hM : u F a * inclusion F a X * (u F a)⁻¹ = inclusion F a (beta F a X) := by
    change SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2)) *
      SemidirectProduct.inl X * (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2)))⁻¹ =
        (SemidirectProduct.inl (beta F a X) : M F a)
    rw [← map_inv, ← SemidirectProduct.inl_aut, MatrixCoverData.action_one F a]
  change SemidirectProduct.inl (u F a) * SemidirectProduct.inl (inclusion F a X) *
    (SemidirectProduct.inl (u F a))⁻¹ =
      (SemidirectProduct.inl (inclusion F a (beta F a X)) : OriginalH F a A hfix)
  rw [← map_inv, ← map_mul, ← map_mul, hM]

theorem slSemilinearAut_J_refl (X : SL F) :
    CFSG.LinearGroups.slSemilinearAut (J F a) (RingEquiv.refl F) X = beta F a X := by
  apply Subtype.ext
  change (J F a : Matrix (Fin 2) (Fin 2) F) * (X : Matrix (Fin 2) (Fin 2) F).map
      (RingEquiv.refl F) * (((J F a)⁻¹ : GL2 F) : Matrix (Fin 2) (Fin 2) F) =
    (slConjugation F (J F a) X : Matrix (Fin 2) (Fin 2) F)
  rw [slConjugation_matrix]
  congr 2

theorem originalOddInclusion_mem_range_iff (w : OriginalWProduct F A a hfix) :
    originalOddInclusion F A a hfix w ∈ (originalSlInH F a A hfix).range ↔ w.right = 1 := by
  rw [mem_originalSlInH_range_iff, originalOddInclusion_coordinates]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

theorem originalOddInclusion_inl (w : W F a) :
    originalOddInclusion F A a hfix (SemidirectProduct.inl w) =
      originalSlInH F a A hfix w.val.val := rfl

omit [Field F] in
theorem card_SL_two_congr {k k' : Type*} [Field k] [Field k'] [Finite k] [Finite k']
    (h : Nat.card k = Nat.card k') :
    Nat.card (SpecialLinearGroup (Fin 2) k) = Nat.card (SpecialLinearGroup (Fin 2) k') := by
  classical
  let _ := Fintype.ofFinite k
  let _ := Fintype.ofFinite k'
  rw [Matrix.card_SL_field, Matrix.card_SL_field, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card, h]

end

end CFSG.Semidihedral.CentralKernelTorusSplit
