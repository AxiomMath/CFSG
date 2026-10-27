module

public import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCoverModel

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal OrthogonalTail OrthogonalSplit
open scoped commutatorElement

section Roots

variable {K : Type*} [Field K] [CharP K 2] {r : ℕ}

theorem coe_map_rootSL {i j : Fin r} (hij : i ≠ j) :
    ((Matrix.GeneralLinearGroup.map (castTwo K)
      (SpecialLinearGroup.toGL (LinearCover.rootSL (K := ZMod 2) i j)) : GL (Fin r) K) :
        Matrix (Fin r) (Fin r) K) = 1 + single i j 1 := by
  change ((LinearCover.rootSL (K := ZMod 2) i j : SpecialLinearGroup (Fin r) (ZMod 2)) :
    Matrix (Fin r) (Fin r) (ZMod 2)).map (castTwo K) = _
  rw [LinearCover.coe_rootSL_of_ne hij]
  ext a b
  simp only [transvection, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, single_apply]
  split_ifs <;> simp

theorem map_rootSL_inv (i j : Fin r) :
    (Matrix.GeneralLinearGroup.map (castTwo K)
      (SpecialLinearGroup.toGL (LinearCover.rootSL (K := ZMod 2) i j)))⁻¹ =
    Matrix.GeneralLinearGroup.map (castTwo K)
      (SpecialLinearGroup.toGL (LinearCover.rootSL (K := ZMod 2) i j)) := by
  rw [← map_inv, ← map_inv, inv_eq_of_mul_eq_one_right (LinearCover.rootSL_mul_self i j)]

variable {A : Type*} [AddCommGroup A] [Module K A] {qA : QuadraticForm K A}

theorem dMap_rootSL_eq_eichler {i j : Fin r} (hij : i ≠ j) :
    dMap (Matrix.GeneralLinearGroup.map (castTwo K)
        (SpecialLinearGroup.toGL (LinearCover.rootSL (K := ZMod 2) i j))) (1 : A ≃ₗ[K] A) =
      eichler (quadTail r qA) (hypVec K A (.inl i)) (hypVec K A (.inr j)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hneg : ∀ x : K, -x = x := fun x => by linear_combination -x * h2
  have hw : polar (quadTail r qA) (hypVec K A (.inl i)) (hypVec K A (.inr j)) = 0 := by
    rw [polar_hypVec_hypVec, Sum.swap_inl, ite_eq_right_iff]
    intro h
    exact absurd (Sum.inr_injective h).symm hij
  refine LinearEquiv.ext fun v => ?_
  rw [dMap_apply, eichler_apply (quadTail_hypVec _) hw, map_rootSL_inv, coe_map_rootSL hij,
    polar_hypVec, polar_hypVec, quadTail_hypVec, zero_mul, add_zero, Sum.swap_inl, Sum.swap_inr]
  refine Prod.ext (funext fun c => ?_) ?_
  · rcases c with k | k
    · simp only [Sum.elim_inl, add_mulVec, one_mulVec, Pi.add_apply, Prod.fst_sub,
        Prod.fst_add, Pi.sub_apply, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, hypVec,
        mulVec, dotProduct, single_apply, Function.comp_apply]
      by_cases hk : k = i
      · subst hk
        simp [sub_eq_add_neg, hneg]
      · simp [Ne.symm hk]
    · simp only [Sum.elim_inr, transpose_add, transpose_one, transpose_single, add_mulVec,
        one_mulVec, Pi.add_apply, Prod.fst_sub, Prod.fst_add, Pi.sub_apply, Prod.smul_fst,
        Pi.smul_apply, smul_eq_mul, hypVec, mulVec, dotProduct, single_apply,
        Function.comp_apply]
      by_cases hk : k = j
      · subst hk
        simp
      · simp [Ne.symm hk]
  · simp [hypVec]

theorem eichler_inl_inl_eq_uMap {i j : Fin r} (hij : i ≠ j) :
    eichler (quadTail r qA) (hypVec K A (.inl i)) (hypVec K A (.inl j)) =
      uMap qA 0 ((MatrixExtension.binaryOff i j).map (castTwo K)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hneg : ∀ x : K, -x = x := fun x => by linear_combination -x * h2
  have hw : polar (quadTail r qA) (hypVec K A (.inl i)) (hypVec K A (.inl j)) = 0 := by
    rw [polar_hypVec_hypVec, Sum.swap_inl, ite_eq_right_iff]
    intro h
    exact absurd h (by simp)
  refine LinearEquiv.ext fun v => ?_
  rw [eichler_apply (quadTail_hypVec _) hw, uMap_zero_eq, LinearEquiv.prodCongr_apply,
    uBlock_apply, polar_hypVec, polar_hypVec, quadTail_hypVec, zero_mul, add_zero, Sum.swap_inl,
    Sum.swap_inl]
  refine Prod.ext (funext fun c => ?_) ?_
  · rcases c with k | k
    · simp only [Sum.elim_inl, Pi.add_apply, Prod.fst_sub, Prod.fst_add, Pi.sub_apply,
        Prod.smul_fst, Pi.smul_apply, smul_eq_mul, hypVec, Function.comp_apply, mulVec,
        dotProduct, Matrix.map_apply, MatrixExtension.binaryOff, Matrix.add_apply, single_apply,
        map_add]
      by_cases hki : k = i
      · subst hki
        simp [hij, sub_eq_add_neg, hneg, Ne.symm hij]
      · by_cases hkj : k = j
        · subst hkj
          simp [hij, ite_mul]
        · simp [Ne.symm hki, Ne.symm hkj]
    · simp [hypVec]
  · simp [hypVec]

end Roots

section Conj

variable {K : Type*} [Field K] [CharP K 2] [Finite K] {r : ℕ}

omit [Finite K] in
theorem conj_leviB_rootSL_mem (hr : 3 ≤ r) {i j a b : Fin r} (hij : i ≠ j) (hab : a ≠ b)
    (w : orthElementaryGroup (quadTail r (minusTailForm K 1 1)))
    (hwi : (w : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] _) (hypVec K (Fin 2 → K) (.inl i)) =
      hypVec K (Fin 2 → K) (.inl a))
    (hwj : (w : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] _) (hypVec K (Fin 2 → K) (.inr j)) =
      hypVec K (Fin 2 → K) (.inl b)) :
    w * leviB K r hr (SpecialLinearGroup.toGL (LinearCover.rootSL (K := ZMod 2) i j)) * w⁻¹ ∈
      (radTau K r).range := by
  refine ⟨Multiplicative.ofAdd ⟨MatrixExtension.binaryOff a b,
    MatrixExtension.binaryOff_mem_binaryAltMatrices a b⟩, Subtype.ext ?_⟩
  rw [coe_radTau, toAdd_ofAdd, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_leviB,
    dMap_rootSL_eq_eichler hij, eichler_conj (orthElementaryGroup_le _ w.2), hwi, hwj,
    eichler_inl_inl_eq_uMap hab]

variable (K r) in
@[expose] def weylB (j : Fin r) : orthElementaryGroup (quadTail r (minusTailForm K 1 1)) :=
  ⟨shortWeyl (hypPairT r (minusTailForm K 1 1) j) ((0 : Fin r ⊕ Fin r → K), ![1, 0]),
    shortWeyl_mem _ _⟩

omit [Finite K] in
theorem weylB_hypVec (j : Fin r) (c : Fin r ⊕ Fin r) :
    ((weylB K r j : orthElementaryGroup (quadTail r (minusTailForm K 1 1))) :
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] _) (hypVec K (Fin 2 → K) c) =
      hypVec K (Fin 2 → K) (Equiv.swap (Sum.inl j) (Sum.inr j) c) :=
  shortWeyl_hypVec j binTail_one c

end Conj

section Node

variable {K : Type*} [Field K] [CharP K 2] [Finite K] (hK : Nat.card K = 2)

theorem exists_conj_rootX_zero (hr : 3 ≤ 3) :
    ∃ w, w * (binShape K 3 hK hr).rootX 0 1 * w⁻¹ ∈ (binShape K 3 hK hr).τ.range ∧
      w * (binShape K 3 hK hr).rootX 0 2 * w⁻¹ ∈ (binShape K 3 hK hr).τ.range := by
  refine ⟨weylB K 3 1 * weylB K 3 2, ?_, ?_⟩
  · refine conj_leviB_rootSL_mem hr (a := 0) (b := 1) (by decide) (by decide) _ ?_ ?_
    · rw [Subgroup.coe_mul, LinearEquiv.mul_apply, weylB_hypVec, weylB_hypVec]
      congr 1
    · rw [Subgroup.coe_mul, LinearEquiv.mul_apply, weylB_hypVec, weylB_hypVec]
      congr 1
  · refine conj_leviB_rootSL_mem hr (a := 0) (b := 2) (by decide) (by decide) _ ?_ ?_
    · rw [Subgroup.coe_mul, LinearEquiv.mul_apply, weylB_hypVec, weylB_hypVec]
      congr 1
    · rw [Subgroup.coe_mul, LinearEquiv.mul_apply, weylB_hypVec, weylB_hypVec]
      congr 1

theorem exists_conj_rootX_one (hr : 3 ≤ 3) :
    ∃ w, w * (binShape K 3 hK hr).rootX 1 2 * w⁻¹ ∈ (binShape K 3 hK hr).τ.range ∧
      w * (binShape K 3 hK hr).rootX 0 2 * w⁻¹ ∈ (binShape K 3 hK hr).τ.range := by
  refine ⟨weylB K 3 2, ?_, ?_⟩
  · refine conj_leviB_rootSL_mem hr (a := 1) (b := 2) (by decide) (by decide) _ ?_ ?_
    · rw [weylB_hypVec]
      congr 1
    · rw [weylB_hypVec]
      congr 1
  · refine conj_leviB_rootSL_mem hr (a := 0) (b := 2) (by decide) (by decide) _ ?_ ?_
    · rw [weylB_hypVec]
      congr 1
    · rw [weylB_hypVec]
      congr 1

include hK in
theorem ker_eq_bot_of_binShape_three {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (θ : E →* orthElementaryGroup (quadTail 3 (minusTailForm K 1 1)))
    (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 θ.ker) :
    θ.ker = ⊥ := by
  refine UnitaryOddCover.ker_eq_bot_of_sq_reduction (fun θ' hθ' hC' hsq' => ?_) θ hθ hC h2
  obtain ⟨U, hU, hUsurj, hUinj⟩ := Shape.exists_lift_of_three hθ' hC' hsq'
    (exists_conj_rootX_zero hK le_rfl) (exists_conj_rootX_one hK le_rfl)
  exact Shape.ker_eq_bot_of_lift hθ' hC' le_rfl hsq' U hU hUsurj hUinj

end Node

end CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover

namespace CFSG.LocalAnalysis.ComponentInitial

open NonsplitOrthogonalCover

theorem even_nonsplit_orthogonal_four_prime_field_central_two_cover_trivial {E : Type*}
    {J : Type} [Group E] [Group J] [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    (hJ : CFSG.Blueprint.LieModel J .POmegaMinus 4 2 1) :
    η.ker = ⊥ ∧ Function.Bijective η := by
  obtain ⟨K, _, _, _, hK, -, ⟨e⟩⟩ := exists_mulEquiv_of_lieModel hJ
  set η' := e.toMonoidHom.comp η with hη'
  have hker' : η'.ker = η.ker := by
    ext z
    exact e.map_eq_one_iff
  have hbot := ker_eq_bot_of_binShape_three hK η' (e.surjective.comp hη) (hker' ▸ hC)
    (hker' ▸ h2)
  rw [hker'] at hbot
  exact ⟨hbot, (MonoidHom.ker_eq_bot_iff η).mp hbot, hη⟩

end CFSG.LocalAnalysis.ComponentInitial
