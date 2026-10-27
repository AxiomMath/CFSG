module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviRootSL2Sp
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionTypeExceptions
public import CFSG.Monster.Existence.Compat.Sp8

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix Equiv Equiv.Perm CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras TauCeti.GLSymplecticFin
open CFSG.ComponentClassification.PresentationLocal (sympFour omegaPerm omegaPerm_injective
  omegaPerm_surjective rootInvolutionA rootInvolutionB rootInvolutionC rootInvolutionD
  omegaPerm_rootInvolutionA omegaPerm_rootInvolutionB omegaPerm_rootInvolutionC
  omegaPerm_rootInvolutionD)
open CFSG.ComponentClassification.StandardRecognition (symplecticIndex symplecticToSympFour
  symplecticToSympFour_bijective)
open CFSG.Monster.Existence.Compat (statedSpEquiv sympMapEquiv ringEquivZMod2)

section Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem cycleType_eq_replicate_of_orderOf_eq_three {σ : Perm α} (h : orderOf σ = 3) :
    σ.cycleType = Multiset.replicate (σ.support.card / 3) 3 := by
  obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (h ▸ Nat.prime_three)
  rw [h] at hn
  have hsum := Perm.sum_cycleType σ
  rw [hn, Multiset.sum_replicate, smul_eq_mul] at hsum
  rw [hn, ← hsum, Nat.mul_div_cancel _ (by norm_num)]

theorem isConj_of_orderOf_eq_three_of_card_support_eq {σ τ : Perm α} (hσ : orderOf σ = 3)
    (hτ : orderOf τ = 3) (h : σ.support.card = τ.support.card) : IsConj σ τ := by
  rw [isConj_iff_cycleType_eq, cycleType_eq_replicate_of_orderOf_eq_three hσ,
    cycleType_eq_replicate_of_orderOf_eq_three hτ, h]

end Perm

theorem card_support_finSix_of_orderOf_eq_three {σ : Perm (Fin 6)} (h : orderOf σ = 3) :
    σ.support.card = 3 ∨ σ.support.card = 6 := by
  obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (h ▸ Nat.prime_three)
  rw [h] at hn
  have hsum := Perm.sum_cycleType σ
  rw [hn, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hle : σ.support.card ≤ 6 := by simpa using σ.support.card_le_univ
  omega

theorem isConj_finSix_of_orderOf_eq_three {σ : Perm (Fin 6)} (h : orderOf σ = 3) :
    IsConj (swap 2 3 * swap 2 4) σ ∨
      IsConj ((swap 0 1 * swap 2 4 * swap 3 5) * (swap 0 5 * swap 1 4 * swap 2 3)) σ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : orderOf (swap (2 : Fin 6) 3 * swap 2 4) = 3 :=
    orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  have h2 : orderOf ((swap (0 : Fin 6) 1 * swap 2 4 * swap 3 5) *
      (swap 0 5 * swap 1 4 * swap 2 3)) = 3 :=
    orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  have c1 : (swap (2 : Fin 6) 3 * swap 2 4).support.card = 3 := by decide +kernel
  have c2 : ((swap (0 : Fin 6) 1 * swap 2 4 * swap 3 5) *
      (swap 0 5 * swap 1 4 * swap 2 3)).support.card = 6 := by decide +kernel
  rcases card_support_finSix_of_orderOf_eq_three h with h' | h'
  · exact Or.inl (isConj_of_orderOf_eq_three_of_card_support_eq h1 h (c1.trans h'.symm))
  · exact Or.inr (isConj_of_orderOf_eq_three_of_card_support_eq h2 h (c2.trans h'.symm))

variable {K : Type} [Field K]

theorem coe_statedSpEquiv_eq_mat (n : ℕ) (x : StatedSp n K) :
    ((statedSpEquiv n K x : Matrix.symplecticGroup (Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = mat n K x := by
  conv_rhs => rw [← (statedSpEquiv n K).symm_apply_apply x]
  rfl

theorem map_E_of_ringHomClass {K' : Type} [Field K'] {F : Type*} [FunLike F K K']
    [RingHomClass F K K'] (f : F) {n : ℕ} (r : RootSubgroupIndex n) :
    (E K r).map f = E K' r := by
  ext a b
  cases r <;> simp only [E, Matrix.map_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.single_apply] <;> split_ifs <;> simp

section Equiv

variable [Finite K] (hK : Nat.card K = 2)

@[expose] noncomputable def sp4EquivSympFour : StatedSp 2 K ≃* sympFour :=
  (statedSpEquiv 2 K).trans ((sympMapEquiv (ringEquivZMod2 hK)).trans
    (MulEquiv.ofBijective symplecticToSympFour symplecticToSympFour_bijective))

theorem coe_sp4EquivSympFour (x : StatedSp 2 K) :
    (((sp4EquivSympFour hK x : sympFour) : GL (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      reindex symplecticIndex symplecticIndex ((mat 2 K x).map (ringEquivZMod2 hK)) := by
  rw [← coe_statedSpEquiv_eq_mat]
  rfl

theorem coe_sp4EquivSympFour_elt (r : RootSubgroupIndex 2) :
    (((sp4EquivSympFour hK (elt r 1) : sympFour) : GL (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      reindex symplecticIndex symplecticIndex (1 + E (ZMod 2) r) := by
  rw [coe_sp4EquivSympFour, mat_elt, one_smul, Matrix.map_add _ (map_add _),
    Matrix.map_one _ (map_zero _) (map_one _), map_E_of_ringHomClass]

theorem sp4EquivSympFour_elt_long :
    sp4EquivSympFour hK (elt (.positiveLong 1) 1) = rootInvolutionA :=
  Subtype.ext (Units.ext (by rw [coe_sp4EquivSympFour_elt]; decide +kernel))

theorem sp4EquivSympFour_elt_long_neg :
    sp4EquivSympFour hK (elt (.negativeLong 1) 1) = rootInvolutionB :=
  Subtype.ext (Units.ext (by rw [coe_sp4EquivSympFour_elt]; decide +kernel))

theorem sp4EquivSympFour_elt_short :
    sp4EquivSympFour hK (elt (.difference 0 1 (by decide)) 1) = rootInvolutionC :=
  Subtype.ext (Units.ext (by rw [coe_sp4EquivSympFour_elt]; decide +kernel))

theorem sp4EquivSympFour_elt_short_neg :
    sp4EquivSympFour hK (elt (.difference 1 0 (by decide)) 1) = rootInvolutionD :=
  Subtype.ext (Units.ext (by rw [coe_sp4EquivSympFour_elt]; decide +kernel))

@[expose] noncomputable def sp4EquivPerm : StatedSp 2 K ≃* Perm (Fin 6) :=
  (sp4EquivSympFour hK).trans
    (MulEquiv.ofBijective omegaPerm ⟨omegaPerm_injective, omegaPerm_surjective⟩)

theorem sp4EquivPerm_apply (x : StatedSp 2 K) :
    sp4EquivPerm hK x = omegaPerm (sp4EquivSympFour hK x) :=
  rfl

theorem sp4EquivPerm_elt_long : sp4EquivPerm hK (elt (.positiveLong 1) 1) = swap 2 3 := by
  rw [sp4EquivPerm_apply, sp4EquivSympFour_elt_long, omegaPerm_rootInvolutionA]

theorem sp4EquivPerm_elt_long_neg : sp4EquivPerm hK (elt (.negativeLong 1) 1) = swap 2 4 := by
  rw [sp4EquivPerm_apply, sp4EquivSympFour_elt_long_neg, omegaPerm_rootInvolutionB]

theorem sp4EquivPerm_elt_short :
    sp4EquivPerm hK (elt (.difference 0 1 (by decide)) 1) = swap 0 1 * swap 2 4 * swap 3 5 := by
  rw [sp4EquivPerm_apply, sp4EquivSympFour_elt_short, omegaPerm_rootInvolutionC]

theorem sp4EquivPerm_elt_short_neg :
    sp4EquivPerm hK (elt (.difference 1 0 (by decide)) 1) = swap 0 5 * swap 1 4 * swap 2 3 := by
  rw [sp4EquivPerm_apply, sp4EquivSympFour_elt_short_neg, omegaPerm_rootInvolutionD]

end Equiv

theorem elt_mul_elt_negIdx_mem_spRootSL2 {n : ℕ} {v : Fin n → ℤ} {r : RootSubgroupIndex n}
    (hr : stdVec r = toStd n v) (c d : K) : elt r c * elt (negIdx r) d ∈ spRootSL2 n K v :=
  mul_mem (mem_sup_left (elt_mem_rootGroup hr c))
    (mem_sup_right (elt_mem_rootGroup (by rw [stdVec_negIdx, hr, toStd_neg']) d))

theorem exists_isSpRootSL2_mem_of_eq_conj {n : ℕ} {v : Fin n → ℤ} {r : RootSubgroupIndex n}
    (hr : stdVec r = toStd n v) {y g : StatedSp n K}
    (hy : g * (elt r 1 * elt (negIdx r) 1) * g⁻¹ = y) :
    ∃ H : Subgroup (StatedSp n K), IsSpRootSL2 n K H ∧ y ∈ H :=
  ⟨(spRootSL2 n K v).map (MulAut.conj g).toMonoidHom, ⟨v, mem_roots_of_stdVec hr, g, rfl⟩,
    _, elt_mul_elt_negIdx_mem_spRootSL2 hr 1 1, hy⟩

theorem exists_isSpRootSL2_mem_of_orderOf_eq_three (hK : Nat.card K = 2) {y : StatedSp 2 K}
    (hy : orderOf y = 3) : ∃ H : Subgroup (StatedSp 2 K), IsSpRootSL2 2 K H ∧ y ∈ H := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  set E := sp4EquivPerm hK with hE
  have hEy : orderOf (E y) = 3 := by rw [MulEquiv.orderOf_eq]; exact hy
  have key : ∀ {r : RootSubgroupIndex 2} {v : Fin 2 → ℤ}, stdVec r = toStd 2 v →
      IsConj (E (elt r 1 * elt (negIdx r) 1)) (E y) →
        ∃ H : Subgroup (StatedSp 2 K), IsSpRootSL2 2 K H ∧ y ∈ H := by
    intro r v hr hc
    obtain ⟨c, hc⟩ := isConj_iff.1 hc
    refine exists_isSpRootSL2_mem_of_eq_conj hr (g := E.symm c) (E.injective ?_)
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hc]
  rcases isConj_finSix_of_orderOf_eq_three hEy with h | h
  · refine key (r := .positiveLong 1) (v := ![0, 1]) (by decide) ?_
    change IsConj (E (elt (.positiveLong 1) 1 * elt (.negativeLong 1) 1)) (E y)
    rwa [map_mul, hE, sp4EquivPerm_elt_long, sp4EquivPerm_elt_long_neg]
  · refine key (r := .difference 0 1 (by decide)) (v := ![1, 0]) (by decide) ?_
    change IsConj (E (elt (.difference 0 1 (by decide)) 1 * elt (.difference 1 0 (by decide)) 1))
      (E y)
    rwa [map_mul, hE, sp4EquivPerm_elt_short, sp4EquivPerm_elt_short_neg]

end CFSG.SeitzReduction.F4Pilot
