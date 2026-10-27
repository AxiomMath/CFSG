module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidLinTwo
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLinearLevi
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviChoice
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviSym
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidDefs

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

section Setup

variable {G : Type} [Group G] {A : Subgroup G} {k : ℕ} {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem proj_trSL_mem_barL (hk : 2 ≤ k) (β : K) :
    proj (2 + k) K (trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) β) ∈ barL K k := by
  have hg : ((trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) β : SpecialLinearGroup (Fin (2 + k)) K) :
      Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
      blk 1 (1 + single ⟨0, by omega⟩ ⟨1, by omega⟩ β) := by
    rw [coe_trSL, ← one_add_smul_stdE hk, stdE_eq_single, smul_single, smul_eq_mul, mul_one]
    rfl
  obtain ⟨S, hS⟩ := mem_range_blkSL₂ hg
  exact ⟨S, by simp only [MonoidHom.comp_apply]; rw [hS]⟩

theorem exists_leviTheta_std (hk : 2 ≤ k) (e : rankTwoQuot A ≃* StatedProj (StatedSL (2 + k) K))
    {p : G} (hp : IsInvolutionOfRank e p 1) :
    ∃ θ : ↥A →* projectiveSL (2 + k) K, θ.ker = center ↥A ∧ Function.Surjective θ ∧
      (∀ y ∈ {y : G | (∃ j : ℕ, y ^ 2 ^ j = 1) ∧ ∃ M N : GL (Fin (2 + k)) K, Represents e p M ∧
        orderOf M = 2 ∧ Represents e y N ∧ ∃ a : K,
          (N : Matrix (Fin (2 + k)) (Fin (2 + k)) K) - 1 = a • ((M : Matrix _ _ K) - 1)},
        y ∈ liftSub θ (barL K k) ∧ ∃ j : ℕ, y ^ 2 ^ j = 1) ∧
      ∃ hpA : p ∈ A,
        θ ⟨p, hpA⟩ = proj (2 + k) K (trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) 1) := by
  obtain ⟨-, M, hpM, hM2, hr⟩ := hp
  have hN := sub_one_mul_self_eq_zero hM2
  have hrank : ((M : Matrix (Fin (2 + k)) (Fin (2 + k)) K) - 1).rank = (stdE (K := K) hk).rank := by
    rw [rank_stdE]
    exact hr
  obtain ⟨P, hP⟩ := exists_conj_of_sq_eq_zero hN (stdE_mul_self hk) hrank
  have hPP : (P : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *
      ((P⁻¹ : GL (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine ⟨conjModelHom e P, ker_conjModelHom P, conjModelHom_surjective P, ?_, ?_⟩
  · rintro y ⟨hyj, M', N, hpM', hM'2, hyN, a, ha⟩
    refine ⟨?_, hyj⟩
    obtain rfl := hpM.eq_of_orderOf_eq_two hpM' hM2 hM'2
    obtain ⟨hyA, g, hg, hgN⟩ := conjModelHom_of_represents P hyN
    refine mem_liftSub.mpr ⟨hyA, ?_⟩
    rw [hg]
    have hNeq : (N : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
        1 + a • ((M : Matrix (Fin (2 + k)) (Fin (2 + k)) K) - 1) := by
      rw [← ha, add_sub_cancel]
    have hgm : (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
        blk 1 (1 + single ⟨0, by omega⟩ ⟨1, by omega⟩ a) := by
      rw [hgN, hNeq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPP, Matrix.mul_smul,
        Matrix.smul_mul, hP, one_add_smul_stdE]
    obtain ⟨S, hS⟩ := mem_range_blkSL₂ hgm
    exact ⟨S, by simp only [MonoidHom.comp_apply]; rw [hS]⟩
  · obtain ⟨hpA, g, hg, hgM⟩ := conjModelHom_of_represents P hpM
    refine ⟨hpA, ?_⟩
    rw [hg]
    congr 1
    apply Subtype.ext
    have hM : (M : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
        1 + ((M : Matrix (Fin (2 + k)) (Fin (2 + k)) K) - 1) := by
      rw [add_sub_cancel]
    rw [hgM, hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPP, hP, stdE_eq_single,
      coe_trSL]
    rfl

end Setup

section Rigid

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {k : ℕ} {K : Type} [Field K]
  [Finite K] [CharP K 2]

omit [Finite G] in
theorem commute_of_theta_commute_of_sq {P : Type*} [Group P] {θ : ↥A →* P}
    (hker : θ.ker = center ↥A) (hodd : Odd (Nat.card (center ↥A))) {a x : ↥A} (hx2 : x ^ 2 = 1)
    (h : θ a * θ x = θ x * θ a) : a * x = x * a := by
  have hzc : ⁅a, x⁆ ∈ center ↥A := by
    rw [← hker, MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr h
  have hzx : a * x * a⁻¹ = ⁅a, x⁆ * x := by
    rw [commutatorElement_def, inv_mul_cancel_right]
  have hcomm : Commute ⁅a, x⁆ x := ((Subgroup.mem_center_iff.1 hzc) x).symm
  have hz2 : ⁅a, x⁆ ^ 2 = 1 := by
    have h1 : (a * x * a⁻¹) ^ 2 = 1 := by
      rw [sq, show a * x * a⁻¹ * (a * x * a⁻¹) = a * (x * x) * a⁻¹ by group, ← sq, hx2,
        mul_one, mul_inv_cancel]
    rw [hzx, hcomm.mul_pow, hx2, mul_one] at h1
    exact h1
  exact commutatorElement_eq_one_iff_mul_comm.mp (eq_one_of_sq_eq_one_of_mem_center hodd hzc hz2)

theorem leviRigid_linear_of (hk : 2 ≤ k) (h4 : 4 ≤ Nat.card K) {θ : ↥A →* projectiveSL (2 + k) K}
    (hθ : Function.Surjective θ) (hker : θ.ker = center ↥A) (hodd : Odd (Nat.card (center ↥A)))
    {p : G} (hpA : p ∈ A) (hp2 : p ^ 2 = 1)
    (hθp : θ ⟨p, hpA⟩ = proj (2 + k) K (trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) 1))
    {Y : Subgroup G}
    (hYc : Y ≤ liftSub θ (centralizer (barL K k : Set (projectiveSL (2 + k) K))))
    (hcore : RigidCore A p Y) : LeviRigid A p Y := by
  refine leviRigid_of_rigidCore ?_ ?_ ?_ hcore
  · exact exists_isSylowOf_le_perfectCore_of_quot hθ hker hodd hpA hp2
      (by rw [hθp]; exact exists_isSylowOf_le_perfectCore_proj hk h4)
  · exact exists_conj_of_quot hθ hker hodd hpA hp2
      (by rw [hθp]; exact fun z hz2 hS => exists_conj_eq_proj_stdT hk hz2 hS)
  · intro z hz hz2 hzX
    have h1 := map_mem_centralizer_perfectCore_of_quot hθ hker hodd hpA hp2 hz hzX
    rw [hθp] at h1
    obtain ⟨β, hβ⟩ := exists_eq_proj_trSL_of_mem_centralizer hk h4 h1
    have hz2' : (⟨z, hz⟩ : ↥A) ^ 2 = 1 := by
      have h := pow_orderOf_eq_one (⟨z, hz⟩ : ↥A)
      rwa [Subgroup.orderOf_mk, hz2] at h
    intro y hy
    rw [mem_centralizer_singleton_iff]
    obtain ⟨hyA, hyθ⟩ := mem_liftSub.mp (hYc hy)
    have h2 : θ ⟨y, hyA⟩ * θ ⟨z, hz⟩ = θ ⟨z, hz⟩ * θ ⟨y, hyA⟩ := by
      rw [hβ]
      exact (mem_centralizer_iff.mp hyθ _ (proj_trSL_mem_barL hk β)).symm
    exact congrArg Subtype.val (commute_of_theta_commute_of_sq hker hodd hz2' h2)

end Rigid

theorem rigidLeviChoice_linear : RigidLeviChoiceFor .linear := by
  intro G _ _ A D hD hA hZ hq p hp
  cases D with
  | linear n m hn hm hnm K hK e =>
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 + k := ⟨n - 2, by omega⟩
    have hm2 : 2 ≤ m := by
      have hq' : 2 ^ 2 ≤ 2 ^ m := hq
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hq'
    have hk : 2 ≤ k := by omega
    have : CharP K 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have := Fintype.ofFinite K
      exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
    have h4' : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    have h4 : ∃ s : Finset K, s.card = 4 := by
      have : Fintype K := Fintype.ofFinite K
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
        (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4')
      exact ⟨s, hs⟩
    have hp' : IsInvolutionOfRank e p 1 := hp
    have hp2 : p ^ 2 = 1 := by rw [← hp'.1, pow_orderOf_eq_one]
    obtain ⟨θ, hker, hθ, hα, hpA, hθp⟩ := exists_leviTheta_std hk e hp'
    rcases (show k = 2 ∨ 3 ≤ k by omega) with rfl | hk3
    ·
      obtain ⟨c, hc⟩ := exists_unit_ne_one h4
      have hYc : liftSub θ (barT K) ⊔ leviW θ ≤
          liftSub θ (centralizer (barL K 2 : Set (projectiveSL (2 + 2) K))) :=
        sup_le (liftSub_mono barT_le_centralizer_barL)
          (levLift_le_liftSub.trans (liftSub_mono barW_le_centralizer_barL))
      refine ⟨leviW θ, liftSub θ (barT K) ⊔ leviW θ,
        leviChoice_linear_of hn hm hnm hK e hZ hm2 hker hθ hα le_sup_right hYc
          (noInv_two hA.1 hker hθ h4 hc) ?_ ?_ ?_, ?_⟩
      · intro h
        have h' : 2 + 2 = 5 ∧ m = 2 := h
        omega
      · intro _ σ _ hfix
        exact outerFree_two hker hθ h4 hc σ hfix
      · intro h
        have h' : 2 + 2 = 4 ∧ m = 2 := h
        have hK4 : Nat.card K = 4 := by rw [hK, h'.2]; norm_num
        exact sym_two_four hA.1 hker hθ hZ hK4 h4
      · exact leviRigid_linear_of le_rfl h4' hθ hker hZ hpA hp2 hθp hYc
          (rigidCore_linear_two h4' h4 hm2 hK hθ hker hZ hA.1 hpA hp2 hθp)
    ·
      have hYc : leviW θ ≤ liftSub θ (centralizer (barL K k : Set (projectiveSL (2 + k) K))) :=
        levLift_le_liftSub.trans (liftSub_mono barW_le_centralizer_barL)
      refine ⟨leviW θ, leviW θ,
        leviChoice_linear_of hn hm hnm hK e hZ hm2 hker hθ hα le_rfl hYc
          (noInv_of_three_le hA.1 hker hθ h4 hk3) ?_ ?_ ?_, ?_⟩
      · intro h
        have h' : 2 + k = 5 ∧ m = 2 := h
        obtain rfl : k = 3 := by omega
        have hK4 : Nat.card K = 4 := by rw [hK, h'.2]; norm_num
        exact diag_five_four hker hθ h4 hK4
      · intro h
        have h' : 2 + k = 4 ∧ m = 2 := h
        omega
      · intro h
        have h' : 2 + k = 4 ∧ m = 2 := h
        omega
      · exact leviRigid_linear_of hk h4' hθ hker hZ hpA hp2 hθp hYc
          (rigidCore_leviW_of_three_le hk hk3 h4' h4 hm2 hK hθ hker hZ hpA hp2 hθp)
  | unitary => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

end CFSG.ComponentClassification.RankTwoClassical
