module

public import CFSG.CGT.PushingUpLit.SolKAb.Setup
public import CFSG.RankThree.GF2n.Tim78Thm1Gold
import CFSG.CGT.T75N.BenderCenter
import CFSG.CGT.T75N.UnitaryTwoGen

public section

namespace CFSG.CGT.PushingUpLit.SolKAb

open CFSG CFSG.RankThree.GF2n.Tim78
open CFSG.Open (IsElemAbelian)
open CFSG.RankThree.PartTwo (omegaOneSub)

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

omit [Finite G] in
theorem isElemAbelian_of_card_two {A : Subgroup G} (hc : IsCommSubgroup A)
    (h : Nat.card ↥A = 2) : IsElemAbelian 2 A := by
  refine ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, fun x hx => ?_⟩
  have h1 : orderOf x ∣ 2 := by
    have := Subgroup.orderOf_dvd_natCard A hx
    rwa [h] at this
  exact orderOf_dvd_iff_pow_eq_one.mp h1

theorem omegaOne_card_cases {A : Subgroup G} (hc : IsCommSubgroup A) (h2 : IsPGroup 2 A)
    (hA : A ≠ ⊥) :
    Nat.card ↥(omegaOneSub A) = 2 ∨ Nat.card ↥(omegaOneSub A) = 4 ∨
      8 ≤ Nat.card ↥(omegaOneSub A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ2 : IsPGroup 2 (omegaOneSub A) := h2.to_le (CFSG.RankThree.PartTwo.omegaOneSub_le A)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hΩ2
  have hne : omegaOneSub A ≠ ⊥ := by
    intro hbot
    have hdvd : 2 ∣ Nat.card ↥A := by
      rcases h2.card_eq_or_dvd with h1 | h1
      · exact absurd (Subgroup.eq_bot_of_card_eq A h1) hA
      · exact h1
    let _ : Fintype ↥A := Fintype.ofFinite _
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 2 (by rwa [Nat.card_eq_fintype_card] at hdvd)
    have hx2 : x ^ 2 = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hx] at this
    have hxx : (x : G) * x = 1 := by
      have := congrArg Subtype.val hx2
      simpa [sq] using this
    have hx1 : (x : G) ≠ 1 := by
      intro h1
      have : x = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hx
      omega
    have hmem : (x : G) ∈ omegaOneSub A := (mem_omegaOneSub_iff hc).mpr ⟨x.2, hxx⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hx1 hmem
  have hk0 : k ≠ 0 := by
    intro h0
    apply hne
    apply Subgroup.eq_bot_of_card_eq
    rw [hk, h0]; rfl
  rcases (show k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | h3
  · left; simpa using hk
  · right; left; simpa using hk
  · right; right
    rw [hk]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h3

theorem isCyclic_of_card_omegaOne_two {A : Subgroup G} (hc : IsCommSubgroup A)
    (h2 : IsPGroup 2 A) (hn : Nat.card ↥(omegaOneSub A) = 2) : IsCyclic ↥A := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ∀ x y : ↥A, x * y = y * x := fun x y => Subtype.ext (hc x x.2 y y.2)
  let _ : Fintype ↥A := Fintype.ofFinite _
  have hΩ : (Finset.univ.filter fun y : ↥A => y ^ 2 = 1).card ≤ 2 := by
    have hinj : Function.Injective (fun y : {y : ↥A // y ^ 2 = 1} =>
        (⟨(y.1 : G), (mem_omegaOneSub_iff hc).mpr ⟨y.1.2, by
          have := congrArg Subtype.val y.2
          simpa [sq] using this⟩⟩ : ↥(omegaOneSub A))) := by
      intro y z h
      exact Subtype.ext (Subtype.ext (congrArg (Subtype.val : ↥(omegaOneSub A) → G) h))
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [hn] at h1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h1
    exact h1
  have key : ∀ k : ℕ, (Finset.univ.filter fun a : ↥A => a ^ 2 ^ k = 1).card ≤ 2 ^ k := by
    intro k
    induction k with
    | zero =>
      have : (Finset.univ.filter fun a : ↥A => a ^ 2 ^ 0 = 1) = {1} := by
        ext a; simp
      rw [this]; simp
    | succ k ih =>
      have himg : (Finset.univ.filter fun a : ↥A => a ^ 2 ^ (k + 1) = 1).image (fun a => a ^ 2) ⊆
          Finset.univ.filter fun a : ↥A => a ^ 2 ^ k = 1 := by
        intro b hb
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
        rw [← pow_mul, ← pow_succ']; exact ha
      have hfib : ∀ b ∈ (Finset.univ.filter fun a : ↥A => a ^ 2 ^ (k + 1) = 1).image
          (fun a => a ^ 2),
          ((Finset.univ.filter fun a : ↥A => a ^ 2 ^ (k + 1) = 1).filter
            fun a => a ^ 2 = b).card ≤ 2 := by
        intro b hb
        obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.mp hb
        refine le_trans (Finset.card_le_card_of_injOn (fun a => a₀⁻¹ * a) ?_ ?_) hΩ
        · intro a ha
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha ⊢
          have h1 : a ^ 2 = a₀ ^ 2 := ha.2
          rw [Commute.mul_pow (hcomm _ _), inv_pow, h1, inv_mul_cancel]
        · intro a _ a' _ h
          exact mul_left_cancel h
      calc (Finset.univ.filter fun a : ↥A => a ^ 2 ^ (k + 1) = 1).card
          ≤ 2 * ((Finset.univ.filter fun a : ↥A => a ^ 2 ^ (k + 1) = 1).image
              (fun a => a ^ 2)).card := Finset.card_le_mul_card_image _ 2 hfib
        _ ≤ 2 * (Finset.univ.filter fun a : ↥A => a ^ 2 ^ k = 1).card :=
            Nat.mul_le_mul_left 2 (Finset.card_le_card himg)
        _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (k + 1) := by ring
  apply isCyclic_of_card_pow_eq_one_le
  intro n hn0
  obtain ⟨k, m, hm, hnk⟩ := Nat.exists_eq_two_pow_mul_odd hn0.ne'
  have hsub : (Finset.univ.filter fun a : ↥A => a ^ n = 1) ⊆
      Finset.univ.filter fun a : ↥A => a ^ 2 ^ k = 1 := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp h2) a
    have hd : 2 ^ j ∣ 2 ^ k * m := by rw [← hj, ← hnk]; exact orderOf_dvd_of_pow_eq_one ha
    have hcop : Nat.Coprime (2 ^ j) m := Nat.Coprime.pow_left _ ((Nat.coprime_two_left).mpr hm)
    have hd' : 2 ^ j ∣ 2 ^ k := hcop.dvd_of_dvd_mul_right hd
    have : orderOf a ∣ 2 ^ k := by rw [hj]; exact hd'
    exact orderOf_dvd_iff_pow_eq_one.mp this
  calc (Finset.univ.filter fun a : ↥A => a ^ n = 1).card
      ≤ (Finset.univ.filter fun a : ↥A => a ^ 2 ^ k = 1).card := Finset.card_le_card hsub
    _ ≤ 2 ^ k := key k
    _ ≤ n := by rw [hnk]; exact Nat.le_mul_of_pos_right _ hm.pos

theorem STSetting.hypH (S : STSetting G K) (R : Sylow 2 K) (h : IsCommSubgroup (sylowImg R)) :
    HypH (Subgroup.normalizer (K : Set G)) (sylowImg R) := by
  have := S.simple
  exact
    { o2 := pCore_two_eq_bot_of_simple_of_nonabelian S.nonab
      max := S.max
      fstar := (isCharacteristicP_iff_generalizedFitting_eq_pCore _ 2).mp S.isCharacteristicP
      le := (Subgroup.map_subtype_le _).trans Subgroup.le_normalizer
      normal := (S.normalizer_sylowImg_eq R h).ge
      comm := h
      ti := S.isTI_sylowImg R h }

section T78


theorem STSetting.isElemAbelian_sylowImg_of_eight_le (S : STSetting G K) (R : Sylow 2 K)
    (h : IsCommSubgroup (sylowImg R)) (h8 : 8 ≤ Nat.card ↥(omegaOneSub (sylowImg R))) :
    IsElemAbelian 2 (sylowImg R) :=
  CFSG.RankThree.GF2n.Tim78.tim78_theorem1_of_eight_le' CFSG.CGT.T75N.benderCenterInput
    CFSG.CGT.T75N.unitaryTwoGenerationInput (S.hypH R h) h8

theorem STSetting.nonempty_omegaTwoSub_equiv_of_card_omegaOne_four (S : STSetting G K)
    (R : Sylow 2 K) (h : IsCommSubgroup (sylowImg R)) (hne : ¬ IsElemAbelian 2 (sylowImg R))
    (h4 : Nat.card ↥(omegaOneSub (sylowImg R)) = 4) :
    Nonempty (↥(omegaTwoSub (sylowImg R)) ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) := by
  by_contra hno
  have hCen := CFSG.CGT.T75N.benderCenterInput
  have hU := CFSG.CGT.T75N.unitaryTwoGenerationInput
  have H := S.hypH R h
  have hne' : omegaOneSub (sylowImg R) ≠ sylowImg R := by
    intro heq
    apply hne
    refine ⟨⟨⟨fun a b => Subtype.ext (H.comm _ a.2 _ b.2)⟩⟩, fun x hx => ?_⟩
    rw [← heq] at hx
    rw [sq]
    exact ((mem_omegaOneSub_iff H.comm).mp hx).2
  have hUV : omegaOneSub (omegaTwoSub (sylowImg R)) = omegaOneSub (sylowImg R) :=
    omegaOneSub_omegaTwoSub H.comm
  have S3 : S3Hyp (Subgroup.normalizer (K : Set G)) (omegaTwoSub (sylowImg R)) :=
    { max := H.max
      fstar := H.fstar
      le := le_trans (omegaTwoSub_le _) H.le
      normal := H.le_normalizer_omegaTwo
      comm := comm_omegaTwoSub H.comm
      two := H.two.to_le (omegaTwoSub_le _)
      ti := isTI_omegaTwoSub H.comm H.ti
      exp := fun x hx => pow_four_of_mem_omegaTwoSub H.comm hx
      ne := omegaOneSub_omegaTwoSub_ne H.comm H.two hne'
      card4 := by rw [hUV, h4] }
  have hS : SigmaComm (omegaOneSub (omegaTwoSub (sylowImg R))) :=
    sigmaComm_of_elem fun R' hR' => by
      rcases tim78_3_1_of_isPGroup hCen hU S3.comm S3.two S3.ti S3.exp S3.ne
        (by rw [hUV, h4]) hR' with h1 | ⟨hc, -⟩
      · exact h1
      · exact absurd hc hno
  exact S3.false_of_sigmaComm goldschmidtInput hCen hU H.o2 hS

end T78

end CFSG.CGT.PushingUpLit.SolKAb
