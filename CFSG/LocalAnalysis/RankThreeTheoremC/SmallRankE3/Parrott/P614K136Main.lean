module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614R3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K136Basis
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K136Bender
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K136Torus

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open Subgroup
open scoped MatrixGroups

namespace P614K136

@[expose] noncomputable def equivOfIff {G G' : Type*} [Group G] [Group G'] (τ : G ≃* G')
    {H : Subgroup G} {H' : Subgroup G'} (h : ∀ x, x ∈ H ↔ τ x ∈ H') : H ≃* H' :=
  (τ.subgroupMap H).trans (MulEquiv.subgroupCongr (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (h x).1 hx
    · intro hy
      refine ⟨τ.symm y, (h _).2 ?_, τ.apply_symm_apply y⟩
      rwa [τ.apply_symm_apply]))

theorem lthree_case {K : Type} [Group K] [Finite K] {n : ℕ} (hn : Odd n) (hn3 : 3 ≤ n)
    (e : K ≃* PSL(3, GaloisField 2 n)) {R : Subgroup K} (hR : IsPGroup 2 R) (hR1 : R ≠ ⊥)
    (hRi : 2 ∣ R.index) (hRc : pCoreOf 2 (normalizer (R : Set K)) = R) {f : ℕ} (hf : f.Prime)
    (hfd : f ∣ 2 ^ n - 1) :
    f ∣ Nat.card (CFSG.pLayer ↥(normalizer (R : Set K)) 3) ∧
      2 ≤ CFSG.Open.pRank f (⊤ : Subgroup K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hF3 : ∀ a : GaloisField 2 n, a ^ 3 = 1 → a = 1 := fun a ha =>
    eq_one_of_pow_three hn hcardF ha
  let σ : K ≃* SL(3, GaloisField 2 n) := e.trans (pslEquivSL hF3)
  have hfd' : f ∣ Nat.card (GaloisField 2 n) - 1 := by rwa [hcardF]
  refine ⟨?_, two_le_pRank σ hf hfd'⟩
  have h4 : 4 ≤ Nat.card (GaloisField 2 n) := by
    rw [hcardF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hfSL : f ∣ Nat.card SL(2, GaloisField 2 n) :=
    (hfd'.trans (by rw [Nat.card_units])).trans (card_units_dvd_card_SL2 _)
  rcases exists_parabolic σ hR hR1 hRi hRc with ⟨τ, hτ⟩ | ⟨τ, hτ⟩
  · exact hfSL.trans (card_SL2_dvd_pLayer_A h4 (equivOfIff τ hτ))
  · exact hfSL.trans (card_SL2_dvd_pLayer_B h4 (equivOfIff τ hτ))

theorem kFactBenderTI_holds : KFactBenderTI := by
  intro K _ _ hB T T' hTT'
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl : ∀ S : Sylow 2 K, CFSG.ABGLocalTools.IsSylowOf 2 (S : Subgroup K) ⊤ := fun S =>
    CFSG.ABGLocalTools.isSylowOf_iff.2
      ⟨le_top, S.isPGroup', by rw [Subgroup.relIndex_top_right]; exact S.not_dvd_index⟩
  by_contra hne
  exact hTT' (CFSG.CGT.PushingUpLit.C2L.StrongTI.bender_sylow_inf_eq_bot hB (hsyl T) (hsyl T')
    fun h => hne (Sylow.ext h))

end P614K136

open P614K136 in
theorem kFact136Three_of_rankOne (h : KFactChevTwoRankOneThree) : KFact136Three := by
  intro K _ _ hs hna hc hr R hR hR1 hRi hRc _h3
  by_cases hB : CFSG.Open.fusionIsBenderGroup K
  · exact (false_of_bender hB hR hR1 hRi hRc).elim
  obtain ⟨n, hn, ⟨e⟩⟩ := h K hs hna hc hr hB
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · have hn1 : n = 1 := by
      obtain ⟨k, rfl⟩ := hn
      omega
    subst hn1
    exact Or.inl ⟨e.trans pslThreeTwoEquivGL32⟩
  · right
    have hne : 2 ^ n - 1 ≠ 1 := by
      have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
      omega
    obtain ⟨f, hf, hfd⟩ := Nat.exists_prime_and_dvd hne
    have hf2 : f ≠ 2 := by
      rintro rfl
      have hodd : Odd (2 ^ n - 1) := by
        have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        exact Nat.Even.sub_odd this (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hfd)
    have hf3 : f ≠ 3 := by
      rintro rfl
      exact not_three_dvd_two_pow_sub_one hn hfd
    obtain ⟨hlay, hrk⟩ := lthree_case hn hn3 e hR hR1 hRi hRc hf hfd
    exact ⟨f, hf, hf2, hf3, hlay, hrk⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
