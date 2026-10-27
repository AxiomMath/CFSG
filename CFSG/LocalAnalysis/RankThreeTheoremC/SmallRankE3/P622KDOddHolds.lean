module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KDDefs
public import CFSG.GH74.Uniqueness.Gamma
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFactsBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open Subgroup

theorem kFactFieldAutOddAt_holds
    (p : ℕ) (hp2' : p ≠ 2) : KFactFieldAutOddAt p := by
  intro J _ _ α U hp hα hpn hs hna hK hU hfix
  haveI : IsSimpleGroup J := hs
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnonab : ∃ a b : J, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hna h
  have hU' := CFSG.ABGLocalTools.isSylowOf_iff.mp hU
  have hUidx : ¬ 2 ∣ U.index := by
    have h := hU'.2.2
    rwa [Subgroup.relIndex_top_right] at h
  let S : Sylow 2 J := hU'.2.1.toSylow hUidx
  have hSU : (S : Subgroup J) = U := rfl
  by_contra hne
  have hΓ : Open.properTwoGenCoreGamma (S : Subgroup J) 1 ≠ ⊤ := by
    intro htop
    apply hne
    rw [eq_top_iff, ← htop]
    refine iSup_le fun Q => iSup_le fun hQ => iSup_le fun h1 g hg => ?_
    refine Subgroup.subset_closure (Set.mem_iUnion₂.mpr ⟨Q, ⟨hSU ▸ hQ, ?_⟩, hg⟩)
    intro hbot
    obtain ⟨E, hEQ, -, hcard⟩ :=
      CFSG.RankThreeCoreUniqueness.Helpers.pRank_attained 2 Q (by omega)
    have hE : E = ⊥ := le_bot_iff.mp (hbot ▸ hEQ)
    rw [hE, Subgroup.card_bot] at hcard
    have h2 : 2 ^ 1 ≤ 2 ^ Open.pRank 2 Q := Nat.pow_le_pow_right (by norm_num) h1
    omega
  have hrk : 2 ≤ Open.twoRank J :=
    CFSG.Milestones.lr_nonabelian_simple_two_rank_lower_bound J hnonab
      (CFSG.GH74.even_card_of_nonabelian_simple hnonab)
  have hSrk : Open.pRank 2 (S : Subgroup J) = Open.twoRank J :=
    (CFSG.SectionRank.pRank_sylow S).1
  have hSE := CFSG.GH74.Uniqueness.isStronglyEmbedded_gamma_one S (by omega) hΓ
  have hBender := CFSG.BenderSuzuki.bender_suzuki _
    (CFSG.GH74.Uniqueness.isStronglyEmbeddedOrder_of_isStronglyEmbedded hSE)
  obtain ⟨c, hcS, -, hαc⟩ :=
    CFSG.ComponentClassification.Asc76X.exists_eq_conj_of_forall_apply_eq hBender S α
      (fun x hx => hfix x hx)
  obtain ⟨k, hk⟩ := (S.isPGroup' ) ⟨c, hcS⟩
  have hck : c ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hαk : α ^ 2 ^ k = 1 := by
    rw [hαc, ← map_pow, hck, map_one]
  have hdvd : p ∣ 2 ^ k := hα ▸ orderOf_dvd_of_pow_eq_one hαk
  have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow hdvd
  have := Nat.le_of_dvd (by norm_num) hp2
  have := hp.two_le
  omega

theorem kFactFieldAutOddAt_three_holds :
    KFactFieldAutOddAt 3 :=
  kFactFieldAutOddAt_holds 3 (by norm_num)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
