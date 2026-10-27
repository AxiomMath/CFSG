module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TROne
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.McLaughlin
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem a6a_primePower_card_seven {q : TauCeti.PrimePower} (hq : q.card = 7) :
    q.p = 7 ∧ q.exponent = 1 := by
  have hdvd : q.p ∣ 7 := by
    rw [← hq, TauCeti.PrimePower.card_def]
    exact dvd_pow_self q.p (Nat.ne_of_gt q.exponent_pos)
  have h7 : q.p = 7 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hdvd with h | h
    · exact absurd h q.prime_p.ne_one
    · exact h
  have hpow : q.p ^ q.exponent = 7 := by
    rw [← TauCeti.PrimePower.card_def]
    exact hq
  rw [h7] at hpow
  exact ⟨h7, ((by norm_num : Nat.Prime 7).pow_eq_iff.mp hpow).2⟩

theorem a6a_primePower_card_three {q : TauCeti.PrimePower} (hq : q.card = 3) :
    q.p = 3 ∧ q.exponent = 1 := by
  have hdvd : q.p ∣ 3 := by
    rw [← hq, TauCeti.PrimePower.card_def]
    exact dvd_pow_self q.p (Nat.ne_of_gt q.exponent_pos)
  have h3 : q.p = 3 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
    · exact absurd h q.prime_p.ne_one
    · exact h
  have hpow : q.p ^ q.exponent = 3 := by
    rw [← TauCeti.PrimePower.card_def]
    exact hq
  rw [h3] at hpow
  exact ⟨h3, ((by norm_num : Nat.Prime 3).pow_eq_iff.mp hpow).2⟩

theorem a6a_card_isLThreeTwo {X : Type} [Group X] (hX : IsLThreeTwo X) : Nat.card X = 168 := by
  obtain ⟨d, ⟨q, hq7, hd⟩, ⟨e⟩⟩ := hX
  obtain ⟨hp, hn⟩ := a6a_primePower_card_seven hq7
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hL : IsLinTwoIndex 7 1 d := ⟨q, hd, hp, hn⟩
  have hcard : Nat.card (TauCeti.CFSGIndex.lie d).Group = 7 ^ 1 * (((7 ^ 1) ^ 2 - 1) / 2) :=
    card_catGroup_linTwo (p := 7) (n := 1) (by norm_num) (by norm_num) hL
  rw [Nat.card_congr e.toEquiv, hcard]
  norm_num

theorem a6a_pRank_top_le_one_of_card_168 {X : Type} [Group X] [Finite X]
    (h : Nat.card X = 168) : Open.pRank 3 (⊤ : Subgroup X) ≤ 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨E, -, hE, hEcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3
    Nat.prime_three (⊤ : Subgroup X)
  have h9 : 3 ^ 2 ∣ Nat.card E := by
    rw [hEcard]
    exact pow_dvd_pow 3 hlt
  have := h9.trans (Subgroup.card_subgroup_dvd_card E)
  rw [h] at this
  omega

theorem a6a_pRank_top_le_two_of_isUThreeThree {X : Type} [Group X] [Finite X]
    (hX : IsUThreeThree X) : Open.pRank 3 (⊤ : Subgroup X) ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨i, hv⟩, ⟨q, hq3, hd⟩, ⟨e⟩⟩ := hX
  have hd' : i = .twistedA 2 q := hd
  subst hd'
  obtain ⟨hp, hn⟩ := a6a_primePower_card_three hq3
  have hdU : IsUnitaryIndex 3 ⟨.twistedA 2 q, hv⟩ := ⟨q, hp, rfl⟩
  have hfe : (TauCeti.LieTypeIndex.twistedA 2 q).fieldExponent = 1 :=
    (TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q).trans hn
  have hstruct := kFactUnitarySylowStructure X 3 ⟨.twistedA 2 q, hv⟩ (by norm_num) hdU ⟨e⟩
  refine csSup_le' ?_
  rintro k ⟨E, -, hEel, hEk⟩
  by_contra hk
  push Not at hk
  have hE3 : IsPGroup 3 E := by
    intro g
    obtain ⟨-, hg⟩ := hEel
    refine ⟨1, Subtype.ext ?_⟩
    simpa using hg g.1 g.2
  obtain ⟨U, hEU⟩ := hE3.exists_le_sylow
  obtain ⟨hUcard, hUcomm, -, -⟩ := hstruct U
  have hfe' : (⟨.twistedA 2 q, hv⟩ : TauCeti.ValidLieTypeIndex).1.fieldExponent = 1 := hfe
  rw [hfe', mul_one] at hUcard
  have hle : Nat.card E ≤ Nat.card (U : Subgroup X) := Subgroup.card_le_of_le hEU
  have hk3 : k = 3 := by
    rw [hUcard, hEk] at hle
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
    omega
  have hEU' : E = (U : Subgroup X) := by
    refine Subgroup.eq_of_le_of_card_ge hEU ?_
    rw [hUcard, hEk, hk3]
  have hcomm : ∀ a ∈ (U : Subgroup X), ∀ b ∈ (U : Subgroup X), a * b = b * a := by
    intro a ha b hb
    rw [← hEU'] at ha hb
    exact hEel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩ |> congrArg Subtype.val
  have hbot : ⁅(U : Subgroup X), (U : Subgroup X)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hcomm a ha b hb).symm
  have hUc : (U : Subgroup X) ⊓ Subgroup.centralizer ((U : Subgroup X) : Set X) = U := by
    refine inf_eq_left.mpr (fun a ha => ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hcomm b hb a ha
  rw [hUc] at hUcomm
  rw [hUcomm] at hbot
  have : Nat.card (U : Subgroup X) = 1 := by
    rw [show (U : Subgroup X) = ⊥ from hbot]
    exact Subgroup.card_bot
  rw [hUcard] at this
  norm_num at this

theorem smallRankAtlas_proved : SmallRankAtlas := by
  intro X _ _ hX
  rcases hX with ⟨d, hd, ⟨e⟩⟩ | hU
  · have h168 : Nat.card X = 168 := a6a_card_isLThreeTwo ⟨d, hd, ⟨e⟩⟩
    have := a6a_pRank_top_le_one_of_card_168 h168
    omega
  · exact a6a_pRank_top_le_two_of_isUThreeThree hU

end CFSG.LocalAnalysis.RankThreeTheoremC
