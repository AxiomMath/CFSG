module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291SCField
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291N1Unit
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291R3ExDef
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291R3ExThree
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossLinearOne
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossLinearThree
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossSuzuki
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294SporRankFive

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup TauCeti
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt)
open CFSG.AGLEmbedding (CatalogSimpleSections)

set_option linter.unusedSectionVars false

section CertificateInstances


theorem kdR3_false_of_sporadic {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {S : Type} [Group S] [Finite S]
    (s : SporadicName) (e : S ≃* (CFSGIndex.sporadic s).Group)
    (hmp : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup S)) {x : S} (hxo : orderOf x = p)
    (hxc : CFSG.Open.pRank p (centralizer ({x} : Set S)) ≤ 2) : False :=
  absurd (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.sporadicCentralizerRank_holds
    s p hp hp5 S ⟨e⟩ (by omega) x hxo) (by omega)

theorem kdR3_false_of_lie {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hlu : ¬ IsLinearOrUnitaryAt p S) (d : ValidLieTypeIndex)
    (e : S ≃* (CFSGIndex.lie d).Group) (hm3 : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 1)
    (hmp : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup S)) {x : S} (hxo : orderOf x = p)
    (hxc : CFSG.Open.pRank p (centralizer ({x} : Set S)) ≤ 2) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hxp : x ^ p = 1 := hxo ▸ pow_orderOf_eq_one x
  have h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup S) := by omega
  rcases three_rank_le_one_lie d e hm3 with ⟨q, hq3, hdq⟩ | ⟨q, hq3, hdq⟩ | ⟨q, hq3, hdq⟩ |
    ⟨m, hdm⟩
  ·
    obtain ⟨d, hv⟩ := d
    obtain rfl : d = .A 1 q := hdq
    by_cases hch : q.p = p
    · subst hch
      haveI : Fact q.p.Prime := ⟨q.prime_p⟩
      obtain ⟨eP⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (p := q.p)
        (n := q.exponent) (d := ⟨.A 1 q, hv⟩) ⟨q, rfl, rfl, rfl⟩
      exact absurd (three_le_pRank_centralizer_of_psl2GF q.exponent_pos (e.trans eP) h3 hxp)
        (by omega)
    · exact absurd ((crossAt_linearOne hv).2 p hp hp5 (by simpa using hch) S hs ⟨e⟩ hlu h3 x hxo)
        (by omega)
  ·
    obtain ⟨d, hv⟩ := d
    obtain rfl : d = .A 2 q := hdq
    by_cases hch : q.p = p
    · subst hch
      haveI : Fact q.p.Prime := ⟨q.prime_p⟩
      obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ :=
        CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
      exact absurd (three_le_pRank_centralizer_of_statedSL_three q.exponent_pos hK eK hmp hxp)
        (by omega)
    · exact absurd ((crossAt_linearTwo hv).2 p hp hp5 (by simpa using hch) S hs ⟨e⟩ hlu h3 x hxo)
        (by omega)
  ·
    obtain ⟨d, hv⟩ := d
    obtain rfl : d = .twistedA 2 q := hdq
    by_cases hch : q.p = p
    · subst hch
      haveI : Fact q.p.Prime := ⟨q.prime_p⟩
      obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ :=
        CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      exact absurd (three_le_pRank_centralizer_of_statedSU_three (by omega) q.exponent_pos hK eK
        hmp hxp) (by omega)
    · exact absurd ((crossAt_unitaryTwo hv).2 p hp hp5 (by simpa using hch) S hs ⟨e⟩ hlu h3 x hxo)
        (by omega)
  ·
    obtain ⟨d, hv⟩ := d
    obtain rfl : d = .suzuki m := hdm
    exact absurd ((crossAt_suzuki hv).2 p hp hp5 (by simp; omega) S hs ⟨e⟩ hlu h3 x hxo)
      (by omega)

theorem kdR3_false_of_all_in_simple {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {Y : Type} [Group Y]
    [Finite Y] (S : Subgroup Y) [S.Normal] (hs : IsSimpleGroup S)
    (hn : ∃ a b : S, a * b ≠ b * a) (hc : IsCatalogGroup S) (hlu : ¬ IsLinearOrUnitaryAt p S)
    (hC : centralizer (S : Set Y) = ⊥) (hm3 : CFSG.Open.pRank 3 S ≤ 1)
    (hmp : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup Y)) (hall : ∀ y : Y, orderOf y = p → y ∈ S)
    {x : Y} (hxo : orderOf x = p) (hxc : CFSG.Open.pRank p (centralizer ({x} : Set Y)) ≤ 2) :
    False := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hs
  have hp1 : 1 < p := hp.one_lt
  have hxS : x ∈ S := hall x hxo
  have hEL : ∀ E : Subgroup Y, IsElemAbelian p E → E ≤ S := by
    intro E hE y hy
    by_cases hy1 : y = 1
    · rw [hy1]
      exact S.one_mem
    · exact hall y (orderOf_eq_prime (hE.2 y hy) hy1)
  have hmpS : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup S) :=
    hmp.trans (pRank_top_le_pRank_top_of_forall_le S hEL)
  have hm3S : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 1 := by
    rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  have hxo' : orderOf (⟨x, hxS⟩ : S) = p := by
    rw [← hxo, ← Subgroup.orderOf_coe]
  have hxc' : CFSG.Open.pRank p (centralizer ({(⟨x, hxS⟩ : S)} : Set S)) ≤ 2 := by
    refine le_trans ?_ hxc
    refine (CFSG.SectionRank.pRank_le_map hp1 S.subtype S.subtype_injective _).trans
      (CFSG.SectionRank.pRank_mono hp1 ?_)
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ centralizer ({(⟨x, hxS⟩ : S)} : Set S) := hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy'
    exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hy')
  obtain ⟨i, ⟨e⟩⟩ := id hc
  cases i with
  | cyclic r hr =>
    obtain ⟨a, b, hab⟩ := hn
    exact hab (e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _))
  | alternating n hn5 => exact i294Alt_false hp hp5 S hn hn5 e hC (by omega) hxS hxo hxc
  | sporadic s => exact kdR3_false_of_sporadic hp hp5 s e hmpS hxo' hxc'
  | lie d => exact kdR3_false_of_lie hp hp5 hs hlu d e hm3S hmpS hxo' hxc'

theorem kdR3Exclusion_holds : KDR3Exclusion := by
  intro p hp hp5 Y _ _ hcat _ S hSn hs hn hC hm3 hmp ⟨x, hxo, hxc⟩
  haveI := hSn
  haveI := hs
  haveI : Fact p.Prime := ⟨hp⟩
  have hcatS : IsCatalogGroup S := hcat.simple_subgroup S hs hn
  have hlu : ¬ IsLinearOrUnitaryAt p S := by
    intro h
    have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) :=
      I291.linUniE9_of_uniE9 I291.uniE9_holds hp5 S h hn
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h2
    omega
  by_cases hall : ∀ y : Y, orderOf y = p → y ∈ S
  · exact (kdR3_false_of_all_in_simple hp hp5 S hs hn hcatS hlu hC hm3 hmp hall hxo hxc).elim
  · push Not at hall
    obtain ⟨y, hyo, hyS⟩ := hall
    have hyp : IsPGroup p (zpowers y) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo, pow_one])
    obtain ⟨P, hP⟩ := hyp.exists_le_sylow
    refine exists_index_prime_of_focal_ne P fun hF => hyS ?_
    have hle := focalSubgroup_le_of_kdInndiag kdInndiagP5_holds hp hp5 S hs hn hcatS hlu hC P
    rw [hF] at hle
    exact hle (hP (mem_zpowers y))

end CertificateInstances

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
