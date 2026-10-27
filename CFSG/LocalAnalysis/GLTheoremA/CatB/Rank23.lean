module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Transport
public import CFSG.LocalAnalysis.GLTheoremA.CatB.RankFineSp
public import CFSG.LocalAnalysis.GLTheoremA.CatB.RankFineU
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U42
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U52
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreExcOut
public import CFSG.LargeExtraspecial.OutSix
public import CFSG.GF2Type.ModelPSU
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Sporadic.Schreier.Co1WeightChar

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

section Centres

variable {G : Type} [Group G] [Finite G]

theorem center_pQuot_eq_bot_sp6two (hGA : CFSG.Open.GriessAllModelsStatement) {J : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (PQuot 3 J)) (h : catalogIs (PSimple 3 J) S9.isSp6two) :
    Subgroup.center (PQuot 3 J) = ⊥ := by
  obtain ⟨q, hv, hq2, ⟨e⟩⟩ := lieIndex_isSp6two h
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq2.trans (by norm_num))
  rcases CFSG.Models.lieModel_B 3 q hv e with hm | hm
  · rw [h1, h2] at hm
    have hdvd := card_center_dvd_of_table hGA hq hm (a := 1) (b := 1) (c := 2) (d := 1)
      (by decide) (by decide) (by norm_num)
    by_contra hne
    haveI : Nontrivial (Subgroup.center (PQuot 3 J)) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact false_of_pGroup_dvd Nat.prime_three
      (CFSG.LocalAnalysis.GLTheoremA.I2611.isPGroup_center_pQuot' Nat.prime_three J) hdvd
      (by norm_num)
  · rw [h1, h2] at hm
    exact absurd hm.admissible.2.2.2 (by norm_num)

theorem center_pQuot_eq_bot_d4two (hGA : CFSG.Open.GriessAllModelsStatement) {J : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (PQuot 3 J)) (h : catalogIs (PSimple 3 J) S9.isD4two) :
    Subgroup.center (PQuot 3 J) = ⊥ := by
  obtain ⟨q, hv, hq2, ⟨e⟩⟩ := lieIndex_isD4two h
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq2.trans (by norm_num))
  have hm := CFSG.Models.lieModel_D 4 q hv e
  rw [h1, h2] at hm
  have hdvd := card_center_dvd_of_table hGA hq hm (a := 1) (b := 1) (c := 2) (d := 2)
    (by decide) (by decide) (by norm_num)
  by_contra hne
  haveI : Nontrivial (Subgroup.center (PQuot 3 J)) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  exact false_of_pGroup_dvd Nat.prime_three
    (CFSG.LocalAnalysis.GLTheoremA.I2611.isPGroup_center_pQuot' Nat.prime_three J) hdvd
    (by norm_num)

theorem center_pQuot_eq_bot_list94 (hGA : CFSG.Open.GriessAllModelsStatement) {J : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (PQuot 3 J)) (h : catalogIs (PSimple 3 J) S9.isList94) :
    Subgroup.center (PQuot 3 J) = ⊥ := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with h | h | h | h
  · exact center_pQuot_eq_bot_sp6two hGA hq ⟨i, h, ⟨e⟩⟩
  · exact center_pQuot_eq_bot_u4two hGA hq ⟨i, h, ⟨e⟩⟩
  · exact center_pQuot_eq_bot_d4two hGA hq ⟨i, h, ⟨e⟩⟩
  · exact center_pQuot_eq_bot_u5two hGA hq ⟨i, h, ⟨e⟩⟩

end Centres


section Outer

theorem not_three_dvd_outer_sp6two {S : Type} [Group S] (h : catalogIs S S9.isSp6two) :
    ¬ 3 ∣ Nat.card (Outer S) := by
  obtain ⟨q, hv, hq2, ⟨e⟩⟩ := lieIndex_isSp6two h
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq2.trans (by norm_num))
  rcases CFSG.Models.lieModel_B 3 q hv e with hm | hm
  · rw [h1, h2] at hm
    have := CFSG.ComponentClassification.Foote5.card_outer_eq_one_of_psp_three_two
      (hm.statedClassicalModel (by decide))
    rw [this]
    norm_num
  · rw [h1, h2] at hm
    exact absurd hm.admissible.2.2.2 (by norm_num)

theorem nonempty_equiv_timmesfeldPSU {S : Type} [Group S] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) (hq2 : q.card = 2)
    (e : S ≃* ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩) :
    Nonempty (S ≃* CFSG.Open.timmesfeldPSU (r + 1)) := by
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq2.trans (by norm_num))
  have hm := lieModel_twistedA' r q hv e
  rw [h1, h2] at hm
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hm.statedClassicalModel (by decide)
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hc : Fintype.card K = Fintype.card (GaloisField 2 2) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 2 2 (by norm_num)]
    norm_num
  exact ⟨(e'.trans (CFSG.Open.StatedSUFieldChange.statedProjSUEquiv
    (FiniteField.ringEquivOfCardEq hc) (r + 1) (2 ^ 1))).trans
    (CFSG.GF2Type.timmesfeldPSUEquivStatedProj (r + 1)).symm⟩

theorem not_three_dvd_outer_u4two {S : Type} [Group S] (h : catalogIs S S9.isU4two) :
    ¬ 3 ∣ Nat.card (Outer S) := by
  obtain ⟨q, hv, hq2, ⟨e⟩⟩ := lieIndex_isU4two h
  obtain ⟨e'⟩ := nonempty_equiv_timmesfeldPSU 3 q hv hq2 e
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv,
    CFSG.LargeExtraspecial.S14.card_outer_timmesfeldPSU (by norm_num)]
  norm_num

theorem not_three_dvd_outer_u5two {S : Type} [Group S] (h : catalogIs S S9.isU5two) :
    ¬ 3 ∣ Nat.card (Outer S) := by
  obtain ⟨q, hv, hq2, ⟨e⟩⟩ := lieIndex_isU5two h
  obtain ⟨e'⟩ := nonempty_equiv_timmesfeldPSU 4 q hv hq2 e
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv,
    CFSG.LargeExtraspecial.S14.card_outer_timmesfeldPSU (by norm_num)]
  norm_num

end Outer


section Assembly

variable {G : Type} [Group G] [Finite G]

theorem rank23At_of_rankFine (hGA : CFSG.Open.GriessAllModelsStatement)
    (h_sp : RankFine CFSG.Sporadic.Co2Smith.Sp62 9)
    (h_u4 : RankFine (StatedProj (StatedSU 4 2 K4)) 9)
    (h_d4 : RankFine CFSG.AGLEmbedding.Om8 27)
    (h_u5 : RankFine (StatedProj (StatedSU 5 2 K4)) 27) : Rank23At G := by
  intro X L hL hcat
  have hq := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hL
  have hZ := center_pQuot_eq_bot_list94 hGA hq hcat
  have eZ : PSimple 3 L ≃* PQuot 3 L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨hZ, ?_, ?_⟩
  ·
    intro b hb hb3 hnot
    have hinner : (∀ α : MulAut (PQuot 3 L), α ^ 3 = 1 → α ∈ inner (PQuot 3 L)) →
        False := fun hall => hnot (inducesInnerMod_of_inner hb (hall _ (barAut_pow_three L b hb hb3)))
    obtain ⟨i, hi, ⟨e⟩⟩ := hcat
    rcases hi with h | h | h | h
    · exact (hinner fun α hα => forall_cube_inner_of_card_outer
        (not_three_dvd_outer_sp6two ((catalogIs_congr eZ).1 ⟨i, h, ⟨e⟩⟩)) α hα).elim
    · exact (hinner fun α hα => forall_cube_inner_of_card_outer
        (not_three_dvd_outer_u4two ((catalogIs_congr eZ).1 ⟨i, h, ⟨e⟩⟩)) α hα).elim
    · exact ⟨i, h, ⟨e⟩⟩
    · exact (hinner fun α hα => forall_cube_inner_of_card_outer
        (not_three_dvd_outer_u5two ((catalogIs_congr eZ).1 ⟨i, h, ⟨e⟩⟩)) α hα).elim
  ·
    intro E T hEL hE hTL hT hTN hET
    have sp : ∀ (h : catalogIs (PSimple 3 L) S9.isSp6two), Nat.card E ≤ 9 := fun h => by
      obtain ⟨e⟩ := bridge_sp6two h
      exact rankFine_transport (eZ.symm.trans e) h_sp E T hEL hE hTL hT hTN hET
    have u4 : ∀ (h : catalogIs (PSimple 3 L) S9.isU4two), Nat.card E ≤ 9 := fun h => by
      obtain ⟨q, hv, hq2, ⟨e0⟩⟩ := lieIndex_isU4two h
      obtain ⟨e1⟩ := nonempty_equiv_timmesfeldPSU 3 q hv hq2 e0
      exact rankFine_transport
        (eZ.symm.trans (e1.trans (CFSG.GF2Type.timmesfeldPSUEquivStatedProj 4))) h_u4 E T hEL hE
        hTL hT hTN hET
    have d4 : ∀ (h : catalogIs (PSimple 3 L) S9.isD4two), Nat.card E ≤ 27 := fun h => by
      obtain ⟨e⟩ := bridge_d4two h
      exact rankFine_transport (eZ.symm.trans e) h_d4 E T hEL hE hTL hT hTN hET
    have u5 : ∀ (h : catalogIs (PSimple 3 L) S9.isU5two), Nat.card E ≤ 27 := fun h => by
      obtain ⟨q, hv, hq2, ⟨e0⟩⟩ := lieIndex_isU5two h
      obtain ⟨e1⟩ := nonempty_equiv_timmesfeldPSU 4 q hv hq2 e0
      exact rankFine_transport
        (eZ.symm.trans (e1.trans (CFSG.GF2Type.timmesfeldPSUEquivStatedProj 5))) h_u5 E T hEL hE
        hTL hT hTN hET
    refine ⟨?_, ?_⟩
    · obtain ⟨i, hi, ⟨e⟩⟩ := hcat
      rcases hi with h | h | h | h
      · exact (sp ⟨i, h, ⟨e⟩⟩).trans (by norm_num)
      · exact (u4 ⟨i, h, ⟨e⟩⟩).trans (by norm_num)
      · exact d4 ⟨i, h, ⟨e⟩⟩
      · exact u5 ⟨i, h, ⟨e⟩⟩
    · rintro ⟨i, hi, ⟨e⟩⟩
      rcases hi with h | h
      · exact sp ⟨i, h, ⟨e⟩⟩
      · exact u4 ⟨i, h, ⟨e⟩⟩

end Assembly


section Models

theorem rankFine_sp62 : RankFine CFSG.Sporadic.Co2Smith.Sp62 9 := by
  simpa using rankFine_statedSp_two 3

end Models

section Holds


theorem rank23At_holds (G : Type) [Group G] [Finite G] : Rank23At G :=
  rank23At_of_rankFine CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    rankFine_sp62 rankFine_u4 rankFine_om8 rankFine_u5

end Holds

end CFSG.LocalAnalysis.GLTheoremA.CatB
