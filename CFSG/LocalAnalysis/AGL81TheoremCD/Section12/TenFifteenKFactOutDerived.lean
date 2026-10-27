module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TenFifteenKFacts
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TenFifteenKFactOutGroup
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TenFifteenKFactSmall
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerIndex
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerD4
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerTorusLin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerTorusUni
public import CFSG.LocalAnalysis.RankThreeUC.GN15JOutOdd

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.AGLEmbedding CFSG.AGLEmbedding.TwoGenInner CFSG.Open CFSG.QuasithinUnique
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem dvd_card_normalizer_of_equiv {Y : Type*} [Group Y] [Finite Y] {T : Subgroup Y}
    (hT : IsSylowTwoOf T ⊤) {A : Type*} [Group A] (e : Y ≃* A) {m : ℕ}
    (hm : ∀ Q : Sylow 2 A, m ∣ Nat.card ↥(Subgroup.normalizer (Q : Set A))) :
    m ∣ Nat.card ↥(Subgroup.normalizer (T : Set Y)) := by
  let E : ↥(⊤ : Subgroup Y) ≃* A := Subgroup.topEquiv.trans e
  have h1 : m ∣ Nat.card ↥(Subgroup.normalizer
      ((((sylowOfIsSylowTwoOf hT : Sylow 2 ↥(⊤ : Subgroup Y)) : Subgroup ↥(⊤ : Subgroup Y)).map
        E.toMonoidHom : Subgroup A) : Set A)) :=
    hm (Sylow.mapSurjective (f := E.toMonoidHom) E.surjective (sylowOfIsSylowTwoOf hT))
  rwa [card_normalizer_map_equiv E, coe_sylowOfIsSylowTwoOf, ← card_inf_normalizer_eq hT.1,
    top_inf_eq] at h1

theorem not_dvd_gcd_of_model_psl {Y : Type} [Group Y] [Finite Y] {d n f : ℕ} (hd : d.Prime)
    (hd5 : 5 ≤ d) {T : Subgroup Y} (hT : IsSylowTwoOf T ⊤)
    (hN : ¬ d ∣ Nat.card (Subgroup.normalizer (T : Set Y)))
    (h : StatedClassicalModel Y .PSL n 2 f) : ¬ d ∣ Nat.gcd n (2 ^ f - 1) := by
  intro hdvd
  obtain ⟨⟨_, _, hn2, _⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hpn : d ∣ n := hdvd.trans (Nat.gcd_dvd_left _ _)
  have hpq : d ∣ 2 ^ f - 1 := hdvd.trans (Nat.gcd_dvd_right _ _)
  have hn5 : 5 ≤ n := hd5.trans (Nat.le_of_dvd (by omega) hpn)
  let e₁ := e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm
  let e₂ := e₁.trans
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)
  exact hN (dvd_card_normalizer_of_equiv hT e₂ fun Q => torusLin_model hK hd hpq (by omega) Q)

theorem not_dvd_gcd_of_model_psu {Y : Type} [Group Y] [Finite Y] {d n f : ℕ} (hd : d.Prime)
    (hd5 : 5 ≤ d) {T : Subgroup Y} (hT : IsSylowTwoOf T ⊤)
    (hN : ¬ d ∣ Nat.card (Subgroup.normalizer (T : Set Y)))
    (h : StatedClassicalModel Y .PSU n 2 f) : ¬ d ∣ Nat.gcd n (2 ^ f + 1) := by
  intro hdvd
  obtain ⟨⟨_, hf, hn3, _⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hpn : d ∣ n := hdvd.trans (Nat.gcd_dvd_left _ _)
  have hpq : d ∣ 2 ^ f + 1 := hdvd.trans (Nat.gcd_dvd_right _ _)
  have hn5 : 5 ≤ n := hd5.trans (Nat.le_of_dvd (by omega) hpn)
  exact hN (dvd_card_normalizer_of_equiv hT e fun Q => torusUni_model hK hf hd hd5 hpq hn5 Q)

section Odd

open CFSG.LocalAnalysis.RankThreeUC.S15.GN15


theorem odd_card_commutator_outer_of_isClassicalTwoOrG2 {Y : Type} [Group Y] [Finite Y]
    (h : IsClassicalTwoOrG2 Y) : Odd (Nat.card (commutator (Outer Y))) := by
  rcases h with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨⟨d1, hv⟩, hd, ⟨e⟩⟩
  · exact JOutOdd.odd_card_commutator_outer_of_lie_index d hd e
  · exact CFSG.GH74.Generic.S45.odd_card_commutator_of_isMulCommutative
      (CFSG.ComponentClassification.CatalogueSchreierAlternating.commutative_of_card_le_four
        (card_outer_le_four_of_mulEquiv_alternating (by omega) e))
  · rcases hd with ⟨q, hq, hd1⟩ | ⟨q, hq, hd1⟩
    · simp only at hd1
      subst hd1
      have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      have hq' : q.p ^ q.exponent = 7 := by rw [← TauCeti.PrimePower.card_def]; exact hq
      obtain ⟨hp7, he1⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).mp hq'
      rw [hp7, he1] at h
      exact JOutOdd.odd_card_commutator_outer_of_psl_two_seven h
    · simp only at hd1
      subst hd1
      exact JOutOdd.odd_card_commutator_outer_of_u33 q hv hq e

end Odd

section Main


theorem pGoodOut_of_not_dvd_card_normalizer {Y : Type} [Group Y] [Finite Y] {d : ℕ}
    (hd : d.Prime) (hd5 : 5 ≤ d) (h : IsClassicalTwoOrG2 Y) {T : Subgroup Y}
    (hT : IsSylowTwoOf T ⊤) (hN : ¬ d ∣ Nat.card (Subgroup.normalizer (T : Set Y))) :
    PGoodOut d Y :=
  pGoodOut_of_isClassicalTwoOrG2 hd hd5 h (fun hm => not_dvd_gcd_of_model_psl hd hd5 hT hN hm)
    (fun hm => not_dvd_gcd_of_model_psu hd hd5 hT hN hm) d4PGood

theorem kFactLieOutDerived_holds : KFactLieOutDerived := by
  rintro Y _ _ - hY d hd hd5 ⟨T, hT, hN⟩
  have h2 := odd_card_commutator_outer_of_isClassicalTwoOrG2 hY
  have hdd := not_dvd_card_commutator_outer_of_pGoodOut hd
    (pGoodOut_of_not_dvd_card_normalizer hd hd5 hY hT hN)
  exact Nat.Coprime.mul_right (Nat.coprime_two_right.2 h2)
    ((Nat.Prime.coprime_iff_not_dvd hd).2 hdd).symm

end Main

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
