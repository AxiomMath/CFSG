module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutPrime
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.Chevalley
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
import CFSG.RankThree.PartOne.KF.F128Act
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutModels
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerTorusLin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerTorusUni
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsLie
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutFieldG2

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.RankThree.PartOne (centerQuotientConj)
open CFSG.RankThree.PartOne.Sec66T (innerAut lieModel_untwisted_iff untwistedTag_G2)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne.FieldFix (ChevalleySubfieldNonLocalized)

section G2


theorem overgroupLocal_of_lieModel_g2 {Y : Type} [Group Y] [Finite Y] {f : ℕ}
    (h : LieModel Y .G2 0 2 f) : OvergroupLocal Y := by
  obtain ⟨-, -, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := (lieModel_untwisted_iff untwistedTag_G2).mp h
  have := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hKcard)
  exact overgroupLocal_of_g2 e

end G2

theorem primePower_eq_of_card_eq' {q : TauCeti.PrimePower} {ℓ : ℕ} (hℓ : ℓ.Prime)
    (h : q.card = ℓ) : q.p = ℓ ∧ q.exponent = 1 := by
  rw [TauCeti.PrimePower.card_def] at h
  exact (Nat.Prime.pow_eq_iff hℓ).1 h

section Main


variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {p : ℕ} {x : Y}

theorem lieOut_of_model_g2 (hNL : ChevalleySubfieldNonLocalized) (I : LieOutInputs)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hx : x ∈ Subgroup.normalizer (L : Set Y)) (hxp : x ^ p = 1)
    (hαinn : centerQuotientConj L ⟨x, hx⟩ ∉ innerAut (↥L ⧸ Subgroup.center ↥L))
    [Nontrivial (↥L ⧸ Subgroup.center ↥L)] {f : ℕ}
    (h : LieModel (↥L ⧸ Subgroup.center ↥L) .G2 0 2 f) :
    DiagType (↥L ⧸ Subgroup.center ↥L) p ∨ LieOutConcl L x := by
  have hαp := CFSG.RankThree.PartOne.Sec66T.centerQuotientConj_pow hx hxp
  refine Or.inr ?_
  by_cases hfp : f = p
  · subst hfp
    exact I.g2 hp hp5 hx hxp hαinn h
  · exact lieOutConcl_of_fixesNonLocalized hx (overgroupLocal_of_lieModel_g2 h)
      (fixesNonLocalized_g2 hNL hp h hfp hαp hαinn)

theorem lieOut_of_index (hNL : ChevalleySubfieldNonLocalized) (I : LieOutInputs)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hx : x ∈ Subgroup.normalizer (L : Set Y)) (hxp : x ^ p = 1)
    (hαinn : centerQuotientConj L ⟨x, hx⟩ ∉ innerAut (↥L ⧸ Subgroup.center ↥L))
    [Nontrivial (↥L ⧸ Subgroup.center ↥L)] (d : TauCeti.ValidLieTypeIndex)
    (hd : IsClassicalOrG2Index d.1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group) :
    DiagType (↥L ⧸ Subgroup.center ↥L) p ∨ LieOutConcl L x := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    rw [hd] at h
    exact lieOut_of_model_psl I hp hp5 hx hxp hαinn h
  | twistedA r q =>
    change q.p = 2 at hd
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    rw [hd] at h
    exact lieOut_of_model_psu I hp hp5 hx hxp hαinn h
  | B r q =>
    change q.p = 2 at hd
    have hr := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    by_cases h2 : r = 2
    · subst h2
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
      rw [hd] at h
      exact lieOut_of_model_psp I hp hp5 hx hxp hαinn h
    · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hd
        (by omega) e
      rw [hd] at h
      exact lieOut_of_model_psp I hp hp5 hx hxp hαinn h
  | C r q => exact hd.elim
  | D r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hd e
    rw [hd] at h
    exact lieOut_of_model_pomegaPlus hp hp5 hx hxp hαinn h
  | twistedD r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hd e
    rw [hd] at h
    exact lieOut_of_model_pomegaMinus hp hp5 hx hxp hαinn h
  | G2 q =>
    change q.p = 2 at hd
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hd
    have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
      rw [TauCeti.PrimePower.card_def, GaloisField.card q.p q.exponent q.exponent_pos.ne']
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hd
      (GaloisField q.p q.exponent) hK
    have hq3 : 3 ≤ q.card :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have hcard : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hd]
    have hm : 2 ≤ q.exponent := by
      by_contra hm
      have h1 : 2 ^ q.exponent ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hL : LieModel (↥L ⧸ Subgroup.center ↥L) .G2 0 2 q.exponent :=
      (lieModel_untwisted_iff untwistedTag_G2).mpr ⟨rfl,
        CFSG.RankThree.PartOne.Sec66T.admissible_G2 hm, GaloisField q.p q.exponent, inferInstance,
        inferInstance, hK.trans hcard, ⟨e.trans b.symm⟩⟩
    exact lieOut_of_model_g2 hNL I hp hp5 hx hxp hαinn hL
  | _ => exact hd.elim


theorem lieOut_diag_or_concl (hNL : ChevalleySubfieldNonLocalized) (I : LieOutInputs)
    (hL : CFSG.Open.IsComponentOf L ⊤) (hcl : IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hx : x ∈ Subgroup.normalizer (L : Set Y)) (hxp : x ^ p = 1)
    (hxL : x ∉ L ⊔ Subgroup.centralizer (L : Set Y)) :
    DiagType (↥L ⧸ Subgroup.center ↥L) p ∨ LieOutConcl L x := by
  have hq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hperf : Group.IsPerfect ↥L := ⟨hq.1⟩
  have hsimple : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2
  have hnab : ∃ a b : ↥L ⧸ Subgroup.center ↥L, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq
  have hαinn : centerQuotientConj L ⟨x, hx⟩ ∉ innerAut (↥L ⧸ Subgroup.center ↥L) := fun h =>
    hxL ((CFSG.RankThree.PartOne.centerQuotientConj_mem_innerAut_iff hperf hx).1 h)
  have hαp := CFSG.RankThree.PartOne.Sec66T.centerQuotientConj_pow hx hxp
  have : Nontrivial (↥L ⧸ Subgroup.center ↥L) := hsimple.toNontrivial
  rcases hcl with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · exact lieOut_of_index hNL I hp hp5 hx hxp hαinn d hd e
  · exfalso
    rcases hn with rfl | rfl | rfl <;>
      exact false_of_alternating (by norm_num) hp hp5 e hαp hαinn
  · exfalso
    rcases hd with ⟨q, hq7, hd⟩ | ⟨q, hq3, hd⟩
    · obtain ⟨dd, hv⟩ := d
      simp only at hd
      subst hd
      obtain ⟨hp7, hf⟩ := primePower_eq_of_card_eq' Nat.prime_seven hq7
      have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      rw [hp7, hf] at h
      exact false_of_psl_seven hp hp5 h hαp hαinn
    · obtain ⟨dd, hv⟩ := d
      simp only at hd
      subst hd
      obtain ⟨hp3, hf⟩ := primePower_eq_of_card_eq' Nat.prime_three hq3
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      rw [hp3, hf] at h
      exact false_of_psu_three_three hp hp5 hnab h hαp hαinn

theorem kFactLieOutPrime_of_inputs (I : LieOutInputs) : KFactLieOutPrime := by
  have hNL : ChevalleySubfieldNonLocalized := fun τ hτ σ =>
    CFSG.SignalizerFunctorTheorem.NonLocalExc.nonLocalized_chevalley τ hτ σ
  intro Y _ _ L hL hcl p hp hp5 x hx hxp hxL
  rcases lieOut_diag_or_concl hNL I hL hcl hp hp5 hx hxp hxL with hdiag | hconcl
  · left
    intro T hT
    rcases hdiag with ⟨n, f, hm, hdvd⟩ | ⟨n, f, hm, hdvd⟩
    · exact CFSG.AGLEmbedding.TwoGenInner.torusLin Y L T n f p hp hp5 hL.2.2 hm hdvd hT
    · exact CFSG.AGLEmbedding.TwoGenInner.torusUni Y L T n f p hp hp5 hL.2.2 hm hdvd hT
  · exact Or.inr hconcl

end Main

end CFSG.AGLEmbedding.LieOut
