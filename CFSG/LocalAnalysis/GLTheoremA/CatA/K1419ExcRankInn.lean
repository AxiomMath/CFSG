module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OutG2
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OutTriD4
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OutReeF4
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.ExcPlaneG2Three
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcThreeSplit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open TauCeti CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived mem_innAutDerived_congr)
open CFSG.ComponentClassification.OuterAutomorphisms renaming inner → innerAut
open CFSG.RankThree.PartTwo.KFacts (isInnerAut_congr)
open CFSG.HardMathSupport.Dickson.Sec6.I1431

theorem l3u3Rank_mem_inner_of_equiv {S P : Type} [Group S] [Group P] (e : S ≃* P)
    (h : innAutDerived P ≤ innerAut P) {β : MulAut S}
    (hβ : β ∈ innAutDerived S) : β ∈ innerAut S :=
  (isInnerAut_congr e β).1 (h ((mem_innAutDerived_congr e).2 hβ))

section Tri


theorem l3u3Rank_g2 {S : Type} [Group S] (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid)
    (hq : q.p = 2) (e : S ≃* (CFSGIndex.lie ⟨.G2 q, hv⟩).Group) :
    innAutDerived S ≤ innerAut S ∧ RankLE2 3 S := by
  obtain ⟨K, _, _, hK, hKc, ⟨eK⟩⟩ := exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
  have hKchar : ringChar K = 2 := by
    have : CharP K 2 := hq ▸ hKc
    exact ringChar.eq K 2
  have hq3 : 3 ≤ q.card :=
    (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have hqeven : 2 ∣ q.card := by
    rw [PrimePower.card_def, hq]
    exact dvd_pow_self 2 q.exponent_pos.ne'
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    omega
  refine ⟨fun β hβ => l3u3Rank_mem_inner_of_equiv (e.trans eK)
    (t6outg2_innAutDerived_le_inner (by omega) hK4) hβ, ?_⟩
  exact RankLE2.of_mulEquiv e.symm
    (CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.rankLE2_three_cat_G2 q hv (by omega))

theorem l3u3Rank_triD4 {S : Type} [Group S] (q : PrimePower)
    (hv : (LieTypeIndex.trialityD4 q).Valid) (hq : q.p = 2)
    (e : S ≃* (CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) :
    innAutDerived S ≤ innerAut S ∧ RankLE2 3 S := by
  have hm : LieModel (Cat ⟨.trialityD4 q, hv⟩) .trialityD4 0 q.p q.exponent :=
    Or.inr (Or.inl ⟨rfl, by decide, chevalleyModel_cat_trialityD4 hv⟩)
  refine ⟨fun β hβ => t6outtrid4_isInnerAut_of_mem_innAutDerived (LieModel.of_mulEquiv e.symm hm)
    hβ, ?_⟩
  exact RankLE2.of_mulEquiv e.symm
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_trialityD4 q hv (by omega))

end Tri

section Ree


theorem l3u3Rank_reeF4 {S : Type} [Group S] {m : ℕ} (hv : (LieTypeIndex.reeF4 m).Valid)
    (e : S ≃* (CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group) :
    innAutDerived S ≤ innerAut S ∧ RankLE2 3 S :=
  ⟨fun β hβ => l3u3Rank_mem_inner_of_equiv e
    (t6outreef4_innAutDerived_le_inner (reeTitsModel_cat_reeF4 hv)) hβ,
    RankLE2.of_mulEquiv e.symm
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_reeF4 hv)⟩

end Ree

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
