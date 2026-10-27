module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263CITD4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.FR.Res

section Cell


theorem t263CaseIxTD4_holds : T263CaseIxTD4 := by
  intro p hp hp2 Ω _ _ hK S B hSn hSq hSp hSc hp3 hTD4 hF2 hSB hΩ hB h4 hT B₀ hB₀ hdich hCc hB₀c hBc b hb hbB₀
    hlay
  subst hp3
  exfalso
  classical
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hBel : CFSG.Open.IsElemAbelian 3 B := hB.1
  have hbp : b ^ 3 = 1 := hBel.2 b hb
  have hbN : b ∈ Subgroup.normalizer (S : Set Ω) := t263_normalizer_of_normal hSn
  have hcomp : GLAPComponent 3 S S := glaPComponent_self_p hSq hSp
  have e₆ : PSimple 3 S ≃* ↥S ⧸ Subgroup.center ↥S := pSimpleEquiv hSp
  have hchev : IsChevSimple 2 (PSimple 3 S) := by
    unfold IsChevSimple at hSc ⊢
    rcases hSc with h | h
    · exact Or.inl ((catalogIs_congr e₆).2 h)
    · exact Or.inr ((catalogIs_congr e₆).2 h)
  have hnon : NonInnDiag 3 b S := ⟨hbN, fun hin => hbB₀ (hB₀.2.2.2.1 b hb hin)⟩
  have hNI : NonInner 3 b S :=
    ⟨hbN, fun h1 => hnon.2 (MI.inner_innDiag_any hcomp hchev hbN h1)⟩
  obtain ⟨q, hv, ⟨eS⟩⟩ := td4_index' hTD4
  have hq2 : q.p = 2 := by
    by_contra hne
    exact td4_odd_false' hv hne eS hchev
  rcases Nat.lt_or_ge q.exponent 2 with hf1 | hf2
  ·
    have hexp : q.exponent = 1 := by
      have := q.exponent_pos
      omega
    have hLM : CFSG.Blueprint.LieModel (PSimple 3 S) .trialityD4 0 2 1 := by
      have := td4_blueprint_model' hv eS
      rwa [hq2, hexp] at this
    have hLM' : CFSG.Blueprint.LieModel (↥S ⧸ Subgroup.center ↥S) .trialityD4 0 2 1 :=
      CFSG.StandardType.lieModel_of_mulEquiv' e₆ hLM
    refine hF2 rfl ?_
    refine CFSG.StandardType.Canonical.largeEvenMarking_mono ?_
      (CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hSq.1 hLM')
    intro lab R _ I F θ hlab
    obtain ⟨-, -, hc, hd⟩ := hlab
    exact t263_n_eq_one_of_mark hc hd
  ·
    obtain ⟨E, hEC, hEs, hEna, hperf, hpE⟩ := t263CI_td4_core3 hbN hcomp hbp hNI hv hq2 hf2 eS
    haveI := hEs
    exact t263CI_layer_ne_bot_of_perfect_core hp hp2 hSp hbN hbp hEna hEC hperf hpE hlay

end Cell

end CFSG.LocalAnalysis.GLTheoremA.T263

end
