module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.OrthPlus
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.Engine
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSpin

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin

section Main


theorem simpleStmt_of_orth_plus_model (hL : OrthPlusLeviOb) (hC : OrthPlusCentOb) {Y : Type}
    [Group Y] [Finite Y] (hcl : IsClassicalTwoOrG2 Y) {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaPlus n 2 f) : SimpleStmt Y := by
  obtain ⟨hadm, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have hcharP : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hn : 3 ≤ n := by have := hadm.2.2; omega
  have : NeZero n := ⟨by omega⟩
  have hq : IsQuasisimple (spinGroup (quadPlus n F)) := isQuasisimple_spinGroup_quadPlus hn
  have hqQ : IsQuasisimple (spinGroup (quadPlus n F) ⧸ Subgroup.center (spinGroup (quadPlus n F))) :=
    (isQuasisimple_of_central_quotient
      (QuotientGroup.mk' (Subgroup.center (spinGroup (quadPlus n F))))
      (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) hq).1
  have eY : Y ≃* spinGroup (quadPlus n F) ⧸ Subgroup.center (spinGroup (quadPlus n F)) :=
    e.trans (spinQuotientCenterEquivQuadPlus hn).symm
  have hsY : IsSimpleGroup Y := by
    have : IsSimpleGroup (spinGroup (quadPlus n F) ⧸ Subgroup.center (spinGroup (quadPlus n F))) :=
      hq.2.1
    exact eY.isSimpleGroup
  have hqY : CFSG.IsQuasisimple Y := isQuasisimple_of_mulEquiv eY.symm hqQ
  have hZ : Subgroup.center Y = ⊥ := center_eq_bot_of_quasisimple_simple hqY
  have : Finite (spinGroup (quadPlus n F)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus)
  have hb := borelQuotient_spinPlus hn e
  have hX := CFSG.HardMathSupport.Cooperstein.StructureLie.evenLieType_or_alt_six_or_psu_of_isClassicalTwoOrG2
    hcl
  have hrad : CFSG.Quasithin.SmithC27.IsRadicalParabolic (⊤ : Subgroup Y) :=
    CFSG.Quasithin.C22Pf.isRadicalParabolic_c224_holds Y hX
  exact simpleStmt_of_borelQuotient hqY hZ hcl hrad hb
    (fun π' hπ' I hI => hL n f F hadm hn hcard π' (fun z hz => hπ'.ker_central z hz) I hI)
    (fun I hI => hC n f F hadm hn hcard I hI)

end Main

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

end
