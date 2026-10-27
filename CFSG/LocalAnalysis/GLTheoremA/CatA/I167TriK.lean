module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167TriS
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144OutHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144FieldConj
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144Transfer
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsUni
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsSympA6
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsOrth
import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblyAll

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10F
  (HasLabel hasLabel_centerQuot center_centerQuot_eq_bot centerQuotAut)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (InnDiagKind FieldKind)

set_option linter.unusedSectionVars false


theorem false_of_triality_K {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    (hchev : IsChevSimple 2 (K ⧸ Subgroup.center K)) {α : MulAut K} (hα : α ^ 3 = 1)
    (hnInn : ¬ K144.I144Inner K α)
    (hnFld : ¬ GLAMarking K (fun lab _ _ I F θ =>
      GLAPrimeField 3 lab I F (GLAInduces θ fun x y => α x = y)))
    {Jb : Subgroup (K ⧸ Subgroup.center K)}
    (hJ : GLAPComponent 3 (fixSubgroup (centerQuotAut K α)) Jb)
    (hcat : Type167Grp 3 (PSimple 3 Jb)) : False := by
  have hmark : HasLabel K (fun _ : GLALabel => True) :=
    CFSG.StandardType.ChevTwo.ys08_holds K hq hchev
  obtain ⟨labK, -, hlabK⟩ := K144.exists_label_of_hasLabel hmark
  have hcen : Subgroup.center (K ⧸ Subgroup.center K) = ⊥ := center_centerQuot_eq_bot hq
  have hlabS : HasLabel (K ⧸ Subgroup.center K) (fun l : GLALabel => l = labK) :=
    hasLabel_centerQuot hlabK
  have hβ3 : centerQuotAut K α ^ 3 = 1 := by rw [← map_pow, hα, map_one]
  have hcls := CFSG.LocalAnalysis.GLTheoremA.Y10GField.cls_of_families
    CFSG.LocalAnalysis.GLTheoremA.Y10GField.ClsLin_holds
    CFSG.LocalAnalysis.GLTheoremA.Y10GField.ClsUni_holds
    CFSG.LocalAnalysis.GLTheoremA.Y10GField.ClsSymp_holds
    CFSG.LocalAnalysis.GLTheoremA.Y10GClsOrth.clsOrth_holds
    CFSG.LocalAnalysis.GLTheoremA.Y10GClsExc.clsExc_holds
    (K ⧸ Subgroup.center K) 3 (centerQuotAut K α) labK Nat.prime_three (by norm_num) hcen hlabS hβ3
  have hnin : ¬ InnDiagKind (K ⧸ Subgroup.center K) labK (centerQuotAut K α) :=
    fun h => hnInn (K144.inner_of_innDiagKind hq h)
  rcases hcls with hin | hfld | ⟨htag, hrk, -⟩
  · exact hnin hin
  · by_cases htd : labK.tag = .triD4
    · exact out167_triD4_false CFSG.StandardType.ggLabelRigidInput_holds
        CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent
        CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds hcen hlabS htd hβ3 hfld hJ hcat
    · exact hnFld (K144.primeField_of_fieldKind hq hα htd hfld)
  · by_cases hfld : FieldKind (K ⧸ Subgroup.center K) labK (centerQuotAut K α)
    · exact hnFld (K144.primeField_of_fieldKind hq hα (by rw [htag]; decide) hfld)
    · exact out167_D4_false CFSG.StandardType.ggLabelRigidInput_holds
        CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent
        CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds hcen hlabS htag hrk hβ3 hnin
        hfld hJ hcat

end CFSG.LocalAnalysis.GLTheoremA.I167

end
