module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.Combinator
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.SectionXExists
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.WpGMain
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.StrayTwoSec
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.Trichotomy
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLHolds
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwConjX
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwCaseI
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwCaseA10
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwCaseHS
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwKhatG
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwCaseL44

public section

set_option linter.unusedSectionVars false

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern CFSG.OddStandard.AltStdBal
  CFSG.Blueprint

open scoped commutatorElement


theorem swapFrameP2Two_of_inputs (hFus : TwHSFusion) : SwapFrameP2Two := by
  intro G _ _ L Q z h d ι F hP2 hp
  have hC : CentData z ι := F.cent
  have hx : IsConj z (ι τ₀) := F.conj
  obtain ⟨Sg, V, hshape, hAbar⟩ := exists_swapShape_twoSec hC hx hP2
  have hO := twoSec_oddCore_eq_bot h hC
  have hKg := twoSec_isKGroupCat h hC
  have hStray := hStray_twoSec_holds hshape
  obtain ⟨y, a, ha, eA, hy2, hy, heA⟩ := exists_conj_abar hC hx hP2 hp hAbar
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply abType22_ne_one
    rw [← heA]
    exact map_one eA
  exfalso
  rcases trichotomy hO hshape hStray with ⟨-, hnorm, -⟩ | ⟨K, hW⟩ | ⟨K, hK, hKc, hAK, hne, -⟩
  · haveI := hnorm
    exact false_of_normal_abar_of_conj hshape ha ha1 hy
  · exact false_of_wreathCase F hP2 (z_mem_centralizer_x₂ hC) hW
  · haveI hKc' : K.Characteristic := by
      subst hK
      exact CFSG.LocalCores.layer_characteristic
    haveI hKn : K.Normal := inferInstance
    rcases nonExactShapeEightLookup_holds _ _ Sg V K hKg hO hshape hK hKc hAK hne with
      hA10 | hHS | hL
    · obtain ⟨e⟩ := hA10
      exact false_of_alternating_ten_of_conj hshape hKc.1 hAK hne e ha ha1 hy2 hy
    · exact false_of_hs_of_conj hFus hshape hAK hHS eA ha heA hy
    · have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hKc.1.1
      have hAK' : ((Agrp ι).subgroupOf (centralizer ({z * ι τ₀} : Set G))).map
          (QuotientGroup.mk' (zpowers (selfC (z * ι τ₀)))) ≤ K := by
        rw [hAbar]
        exact hAK
      obtain ⟨Kh, hle, hn, hperf, hA, ⟨eK⟩, hmap⟩ :=
        exists_khat_map (Agrp_le_centralizer_x₂ hC) (commutator_Agrp ι) hKperf hAK'
      have hne' : Kh ≠ Agrp ι := by
        intro hEq
        apply hne
        rw [← hAbar, ← hmap, hEq]
      exact false_of_lieModel_l44_twisted hC hx hP2 hp hle hn hperf hA
        (not_centralizes_z_of_ne_agrp hC hle hperf hA hne') (LieModel.of_mulEquiv eK.symm hL)

end CFSG.OddStandard.AltStdSec.SwapPartner
