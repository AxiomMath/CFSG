module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10CorIIIBMain
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10CorIIIBPocket
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10CorIIIBArith
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10CorIIIBComp

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem c3b_false_of_witness
    (hCI : CFSG.ComponentClassification.GSLit.ClassicalInvolutionInput)
    (hCL1 : CFSG.ComponentClassification.CatLeaf.GLS3OddLieAutComponentsInput)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {G : Type} [Group G] [Finite G] {t : G} {L : Subgroup G} (hS : Sec3SettingLB G t L)
    {z : G} (hz : orderOf z = 2) {J : Subgroup G} (hzJ : z ∈ J)
    (hJ : CFSG.Open.IsSubnormal J (centralizer ({z} : Set G))) (Sy : Sylow 2 J)
    (hSy : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((Sy : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2))))
    (hw : CFSG.Open.classicalInvolutionWitness J) : False := by
  haveI : IsSimpleGroup G := hS.simple
  have hnab : ∃ a b : G, a * b ≠ b * a := c3b_nonabelian_of_inF hS.inF
  obtain ⟨hFs, hFnab⟩ := c3b_genFittingFStar_simple hnab
  haveI := hFs
  obtain ⟨eF⟩ := c3b_nonempty_genFittingFStar_equiv hnab
  rcases (hCI G hFnab z hz J hzJ hJ Sy hSy).1 hw with
    ⟨τ, n, p, f, hp, hp2, hadm, hm⟩ | hM11
  · have hmG : LieModel G τ n p f := LieModel.of_mulEquiv eF hm
    by_cases hp3 : p = 3
    · subst hp3
      exact hS.notChev3 ⟨τ, n, f, hadm, hmG⟩
    · rcases c3b_lieModel_of_component hCL1 (c3b_center_eq_bot hnab) hp hp2 hadm hmG
          hS.involution hS.component with ⟨τ', n', f', hadm', hm'⟩ | h3
      · obtain ⟨-, hmul, hfac⟩ := hO _ τ' n' p f' hadm' hm'
        exact c3b_false_of_fOrder hadm' hp2 hp3 hmul hfac (c3b_card_quot_center_of_inF hS.inF)
      · exact hp3 h3
  · exact c3b_false_of_m11 hnab hS.inF hM11

end CFSG.OddStandard.SmallF3.Omega
