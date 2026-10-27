module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34G2Q8

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem l34g_mem_pCore_of_pocketData [Finite G] (hG1 : Asc82NoQ8InL2)
    (hG2 : Asc82OddCoreCentralizerQ8) {x : G} {X : Subgroup G} {y : G} {K : Subgroup G}
    (hD : Sec3PocketData x X y K) : y ∈ CFSG.inSubgroup (CFSG.pCore 2) K := by
  obtain ⟨f, _, hfy, hfQ⟩ := exists_quaternion_of_pocketData_q8 hG1 hG2 hD
  exact hfQ ⟨QuaternionGroup.a 2, hfy⟩

theorem l34g_false_of_pCore_le_component [Finite G] (hG1 : Asc82NoQ8InL2)
    (hG2 : Asc82OddCoreCentralizerQ8) (hS : Asc82SchurU43) {x : G} {X : Subgroup G} {y : G}
    {K : Subgroup G} (hD : Sec3PocketData x X y K) {J : Subgroup G}
    (hJ : IsComponentIn J (centralizer ({y} : Set G))) (hJF : InFStar J)
    (hQJ : CFSG.inSubgroup (CFSG.pCore 2) K ≤ J) : False := by
  have hy := hD.involution_y
  obtain ⟨f, hf, hfy, hfQ⟩ := exists_quaternion_of_pocketData_q8 hG1 hG2 hD
  have hfJ : f.range ≤ J := hfQ.trans hQJ
  have hyJ : y ∈ J := hfJ ⟨QuaternionGroup.a 2, hfy⟩
  have hJc : ∀ a ∈ J, a * y = y * a := fun a ha =>
    (Subgroup.mem_centralizer_iff.mp (hJ.1 ha) y rfl).symm
  have hT := isTwoU43_of_mem_center hJF hy hyJ hJc
  let fJ : QuaternionGroup 2 →* ↥J := f.codRestrict J (fun g => hfJ ⟨g, rfl⟩)
  have hfJinj : Function.Injective fJ := fun a b hab => hf (congrArg Subtype.val hab)
  have hz : fJ (QuaternionGroup.a 2) ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (by
      change (g : G) * f (QuaternionGroup.a 2) = f (QuaternionGroup.a 2) * g
      rw [hfy]
      exact hJc g g.2)
  exact false_of_central_quaternion hS (inFStar_isQuasisimple hJF) hT hfJinj hz

end CFSG.OddStandard.SmallF3.Omega
