module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.Quasithin.Vol2.Ch3T326GD

public section
namespace CFSG.Quasithin.H13.T326

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace Ctx

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem qhatStar_acts_of_eq_F4 (h316 : Theorem316Statement) (h6 : Vol2.Ch11.TmpL6_3_2_2_six_F4)
    [IsMulCommutative ↥(conjClosure V₀ T)]
    [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))]
    (hV : conjClosure V₀ T =
      conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))
    (hC : conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ⊓
      Subgroup.centralizer (conjClosure L T : Set G) ≠ ⊥) :
    ∀ A ∈ QhatStar (V := ↥(conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))))
        (autOn (Subgroup.normalizer (conjClosure L T : Set G))
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))),
      ∀ a ∈ A, ∀ u : ↥(conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G))),
        (u : G) ∈ ⁅conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ →
        ((a u : ↥(conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)))) : G) ∈
          ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ := by
  have huniq : IsUniqueM (fsuL0 T L ⊔ T) (fsuM T L) := by
    have h := c.uniq
    rwa [← sup_eq T L] at h
  obtain ⟨-, hcomm, hff⟩ := h6 G T L V₀ c.fsu hC huniq
  have hff' := isFFModule_autOn_of_eq hV (conjClosure L T ⊔ T) hff
  have hYX : autOn (conjClosure L T ⊔ T) (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))) ≤
      autOn (Subgroup.normalizer (conjClosure L T : Set G)) (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))) :=
    InternalSec.autOn_le_autOn_of_le c.sup_le_M
  have hD := c.d3Std h316
  have hq1 := qhatOf_le_one_of_isFFModule hD.hyp.exp hYX hff'
  have hK := isComponentOf_of_mem_cComp hD.hyp.comp hD.hyp.quasi
  intro A hA a ha u hu
  have haN := qhatStar_le_normalizer_of_qhatOf_le_one hD.hyp.exp hq1 hA hK ha
  have hU : u ∈ commV (autOn L (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))) := by
    rw [Vol2.Ch11.SecC.B51.commV_autOn c.L_le_NVM]
    exact Subgroup.mem_subgroupOf.2 hu
  have h1 := B15P4.map_commV_mem haN u hU
  rw [Vol2.Ch11.SecC.B51.commV_autOn c.L_le_NVM] at h1
  exact Subgroup.mem_subgroupOf.1 h1

end Ctx

end CFSG.Quasithin.H13.T326
