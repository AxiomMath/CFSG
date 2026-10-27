module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchFinal
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitInMain

public section

namespace CFSG.EvenSmallLie.OmegaEight.SplitIn

open Subgroup Stage1 Stage0

theorem standardSetting_of_hypSplit {G : Type} [Group G] [Finite G] {L : Subgroup G} :
    ∀ {ε : Eps}, HypSplit G L ε → StandardSetting G L
  | .plus, h => h.1
  | .minus, h => h.1


theorem sp6Kill (ε : Eps) : Sp6Kill ε := by
  intro G _ _ t L H₀ U Q P a ψ p u x₀ hH hK hsh hI hZ
  have hS := hI.setting
  have hNQ := hS.normalizer_E_le_of_singular fun v => (hZ v).2
  have hSt := standardSetting_of_hypSplit hH
  exact SpBranch.false_of_branch_of_simple hSt.simple hSt.nonab
    (TH := U ⊔ zpowers x₀ ⊔ zpowers t)
    { orderOf_t := hS.shape.orderOf_eq
      ψ_add := hS.rad.ψ_add
      ψ_inj := hS.rad.ψ_inj
      ψ_mem := hS.rad.ψ_mem
      mem_ψ := hS.rad.mem_ψ
      commute_ψ := hS.commute_ψ
      t_not_mem := fun h => hS.shape.not_mem (hS.Q_le_H₀ h)
      centralizer_E := hS.centralizer_E
      normalizer_le := hNQ
      Zset_eq := hZ
      onto := fun σ hσ => hS.exists_affF_eq hNQ hZ hI.orth hσ
      levi := hI.levi
      TH_le := hS.TH_le_centralizer
      TH_pgroup := hS.isPGroup_TH
      TH_max := hS.data.sylow
      TH_le_normalizer := hS.TH_le_normalizer_E }

end CFSG.EvenSmallLie.OmegaEight.SplitIn
