module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Main
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6ShapesDef

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Hyp62_of_aschOmega6Plus (h : AschOmega6Plus) {G : Type} [Group G] [Finite G]
    {t : G} {L : Subgroup G} (hS : Sec3SettingLB G t L) : Asc82Hyp62 G := by
  intro X hX hΩ
  obtain ⟨y, hy, hXy⟩ := hX
  have hF : InF X := ⟨hXy.isQuasisimple, Or.inl (Or.inr (Or.inl hΩ))⟩
  exact (h G y X (sec3SettingLB_of_component hS hy hXy hF) hΩ).elim

theorem asc82Hyp62All_of_aschOmega6Plus (h : AschOmega6Plus) :
    ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
      Asc82Hyp62 G :=
  fun _ _ _ _ _ hS => asc82Hyp62_of_aschOmega6Plus h hS

end CFSG.OddStandard.SmallF3.Omega
