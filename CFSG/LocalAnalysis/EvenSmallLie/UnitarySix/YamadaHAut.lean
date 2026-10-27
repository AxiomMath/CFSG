module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3HAField
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5HAutFields2
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAutZField
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5Assembly
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAutTheta

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaHAut


theorem hypAutInput : Child5.HypAutInput := by
  intro G _ _ L hset hZ hQ t htL ht e
  obtain ⟨Θ, hΘ⟩ := exists_thetaSpec hset hZ hQ htL ht e
  exact { NHA₄_le := YamadaSec3.NHA₄_le' hΘ,
          oTwo_NA₄ := YamadaSec3.oTwo_NA₄' hΘ,
          oTwo_CA₄ := YamadaSec3.oTwo_CA₄' hΘ,
          Λ_comm_CA₄ := Child5.Λ_comm_CA₄' hΘ,
          center_CA₄ := Child5.center_CA₄' hΘ,
          CHz_le := CHz_le' hΘ,
          CH_A₁ := CH_A₁' hΘ,
          oTwo_CHz := oTwo_CHz' hΘ,
          card_CHz := card_CHz' hΘ ht,
          CH_A₁_mod := CH_A₁_mod' hΘ,
          NZ₂S := YamadaSec3.NZ₂S' hΘ }

end CFSG.EvenSmallLie.UnitarySix.YamadaHAut
