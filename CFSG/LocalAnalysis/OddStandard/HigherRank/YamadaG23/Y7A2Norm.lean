module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Set

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_Z_normal_A (c : Ctx7 G L) (hH : F33Hyp c.s c.e) :
    (c.s.fr.Z.subgroupOf c.s.fr.A).Normal := by
  have hcfg := c.y7acfg hH
  have hle : c.s.fr.Z ≤ c.s.fr.A := by
    rw [SFrame.Z]
    exact Subgroup.zpowers_le.mpr (y7a_z_mem_A hcfg)
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro w a hw ha
  rw [SFrame.Z] at hw ⊢
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hcomm : a * c.s.fr.z = c.s.fr.z * a :=
    y6q8_z_central hcfg.cfg.rel a (by rwa [hcfg.cfg.hA] at ha)
  rw [show a * c.s.fr.z ^ k * a⁻¹ = c.s.fr.z ^ k by
    rw [← conj_zpow, hcomm, mul_assoc, mul_inv_cancel, mul_one]]
  exact Subgroup.zpow_mem_zpowers c.s.fr.z k

end CFSG.OddStandard.HigherRank.YamadaG23
