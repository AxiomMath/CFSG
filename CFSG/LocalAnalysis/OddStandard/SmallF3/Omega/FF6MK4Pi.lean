module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK4Core
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFShapes

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff6m_K4_pi_not_mem (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    {ρ : ↥(simGroup Q)} (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1))
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = -v) :
    piOrth Q ∉ ⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆ := by
  intro h
  obtain ⟨hLie, -, -⟩ := ff6m_K4_core hQ hdim hρ hρρ
  obtain ⟨hs, a, b, hab⟩ := ff_simple_of_lieModel_psl2 hLie
  haveI := hs
  have hcent : (⟨piOrth Q, h⟩ : ↥⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆) ∈
      Subgroup.center ↥⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆ := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) g.1)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.center ↥⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆) with hbot | htop
  · rw [hbot, Subgroup.mem_bot] at hcent
    exact piOrth_ne_one (by omega) (congrArg Subtype.val hcent)
  · exact hab (Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top b) a)

end CFSG.OddStandard.SmallF3.Omega
