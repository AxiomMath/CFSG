module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FSignT1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FT1Syl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FThompson

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B P : Subgroup G}
  {x : G} {φ : (Fin 7 → ZMod 2) → G}

theorem Sec4FSetup.caseII (h : Sec4FSetup t L S z A B φ) (hT : Sec4FTwo A P x) : False := by
  obtain ⟨ψ, hψ⟩ := h.sign_T1 hT
  have htT : t ∈ P ⊔ zpowers x := Subgroup.mem_sup_left (hT.AP h.t_mem_A)
  exact sec4F_thompson_hom h.ctx.simple (sec4_nonabelian h.ctx.toSec3Setting) h.ctx.involution
    (h.T1_sylow hT) htT ψ hψ

end CFSG.OddStandard.SmallF3.Omega
