module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FChi
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FThompson

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

theorem Sec4FSetup.caseI (h : Sec4FSetup t L S z A B φ) (hsplit : Asc82Split47) {P : Subgroup G}
    (hPM : P ≤ normalizer (A : Set G)) (htP : t ∈ P) (hS : IsSylow2Of P ⊤) : False := by
  obtain ⟨χ, hχ⟩ := h.chi_exists hsplit
  exact sec4F_thompson_hom h.ctx.simple (sec4_nonabelian h.ctx.toSec3Setting) h.ctx.involution
    hS htP (χ.comp (Subgroup.inclusion hPM)) (fun g hg hconj => hχ g (hPM hg) hconj)

end CFSG.OddStandard.SmallF3.Omega
