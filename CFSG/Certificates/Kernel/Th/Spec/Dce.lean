module

public import CFSG.Certificates.Kernel.Th.Spec.DceMain
public import CFSG.Certificates.Kernel.Th.Spec.DceHsw
import all CFSG.Sporadic.Bridge.Common

public section

namespace CFSG.KC.Th.Spec.Dce

open CFSG.KC.Th.Gen CFSG.Sporadic.Bridge

theorem presGen_closure (p : TauCeti.GroupPresentation) (h1 : p.generatorCount = 8) :
    Subgroup.closure (presGen p '' {g | g < 8}) = ⊤ := by
  rw [eq_top_iff, ← PresentedGroup.closure_range_of p.relatorSet]
  apply Subgroup.closure_mono
  rintro _ ⟨a, rfl⟩
  refine ⟨a.val, by simp only [Set.mem_setOf_eq]; omega, ?_⟩
  rw [presGen, dite_eq_left a.isLt]

theorem dce_sound_of_pres (p : TauCeti.GroupPresentation) (h1 : p.generatorCount = 8)
    (h2 : ∀ r ∈ p.relatorLetters, r.length < 1024) (h3 : p.relatorLetters.map enT = Hsw.list)
    (D : DceData) (h : dceChk D = true) :
    Finite p.Group ∧ Nat.card p.Group ≤ 90745943887872000 :=
  main_core (presGen p) (hsw_rel_of_pres p h1 h2 h3) (presGen_closure p h1) D (chk_of D h)

end CFSG.KC.Th.Spec.Dce

end
