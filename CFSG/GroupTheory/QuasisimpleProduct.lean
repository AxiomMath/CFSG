module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rj

public section

namespace CFSG.GroupTheory

open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem nonempty_mulEquiv_factor_of_isSubnormal_quasisimple {X P A B : Type} [Group X] [Finite X]
    [Group P] [Group A] [Group B] [IsSimpleGroup A] [IsSimpleGroup B] (f : X ≃* A × B)
    {K' : Subgroup X} (e : P ≃* ↥K') (hP : CFSG.Open.IsQuasisimple P)
    (hsub : CFSG.Open.IsSubnormal K' ⊤) :
    Nonempty (P ≃* A) ∨ Nonempty (P ≃* B) := by
  have hK' : CFSG.Open.IsComponentOf K' ⊤ :=
    ⟨le_top, hsub, CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hP⟩
  have hne : K' ≠ ⊥ := uc22p22r_ne_bot_of_equiv e hP
  have hsub' : K'.IsSubnormal := CFSG.Open.IsSubnormal.top_iff.1 hsub
  have hsup : ((MonoidHom.snd A B).comp f.toMonoidHom).ker ⊔
      ((MonoidHom.fst A B).comp f.toMonoidHom).ker = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x = f.symm ((f x).1, 1) * f.symm (1, (f x).2) := by
      rw [← map_mul]
      simp
    rw [hx]
    refine Subgroup.mul_mem_sup ?_ ?_
    · show (f (f.symm ((f x).1, 1))).2 = 1
      simp
    · show (f (f.symm (1, (f x).2))).1 = 1
      simp
  rcases uc22p22r_component_le_or_le hsup hK' with hle | hle
  · obtain ⟨g⟩ := uc22p22r_equiv_factor f hsub' hne hle
    exact Or.inl ⟨e.trans g⟩
  · obtain ⟨g⟩ := uc22p22r_equiv_factor (f.trans MulEquiv.prodComm) hsub' hne
      (fun x hx => hle hx)
    exact Or.inr ⟨e.trans g⟩

end CFSG.GroupTheory
