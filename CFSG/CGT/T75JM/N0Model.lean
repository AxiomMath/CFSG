
module

public import CFSG.CGT.T75JM.N0ModelBase

public import Certificates.Certificate14988

public section

namespace CFSG.CGT.T75JM

open CFSG.CosetTable CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Blueprint

noncomputable def n0Phi : N0 →* NativeSporadic.M22 :=
  PresentedGroup.toGroup (lift_n0Gen_eq_one Certificates.certificate14988.1
    Certificates.certificate14988.2.1)

theorem n0Phi_mk (w : List (Fin 6 × Bool)) :
    n0Phi (n0 w) = FreeGroup.lift n0Gen (FreeGroup.mk w) := by
  have hcomp : (n0Phi : N0 →* NativeSporadic.M22).comp (PresentedGroup.mk _) =
      FreeGroup.lift n0Gen := by
    apply FreeGroup.ext_hom
    intro i
    simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
    exact PresentedGroup.toGroup.of _
  exact congrArg (fun f => f (FreeGroup.mk w)) hcomp

theorem rep_n0Phi (w : List (Fin 6 × Bool)) :
    Rep 22 (n0Tab w) (n0Phi (n0 w)) := by
  rw [n0Phi_mk, ← evalWord7_m22Gen]
  exact rep_n0Tab Certificates.certificate14988.1 w

theorem n0_eq_of_tab_eq
    {w w' : List (Fin 6 × Bool)} (h : n0Tab w = n0Tab w') :
    n0 w = n0 w' :=
  Certificates.certificate14988.2.2 w w' h

theorem n0Tab_eq_of_eq {w w' : List (Fin 6 × Bool)}
    (h : n0 w = n0 w') : n0Tab w = n0Tab w' := by
  have h1 := rep_n0Phi w
  rw [h] at h1
  exact table_eq_of_rep h1 (rep_n0Phi w') (n0Tab_size w) (n0Tab_size w')

theorem n0Tab_append (w w' : List (Fin 6 × Bool)) :
    n0Tab (w ++ w') = compT 22 (n0Tab w) (n0Tab w') := by
  refine table_eq_of_rep (g := n0Phi (n0 (w ++ w'))) (rep_n0Phi _) ?_ (n0Tab_size _)
    (compT_size _ _)
  rw [n0_append, map_mul]
  exact Rep.compT (rep_n0Phi w) (rep_n0Phi w')

theorem n0_eq_iff_tab
    {w w' : List (Fin 6 × Bool)} : n0 w = n0 w' ↔ n0Tab w = n0Tab w' :=
  ⟨n0Tab_eq_of_eq, n0_eq_of_tab_eq⟩

end CFSG.CGT.T75JM
