
module

public import CFSG.CGT.T75M23.N7ModelBase

public import Certificates.Certificate271011

public section

namespace CFSG.CGT.T75M23

open CFSG.CosetTable CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Blueprint

noncomputable def n7Phi : N7 →* NativeSporadic.M23 :=
  PresentedGroup.toGroup (lift_n7Gen_eq_one Certificates.certificate271011.1
    Certificates.certificate271011.2.1)

theorem n7Phi_mk (w : List (Fin 6 × Bool)) :
    n7Phi (n7 w) = FreeGroup.lift n7Gen (FreeGroup.mk w) := by
  have hcomp : (n7Phi : N7 →* NativeSporadic.M23).comp (PresentedGroup.mk _) =
      FreeGroup.lift n7Gen := by
    apply FreeGroup.ext_hom
    intro i
    simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
    exact PresentedGroup.toGroup.of _
  exact congrArg (fun f => f (FreeGroup.mk w)) hcomp

theorem rep_n7Phi (w : List (Fin 6 × Bool)) :
    Rep 23 (n7Tab w) (n7Phi (n7 w)) := by
  rw [n7Phi_mk, ← evalWord7_m23Gen]
  exact rep_n7Tab Certificates.certificate271011.1 w

theorem n7_eq_of_tab_eq {w w' : List (Fin 6 × Bool)}
    (h : n7Tab w = n7Tab w') : n7 w = n7 w' :=
  Certificates.certificate271011.2.2 w w' h

theorem n7Tab_eq_of_eq {w w' : List (Fin 6 × Bool)}
    (h : n7 w = n7 w') : n7Tab w = n7Tab w' := by
  have h1 := rep_n7Phi w
  rw [h] at h1
  exact table_eq_of_rep h1 (rep_n7Phi w') (n7Tab_size w) (n7Tab_size w')

theorem n7Tab_append (w w' : List (Fin 6 × Bool)) :
    n7Tab (w ++ w') = compT 23 (n7Tab w) (n7Tab w') := by
  refine table_eq_of_rep (g := n7Phi (n7 (w ++ w'))) (rep_n7Phi _) ?_ (n7Tab_size _)
    (compT_size _ _)
  rw [n7_append, map_mul]
  exact Rep.compT (rep_n7Phi w) (rep_n7Phi w')

theorem n7_eq_iff_tab {w w' : List (Fin 6 × Bool)} :
    n7 w = n7 w' ↔ n7Tab w = n7Tab w' :=
  ⟨n7Tab_eq_of_eq, n7_eq_of_tab_eq⟩

end CFSG.CGT.T75M23
