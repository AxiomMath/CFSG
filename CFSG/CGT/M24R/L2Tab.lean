
module

public import CFSG.CGT.M24R.L2TabBase

public import Certificates.Certificate21193

public section

namespace CFSG.CGT.M24R

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CosetTable

section Pi

noncomputable def π8 : N8 →* Equiv.Perm (Fin 16) :=
  PresentedGroup.toGroup (lift_gPerm_eq_one Certificates.certificate21193.1)

theorem π8_n8 (w : List (Fin 10 × Bool)) : π8 (n8 w) = FreeGroup.lift gPerm (FreeGroup.mk w) := by
  have hcomp : (π8 : N8 →* Equiv.Perm (Fin 16)).comp (PresentedGroup.mk _) =
      FreeGroup.lift gPerm := by
    apply FreeGroup.ext_hom
    intro i
    simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
    exact PresentedGroup.toGroup.of _
  exact congrArg (fun f => f (FreeGroup.mk w)) hcomp

@[expose] def IsTab (X : Table) (x : N8) : Prop := Rep 16 X (π8 x)

theorem isTab_wTab (w : List (Fin 10 × Bool)) : IsTab (wTab w) (n8 w) := by
  unfold IsTab
  rw [π8_n8]
  exact rep_wTab w

theorem IsTab.one : IsTab (idT 16) 1 := by
  unfold IsTab
  rw [map_one]
  exact Rep.idT (by norm_num)

theorem IsTab.mul {X Y : Table} {x y : N8} (hX : IsTab X x) (hY : IsTab Y y) :
    IsTab (compT 16 X Y) (x * y) := by
  unfold IsTab at *
  rw [map_mul]
  exact Rep.compT hX hY

end Pi

end CFSG.CGT.M24R
