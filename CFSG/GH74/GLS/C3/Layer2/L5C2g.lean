module

public import CFSG.GH74.GLS.C3.Layer2.L5C2e
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public meta import CFSG.GH74.GLS.C3.Layer2.L5B2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2a
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2b
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2c
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2d
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2e
public import CFSG.GH74.GLS.C3.Layer2.L5C2gInputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2gInputs
public import CFSG.GH74.GLS.C3.Layer2.L5C2gListInputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2gListInputs
public import CFSG.GH74.GLS.C3.Layer2.L5C2gTableInputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2gTableInputs
public import Certificates.Certificate5045
public import Certificates.Certificate5051
public import Certificates.Certificate5057
public import Certificates.Certificate5143
public import Certificates.Certificate5144

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

namespace Fus

theorem chk1_true :
    chk1 = true :=
  Certificates.certificate5144

end Fus

open Fus

theorem engine1
    {E : ↥Sh1 → ↥Sh1 → Prop} (h : FusionHyp ↥Sh1 embHom1 E)
    (hR : RExact ↥Sh1 embHom1 E) : False := by
  let _ := sh1D.grp
  have hc := chk1_true
  simp only [chk1, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at hc
  obtain ⟨⟨hok, hsurv⟩, a, -, b, -, ⟨⟨hia, hib⟩, hbl⟩, hnoA⟩ := hc
  obtain ⟨ld, hld, hblk⟩ := fusion_blocks h sh1D hok
  have hld' : ld = [0, 0, 2, 0, 2, 2] := by
    have := hld
    rw [show survivors (engOf sh1D embHom1) = [[0, 0, 2, 0, 2, 2]] from hsurv] at this
    simpa using this
  subst hld'
  obtain ⟨ha2, ha1⟩ := (isInv_idx sh1D (embHom1 (elT a))).1 hia
  obtain ⟨hb2, hb1⟩ := (isInv_idx sh1D (embHom1 (elT b))).1 hib
  have hE : E (embHom1 (elT a)) (embHom1 (elT b)) := (hblk _ _ ha2 ha1 hb2 hb1).2 hbl
  obtain ⟨A, hA, hAab⟩ := hR a b hE
  have hany : (n24L.any fun A => decide (A a = b)) = true :=
    List.any_eq_true.2 ⟨A, hA, decide_eq_true hAab⟩
  rw [hany] at hnoA
  exact absurd hnoA (by decide)

end CFSG.GH74.GLS.C3.Layer2.L5
