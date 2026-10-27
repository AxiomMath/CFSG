module

public import CFSG.GH74.GLS.C3.Layer2.L5C5g
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
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5a
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5b
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5c
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5d
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5e
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5g
public import CFSG.GH74.GLS.C3.Layer2.L5C5fInputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5fInputs
public import Certificates.Certificate5045
public import Certificates.Certificate5051
public import Certificates.Certificate5065
public import Certificates.Certificate5066
public import Certificates.Certificate5069

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

namespace Fus

theorem sh2EngChk_all :
    (List.finRange 4).all sh2EngChk = true :=
  Certificates.certificate5069

end Fus

open Fus

theorem engine2
    (ty : Fin 4) {E : Sh2 ty → Sh2 ty → Prop}
    (h : FusionHyp (Sh2 ty) ((inc ty).comp embHom0) E) : False := by
  let _ := (sh2TabD ty).grp
  have hc := sh2EngChk_all
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hc
  have hc' := hc ty
  simp only [sh2EngChk, Bool.and_eq_true, decide_eq_true_eq] at hc'
  obtain ⟨hok, hsurv⟩ := hc'
  obtain ⟨ld, hld, -⟩ := fusion_blocks h (sh2TabD ty) hok
  rw [show survivors (engOf (sh2TabD ty) ((inc ty).comp embHom0)) = [] from hsurv] at hld
  exact absurd hld (by simp)

end CFSG.GH74.GLS.C3.Layer2.L5
