
module

public import CFSG.GH74.GLS.C3.Layer2.L5C2gTableInputsBase

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
public import CFSG.GH74.GLS.C3.Layer2.L5Fin
public import CFSG.GH74.GLS.C3.Layer2.L5A1Inputs
public import CFSG.GH74.GLS.C3.Layer2.L5B2
public import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public import CFSG.GH74.GLS.C3.Layer2.L5C0Inputs
public import Certificates.Certificate5143
public import Certificates.Certificate5051Base

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

namespace Fus

theorem sh1_chk :
    tabCheck sh1M sh1Code (buildTab sh1M sh1Code) (buildInv sh1M sh1Code)
    (buildOne sh1M sh1Code) = true :=
  Certificates.certificate5143

@[expose] def sh1D :
    TabData ↥Sh1 :=
  mkTabData sh1M sh1Code sh1M_complete (buildTab sh1M sh1Code) (buildInv sh1M sh1Code)
    (buildOne sh1M sh1Code) sh1_chk

@[expose] def eng1 :
    Eng sh1D.n := engOf sh1D embHom1

@[expose] def embIdx1
    (a : Fin 16) : Idx sh1D.n := sh1D.idx (embHom1 (elT a))

@[expose] def chk1 :
    Bool :=
  letI := sh1D.grp
  engOK eng1 && decide (survivors eng1 = [[0, 0, 2, 0, 2, 2]]) &&
    (List.finRange 16).any fun a => (List.finRange 16).any fun b =>
      isInv (embIdx1 a) && isInv (embIdx1 b) &&
        decide (blkOf eng1.ciA [0, 0, 2, 0, 2, 2] (embIdx1 a) =
          blkOf eng1.ciA [0, 0, 2, 0, 2, 2] (embIdx1 b)) &&
        !(n24L.any fun A => decide (A a = b))

end Fus

end CFSG.GH74.GLS.C3.Layer2.L5
