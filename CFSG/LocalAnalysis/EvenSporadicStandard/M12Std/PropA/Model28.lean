module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM12ModelData
public import Certificates.Data.PropAModelData

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Equiv CFSG.Sporadic CFSG.Sporadic.Schreier

@[expose] noncomputable def block28 : Perm (Fin 24) × Perm (Fin 4) →* Perm (Fin 28) :=
  (Equiv.permCongrHom finSumFinEquiv).toMonoidHom.comp (Equiv.Perm.sumCongrHom (Fin 24) (Fin 4))

theorem block28_injective : Function.Injective block28 :=
  (Equiv.permCongrHom finSumFinEquiv).injective.comp Equiv.Perm.sumCongrHom_injective

@[expose] def hOne : Perm (Fin 4) := List.formPerm [0, 1] * List.formPerm [2, 3]

@[expose] def hTwo : Perm (Fin 4) := List.formPerm [0, 1, 2, 3]

@[expose] def tFour : Perm (Fin 4) := List.formPerm [0, 2] * List.formPerm [1, 3]

@[expose] noncomputable def pA : Perm (Fin 28) := block28 (m12A1, 1)

@[expose] noncomputable def pB : Perm (Fin 28) := block28 (m12B1, 1)

@[expose] noncomputable def pT : Perm (Fin 28) := block28 (1, tFour)

@[expose] noncomputable def pG (b : Bool) : Perm (Fin 28) :=
  block28 (m12Sigma, if b then hTwo else hOne)

@[expose] noncomputable def D28 : Subgroup (Perm (Fin 28)) := Subgroup.closure {pA, pB}

@[expose] noncomputable def K28 (b : Bool) : Subgroup (Perm (Fin 28)) :=
  Subgroup.closure {pA, pB, pG b, pT}

theorem rep_tabA : Th.Rep 28 Data.tabA pA := by
  unfold CFSG.Sporadic.Th.Rep
  decide +kernel

theorem rep_tabB : Th.Rep 28 Data.tabB pB := by
  unfold CFSG.Sporadic.Th.Rep
  decide +kernel

theorem rep_tabG1 : Th.Rep 28 Data.tabG1 (pG false) := by
  unfold CFSG.Sporadic.Th.Rep
  decide +kernel

theorem rep_tabG2 : Th.Rep 28 Data.tabG2 (pG true) := by
  unfold CFSG.Sporadic.Th.Rep
  decide +kernel

theorem rep_tabT : Th.Rep 28 Data.tabT pT := by
  unfold CFSG.Sporadic.Th.Rep
  decide +kernel

end CFSG.EvenSporadicStandard.M12Std.PropA
