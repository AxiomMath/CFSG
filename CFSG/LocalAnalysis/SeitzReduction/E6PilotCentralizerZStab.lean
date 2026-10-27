module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerZLevi

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {K : Type} [Field K]


variable (K) in
@[expose] def ZLeviStabilizer : Prop :=
  ∀ m ∈ parabolicLevi .E6 K zNodes, m ∈ centralizer ({zAS K} : Set (ModGL .E6 K)) →
    m ∈ zJ K ⊔ zS K

theorem levi_inf_centralizer_eq_of_stabilizer [CharP K 2] (h : ZLeviStabilizer K) :
    parabolicLevi .E6 K zNodes ⊓ centralizer ({zAS K} : Set (ModGL .E6 K)) = zJ K ⊔ zS K :=
  le_antisymm (fun m hm => h m (mem_inf.1 hm).1 (mem_inf.1 hm).2)
    (sup_le zJ_le_levi_inf_centralizer zS_le_levi_inf_centralizer)

theorem zLevi_eq_of_stabilizer [CharP K 2] (h : ZLeviStabilizer K) :
    zLevi K = (zJ K ⊔ zS K).subgroupOf (adjointGroup .E6 K) := by
  rw [zLevi, levi_inf_centralizer_eq_of_stabilizer h]

theorem zDLevi_eq_of_stabilizer [CharP K 2] (h : ZLeviStabilizer K) :
    zDLevi K = ((zJ K ⊔ zS K).subgroupOf (adjointGroup .E6 K)).map
      (MulAut.conj (e6RepConj K 2)).toMonoidHom := by
  rw [zDLevi, zLevi_eq_of_stabilizer h]

end CFSG.SeitzReduction.E6Pilot
