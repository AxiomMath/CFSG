module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open Matrix CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem isPGroup_hypUnitriangular_of_sylow (h : UnitaryFieldData p f K) (hr : 1 ≤ r)
    (hε : ε ≤ 1) : IsPGroup p (hypUnitriangular h r ε) := by
  obtain ⟨-, ⟨P, hP⟩, -, -, -, -, -⟩ := unitary_order_and_Sylow h hr hε
  rw [← hP]
  exact P.isPGroup'

theorem isSolvable_hypBorel (h : UnitaryFieldData p f K) (hr : 1 ≤ r) (hε : ε ≤ 1) :
    Group.IsSolvable ↥(hypBorel h r ε) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI := finite_hypSU (r := r) (ε := ε) h
  haveI hU : Group.IsSolvable ↥((hypUnitriangular h r ε).subgroupOf (hypBorel h r ε)) := by
    have hUp : IsPGroup p (hypUnitriangular h r ε) :=
      isPGroup_hypUnitriangular_of_sylow h hr hε
    have hUsub : IsPGroup p ((hypUnitriangular h r ε).subgroupOf (hypBorel h r ε)) :=
      hUp.of_equiv (Subgroup.subgroupOfEquivOfLe (hypUnitriangular_le_hypBorel h)).symm
    haveI hnil : Group.IsNilpotent ↥((hypUnitriangular h r ε).subgroupOf (hypBorel h r ε)) :=
      hUsub.isNilpotent
    exact IsNilpotent.to_isSolvable
  haveI hT : Group.IsSolvable (Fin r → Kˣ) := Group.isSolvable_of_comm fun a b => mul_comm a b
  refine Group.isSolvable_of_ker_le_range
    ((hypUnitriangular h r ε).subgroupOf (hypBorel h r ε)).subtype
    (hypDiagHom h r ε hε) ?_
  rw [ker_hypDiagHom, Subgroup.range_subtype]

theorem isSolvable_hypProjBorel (h : UnitaryFieldData p f K) (hr : 1 ≤ r) (hε : ε ≤ 1) :
    Group.IsSolvable ↥(hypProjBorel h r ε) := by
  haveI hB : Group.IsSolvable ↥(hypBorel h r ε) := isSolvable_hypBorel h hr hε
  let f : ↥(hypBorel h r ε) →* ↥(hypProjBorel h r ε) :=
    MonoidHom.codRestrict ((hypProj h r ε).comp (hypBorel h r ε).subtype)
      (hypProjBorel h r ε) fun x => Subgroup.mem_map_of_mem (hypProj h r ε) x.2
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact Group.isSolvable_of_surjective hf

end CFSG.ClassicalGroups.UnitaryFlag
