module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem le_commutator_sup_inf_centralizer_of_coprime_of_finite {R A : Subgroup G}
    [Finite ↥R] [Finite ↥A] (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hcop : Nat.Coprime (Nat.card A) (Nat.card R)) (hsolv : Group.IsSolvable R) :
    R ≤ ⁅R, A⁆ ⊔ R ⊓ Subgroup.centralizer (A : Set G) := by
  haveI : Fact (A ≤ Subgroup.normalizer (R : Set G)) := ⟨hAR⟩
  have hsup := CFSG.fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (A := ↥A) (G := ↥R) hsolv hcop
  have hcommMap : (CFSG.commutatorAction (A := ↥A) (G := ↥R)).map R.subtype = ⁅R, A⁆ :=
    CFSG.commutatorAction_subgroup_conj_map_eq_commutator R A hAR
  have hfixEq : CFSG.fixedPointSubgroup ↥A ↥R =
      (R ⊓ Subgroup.centralizer (A : Set G)).subgroupOf R := by
    simpa [CFSG.subgroupCentralizerIn] using
      CFSG.fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn R A hAR
  intro x hx
  have htop : (⟨x, hx⟩ : ↥R) ∈ CFSG.fixedPointSubgroup ↥A ↥R ⊔
      CFSG.commutatorAction (A := ↥A) (G := ↥R) := by
    rw [hsup]
    exact Subgroup.mem_top _
  have hmap := Subgroup.mem_map_of_mem R.subtype htop
  rw [Subgroup.map_sup, hcommMap, hfixEq, Subgroup.map_subgroupOf_eq_of_le inf_le_left] at hmap
  rw [sup_comm]
  exact hmap

end CFSG.GroupTheory

end
