module

public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Open.Defs

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open scoped commutatorElement

theorem tables112_T0_holds : ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L →
    CFSG.Open.IsKGroup L → ∃ t : L, orderOf t = 2 := by
  intro L _ _ hQ _
  obtain ⟨hcomm, hsimp⟩ := hQ
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hsimp
  have hEven : 2 ∣ Nat.card L := by
    rcases Nat.even_or_odd (Nat.card L) with he | hodd
    · exact even_iff_two_dvd.mp he
    · exfalso
      have hsolv : Group.IsSolvable L := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
      have : Group.IsSolvable L := hsolv
      have hQsolv : Group.IsSolvable (L ⧸ Subgroup.center L) := inferInstance
      have hQcomm : ∀ a b : L ⧸ Subgroup.center L, a * b = b * a :=
        (IsSimpleGroup.comm_iff_isSolvable (G := L ⧸ Subgroup.center L)).2 hQsolv
      have hcen : ∀ x y : L, ⁅x, y⁆ ∈ Subgroup.center L := by
        intro x y
        have h1 : QuotientGroup.mk' (Subgroup.center L) ⁅x, y⁆ = 1 := by
          rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.2 (hQcomm _ _)]
        exact (QuotientGroup.eq_one_iff _).1 h1
      have hle : commutator L ≤ Subgroup.center L :=
        Subgroup.commutator_le.2 (fun x _ y _ => hcen x y)
      have htop : (⊤ : Subgroup L) ≤ Subgroup.center L := hcomm ▸ hle
      have hcenter : ∀ x : L, x ∈ Subgroup.center L := fun x => htop (Subgroup.mem_top x)
      have : Nontrivial (L ⧸ Subgroup.center L) := IsSimpleGroup.toNontrivial
      obtain ⟨a, ha⟩ := exists_ne (1 : L ⧸ Subgroup.center L)
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      exact ha ((QuotientGroup.eq_one_iff x).2 (hcenter x))
  exact exists_prime_orderOf_dvd_card' 2 hEven

end CFSG.HardMathSupport.Solomon.Proving

end
