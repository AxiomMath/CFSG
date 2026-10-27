module

public import CFSG.GH74.KGroups.PermCheck
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier

variable {G : Type} [Group G]

theorem mem_centerIn_iff {X : Subgroup G} {x : G} :
    x ∈ centerIn X ↔ x ∈ X ∧ ∀ y ∈ X, x * y = y * x := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, fun y hy => ?_⟩
    have := Subgroup.mem_center_iff.1 hc ⟨y, hy⟩
    exact congrArg Subtype.val this.symm
  · rintro ⟨hx, h⟩
    refine ⟨⟨x, hx⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
    exact (h g g.2).symm

theorem centerIn_le (X : Subgroup G) : centerIn X ≤ X := fun _ hx => (mem_centerIn_iff.1 hx).1

theorem card_centerIn_originalSubgroup {n : ℕ} (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) :
    Nat.card ↥(centerIn Q.originalSubgroup) =
      ((elemsT Q).filter fun g => (elemsT Q).all fun t => decide (g * t = t * g)).length := by
  refine card_eq_length (fun g : Equiv.Perm (Fin n) => g ∈ centerIn Q.originalSubgroup)
    id Function.injective_id _ ((nodup_elemsT Q hQ).filter _) ?_
  intro b
  simp only [List.mem_filter, List.all_eq_true, decide_eq_true_eq, mem_elemsT Q hQ,
    mem_centerIn_iff, id_eq, exists_eq_right]

end CFSG.OddStandard.SmallF3.Omega
