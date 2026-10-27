module

public import CFSG.Quasithin.H13.U3S1348J

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem sup_zpowers_isElemAbelian_of_commute {H K E : Subgroup G}
    (hcomm : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) (hE : CFSG.Open.IsElemAbelian p E)
    (hEH : E ≤ H) {u : K} (hup : orderOf u = p)
    (hucent : u ∉ Subgroup.center K) :
    CFSG.Open.IsElemAbelian p (E ⊔ Subgroup.zpowers (u : G)) ∧
      Nat.card ↥(E ⊔ Subgroup.zpowers (u : G)) = p * Nat.card E := by
  have huK : (u : G) ∈ K := u.2
  have hu_notin_E : (u : G) ∉ E := by
    intro huE
    apply hucent
    rw [Subgroup.mem_center_iff]
    intro v
    exact Subtype.ext (hcomm (u : G) (hEH huE) (v : G) v.2).symm
  have hupow : (u : G) ^ p = 1 := by
    have := pow_orderOf_eq_one u
    rw [hup] at this
    simpa using congrArg Subtype.val this
  have hcommEu : ∀ a ∈ E, a * (u : G) = (u : G) * a :=
    fun a ha => hcomm a (hEH ha) (u : G) huK
  obtain ⟨hEsup, hcard⟩ :=
    CFSG.Quasithin.H13.U3.elemAbelian_sup_zpowers hE hu_notin_E hupow hcommEu
  exact ⟨hEsup, by rw [hcard, Nat.mul_comm]⟩

end CFSG.GroupTheory

end
