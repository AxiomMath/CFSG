module

public import CFSG.Sporadic.Schreier.Enumeration

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Certificates CFSG.Sporadic.Schreier

variable {n : ℕ}

theorem inf_eq_of_forall {X Y Z : Subgroup (Equiv.Perm (Fin n))} (hZX : Z ≤ X)
    (h : ∀ g ∈ X, (g ∈ Y ↔ g ∈ Z)) : X ⊓ Y = Z :=
  le_antisymm (fun g hg => (h g hg.1).1 hg.2) fun g hg => ⟨hZX hg, (h g (hZX hg)).2 hg⟩

theorem inf_eq_bot_of_forall {X Y : Subgroup (Equiv.Perm (Fin n))}
    (h : ∀ g ∈ X, g ∈ Y → g = 1) : X ⊓ Y = ⊥ :=
  eq_bot_iff.2 fun g hg => (Subgroup.mem_bot).2 (h g hg.1 hg.2)

theorem closure_le_centralizer {G : Type*} [Group G] {s t : Set G}
    (h : ∀ a ∈ s, ∀ b ∈ t, a * b = b * a) :
    Subgroup.closure s ≤ Subgroup.centralizer (Subgroup.closure t : Set G) := by
  rw [Subgroup.closure_le]
  intro a ha
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro b hb
  induction hb using Subgroup.closure_induction with
  | mem b hb => exact (h a ha b hb).symm
  | one => rw [one_mul, mul_one]
  | mul b c _ _ hb hc => rw [mul_assoc, hc, ← mul_assoc, hb, mul_assoc]
  | inv b _ hb => exact (Commute.inv_left (show Commute b a from hb)).eq

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
