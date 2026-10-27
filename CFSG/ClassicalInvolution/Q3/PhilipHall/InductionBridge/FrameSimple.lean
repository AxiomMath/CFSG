module

public import CFSG.ClassicalInvolution.Asc77.AscP1Transfer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Proving.SimpleGroupFacts
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge

open Subgroup CFSG.ClassicalInvolution.Asc77

class FrameSimple (G : Type*) [Group G] : Prop where
  noIndexTwo : (∃ a b : G, a * b ≠ b * a) → ∀ H : Subgroup G, H.index ≠ 2
  center : (∃ a b : G, a * b ≠ b * a) → Subgroup.center G = ⊥
  oddNormal : (∃ a b : G, a * b ≠ b * a) → ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) →
    N = ⊥

instance FrameSimple.of_isSimpleGroup (G : Type*) [Group G] [IsSimpleGroup G] : FrameSimple G where
  noIndexTwo hnab H := CFSG.ClassicalInvolution.Q3.PhilipHall.Proving.simple_index_ne_two hnab H
  center hnab := CFSG.ClassicalInvolution.Q3.PhilipHall.Proving.simple_center_eq_bot hnab
  oddNormal hnab N hN hodd := by
    have := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exfalso
      have hG : Odd (Nat.card G) := by
        rw [← Subgroup.card_top (G := G), ← h]
        exact hodd
      have hsol : Group.IsSolvable G := by
        haveI : Finite G := Nat.finite_of_card_ne_zero hG.pos.ne'
        exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ hG
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsol a b)

variable {G : Type*} [Group G]

theorem hom_eq_one_of_noIndexTwo [Finite G] (hno : ∀ H : Subgroup G, H.index ≠ 2)
    (f : G →* Multiplicative (ZMod 2)) : f = 1 := by
  have h1 : f.ker.index ∣ 2 := by
    rw [Subgroup.index_ker]
    have := Subgroup.card_subgroup_dvd_card f.range
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card]
      decide
    rwa [h2] at this
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
  · have hker : f.ker = ⊤ := Subgroup.index_eq_one.mp h
    ext x
    have : x ∈ f.ker := by rw [hker]; exact Subgroup.mem_top x
    simpa using this
  · exact absurd h (hno _)

theorem exists_fusion_of_noIndexTwo [Finite G] (hno : ∀ H : Subgroup G, H.index ≠ 2)
    {H : Subgroup G} (hodd : Odd H.index) (ϕ : ↥H →* Multiplicative (ZMod 2))
    {a : G} (ha : a ∈ H) (ha2 : IsPGroup 2 (zpowers a)) (hϕ : ϕ ⟨a, ha⟩ ≠ 1) :
    ∃ (g : G) (n : ℕ) (hg : g⁻¹ * a ^ n * g ∈ H),
      ϕ ⟨g⁻¹ * a ^ n * g, hg⟩ ≠ ϕ ⟨a, ha⟩ ^ n := by
  by_contra hcon
  push Not at hcon
  have h1 := transfer_apply_ne_one ϕ a ha ha2 hϕ hodd hcon
  apply h1
  rw [hom_eq_one_of_noIndexTwo hno (MonoidHom.transfer ϕ)]
  rfl

end CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge
