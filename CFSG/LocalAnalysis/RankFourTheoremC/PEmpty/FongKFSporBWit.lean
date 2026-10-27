module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKFSporBRed
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKF

open scoped commutatorElement

theorem oneClassE_of_witness {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {G : Type*} [Group G]
    [Finite G] (hsyl : ¬ p ^ 4 ∣ Nat.card G) {x y g₁ g₂ : G} (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hne : ⁅x, y⁆ ≠ 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    {a b k c d l a' b' k' c' d' l' : ℕ}
    (h₁x : g₁ * x * g₁⁻¹ = x ^ a * y ^ b * ⁅x, y⁆ ^ k)
    (h₁y : g₁ * y * g₁⁻¹ = x ^ c * y ^ d * ⁅x, y⁆ ^ l)
    (h₂x : g₂ * x * g₂⁻¹ = x ^ a' * y ^ b' * ⁅x, y⁆ ^ k')
    (h₂y : g₂ * y * g₂⁻¹ = x ^ c' * y ^ d' * ⁅x, y⁆ ^ l') (n : ℕ)
    (hreach : ∀ w : Fin 2 → ZMod p, w ≠ 0 → ∃ s : ZMod p, s ≠ 0 ∧
      s • w ∈ Heis.reach [!![(a : ZMod p), (c : ZMod p); (b : ZMod p), (d : ZMod p)],
        !![(a' : ZMod p), (c' : ZMod p); (b' : ZMod p), (d' : ZMod p)]] n) :
    OneClassE p G := by
  have hz : ⁅x, y⁆ ^ p = 1 := by
    rw [CFSG.SectionRank.LocalWitness.commutator_pow_eq hzx, hx]
    simp [commutatorElement_def]
  have hd : Heis.Data p x y := ⟨hx, hy, hz, hzx.eq, hzy.eq, hne⟩
  intro B U hB hU
  refine Heis.oneClassE hp hd hsyl
    {A | A ∈ [!![(a : ZMod p), (c : ZMod p); (b : ZMod p), (d : ZMod p)],
      !![(a' : ZMod p), (c' : ZMod p); (b' : ZMod p), (d' : ZMod p)]]} ?_
    (Heis.trans_of_reach _ n hreach) B U hB hU
  intro A hA
  simp only [List.mem_cons, List.mem_nil_iff, or_false, Set.mem_setOf_eq] at hA
  rcases hA with rfl | rfl
  · exact ⟨g₁, a, b, k, c, d, l, rfl, h₁x, h₁y⟩
  · exact ⟨g₂, a', b', k', c', d', l', rfl, h₂x, h₂y⟩

theorem pow_eq_one_of_mem_exponent {G : Type*} [Group G] {S : Subgroup G} {x : G} (hx : x ∈ S)
    {n : ℕ} (h : Monoid.exponent S = n) : x ^ n = 1 := by
  have := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : S)
  rw [h] at this
  exact congrArg Subtype.val this

theorem commute_of_mem_center_map {G : Type*} [Group G] {S : Subgroup G} {z x : G}
    (hz : z ∈ (Subgroup.center S).map S.subtype) (hx : x ∈ S) : Commute z x := by
  obtain ⟨q, hqc, rfl⟩ := hz
  have h := congrArg Subtype.val (Subgroup.mem_center_iff.1 hqc ⟨x, hx⟩)
  exact h.symm

theorem ne_one_of_center_card {G : Type*} [Group G] {S : Subgroup G} {z : G} {p : ℕ}
    (hcenter : (Subgroup.center S).map S.subtype = Subgroup.zpowers z)
    (hc : Nat.card (Subgroup.center S) = p) (hp : 1 < p) : z ≠ 1 := by
  intro h1
  have h3 : Nat.card ((Subgroup.center S).map S.subtype) = p := by
    rw [Subgroup.card_map_of_injective S.subtype_injective]
    exact hc
  rw [hcenter, h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at h3
  omega

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKF
