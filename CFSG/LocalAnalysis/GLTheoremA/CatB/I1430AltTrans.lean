module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84

open CFSG.Open

section Transport

variable {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G']

theorem normalizer_map_of_injective {f : G →* G'} (hf : Function.Injective f) {U : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (U : Set G)) :
    f x ∈ Subgroup.normalizer ((U.map f : Subgroup G') : Set G') := by
  have hx' : ∀ h : G, h ∈ U ↔ x * h * x⁻¹ ∈ U := fun h => Subgroup.mem_normalizer_iff.1 hx h
  have hxinv : ∀ h : G, h ∈ U ↔ x⁻¹ * h * x ∈ U := by
    intro h
    have hxi : x⁻¹ ∈ Subgroup.normalizer (U : Set G) := Subgroup.inv_mem _ hx
    simpa using Subgroup.mem_normalizer_iff.1 hxi h
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine Subgroup.mem_map.2 ⟨x * u * x⁻¹, (hx' u).1 hu, ?_⟩
    simp [map_mul, map_inv, mul_assoc]
  · intro hv
    obtain ⟨v, hv', hfv⟩ := Subgroup.mem_map.1 hv
    refine Subgroup.mem_map.2 ⟨x⁻¹ * v * x, (hxinv v).1 hv', ?_⟩
    rw [map_mul, map_mul, map_inv, hfv]
    group

theorem i1430TwoLocal_of_injective {r : ℕ} (f : G →* G') (hf : Function.Injective f)
    (h : I1430TwoLocal G r) : I1430TwoLocal G' r := by
  obtain ⟨U, E, hU, hUp, hEN, hE, hcard⟩ := h
  refine ⟨U.map f, E.map f, ?_, ?_, ?_, ?_, ?_⟩
  · intro hbot
    apply hU
    have h1 : Nat.card (U.map f) = Nat.card U := Subgroup.card_map_of_injective hf
    rw [hbot, Subgroup.card_bot] at h1
    exact Subgroup.card_eq_one.1 h1.symm
  · obtain ⟨k, hk⟩ := hUp.exists_card_eq
    exact IsPGroup.of_card (n := k) (by rw [Subgroup.card_map_of_injective hf, hk])
  · rintro _ ⟨x, hx, rfl⟩
    exact normalizer_map_of_injective hf (hEN hx)
  · have hcomm : ∀ a ∈ E.map f, ∀ b ∈ E.map f, a * b = b * a := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, isElemAbelian_commute hE hx hy]
    refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2)⟩⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x hx, map_one]
  · rw [Subgroup.card_map_of_injective hf]
    exact hcard

end Transport

theorem pRank_bot_eq_zero {G : Type} [Group G] [Finite G] (p : ℕ) (hp : 2 ≤ p) :
    CFSG.Open.pRank p (⊥ : Subgroup G) = 0 := by
  have hset : {k : ℕ | ∃ E : Subgroup G, E ≤ ⊥ ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k} = {0} := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨E, hE, -, hcard⟩
      have hE' : E = ⊥ := le_bot_iff.1 hE
      subst hE'
      rw [Subgroup.card_bot] at hcard
      exact (Nat.pow_eq_one.1 hcard.symm).resolve_left (by omega)
    · rintro rfl
      refine ⟨⊥, le_rfl, ?_, by simp⟩
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
      · simp [Subgroup.mem_bot.1 a.2, Subgroup.mem_bot.1 b.2]
      · rw [Subgroup.mem_bot.1 hx, one_pow]
  unfold CFSG.Open.pRank
  rw [hset, csSup_singleton]

end CFSG.LocalAnalysis.GLTheoremA.S8.L84
