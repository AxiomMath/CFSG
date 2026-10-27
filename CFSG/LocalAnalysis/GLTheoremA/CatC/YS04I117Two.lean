module

public import CFSG.HardMathSupport.Timmesfeld.DFour.FixDescent

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open Module CFSG.HardMathSupport.Timmesfeld.DFour

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {E : Type*} [Group E] [IsMulCommutative E] [Finite E]

theorem D_eq_two {dm d1 d2 d3 D : ℕ} (hdm : dm = 4) (h : dm + d1 + d2 + d3 = 8 + 3 * D)
    (h1 : 2 ≤ d1 ∧ d1 ≤ 4 ∧ d1 % 2 = 0) (h2 : 2 ≤ d2 ∧ d2 ≤ 4 ∧ d2 % 2 = 0)
    (h3 : 2 ≤ d3 ∧ d3 ≤ 4 ∧ d3 % 2 = 0) : D = 2 := by omega

theorem D_eq_zero {dm d1 d2 d3 D : ℕ} (hdm : dm = 2) (h1 : d1 = 2) (h2 : d2 = 2) (h3 : d3 = 2)
    (h : dm + d1 + d2 + d3 = 8 + 3 * D) : D = 0 := by omega

theorem false_of_fixDim_two_four (h3 : (3 : K) ≠ 0) (hV : finrank K V = 8) (ρ : E →* Module.End K V)
    (hρ : Function.Injective ρ) (hexp : ∀ x : E, x ^ 3 = 1) (hcard : 27 ≤ Nat.card E)
    (heven : ∀ x : E, Even (finrank K (LinearMap.ker (ρ x - 1))))
    (h24 : ∀ x : E, x ≠ 1 →
      finrank K (LinearMap.ker (ρ x - 1)) = 2 ∨ finrank K (LinearMap.ker (ρ x - 1)) = 4) :
    False := by
  classical
  have : Fintype E := Fintype.ofFinite E
  obtain ⟨A, _, φ, ι, c, hφ, hφι, hc⟩ := exists_commRing_model3 h3 ρ
  set F : E → Submodule K V := fun x => LinearMap.ker (ρ x - 1) with hF
  have hFA : ∀ x, fixA φ (ι x) = F x := fun x => by simp only [fixA, hF, hφι]
  have hι3 : ∀ x, ι x ^ 3 = 1 := fun x => by rw [← map_pow, hexp, map_one]
  have e1 : ∀ g h : E, ι g * ι h = ι (g * h) := fun g h => (map_mul ι g h).symm
  have e2 : ∀ g h : E, ι g * ι h ^ 2 = ι (g * h ^ 2) := fun g h => by rw [map_mul, map_pow]
  have R1 : ∀ g h : E, finrank K (F g) + finrank K (F h) + finrank K (F (g * h)) +
      finrank K (F (g * h ^ 2)) = 8 + 3 * finrank K ↥(F g ⊓ F h) := by
    intro g h
    have := card_fix_one φ hc (hι3 g) (hι3 h)
    rw [e1, e2, hFA, hFA, hFA, hFA, hV] at this
    exact this
  have R2 : ∀ x g h : E, finrank K ↥(F x ⊓ F g) + finrank K ↥(F x ⊓ F h) +
      finrank K ↥(F x ⊓ F (g * h)) + finrank K ↥(F x ⊓ F (g * h ^ 2)) =
        finrank K (F x) + 3 * finrank K ↥(F x ⊓ F g ⊓ F h) := by
    intro x g h
    have := card_fix_two φ hc (hι3 x) (hι3 g) (hι3 h)
    rw [e1, e2, hFA, hFA, hFA, hFA, hFA] at this
    exact this
  have hd24 : ∀ x : E, x ≠ 1 → finrank K (F x) = 2 ∨ finrank K (F x) = 4 := h24
  have hb24 : ∀ x : E, x ≠ 1 → 2 ≤ finrank K (F x) ∧ finrank K (F x) ≤ 4 ∧
      finrank K (F x) % 2 = 0 := fun x hx => by
    have := Nat.even_iff.mp (heven x)
    rcases hd24 x hx with h | h <;> omega
  clear_value F
  clear hFA h24 hφ hφι e1 e2 hι3
  have key : ∀ m a : E, m ≠ 1 → a ∉ Subgroup.zpowers m →
      finrank K (F m) + finrank K (F a) + finrank K (F (m * a)) + finrank K (F (m * a ^ 2)) =
        8 + 3 * finrank K ↥(F m ⊓ F a) ∧ a ≠ 1 ∧ m * a ≠ 1 ∧ m * a ^ 2 ≠ 1 := by
    intro m a hm ha
    obtain ⟨h1, h2⟩ := not_mem_mul_facts (H := Subgroup.zpowers m) hexp (Subgroup.mem_zpowers m) ha
    exact ⟨R1 m a, fun h => ha (h ▸ Subgroup.one_mem _), fun h => h1 (h ▸ Subgroup.one_mem _),
      fun h => h2 (h ▸ Subgroup.one_mem _)⟩
  have hcard9 : ∀ H : Subgroup E, Nat.card H ≤ 9 → ∃ z, z ∉ H := fun H hH =>
    exists_not_mem_of_card_lt (by omega)
  have hcardE : 1 < Nat.card E := by omega
  have hex1 : ∃ m : E, m ≠ 1 := by
    have h1 : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp hcardE
    exact exists_ne 1
  obtain ⟨m, hm1, hmd⟩ : ∃ m : E, m ≠ 1 ∧
      (finrank K (F m) = 4 ∨ ∀ x : E, x ≠ 1 → finrank K (F x) = 2) := by
    by_cases hex : ∃ m : E, m ≠ 1 ∧ finrank K (F m) = 4
    · obtain ⟨m, hm, h4⟩ := hex
      exact ⟨m, hm, Or.inl h4⟩
    · push Not at hex
      obtain ⟨m, hm⟩ := hex1
      refine ⟨m, hm, Or.inr fun x hx => ?_⟩
      rcases hd24 x hx with h | h
      · exact h
      · exact absurd h (hex x hx)
  obtain ⟨y, hy⟩ := exists_not_mem_of_card_lt (H := Subgroup.zpowers m)
    (lt_of_le_of_lt (by rw [Nat.card_zpowers]; exact orderOf_le_of_pow_eq_one (by norm_num) (hexp m))
      (by omega : 3 < Nat.card E))
  set H₂ : Subgroup E := Subgroup.zpowers m ⊔ Subgroup.zpowers y with hH₂
  obtain ⟨z, hz⟩ := hcard9 H₂ (by
    have h1 := card_sup_zpowers_le hexp (Subgroup.zpowers m) y
    have h3m : Nat.card (Subgroup.zpowers m) ≤ 3 := card_zpowers_le_three hexp m
    change Nat.card ↥(Subgroup.zpowers m ⊔ Subgroup.zpowers y) ≤ 9
    omega)
  have hmH₂ : m ∈ H₂ := Subgroup.mem_sup_left (Subgroup.mem_zpowers m)
  have hyH₂ : y ∈ H₂ := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hzm : z ∉ Subgroup.zpowers m := fun h => hz (Subgroup.mem_sup_left h)
  obtain ⟨hyz, hyz2⟩ := not_mem_mul_facts (H := H₂) hexp hyH₂ hz
  have hyzm : y * z ∉ Subgroup.zpowers m := fun h => hyz (Subgroup.mem_sup_left h)
  have hyz2m : y * z ^ 2 ∉ Subgroup.zpowers m := fun h => hyz2 (Subgroup.mem_sup_left h)
  obtain ⟨k1, a1, b1, c1⟩ := key m y hm1 hy
  obtain ⟨k2, a2, b2, c2⟩ := key m z hm1 hzm
  obtain ⟨k3, a3, b3, c3⟩ := key m (y * z) hm1 hyzm
  obtain ⟨k4, a4, b4, c4⟩ := key m (y * z ^ 2) hm1 hyz2m
  have r2 := R2 m y z
  have hall2 : finrank K (F m) = 4 ∨ ∀ x : E, x ≠ 1 → finrank K (F x) = 2 := hmd
  rcases hall2 with h4 | hall
  · have hD : ∀ a : E, ∀ (ha : a ∉ Subgroup.zpowers m),
        finrank K (F m) + finrank K (F a) + finrank K (F (m * a)) + finrank K (F (m * a ^ 2)) =
          8 + 3 * finrank K ↥(F m ⊓ F a) → a ≠ 1 → m * a ≠ 1 → m * a ^ 2 ≠ 1 →
          finrank K ↥(F m ⊓ F a) = 2 := fun a ha hk h1 h2 h3 =>
      D_eq_two h4 hk (hb24 a h1) (hb24 _ h2) (hb24 _ h3)
    have d1 := hD y hy k1 a1 b1 c1
    have d2 := hD z hzm k2 a2 b2 c2
    have d3 := hD (y * z) hyzm k3 a3 b3 c3
    have d4 := hD (y * z ^ 2) hyz2m k4 a4 b4 c4
    rw [d1, d2, d3, d4, h4] at r2
    omega
  · have hD : ∀ a : E,
        finrank K (F m) + finrank K (F a) + finrank K (F (m * a)) + finrank K (F (m * a ^ 2)) =
          8 + 3 * finrank K ↥(F m ⊓ F a) → a ≠ 1 → m * a ≠ 1 → m * a ^ 2 ≠ 1 →
          finrank K ↥(F m ⊓ F a) = 0 := fun a hk h1 h2 h3 =>
      D_eq_zero (hall m hm1) (hall a h1) (hall _ h2) (hall _ h3) hk
    have d1 := hD y k1 a1 b1 c1
    have d2 := hD z k2 a2 b2 c2
    have d3 := hD (y * z) k3 a3 b3 c3
    have d4 := hD (y * z ^ 2) k4 a4 b4 c4
    rw [d1, d2, d3, d4, hall m hm1] at r2
    omega

end CFSG.LocalAnalysis.GLTheoremA
