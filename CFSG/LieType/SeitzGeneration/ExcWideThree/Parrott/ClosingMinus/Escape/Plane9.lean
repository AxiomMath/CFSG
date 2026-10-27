module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNFDefs
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNF1

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape

open CFSG.RankThree.PartTwo.Sec19

variable {G : Type} [Group G]

theorem pow_mod_three {x : G} (hx3 : x ^ 3 = 1) (a : ℕ) : x ^ a = x ^ (a % 3) := by
  conv_lhs => rw [← Nat.mod_add_div a 3, pow_add, pow_mul, hx3, one_pow, mul_one]

theorem closure_pair_normal_form {x y : G} (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hxy : x * y = y * x) {f : G} (hf : f ∈ Subgroup.closure ({x, y} : Set G)) :
    ∃ a b : ℕ, a < 3 ∧ b < 3 ∧ f = x ^ a * y ^ b := by
  have hc : Commute x y := hxy
  induction hf using Subgroup.closure_induction with
  | mem f hf =>
    rcases hf with rfl | rfl
    · exact ⟨1, 0, by norm_num, by norm_num, by simp⟩
    · exact ⟨0, 1, by norm_num, by norm_num, by simp⟩
  | one => exact ⟨0, 0, by norm_num, by norm_num, by simp⟩
  | mul f g _ _ hf hg =>
    obtain ⟨a, b, -, -, rfl⟩ := hf
    obtain ⟨c, d, -, -, rfl⟩ := hg
    refine ⟨(a + c) % 3, (b + d) % 3, Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), ?_⟩
    rw [← pow_mod_three hx3, ← pow_mod_three hy3, pow_add, pow_add]
    have h1 : y ^ b * x ^ c = x ^ c * y ^ b := ((hc.pow_pow c b).eq).symm
    calc x ^ a * y ^ b * (x ^ c * y ^ d) = x ^ a * (y ^ b * x ^ c) * y ^ d := by group
      _ = x ^ a * (x ^ c * y ^ b) * y ^ d := by rw [h1]
      _ = x ^ a * x ^ c * (y ^ b * y ^ d) := by group
  | inv f _ hf =>
    obtain ⟨a, b, ha, hb, rfl⟩ := hf
    refine ⟨(3 - a) % 3, (3 - b) % 3, Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), ?_⟩
    rw [← pow_mod_three hx3, ← pow_mod_three hy3]
    have hxa : (x ^ a)⁻¹ = x ^ (3 - a) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, show a + (3 - a) = 3 by omega, hx3]
    have hyb : (y ^ b)⁻¹ = y ^ (3 - b) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, show b + (3 - b) = 3 by omega, hy3]
    rw [mul_inv_rev, hxa, hyb]
    exact ((hc.pow_pow (3 - a) (3 - b)).eq).symm

theorem closure_pair_comm_cube {x y : G} (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hxy : x * y = y * x) :
    (∀ f ∈ Subgroup.closure ({x, y} : Set G), ∀ g ∈ Subgroup.closure ({x, y} : Set G),
      f * g = g * f) ∧ ∀ f ∈ Subgroup.closure ({x, y} : Set G), f ^ 3 = 1 := by
  have hc : Commute x y := hxy
  refine ⟨fun f hf g hg => ?_, fun f hf => ?_⟩
  · obtain ⟨a, b, -, -, rfl⟩ := closure_pair_normal_form hx3 hy3 hxy hf
    obtain ⟨c, d, -, -, rfl⟩ := closure_pair_normal_form hx3 hy3 hxy hg
    have h1 : Commute (x ^ a) (y ^ d) := hc.pow_pow a d
    have h2 : Commute (y ^ b) (x ^ c) := (hc.pow_pow c b).symm
    have h3 : Commute (x ^ a) (x ^ c) := Commute.pow_pow_self x a c
    have h4 : Commute (y ^ b) (y ^ d) := Commute.pow_pow_self y b d
    exact ((h3.mul_right h1).mul_left (h2.mul_right h4)).eq
  · obtain ⟨a, b, -, -, rfl⟩ := closure_pair_normal_form hx3 hy3 hxy hf
    rw [(hc.pow_pow a b).mul_pow, ← pow_mul, ← pow_mul, mul_comm a, mul_comm b, pow_mul, pow_mul,
      hx3, hy3, one_pow, one_pow, one_mul]

theorem isElementaryAbelian_closure_pair {x y : G} (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hxy : x * y = y * x) : CFSG.IsElementaryAbelian 3 (Subgroup.closure ({x, y} : Set G)) :=
  isElementaryAbelian_three_of (closure_pair_comm_cube hx3 hy3 hxy).1
    (closure_pair_comm_cube hx3 hy3 hxy).2

theorem card_closure_pair {x y : G} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hy3 : y ^ 3 = 1)
    (hxy : x * y = y * x) (hyx : y ∉ Subgroup.zpowers x) :
    Nat.card (Subgroup.closure ({x, y} : Set G)) = 3 ^ 2 := by
  classical
  set F := Subgroup.closure ({x, y} : Set G) with hF
  have hfin : Finite F := by
    let φ : Fin 3 × Fin 3 → G := fun p => x ^ (p.1 : ℕ) * y ^ (p.2 : ℕ)
    have hsub : (F : Set G) ⊆ Set.range φ := by
      intro f hf
      obtain ⟨a, b, ha, hb, rfl⟩ := closure_pair_normal_form hx3 hy3 hxy hf
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
    exact Set.Finite.subset (Set.finite_range φ) hsub
  have hle : Nat.card F ≤ 9 := by
    let φ : Fin 3 × Fin 3 → F := fun p => ⟨x ^ (p.1 : ℕ) * y ^ (p.2 : ℕ), mul_mem
      (pow_mem (Subgroup.subset_closure (by simp)) _)
      (pow_mem (Subgroup.subset_closure (by simp)) _)⟩
    have hφ : Function.Surjective φ := by
      rintro ⟨f, hf⟩
      obtain ⟨a, b, ha, hb, rfl⟩ := closure_pair_normal_form hx3 hy3 hxy hf
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
    have := Nat.card_le_card_of_surjective φ hφ
    simpa using this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 F := by
    intro f
    refine ⟨1, Subtype.ext ?_⟩
    simpa using (closure_pair_comm_cube hx3 hy3 hxy).2 f f.2
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hxF : x ∈ F := Subgroup.subset_closure (by simp)
  have hyF : y ∈ F := Subgroup.subset_closure (by simp)
  have hx2 : x ^ 2 ≠ 1 := fun h => hx1 (by
    have e : x ^ 3 = x ^ 2 * x := pow_succ x 2
    rw [h, one_mul] at e
    exact e.symm.trans hx3)
  have hxx2 : x ≠ x ^ 2 := fun h => hx1 (mul_left_cancel (a := x) (by
    rw [mul_one, ← pow_two]
    exact h.symm))
  have hy1 : y ≠ 1 := fun h => hyx (h ▸ one_mem _)
  have hyx1 : y ≠ x := fun h => hyx (h ▸ Subgroup.mem_zpowers x)
  have hyx2 : y ≠ x ^ 2 := fun h => hyx (h ▸ Subgroup.npow_mem_zpowers x 2)
  have h4 : 4 ≤ Nat.card F :=
    nf1_four_le_card F (one_mem _) hxF (pow_mem hxF 2) hyF (Ne.symm hx1) (Ne.symm hx2)
      (Ne.symm hy1) hxx2 (Ne.symm hyx1) (Ne.symm hyx2)
  rw [hn] at hle h4 ⊢
  have hn2 : n = 2 := by
    rcases (by omega : n ≤ 1 ∨ n = 2 ∨ 3 ≤ n) with h | h | h
    · exfalso
      have : 3 ^ n ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) h
      omega
    · exact h
    · exfalso
      have : 3 ^ 3 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) h
      omega
  rw [hn2]

theorem centralizer_sq_le {w : G} (hw3 : w ^ 3 = 1) :
    Subgroup.centralizer ({w ^ 2} : Set G) ≤ Subgroup.centralizer ({w} : Set G) := by
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff] at hk ⊢
  have hw : w = (w ^ 2) ^ 2 := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hw3, one_mul]
  have h2 : Commute k ((w ^ 2) ^ 2) := (show Commute k (w ^ 2) from hk).pow_right 2
  rw [← hw] at h2
  exact h2.eq

theorem centralizer_le_of_mem_closure_pair {x y : G} (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hxy : x * y = y * x) {H : Subgroup G} (hCx : Subgroup.centralizer ({x} : Set G) ≤ H)
    (hCy : Subgroup.centralizer ({y} : Set G) ≤ H)
    (hCxy : Subgroup.centralizer ({x * y} : Set G) ≤ H)
    (hCx2y : Subgroup.centralizer ({x ^ 2 * y} : Set G) ≤ H) {f : G}
    (hf : f ∈ Subgroup.closure ({x, y} : Set G)) (hf1 : f ≠ 1) :
    Subgroup.centralizer ({f} : Set G) ≤ H := by
  have hc : Commute x y := hxy
  have hcube : ∀ w : G, w ∈ Subgroup.closure ({x, y} : Set G) → w ^ 3 = 1 := fun w hw =>
    (closure_pair_comm_cube hx3 hy3 hxy).2 w hw
  have hxF : x ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hyF : y ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hsq : ∀ w, w ∈ Subgroup.closure ({x, y} : Set G) →
      Subgroup.centralizer ({w} : Set G) ≤ H → Subgroup.centralizer ({w ^ 2} : Set G) ≤ H :=
    fun w hw hC => (centralizer_sq_le (hcube w hw)).trans hC
  obtain ⟨a, b, ha, hb, rfl⟩ := closure_pair_normal_form hx3 hy3 hxy hf
  interval_cases a <;> interval_cases b
  · exact absurd (by simp) hf1
  · simpa using hCy
  · simpa using hsq y hyF hCy
  · simpa using hCx
  · simpa using hCxy
  ·
    have e : x ^ 1 * y ^ 2 = (x ^ 2 * y) ^ 2 := by
      rw [(hc.pow_left 2).mul_pow, ← pow_mul]
      rw [show x ^ (2 * 2) = x ^ 1 by rw [show 2 * 2 = 3 + 1 from rfl, pow_add, hx3, one_mul]]
    rw [e]
    exact hsq _ (mul_mem (pow_mem hxF 2) hyF) hCx2y
  · simpa using hsq x hxF hCx
  · simpa using hCx2y
  ·
    have e : x ^ 2 * y ^ 2 = (x * y) ^ 2 := by rw [hc.mul_pow]
    rw [e]
    exact hsq _ (mul_mem hxF hyF) hCxy

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape
