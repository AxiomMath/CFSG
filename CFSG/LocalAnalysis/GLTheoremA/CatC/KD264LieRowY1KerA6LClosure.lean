module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA6L

theorem pow_eq_pow_mod {G : Type} [Group G] {x : G} (hx : x ^ 3 = 1) (n : ℕ) :
    x ^ n = x ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hx, one_pow, one_mul]

theorem exps_eq_of_eq {G : Type} [Group G] {g t : G} (hg3 : g ^ 3 = 1)
    (ht3 : t ^ 3 = 1) (hg1 : g ≠ 1) (hnot : ∀ k : ℕ, t ≠ g ^ k) {a b c d : ℕ}
    (ha : a < 3) (hc : c < 3) (hb : b < 3) (hd : d < 3) (h : g ^ a * t ^ b = g ^ c * t ^ d) :
    b = d ∧ a = c := by
  have hN : t ^ (b + 2 * d) = g ^ (2 * a + c) := by
    have h1 : g ^ a * t ^ b * t ^ (2 * d) = g ^ c * t ^ d * t ^ (2 * d) := by rw [h]
    have h2 : t ^ d * t ^ (2 * d) = 1 := by
      rw [← pow_add, show d + 2 * d = 3 * d by ring, pow_mul, ht3, one_pow]
    have h3 : g ^ a * t ^ b * t ^ (2 * d) = g ^ a * t ^ (b + 2 * d) := by
      rw [mul_assoc, ← pow_add]
    have h4 : g ^ c * t ^ d * t ^ (2 * d) = g ^ c := by
      rw [mul_assoc, h2, mul_one]
    have h5 : g ^ (2 * a) * (g ^ a * t ^ (b + 2 * d)) = g ^ (2 * a) * g ^ c := by
      rw [← h3, ← h4, ← h1]
    have h6 : g ^ (2 * a) * g ^ a = 1 := by
      rw [← pow_add, show 2 * a + a = 3 * a by ring, pow_mul, hg3, one_pow]
    have h7 : g ^ (2 * a) * (g ^ a * t ^ (b + 2 * d)) = t ^ (b + 2 * d) := by
      rw [← mul_assoc, h6, one_mul]
    have h8 : g ^ (2 * a) * g ^ c = g ^ (2 * a + c) := by rw [← pow_add]
    rw [h7, h8] at h5
    exact h5
  have hbd : b = d := by
    by_contra hne
    have hmod : (b + 2 * d) % 3 = 1 ∨ (b + 2 * d) % 3 = 2 := by omega
    rcases hmod with h1 | h1
    · apply hnot (2 * a + c)
      have : t ^ (b + 2 * d) = t := by
        rw [pow_eq_pow_mod ht3 (b + 2 * d), h1, pow_one]
      rw [← this, hN]
    · apply hnot (2 * (2 * a + c))
      have ht2 : t ^ 2 = g ^ (2 * a + c) := by
        rw [← hN, pow_eq_pow_mod ht3 (b + 2 * d), h1]
      calc t = t ^ 4 := by
            rw [show t ^ 4 = t ^ 3 * t from pow_succ t 3, ht3, one_mul]
        _ = (t ^ 2) ^ 2 := by rw [← pow_mul]
        _ = (g ^ (2 * a + c)) ^ 2 := by rw [ht2]
        _ = g ^ (2 * (2 * a + c)) := by rw [← pow_mul]; ring_nf
  subst hbd
  refine ⟨rfl, ?_⟩
  have hac : g ^ a = g ^ c := mul_right_cancel h
  by_contra hne
  have e1 : g ^ a * g ^ (2 * c) = 1 := by
    rw [hac, ← pow_add, show c + 2 * c = 3 * c by ring, pow_mul, hg3, one_pow]
  rw [← pow_add] at e1
  have hm : (a + 2 * c) % 3 = 1 ∨ (a + 2 * c) % 3 = 2 := by omega
  rcases hm with h6 | h6
  · rw [pow_eq_pow_mod hg3, h6, pow_one] at e1
    exact hg1 e1
  · rw [pow_eq_pow_mod hg3, h6] at e1
    apply hg1
    calc g = g ^ 4 := by rw [show g ^ 4 = g ^ 3 * g from pow_succ g 3, hg3, one_mul]
      _ = (g ^ 2) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [e1, one_pow]

theorem normal_form_mul {G : Type} [Group G] {g t : G} (hgt : g * t = t * g) (hg3 : g ^ 3 = 1)
    (ht3 : t ^ 3 = 1) (a b c d : ℕ) :
    g ^ a * t ^ b * (g ^ c * t ^ d) = g ^ ((a + c) % 3) * t ^ ((b + d) % 3) := by
  have hcomm : Commute g t := hgt
  have h1 : g ^ a * t ^ b * (g ^ c * t ^ d) = g ^ (a + c) * t ^ (b + d) := by
    have hc : t ^ b * g ^ c = g ^ c * t ^ b := (hcomm.symm.pow_pow b c)
    calc g ^ a * t ^ b * (g ^ c * t ^ d) = g ^ a * (t ^ b * g ^ c) * t ^ d := by
          simp only [mul_assoc]
      _ = g ^ a * (g ^ c * t ^ b) * t ^ d := by rw [hc]
      _ = g ^ (a + c) * t ^ (b + d) := by
          rw [pow_add, pow_add]
          simp only [mul_assoc]
  rw [h1, pow_eq_pow_mod hg3 (a + c), pow_eq_pow_mod ht3 (b + d)]

theorem card_closure_pair {G : Type} [Group G] (g t : G) (hgt : g * t = t * g) (hg3 : g ^ 3 = 1)
    (ht3 : t ^ 3 = 1) (hg1 : g ≠ 1) (hnot : ∀ k : ℕ, t ≠ g ^ k) :
    Nat.card (Subgroup.closure ({g, t} : Set G)) = 9 := by
  let φ : Fin 3 × Fin 3 → G := fun p => g ^ (p.1 : ℕ) * t ^ (p.2 : ℕ)
  have hφinj : Function.Injective φ := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [φ] at h
    obtain ⟨hbd, hac⟩ := exps_eq_of_eq hg3 ht3 hg1 hnot a.isLt c.isLt b.isLt d.isLt h
    exact Prod.ext (Fin.ext hac) (Fin.ext hbd)
  let S : Subgroup G :=
    { carrier := Set.range φ
      mul_mem' := by
        rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
        refine ⟨(⟨((p.1 : ℕ) + (q.1 : ℕ)) % 3, Nat.mod_lt _ (by norm_num)⟩,
          ⟨((p.2 : ℕ) + (q.2 : ℕ)) % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
        simp only [φ]
        rw [normal_form_mul hgt hg3 ht3]
      one_mem' := ⟨(0, 0), by simp [φ]⟩
      inv_mem' := by
        rintro _ ⟨p, rfl⟩
        refine ⟨(⟨(2 * (p.1 : ℕ)) % 3, Nat.mod_lt _ (by norm_num)⟩,
          ⟨(2 * (p.2 : ℕ)) % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
        simp only [φ]
        have hinv : (g ^ (p.1 : ℕ) * t ^ (p.2 : ℕ))⁻¹ =
            g ^ (2 * (p.1 : ℕ)) * t ^ (2 * (p.2 : ℕ)) := by
          apply inv_eq_of_mul_eq_one_right
          rw [normal_form_mul hgt hg3 ht3, show ((p.1 : ℕ) + 2 * (p.1 : ℕ)) % 3 = 0 by omega,
            show ((p.2 : ℕ) + 2 * (p.2 : ℕ)) % 3 = 0 by omega]
          simp
        rw [hinv, pow_eq_pow_mod hg3 (2 * (p.1 : ℕ)), pow_eq_pow_mod ht3 (2 * (p.2 : ℕ))] }
  have hS : Subgroup.closure ({g, t} : Set G) = S := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact ⟨(1, 0), by simp [φ]⟩
      · exact ⟨(0, 1), by simp [φ]⟩
    · rintro x ⟨p, rfl⟩
      apply Subgroup.mul_mem
      · apply Subgroup.pow_mem
        exact Subgroup.subset_closure (by simp)
      · apply Subgroup.pow_mem
        exact Subgroup.subset_closure (by simp)
  rw [hS]
  show Nat.card (Set.range φ) = 9
  rw [Nat.card_range_of_injective hφinj, Nat.card_prod, Nat.card_eq_fintype_card,
    Fintype.card_fin]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA6L

end
