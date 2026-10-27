module

public import CFSG.LieType.Ree.SuzukiUnipotentStructure

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Bend

open CFSG.Blueprint CFSG.LieType.Ree

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem suzukiU_commutator (hK : Nat.card K = 2 ^ (2 * a + 1)) (u v l : K) :
    suzukiSElt a K u v * suzukiSElt a K (l * u) 0 * (suzukiSElt a K u v)⁻¹ *
        (suzukiSElt a K (l * u) 0)⁻¹ =
      suzukiSElt a K 0 ((l - l ^ 2 ^ (a + 1)) * u ^ (2 ^ (a + 1) + 1)) := by
  set x := suzukiSElt a K u v
  set y := suzukiSElt a K (l * u) 0
  have hθ0 : 2 ^ (a + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hxy : x * y =
      suzukiSElt a K 0 ((l - l ^ 2 ^ (a + 1)) * u ^ (2 ^ (a + 1) + 1)) * (y * x) := by
    simp only [x, y, suzukiSElt_mul hK, zero_pow hθ0, zero_mul, add_zero, zero_add]
    congr 1
    · ring
    · rw [mul_pow, pow_succ]
      ring
  calc x * y * x⁻¹ * y⁻¹ = (x * y) * (y * x)⁻¹ := by group
    _ = _ := by rw [hxy, mul_assoc, mul_inv_cancel, mul_one]

theorem suzukiU_bigComm (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {x : suzukiGroup a K} (hx : x ∈ suzukiU a K) (z : suzukiGroup a K)
    (h : ∀ y ∈ suzukiU a K, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z) :
    ∀ y ∈ suzukiU a K, Commute x y := by
  classical
  obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hx
  obtain ⟨h2, hadd, hθθ⟩ := suzuki_frob_data a hK
  by_cases hu : u = 0
  · subst hu
    intro y hy
    obtain ⟨c, d, rfl⟩ := (mem_suzukiU_iff hK).1 hy
    exact suzukiSElt_zero_commute hK v c d
  exfalso
  set θ := 2 ^ (a + 1) with hθ
  set φ : K → K := fun l => (l - l ^ θ) * u ^ (θ + 1) with hφ
  have hu' : u ^ (θ + 1) ≠ 0 := pow_ne_zero _ hu
  have hφadd : ∀ l₁ l₂ : K, φ (l₁ - l₂) = φ l₁ - φ l₂ := by
    intro l₁ l₂
    have hneg : ∀ w : K, (-w) ^ θ = -w ^ θ := fun w => by
      have := hadd w (-w)
      rw [add_neg_cancel, zero_pow (pow_ne_zero _ two_ne_zero)] at this
      linear_combination -this
    simp only [hφ, sub_eq_add_neg, hadd, hneg]
    ring
  have hker : ∀ l : K, φ l = 0 → l = 0 ∨ l = 1 := by
    intro l hl
    have h1 : l ^ θ = l := by
      have := (mul_eq_zero.mp hl).resolve_right hu'
      linear_combination -this
    have h3 : l ^ 2 = l := by rw [← hθθ l, h1, h1]
    have : l * (l - 1) = 0 := by linear_combination h3
    rcases mul_eq_zero.mp this with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (by linear_combination h0)
  have hcomm : ∀ l : K, φ l = 0 ∨ suzukiSElt a K 0 (φ l) = z := by
    intro l
    rcases h _ (suzukiSElt_mem_suzukiU a K (l * u) 0) with h1 | h1
    · rw [suzukiU_commutator hK, ← suzukiSElt_zero_zero hK, suzukiSElt_inj] at h1
      exact Or.inl h1.2
    · rw [suzukiU_commutator hK] at h1
      exact Or.inr h1
  have hcover : ∃ s : Finset K, s.card ≤ 4 ∧ ∀ l : K, l ∈ s := by
    by_cases hex : ∃ l₁, φ l₁ ≠ 0
    · obtain ⟨l₁, hl₁⟩ := hex
      refine ⟨{0, 1, l₁, l₁ + 1}, ?_, fun l => ?_⟩
      · refine (Finset.card_insert_le _ _).trans ?_
        refine (Nat.succ_le_succ (Finset.card_insert_le _ _)).trans ?_
        refine (Nat.succ_le_succ (Nat.succ_le_succ (Finset.card_insert_le _ _))).trans ?_
        simp
      · by_cases hl : φ l = 0
        · rcases hker l hl with rfl | rfl <;> simp
        · have hz1 := (hcomm l).resolve_left hl
          have hz2 := (hcomm l₁).resolve_left hl₁
          have heq : φ l = φ l₁ := by
            have := hz1.trans hz2.symm
            rw [suzukiSElt_inj] at this
            exact this.2
          have hd : φ (l - l₁) = 0 := by rw [hφadd, heq, sub_self]
          rcases hker _ hd with h0 | h0
          · have : l = l₁ := by linear_combination h0
            simp [this]
          · have : l = l₁ + 1 := by linear_combination h0
            simp [this]
    · push Not at hex
      refine ⟨{0, 1}, ?_, fun l => ?_⟩
      · exact (Finset.card_insert_le _ _).trans (by simp)
      · rcases hker l (hex l) with rfl | rfl <;> simp
  obtain ⟨s, hs, hsK⟩ := hcover
  have : Fintype K := Fintype.ofFinite K
  have hcard : Nat.card K ≤ 4 := by
    rw [Nat.card_eq_fintype_card]
    exact (Finset.card_le_card (fun l _ => hsK l) : Finset.univ.card ≤ s.card).trans hs
  have h8 : 8 ≤ 2 ^ (2 * a + 1) :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end CFSG.ClassicalInvolution.Q3.TL4.Bend
