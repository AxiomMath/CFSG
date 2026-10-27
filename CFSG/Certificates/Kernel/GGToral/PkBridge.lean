module

public import Certificates.Data.Kernel.GGToral.PkTag
public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralCertSpec

public section

namespace CFSG.KC.GGToral

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.StepTwoToralCert

theorem lane_eq (v j : ℕ) : lane v j = v / 2 ^ (16 * j) % 65536 := by
  change (v >>> (16 * j)) % 65536 = _
  rw [Nat.shiftRight_eq_div_pow]

theorem lane_add_mul_pow {A B n j : ℕ} (hj : j < n) :
    lane (A + 2 ^ (16 * n) * B) j = lane A j := by
  rw [lane_eq, lane_eq]
  obtain ⟨k, rfl⟩ : ∃ k, n = j + 1 + k := ⟨n - (j + 1), by omega⟩
  have h : 2 ^ (16 * (j + 1 + k)) * B = 2 ^ (16 * j) * (65536 * (2 ^ (16 * k) * B)) := by
    rw [show 16 * (j + 1 + k) = 16 * j + 16 + 16 * k by ring, pow_add, pow_add]
    norm_num
    ring
  rw [h, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

theorem lane_add_mul_pow_self {A B n : ℕ} (hA : A < 2 ^ (16 * n)) :
    lane (A + 2 ^ (16 * n) * B) n = B % 65536 := by
  rw [lane_eq, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hA, zero_add]

theorem packN_succ (n : ℕ) (f : ℕ → ℕ) : packN (n + 1) f = packN n f + 2 ^ (16 * n) * f n := by
  change packN n f + (f n <<< (16 * n)) = _
  rw [Nat.shiftLeft_eq, mul_comm]

theorem packN_lt {n : ℕ} {f : ℕ → ℕ} (hf : ∀ j < n, f j < 65536) : packN n f < 2 ^ (16 * n) := by
  induction n with
  | zero => simp [packN]
  | succ n ih =>
    rw [packN_succ]
    have h1 := ih fun j hj => hf j (by omega)
    have h2 := hf n (by omega)
    have h3 : 2 ^ (16 * (n + 1)) = 2 ^ (16 * n) * 65536 := by
      rw [show 16 * (n + 1) = 16 * n + 16 by ring, pow_add]
      norm_num
    rw [h3]
    nlinarith

theorem lane_packN {n : ℕ} {f : ℕ → ℕ} (hf : ∀ j < n, f j < 65536) {j : ℕ} (hj : j < n) :
    lane (packN n f) j = f j := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [packN_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [lane_add_mul_pow hj]
      exact ih (fun k hk => hf k (by omega)) hj
    · rw [lane_add_mul_pow_self (packN_lt fun k hk => hf k (by omega))]
      exact Nat.mod_eq_of_lt (hf j (by omega))

theorem modL_eq_packN (p n x : ℕ) : modL p n x = packN n (fun j => lane x j % p) := rfl

theorem packN_eq_sum (n : ℕ) (f : ℕ → ℕ) :
    packN n f = ∑ j ∈ Finset.range n, 2 ^ (16 * j) * f j := by
  induction n with
  | zero => rfl
  | succ n ih => rw [packN_succ, ih, Finset.sum_range_succ]

theorem packN_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, f j = g j) : packN n f = packN n g := by
  rw [packN_eq_sum, packN_eq_sum]
  exact Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.mp hj)]

theorem eq_packN_lane {n x : ℕ} (hx : x < 2 ^ (16 * n)) : x = packN n (lane x) := by
  induction n generalizing x with
  | zero => simp at hx; simp [hx, packN]
  | succ n ih =>
    have hB : 2 ^ (16 * (n + 1)) = 2 ^ (16 * n) * 65536 := by
      rw [show 16 * (n + 1) = 16 * n + 16 by ring, pow_add]
      norm_num
    have hpos : 0 < 2 ^ (16 * n) := by positivity
    have hlo := Nat.mod_lt x hpos
    have hdiv : x / 2 ^ (16 * n) < 65536 := by
      rw [Nat.div_lt_iff_lt_mul hpos]
      rw [hB] at hx
      linarith
    have hsplit : x = x % 2 ^ (16 * n) + 2 ^ (16 * n) * (x / 2 ^ (16 * n)) :=
      (Nat.mod_add_div x _).symm
    rw [packN_succ]
    have hl : ∀ j < n, lane (x % 2 ^ (16 * n)) j = lane x j := fun j hj => by
      conv_rhs => rw [hsplit]
      rw [lane_add_mul_pow hj]
    have htop : lane x n = x / 2 ^ (16 * n) := by
      conv_lhs => rw [hsplit]
      rw [lane_add_mul_pow_self hlo, Nat.mod_eq_of_lt hdiv]
    rw [← packN_congr hl, ← ih hlo, htop]
    exact hsplit

@[expose] def convN (n : ℕ) (f g : ℕ → ℕ) (s : ℕ) : ℕ :=
  ∑ x ∈ (Finset.range n ×ˢ Finset.range n).filter (fun x => x.1 + x.2 = s), f x.1 * g x.2

theorem packN_mul (n : ℕ) (f g : ℕ → ℕ) :
    packN n f * packN n g = packN (2 * n - 1) (convN n f g) := by
  rw [packN_eq_sum, packN_eq_sum, packN_eq_sum, Finset.sum_mul_sum, ← Finset.sum_product']
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun x : ℕ × ℕ => x.1 + x.2)
    (t := Finset.range (2 * n - 1)) (fun x hx => by
      simp only [Finset.mem_product, Finset.mem_range] at hx ⊢
      omega)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [convN, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hs : x.1 + x.2 = s := (Finset.mem_filter.mp hx).2
  rw [← hs, mul_add, pow_add]
  ring

theorem convN_le {n F G : ℕ} {f g : ℕ → ℕ} (hf : ∀ j < n, f j ≤ F) (hg : ∀ j < n, g j ≤ G)
    (s : ℕ) : convN n f g s ≤ n * (F * G) := by
  rw [convN]
  have hcard : ((Finset.range n ×ˢ Finset.range n).filter (fun x => x.1 + x.2 = s)).card ≤ n := by
    calc _ ≤ (Finset.range n).card := Finset.card_le_card_of_injOn (fun x => x.1)
            (fun x hx => by
              simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
                Set.mem_setOf_eq] at hx
              simp only [Finset.coe_range, Set.mem_Iio]
              exact hx.1.1)
            (fun x hx y hy hxy => by
              simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
                Set.mem_setOf_eq] at hx hy
              simp only at hxy
              exact Prod.ext hxy (by omega))
      _ = n := Finset.card_range n
  calc _ ≤ ((Finset.range n ×ˢ Finset.range n).filter (fun x => x.1 + x.2 = s)).card •
          (F * G) := Finset.sum_le_card_nsmul _ _ _ fun x hx => by
            simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx
            exact Nat.mul_le_mul (hf _ hx.1.1) (hg _ hx.1.2)
    _ ≤ n * (F * G) := by
      rw [smul_eq_mul]
      exact Nat.mul_le_mul_right _ hcard

theorem convN_rev (n : ℕ) (a g : ℕ → ℕ) :
    convN n (fun k => a (n - 1 - k)) g (n - 1) = ∑ l ∈ Finset.range n, a l * g l := by
  rw [convN]
  refine Finset.sum_nbij' (fun x => x.2) (fun l => (n - 1 - l, l)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx ⊢
    exact hx.1.2
  · intro l hl
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hl ⊢
    omega
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx
    exact Prod.ext (show n - 1 - x.2 = x.1 by omega) rfl
  · intro l _
    rfl
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx
    rw [show n - 1 - x.1 = x.2 by omega]

theorem lane_mul_rev {n F G : ℕ} {a g : ℕ → ℕ} (hn : 0 < n) (ha : ∀ j < n, a j ≤ F)
    (hg : ∀ j < n, g j ≤ G) (hb : n * (F * G) < 65536) :
    lane (packN n (fun k => a (n - 1 - k)) * packN n g) (n - 1) =
      ∑ l ∈ Finset.range n, a l * g l := by
  rw [packN_mul, lane_packN (fun s _ => lt_of_le_of_lt (convN_le (F := F) (G := G)
    (fun j hj => ha _ (by omega)) hg s) hb) (by omega), convN_rev]

theorem tgRank_eq (τ : Tag) : tgRank τ = τ.rank := by
  cases τ <;> rfl

theorem cartan_self {τ : Tag} (hτ : tgOK τ = true) (i : Fin τ.rank) : τ.cartan i i = 2 := by
  cases τ <;> simp [tgOK] at hτ <;> fin_cases i <;> decide +kernel

theorem tgCneg_lane {τ : Tag} (hτ : tgOK τ = true) (i j : Fin τ.rank) (hij : i ≠ j) :
    τ.cartan i j = -((lane (row (tgCneg τ) i) j : ℕ) : ℤ) := by
  cases τ <;> simp [tgOK] at hτ <;> revert hij <;> fin_cases i <;> fin_cases j <;> decide +kernel

theorem tgCneg_lane_le {τ : Tag} (hτ : tgOK τ = true) (i j : Fin τ.rank) :
    lane (row (tgCneg τ) i) j ≤ 3 ∧ (i = j → lane (row (tgCneg τ) i) j = 0) := by
  cases τ <;> simp [tgOK] at hτ <;> fin_cases i <;> fin_cases j <;> decide +kernel

theorem symmetrizer_eq {τ : Tag} (hτ : tgOK τ = true) (i j : Fin τ.rank) :
    τ.symmetrizer i j = if i = j then ((lane (tgDiag τ) i : ℕ) : ℤ) else 0 := by
  cases τ <;> simp [tgOK] at hτ <;> fin_cases i <;> fin_cases j <;> decide +kernel

theorem tgK0_lt {τ : Tag} (hτ : tgOK τ = true) : tgK0 τ < τ.rank := by
  cases τ <;> simp [tgOK] at hτ <;> decide

section Kac

theorem pkTheta_eq {τ : Tag} (hτ : tgOK τ = true) :
    pkTheta τ = List.ofFn fun i => ((kacOf τ).θ i).toNat := by
  cases τ <;> simp [tgOK] at hτ <;> rfl

theorem tgK0_spec {τ : Tag} (hτ : tgOK τ = true) (i : Fin τ.rank) :
    (kacOf τ).c i = if (i : ℕ) = tgK0 τ then 1 else 0 := by
  cases τ <;> simp [tgOK] at hτ <;> fin_cases i <;> rfl

end Kac

end CFSG.KC.GGToral
