module

public import CFSG.LieType.D4Small.Datum
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.LieType.D4Small

open Matrix

theorem castW_add (N : ℕ) (α β : Fin 4 → ℤ) : castW N (α + β) = castW N α + castW N β := by
  funext k
  simp [castW]

theorem castW_neg (N : ℕ) (α : Fin 4 → ℤ) : castW N (-α) = -castW N α := by
  funext k
  simp [castW]

theorem castW_sub (N : ℕ) (α β : Fin 4 → ℤ) : castW N (α - β) = castW N α - castW N β := by
  funext k
  simp [castW]

theorem smul_castW_neg {N : ℕ} (σ : ZMod N) (α : Fin 4 → ℤ) :
    σ • castW N (-α) = (-σ) • castW N α := by
  rw [castW_neg, smul_neg, neg_smul]

theorem reflW_neg {N : ℕ} (β : Fin 4 → ℤ) (a : Fin 4 → ZMod N) : reflW (-β) a = reflW β a := by
  rw [reflW, reflW, castW_neg, dotProduct_neg, neg_smul_neg]

theorem IsD4Root.abs_apply_le_one {α : Fin 4 → ℤ} (h : IsD4Root α) (k : Fin 4) :
    |α k| ≤ 1 := by
  have hsum : ∑ i, α i * α i = 2 := h
  have hle : α k * α k ≤ ∑ i, α i * α i :=
    Finset.single_le_sum (fun i _ => mul_self_nonneg (α i)) (Finset.mem_univ k)
  rw [hsum] at hle
  by_contra hk
  have h2 : 2 ≤ |α k| := by omega
  have h4 : 4 ≤ |α k| * |α k| := by nlinarith
  rw [abs_mul_abs_self] at h4
  omega

theorem castW_injOn_roots {N : ℕ} (hN : 3 ≤ N) {α β : Fin 4 → ℤ} (hα : IsD4Root α)
    (hβ : IsD4Root β) (h : castW N α = castW N β) : α = β := by
  funext k
  have hk : ((α k : ℤ) : ZMod N) = ((β k : ℤ) : ZMod N) := congrFun h k
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hk
  obtain ⟨c, hc⟩ := hk
  have h1 := hα.abs_apply_le_one k
  have h2 := hβ.abs_apply_le_one k
  rw [abs_le] at h1 h2
  have hN' : (3 : ℤ) ≤ N := by exact_mod_cast hN
  rcases lt_trichotomy c 0 with hc0 | hc0 | hc0
  · nlinarith
  · rw [hc0, mul_zero] at hc
    omega
  · nlinarith

theorem castW_ne_zero {N : ℕ} (hN : 3 ≤ N) {α : Fin 4 → ℤ} (hα : IsD4Root α) :
    castW N α ≠ 0 := by
  intro h0
  obtain ⟨i, j, hij, hi, -, -⟩ := isD4Root_iff.mp hα
  have hk : ((α i : ℤ) : ZMod N) = ((0 : ℤ) : ZMod N) := by
    simpa [castW] using congrFun h0 i
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hk
  obtain ⟨c, hc⟩ := hk
  have hN' : (3 : ℤ) ≤ N := by exact_mod_cast hN
  rcases hi with hi | hi <;> rw [hi] at hc <;>
    rcases lt_trichotomy c 0 with hc0 | hc0 | hc0 <;> nlinarith

structure IsSmallClass (N : ℕ) (σ : ZMod N) (C : Finset (Fin 4 → ZMod N)) : Prop where
  three_le : 3 ≤ N
  odd : Odd N
  isUnit : IsUnit σ
  card_eq : C.card = 8
  neg_mem : ∀ a ∈ C, -a ∈ C
  reflW_mem : ∀ β, IsD4Root β → ∀ a ∈ C, reflW β a ∈ C
  step : ∀ a ∈ C, ∀ α, IsD4Root α → ∀ k : ZMod N, k ≠ 0 → a + k • castW N α ∈ C →
    k = σ ∨ k = -σ
  sub_not_mem : ∀ a ∈ C, ∀ α, IsD4Root α → a + σ • castW N α ∈ C → a - σ • castW N α ∉ C
  reflW_eq : ∀ a ∈ C, ∀ α, IsD4Root α → a + σ • castW N α ∈ C →
    reflW α a = a + σ • castW N α
  adj : ∀ a ∈ C, ∀ a' ∈ C, a' ≠ a → a' ≠ -a → ∃ γ, IsD4Root γ ∧ a' = a + σ • castW N γ
  ne_neg : ∀ a ∈ C, ∀ γ, IsD4Root γ → a + σ • castW N γ ≠ -a
  triangle : ∀ a ∈ C, ∀ γ β, IsD4Root γ → IsD4Root β → a + σ • castW N γ ∈ C →
    a + σ • castW N (γ + β) ∈ C → a + σ • castW N (γ + β) ≠ a →
    a + σ • castW N (γ + β) ≠ -a →
    γ ⬝ᵥ β = -1 ∧ a + σ • castW N β ∉ C ∧ a + σ • castW N (2 • γ + β) ∉ C
  two_mem : ∀ α, IsD4Root α → ∃ a₁ ∈ C, ∃ a₂ ∈ C, a₁ ≠ a₂ ∧
    ∀ a ∈ C, (a + σ • castW N α ∈ C ↔ a = a₁ ∨ a = a₂)
  raise_adj : N = 3 → ∀ a ∈ C, ∀ γ γ', IsD4Root γ → IsD4Root γ' → a + σ • castW N γ ∈ C →
    a + σ • castW N γ' ∈ C → γ ≠ γ' → γ ⬝ᵥ γ' = 1 ∨ ∃ γ'', IsD4Root γ'' ∧
      a + σ • castW N γ'' ∈ C ∧ γ ⬝ᵥ γ'' = 1 ∧ γ' ⬝ᵥ γ'' = 1
  raise_edge : N = 3 → ∀ a ∈ C, ∀ γ γ', IsD4Root γ → IsD4Root γ' → a + σ • castW N γ ∈ C →
    a + σ • castW N γ' ∈ C → γ ⬝ᵥ γ' = 1 →
    a + σ • castW N (γ' - γ) ∉ C ∧ a - σ • castW N (γ' - γ) ∉ C ∧
    a + σ • castW N γ - σ • castW N (γ' - γ) ∉ C ∧
    a + σ • castW N γ' + σ • castW N γ ∉ C

namespace IsSmallClass

variable {N : ℕ} {σ : ZMod N} {C : Finset (Fin 4 → ZMod N)}

theorem nontrivial (h : IsSmallClass N σ C) : Nontrivial (ZMod N) := by
  haveI : Fact (1 < N) := ⟨by have := h.three_le; omega⟩
  infer_instance

theorem isUnit_two (h : IsSmallClass N σ C) : IsUnit (2 : ZMod N) := by
  have h2 : ((2 : ℕ) : ZMod N) = 2 := by norm_num
  rw [← h2, ZMod.isUnit_iff_coprime]
  exact Nat.coprime_two_left.mpr h.odd

theorem smul_castW_inj (h : IsSmallClass N σ C) {α β : Fin 4 → ℤ} (hα : IsD4Root α)
    (hβ : IsD4Root β) (hαβ : σ • castW N α = σ • castW N β) : α = β :=
  castW_injOn_roots h.three_le hα hβ ((h.isUnit.smul_left_cancel).mp hαβ)

theorem add_smul_castW_ne (h : IsSmallClass N σ C) (a : Fin 4 → ZMod N) {α : Fin 4 → ℤ}
    (hα : IsD4Root α) : a + σ • castW N α ≠ a := by
  intro h0
  have h1 : σ • castW N α = σ • (0 : Fin 4 → ZMod N) := by
    rw [smul_zero]
    simpa using h0
  exact castW_ne_zero h.three_le hα ((h.isUnit.smul_left_cancel).mp h1)

theorem two_smul_not_mem (h : IsSmallClass N σ C) {a : Fin 4 → ZMod N} (ha : a ∈ C)
    {α : Fin 4 → ℤ} (hα : IsD4Root α) (hmem : a + σ • castW N α ∈ C) :
    a + (2 * σ) • castW N α ∉ C := by
  haveI := h.nontrivial
  intro h2
  have h2σ : (2 * σ : ZMod N) ≠ 0 := (h.isUnit_two.mul h.isUnit).ne_zero
  rcases h.step a ha α hα (2 * σ) h2σ h2 with h3 | h3
  · exact h.isUnit.ne_zero (by linear_combination h3)
  · apply h.sub_not_mem a ha α hα hmem
    rw [h3, neg_smul, ← sub_eq_add_neg] at h2
    exact h2

theorem neg (h : IsSmallClass N σ C) : IsSmallClass N (-σ) C := by
  have e : ∀ x : Fin 4 → ℤ, (-σ) • castW N x = σ • castW N (-x) := fun x =>
    (smul_castW_neg σ x).symm
  refine ⟨h.three_le, h.odd, h.isUnit.neg, h.card_eq, h.neg_mem, h.reflW_mem, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha α hα k hk hmem
    rcases h.step a ha α hα k hk hmem with h1 | h1
    · exact Or.inr (by rw [h1, neg_neg])
    · exact Or.inl h1
  · intro a ha α hα hmem
    rw [e] at hmem ⊢
    have h2 := h.sub_not_mem a ha (-α) hα.neg hmem
    exact h2
  · intro a ha α hα hmem
    rw [e] at hmem ⊢
    rw [← reflW_neg]
    exact h.reflW_eq a ha (-α) hα.neg hmem
  · intro a ha a' ha' h1 h2
    obtain ⟨γ, hγ, rfl⟩ := h.adj a ha a' ha' h1 h2
    exact ⟨-γ, hγ.neg, by rw [e, neg_neg]⟩
  · intro a ha γ hγ
    rw [e]
    exact h.ne_neg a ha (-γ) hγ.neg
  · intro a ha γ β hγ hβ h1 h2 h3 h4
    rw [e] at h1 h2 h3 h4 ⊢
    rw [e]
    rw [neg_add] at h2 h3 h4
    obtain ⟨hd, hb, h2γ⟩ := h.triangle a ha (-γ) (-β) hγ.neg hβ.neg h1 h2 h3 h4
    refine ⟨by simpa using hd, hb, ?_⟩
    rwa [show -(2 • γ + β) = 2 • (-γ) + -β by rw [smul_neg, neg_add]]
  · intro α hα
    obtain ⟨a₁, ha₁, a₂, ha₂, hne, hiff⟩ := h.two_mem (-α) hα.neg
    exact ⟨a₁, ha₁, a₂, ha₂, hne, fun a ha => by rw [e]; exact hiff a ha⟩
  · intro hN a ha γ γ' hγ hγ' h1 h2 hne
    rw [e] at h1 h2
    rcases h.raise_adj hN a ha (-γ) (-γ') hγ.neg hγ'.neg h1 h2 (neg_injective.ne hne) with
      hd | ⟨γ'', hγ'', hm, hd1, hd2⟩
    · exact Or.inl (by simpa using hd)
    · exact Or.inr ⟨-γ'', hγ''.neg, by rw [e, neg_neg]; exact hm, by simpa using hd1,
        by simpa using hd2⟩
  · intro hN a ha γ γ' hγ hγ' h1 h2 hd
    rw [e] at h1 h2
    obtain ⟨r1, r2, r3, r4⟩ :=
      h.raise_edge hN a ha (-γ) (-γ') hγ.neg hγ'.neg h1 h2 (by simpa using hd)
    have hs : -γ' - -γ = -(γ' - γ) := by rw [neg_sub_neg, neg_sub]
    rw [hs] at r1 r2 r3
    refine ⟨by rwa [e], by rwa [e], ?_, ?_⟩
    · rwa [e, e]
    · rwa [e, e]

end IsSmallClass

end CFSG.LieType.D4Small
