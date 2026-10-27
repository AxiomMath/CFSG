module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.ComponentClassification.SolMax.Sig36.E32

open Equiv Perm Subgroup

@[expose] def p (i : Fin 4) : Perm (Fin 9) :=
  swap ⟨2 * i.val, by omega⟩ ⟨2 * i.val + 1, by omega⟩

@[expose] def σ₀ : Perm (Fin 9) := p 0 * p 1 * p 2

@[expose] def πx : Perm (Fin 9) := p 0 * p 1 * p 2 * p 3

@[expose] def Stab6 : Subgroup (Perm (Fin 9)) where
  carrier := {τ | ∀ i : Fin 9, i.val < 6 → τ i = i}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {a b} ha hb i hi => by
    rw [Perm.mul_apply, hb i hi, ha i hi]
  inv_mem' := fun {a} ha i hi => by
    rw [Perm.inv_eq_iff_eq]
    exact (ha i hi).symm

@[expose] def hatFun (α : Perm (Fin 4)) (x : Fin 9) : Fin 9 :=
  if h : x.val < 8 then
    ⟨2 * (α ⟨x.val / 2, by omega⟩).val + x.val % 2, by
      have := (α ⟨x.val / 2, by omega⟩).isLt
      omega⟩
  else x

private theorem hatFun_lt (α : Perm (Fin 4)) (x : Fin 9) (h : x.val < 8) :
    (hatFun α x).val = 2 * (α ⟨x.val / 2, by omega⟩).val + x.val % 2 := by
  simp [hatFun, h]

private theorem hatFun_ge (α : Perm (Fin 4)) (x : Fin 9) (h : ¬ x.val < 8) : hatFun α x = x := by
  simp [hatFun, h]

namespace PermAux

theorem hatFun_inv (α : Perm (Fin 4)) (x : Fin 9) : hatFun α⁻¹ (hatFun α x) = x := by
  by_cases h : x.val < 8
  · have h1 := hatFun_lt α x h
    have ha := (α ⟨x.val / 2, by omega⟩).isLt
    have h2 : (hatFun α x).val < 8 := by omega
    have h3 : (⟨(hatFun α x).val / 2, by omega⟩ : Fin 4) = α ⟨x.val / 2, by omega⟩ :=
      Fin.ext (by simp only; omega)
    apply Fin.ext
    rw [hatFun_lt α⁻¹ _ h2]
    have h4 : α⁻¹ (α ⟨x.val / 2, by omega⟩) = ⟨x.val / 2, by omega⟩ := by simp
    simp only [h3, h4]
    omega
  · rw [hatFun_ge α x h]
    exact hatFun_ge α⁻¹ x h

end PermAux

@[expose] def hat (α : Perm (Fin 4)) : Perm (Fin 9) where
  toFun := hatFun α
  invFun := hatFun α⁻¹
  left_inv := fun x => PermAux.hatFun_inv α x
  right_inv := fun x => by simpa using PermAux.hatFun_inv α⁻¹ x

theorem p_mul_self (i : Fin 4) : p i * p i = 1 := Equiv.swap_mul_self _ _

theorem p_comm (i j : Fin 4) : p i * p j = p j * p i := by
  revert i j; unfold p; decide

theorem card_support_p (i : Fin 4) : (p i).support.card = 2 := by
  revert i; unfold p; decide

theorem σ₀_mul_self : σ₀ * σ₀ = 1 := by
  unfold σ₀ p; decide

theorem card_support_σ₀ : σ₀.support.card = 6 := by
  unfold σ₀ p; decide

theorem σ₀_not_mem_alt : σ₀ ∉ alternatingGroup (Fin 9) := by
  rw [Perm.mem_alternatingGroup]; unfold σ₀ p; decide

theorem p12_mem_alt : p 1 * p 2 ∈ alternatingGroup (Fin 9) := by
  rw [Perm.mem_alternatingGroup]; unfold p; decide

theorem p02_mem_alt : p 0 * p 2 ∈ alternatingGroup (Fin 9) := by
  rw [Perm.mem_alternatingGroup]; unfold p; decide

theorem πx_mem_alt : πx ∈ alternatingGroup (Fin 9) := by
  rw [Perm.mem_alternatingGroup]; unfold πx p; decide

theorem πx_mul_self : πx * πx = 1 := by
  unfold πx p; decide

theorem hat_conj (α : Perm (Fin 4)) (i : Fin 4) : hat α * p i * (hat α)⁻¹ = p (α i) := by
  revert α i; unfold hat p; decide

theorem hat_mem_alt (α : Perm (Fin 4)) : hat α ∈ alternatingGroup (Fin 9) := by
  rw [Perm.mem_alternatingGroup]; revert α; unfold hat; decide

theorem card_support_p013 : (p 0 * p 1 * p 3).support.card = 6 := by
  unfold p; decide

theorem card_support_p23 : (p 2 * p 3).support.card = 4 := by
  unfold p; decide

private theorem σ₀_ne_self : ∀ a : Fin 9, a.val < 6 → σ₀ a ≠ a := by
  unfold σ₀ p; decide

private theorem σ₀_eq_self : ∀ a : Fin 9, 6 ≤ a.val → σ₀ a = a := by
  unfold σ₀ p; decide

private theorem σ₀_two_mul :
    ∀ i : Fin 3, σ₀ ⟨2 * i.val, by omega⟩ = ⟨2 * i.val + 1, by omega⟩ := by
  unfold σ₀ p; decide

private theorem swap_σ₀ :
    ∀ a : Fin 9, a.val < 6 → ∃ j : Fin 3, swap a (σ₀ a) = p j.castSucc := by
  unfold σ₀ p; decide

private theorem map_σ₀ {π : Perm (Fin 9)} (hπ : π * σ₀ = σ₀ * π) (a : Fin 9) :
    π (σ₀ a) = σ₀ (π a) := by
  have := congrArg (fun f : Perm (Fin 9) => f a) hπ
  simpa [Perm.mul_apply] using this

private theorem lt_six_of_lt_six {π : Perm (Fin 9)} (hπ : π * σ₀ = σ₀ * π) {a : Fin 9}
    (ha : a.val < 6) : (π a).val < 6 := by
  by_contra h
  push_neg at h
  have h1 : σ₀ (π a) = π a := σ₀_eq_self _ h
  have h2 : π (σ₀ a) = π a := by rw [map_σ₀ hπ, h1]
  exact σ₀_ne_self a ha (π.injective h2)

private theorem lt_six_inv {π : Perm (Fin 9)} (hπ : π * σ₀ = σ₀ * π) {a : Fin 9}
    (ha : a.val < 6) : (π⁻¹ a).val < 6 :=
  lt_six_of_lt_six (π := π⁻¹) (Commute.inv_left hπ) ha

private theorem six_le_of_six_le {π : Perm (Fin 9)} (hπ : π * σ₀ = σ₀ * π) {a : Fin 9}
    (ha : 6 ≤ a.val) : 6 ≤ (π a).val := by
  by_contra h
  push_neg at h
  have h1 := lt_six_inv hπ h
  have h2 : π⁻¹ (π a) = a := by simp
  rw [h2] at h1
  omega

theorem Zs_conj_p {π : Perm (Fin 9)} (hπ : π * σ₀ = σ₀ * π) (i : Fin 3) :
    ∃ j : Fin 3, π * p i.castSucc * π⁻¹ = p j.castSucc := by
  have hlt := lt_six_of_lt_six hπ (a := ⟨2 * i.val, by omega⟩)
    (show 2 * i.val < 6 by omega)
  have h1 : π ⟨2 * i.val + 1, by omega⟩ = σ₀ (π ⟨2 * i.val, by omega⟩) := by
    rw [← map_σ₀ hπ, σ₀_two_mul]
  obtain ⟨j, hj⟩ := swap_σ₀ (π ⟨2 * i.val, by omega⟩) hlt
  refine ⟨j, ?_⟩
  rw [← hj, ← h1]
  unfold p
  exact (Equiv.swap_apply_apply π _ _).symm

private theorem p_castSucc_inj : ∀ a b : Fin 3, p a.castSucc = p b.castSucc → a = b := by
  unfold p; decide

private theorem pp_cases : ∀ j₁ j₂ : Fin 3, j₁ ≠ j₂ →
    p j₁.castSucc * p j₂.castSucc = p 1 * p 2 ∨ p j₁.castSucc * p j₂.castSucc = p 0 * p 2 ∨
      p j₁.castSucc * p j₂.castSucc = p 0 * p 1 := by
  unfold p; decide

private theorem conj_pair {π : Perm (Fin 9)} (hπ : π * σ₀ = σ₀ * π) {a b : Fin 3} (hab : a ≠ b) :
    ∃ j₁ j₂ : Fin 3, j₁ ≠ j₂ ∧
      π * (p a.castSucc * p b.castSucc) * π⁻¹ = p j₁.castSucc * p j₂.castSucc := by
  obtain ⟨j₁, h₁⟩ := Zs_conj_p hπ a
  obtain ⟨j₂, h₂⟩ := Zs_conj_p hπ b
  refine ⟨j₁, j₂, ?_, ?_⟩
  · rintro rfl
    have h3 : p a.castSucc = p b.castSucc := by
      have h4 : π * p a.castSucc * π⁻¹ = π * p b.castSucc * π⁻¹ := h₁.trans h₂.symm
      simpa using h4
    exact hab (p_castSucc_inj a b h3)
  · rw [← h₁, ← h₂]
    group

theorem Zs_conj_U12 {π : Perm (Fin 9)} (hπ : π * σ₀ = σ₀ * π) :
    π * (p 1 * p 2) * π⁻¹ = p 1 * p 2 ∨ π * (p 1 * p 2) * π⁻¹ = p 0 * p 2 ∨
      π * (p 1 * p 2) * π⁻¹ = p 0 * p 1 := by
  obtain ⟨j₁, j₂, hne, h⟩ := conj_pair hπ (a := 1) (b := 2) (by decide)
  exact h ▸ pp_cases j₁ j₂ hne

theorem Zs_conj_U02 {π : Perm (Fin 9)} (hπ : π * σ₀ = σ₀ * π) :
    π * (p 0 * p 2) * π⁻¹ = p 1 * p 2 ∨ π * (p 0 * p 2) * π⁻¹ = p 0 * p 2 ∨
      π * (p 0 * p 2) * π⁻¹ = p 0 * p 1 := by
  obtain ⟨j₁, j₂, hne, h⟩ := conj_pair hπ (a := 0) (b := 2) (by decide)
  exact h ▸ pp_cases j₁ j₂ hne

private theorem p3_fix : ∀ i : Fin 9, i.val < 6 → p 3 i = i := by
  unfold p; decide

private theorem sign_p3 : Perm.sign (p 3) = -1 := by
  unfold p
  exact Perm.sign_swap (by decide)

theorem Zs_conj_πx {π : Perm (Fin 9)} (hπ : π * σ₀ = σ₀ * π) :
    πx⁻¹ * (π * πx * π⁻¹) ∈ Stab6 ∧ πx⁻¹ * (π * πx * π⁻¹) ∈ alternatingGroup (Fin 9) := by
  have hπx : πx = σ₀ * p 3 := rfl
  have hσ : π * σ₀ * π⁻¹ = σ₀ := by rw [hπ]; group
  have h3 : π * p 3 * π⁻¹ = swap (π 6) (π 7) := by
    unfold p
    exact (Equiv.swap_apply_apply π _ _).symm
  have hinv : πx⁻¹ = p 3 * σ₀ := by
    rw [hπx, mul_inv_rev, inv_eq_of_mul_eq_one_right (p_mul_self 3),
      inv_eq_of_mul_eq_one_right σ₀_mul_self]
  have h1 : π * πx * π⁻¹ = σ₀ * swap (π 6) (π 7) :=
    calc π * πx * π⁻¹ = (π * σ₀ * π⁻¹) * (π * p 3 * π⁻¹) := by rw [hπx]; group
      _ = σ₀ * swap (π 6) (π 7) := by rw [hσ, h3]
  have h2 : πx⁻¹ * (π * πx * π⁻¹) = p 3 * swap (π 6) (π 7) :=
    calc πx⁻¹ * (π * πx * π⁻¹) = p 3 * σ₀ * (σ₀ * swap (π 6) (π 7)) := by rw [h1, hinv]
      _ = p 3 * (σ₀ * σ₀) * swap (π 6) (π 7) := by group
      _ = p 3 * swap (π 6) (π 7) := by rw [σ₀_mul_self, mul_one]
  have h6 : 6 ≤ (π 6).val := six_le_of_six_le hπ (by decide)
  have h7 : 6 ≤ (π 7).val := six_le_of_six_le hπ (by decide)
  have hne : π 6 ≠ π 7 := fun h => absurd (π.injective h) (by decide)
  rw [h2]
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (fun h => by rw [h] at hi; omega)
      (fun h => by rw [h] at hi; omega)]
    exact p3_fix i hi
  · rw [Perm.mem_alternatingGroup, Perm.sign_mul, sign_p3, Perm.sign_swap hne]
    decide

theorem Zs_conj_Stab6 {π : Perm (Fin 9)} (hπ : π * σ₀ = σ₀ * π) {τ : Perm (Fin 9)}
    (hτ : τ ∈ Stab6) : π * τ * π⁻¹ ∈ Stab6 := by
  intro i hi
  have h1 : (π⁻¹ i).val < 6 := lt_six_inv hπ hi
  rw [Perm.mul_apply, Perm.mul_apply, hτ _ h1]
  simp

private theorem Stab6_ext {τ ρ : Perm (Fin 9)} (hτ : ∀ x : Fin 9, x.val < 6 → τ x = x)
    (hρ : ∀ x : Fin 9, x.val < 6 → ρ x = x) (h6 : τ 6 = ρ 6) (h7 : τ 7 = ρ 7)
    (h8 : τ 8 = ρ 8) : τ = ρ := by
  ext x
  by_cases hx : x.val < 6
  · rw [hτ x hx, hρ x hx]
  · have h9 := x.isLt
    have h : x.val = 6 ∨ x.val = 7 ∨ x.val = 8 := by omega
    rcases h with h | h | h
    · have hx6 : x = 6 := Fin.ext h
      rw [hx6]; exact congrArg Fin.val h6
    · have hx7 : x = 7 := Fin.ext h
      rw [hx7]; exact congrArg Fin.val h7
    · have hx8 : x = 8 := Fin.ext h
      rw [hx8]; exact congrArg Fin.val h8

private def sixPerm : Fin 6 → Perm (Fin 9) :=
  ![1, swap 6 7, swap 6 8, swap 7 8, swap 6 7 * swap 7 8, (swap 6 7 * swap 7 8)⁻¹]

private theorem sixPerm_fix : ∀ k : Fin 6, ∀ x : Fin 9, x.val < 6 → sixPerm k x = x := by
  unfold sixPerm; decide

private theorem sixPerm_pow : ∀ k : Fin 6, sixPerm k ^ 3 = 1 ∨ ¬ Perm.sign (sixPerm k) = 1 := by
  unfold sixPerm; decide

private theorem exists_sixPerm :
    ∀ a b c : Fin 9, 6 ≤ a.val → 6 ≤ b.val → 6 ≤ c.val → a ≠ b → a ≠ c → b ≠ c →
      ∃ k : Fin 6, sixPerm k 6 = a ∧ sixPerm k 7 = b ∧ sixPerm k 8 = c := by
  unfold sixPerm; decide

theorem Stab6_alt_pow_three {τ : Perm (Fin 9)} (hτ : τ ∈ Stab6)
    (hA : τ ∈ alternatingGroup (Fin 9)) : τ ^ 3 = 1 := by
  have hlow : ∀ x : Fin 9, x.val < 6 → τ x = x := hτ
  have hge : ∀ x : Fin 9, 6 ≤ x.val → 6 ≤ (τ x).val := by
    intro x hx
    by_contra h
    push_neg at h
    have h2 : τ x = x := τ.injective (hlow _ h)
    rw [h2] at h
    omega
  have hinj := τ.injective
  obtain ⟨k, h6, h7, h8⟩ := exists_sixPerm (τ 6) (τ 7) (τ 8) (hge 6 (by decide))
    (hge 7 (by decide)) (hge 8 (by decide)) (fun h => absurd (hinj h) (by decide))
    (fun h => absurd (hinj h) (by decide)) (fun h => absurd (hinj h) (by decide))
  have hτρ : τ = sixPerm k := Stab6_ext hlow (sixPerm_fix k) h6.symm h7.symm h8.symm
  rw [hτρ] at hA ⊢
  rcases sixPerm_pow k with h | h
  · exact h
  · exact absurd (Perm.mem_alternatingGroup.mp hA) h

end CFSG.ComponentClassification.SolMax.Sig36.E32
