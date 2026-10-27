module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.OddStandard.Solomon75.FourPartner

open Equiv Equiv.Perm Subgroup

section Orbits

variable {α : Type*} [DecidableEq α]

theorem exists_orbit_union (orb : α → Finset α) (d : ℕ)
    (hself : ∀ x, x ∈ orb x) (hsub : ∀ x, ∀ y ∈ orb x, orb y ⊆ orb x) :
    ∀ (N : ℕ) (Y : Finset α), Y.card = N → (∀ x ∈ Y, orb x ⊆ Y) →
      (∀ x ∈ Y, (orb x).card = d) →
      d ∣ Y.card ∧ ∀ m, m * d ≤ Y.card → ∃ B ⊆ Y, (∀ x ∈ B, orb x ⊆ B) ∧ B.card = m * d := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro Y hYN hY hcard
    by_cases hYe : Y = ∅
    · subst hYe
      refine ⟨by simp, fun m hm => ⟨∅, by simp, by simp, ?_⟩⟩
      simp at hm ⊢
      simp [hm]
    · obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.2 hYe
      have hdy : (orb y).card = d := hcard y hy
      have hdpos : 0 < d := by rw [← hdy]; exact Finset.card_pos.2 ⟨y, hself y⟩
      have hsubY : orb y ⊆ Y := hY y hy
      have hcY' : (Y \ orb y).card = Y.card - d := by
        rw [Finset.card_sdiff_of_subset hsubY, hdy]
      have hdle : d ≤ Y.card := hdy ▸ Finset.card_le_card hsubY
      have hlt : (Y \ orb y).card < N := by omega
      have hY' : ∀ x ∈ Y \ orb y, orb x ⊆ Y \ orb y := by
        intro x hx
        rw [Finset.mem_sdiff] at hx
        intro w hw
        rw [Finset.mem_sdiff]
        refine ⟨hY x hx.1 hw, fun hwy => hx.2 ?_⟩
        have h1 : orb w ⊆ orb x := hsub x w hw
        have h2 : orb w ⊆ orb y := hsub y w hwy
        have hwY : w ∈ Y := hY x hx.1 hw
        have hw1 : (orb w).card = d := hcard w hwY
        have h3 : orb w = orb x := Finset.eq_of_subset_of_card_le h1 (by rw [hw1, hcard x hx.1])
        have h4 : orb w = orb y := Finset.eq_of_subset_of_card_le h2 (by rw [hw1, hdy])
        rw [← h4, h3]
        exact hself x
      have hc' : ∀ x ∈ Y \ orb y, (orb x).card = d := fun x hx =>
        hcard x (Finset.mem_sdiff.1 hx).1
      obtain ⟨hd', hsel'⟩ := ih _ hlt (Y \ orb y) rfl hY' hc'
      refine ⟨?_, fun m hm => ?_⟩
      · have : Y.card = (Y \ orb y).card + d := by omega
        rw [this]
        exact dvd_add hd' dvd_rfl
      · rcases m with _ | m
        · exact ⟨∅, by simp, by simp, by simp⟩
        · have hm' : m * d ≤ (Y \ orb y).card := by
            have : (m + 1) * d = m * d + d := by ring
            omega
          obtain ⟨B', hB'sub, hB'cl, hB'card⟩ := hsel' m hm'
          have hdisj : Disjoint B' (orb y) := by
            rw [Finset.disjoint_left]
            intro w hw hwy
            exact (Finset.mem_sdiff.1 (hB'sub hw)).2 hwy
          refine ⟨B' ∪ orb y, ?_, ?_, ?_⟩
          · exact Finset.union_subset (hB'sub.trans Finset.sdiff_subset) hsubY
          · intro x hx
            rcases Finset.mem_union.1 hx with hx | hx
            · exact (hB'cl x hx).trans Finset.subset_union_left
            · exact (hsub y x hx).trans Finset.subset_union_right
          · rw [Finset.card_union_of_disjoint hdisj, hB'card, hdy]
            ring

end Orbits

section Swaps

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem exists_partialInvol (c : Perm α) (hcc : ∀ x, c (c x) = x) (B : Finset α)
    (hB : ∀ x ∈ B, c x ∈ B) :
    ∃ τ : Perm α, (∀ x ∈ B, τ x = c x) ∧ (∀ x, x ∉ B → τ x = x) ∧ ∀ x, τ (τ x) = x := by
  let f : α → α := fun x => if x ∈ B then c x else x
  have hf : Function.Involutive f := by
    intro x
    by_cases hx : x ∈ B
    · simp only [f, if_pos hx, if_pos (hB x hx), hcc]
    · simp only [f, if_neg hx]
  refine ⟨hf.toPerm f, fun x hx => ?_, fun x hx => ?_, fun x => hf x⟩
  · simp [Function.Involutive.coe_toPerm, f, hx]
  · simp [Function.Involutive.coe_toPerm, f, hx]

theorem card_support_mul_add {c σ τ : Perm α} (hcc : ∀ x, c (c x) = x)
    (hcσ : ∀ x, σ (c x) = c (σ x)) (B : Finset α) (hτB : ∀ x ∈ B, τ x = c x)
    (hτ : ∀ x, x ∉ B → τ x = x) :
    (σ * τ).support.card + (B.filter (fun x => σ x = c x)).card =
      σ.support.card + (B.filter (fun x => σ x = x)).card := by
  classical
  have e1 : ∀ f : Perm α, f.support.card = ∑ x, if f x ≠ x then 1 else 0 := by
    intro f
    rw [Equiv.Perm.support, Finset.card_filter]
  have e2 : ∀ p : α → Prop, [DecidablePred p] →
      (B.filter p).card = ∑ x, if (x ∈ B ∧ p x) then 1 else 0 := by
    intro p _
    rw [← Finset.card_filter]
    congr 1
    ext x
    simp
  rw [e1, e1, e2, e2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ B
  · have e : σ (τ x) = c (σ x) := by rw [hτB x hx, hcσ x]
    rw [Perm.mul_apply, e]
    generalize σ x = t
    have key : c t = x ↔ t = c x := ⟨fun h => by rw [← h, hcc], fun h => by rw [h, hcc]⟩
    have hk : c t ≠ x ↔ ¬ t = c x := not_congr key
    clear e hcσ hτB hτ e1 e2
    split_ifs <;> first | omega | (exfalso; tauto)
  · simp [Perm.mul_apply, hτ x hx, hx]

theorem sign_eq_one_of_card_eight {τ : Perm α} (h2 : ∀ x, τ (τ x) = x)
    (h8 : τ.support.card = 8) : sign τ = 1 := by
  have hτ2 : τ * τ = 1 := by
    ext x
    simp [Perm.mul_apply, h2]
  have hτ1 : τ ≠ 1 := fun h => by simp [h] at h8
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ho : orderOf τ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hτ2) hτ1
  obtain ⟨m, hm⟩ := Equiv.Perm.cycleType_prime_order (σ := τ) (by rw [ho]; exact Nat.prime_two)
  rw [ho] at hm
  have hsum : τ.support.card = 2 * (m + 1) := by
    rw [← Perm.sum_cycleType, hm]
    simp only [Multiset.sum_replicate, smul_eq_mul]
    ring
  have hm3 : m = 3 := by omega
  rw [Perm.sign_of_cycleType, hm, hm3]
  simp only [Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul]
  exact Even.neg_one_pow ⟨6, by norm_num⟩

end Swaps

section Classes

variable {α : Type*} [Fintype α] [DecidableEq α]

@[expose] def cls0 (c σ : Perm α) : Finset α := Finset.univ.filter fun x => c x ≠ x ∧ σ x = x

@[expose] def cls1 (c σ : Perm α) : Finset α := Finset.univ.filter fun x => c x ≠ x ∧ σ x = c x

@[expose] def cls2 (c σ : Perm α) : Finset α :=
  Finset.univ.filter fun x => c x ≠ x ∧ σ x ≠ x ∧ σ x ≠ c x

theorem mem_cls0 {c σ : Perm α} {x : α} : x ∈ cls0 c σ ↔ c x ≠ x ∧ σ x = x := by simp [cls0]

theorem mem_cls1 {c σ : Perm α} {x : α} : x ∈ cls1 c σ ↔ c x ≠ x ∧ σ x = c x := by simp [cls1]

theorem mem_cls2 {c σ : Perm α} {x : α} :
    x ∈ cls2 c σ ↔ c x ≠ x ∧ σ x ≠ x ∧ σ x ≠ c x := by simp [cls2]

theorem disjoint_cls01 (c σ : Perm α) : Disjoint (cls0 c σ) (cls1 c σ) := by
  rw [Finset.disjoint_left]
  intro x h0 h1
  rw [mem_cls0] at h0
  rw [mem_cls1] at h1
  exact h0.1 (h1.2.symm.trans h0.2)

theorem disjoint_cls02 (c σ : Perm α) : Disjoint (cls0 c σ) (cls2 c σ) := by
  rw [Finset.disjoint_left]
  intro x h0 h2
  rw [mem_cls0] at h0
  rw [mem_cls2] at h2
  exact h2.2.1 h0.2

theorem disjoint_cls12 (c σ : Perm α) : Disjoint (cls1 c σ) (cls2 c σ) := by
  rw [Finset.disjoint_left]
  intro x h1 h2
  rw [mem_cls1] at h1
  rw [mem_cls2] at h2
  exact h2.2.2 h1.2

theorem card_cls (c σ : Perm α) :
    (cls0 c σ).card + (cls1 c σ).card + (cls2 c σ).card = c.support.card := by
  rw [← Finset.card_union_of_disjoint (disjoint_cls01 c σ), ← Finset.card_union_of_disjoint
    (Finset.disjoint_union_left.2 ⟨disjoint_cls02 c σ, disjoint_cls12 c σ⟩)]
  congr 1
  ext x
  simp only [Finset.mem_union, mem_cls0, mem_cls1, mem_cls2, Perm.mem_support]
  by_cases hx : c x = x
  · simp [hx]
  · by_cases h1 : σ x = x
    · simp [hx, h1]
    · by_cases h2 : σ x = c x
      · simp [hx, h1, h2]
      · simp [hx, h1, h2]

theorem card_cls_le (c σ : Perm α) :
    (cls1 c σ).card + (cls2 c σ).card ≤ σ.support.card := by
  rw [← Finset.card_union_of_disjoint (disjoint_cls12 c σ)]
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_union] at hx
  rw [Perm.mem_support]
  rcases hx with h | h
  · have := mem_cls1.1 h
    intro h'
    exact this.1 (by rw [← this.2, h'])
  · exact (mem_cls2.1 h).2.1

theorem pair_orbit_sub {c : Perm α} (hcc : ∀ x, c (c x) = x) :
    ∀ x, ∀ y ∈ ({x, c x} : Finset α), ({y, c y} : Finset α) ⊆ {x, c x} := by
  intro x y hy
  rw [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl
  · exact subset_rfl
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton, hcc] at hw ⊢
    tauto

theorem quad_orbit_sub {c σ : Perm α} (hcc : ∀ x, c (c x) = x) (hσσ : ∀ x, σ (σ x) = x)
    (hcσ : ∀ x, σ (c x) = c (σ x)) :
    ∀ x, ∀ y ∈ ({x, c x, σ x, c (σ x)} : Finset α),
      ({y, c y, σ y, c (σ y)} : Finset α) ⊆ {x, c x, σ x, c (σ x)} := by
  intro x y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  intro w hw
  rcases hy with rfl | rfl | rfl | rfl <;>
    · simp only [Finset.mem_insert, Finset.mem_singleton, hcc, hcσ, hσσ] at hw ⊢
      tauto

theorem cls0_orbit {c σ : Perm α} (hcc : ∀ x, c (c x) = x) (hcσ : ∀ x, σ (c x) = c (σ x)) :
    2 ∣ (cls0 c σ).card ∧ ∀ m, m * 2 ≤ (cls0 c σ).card →
      ∃ B ⊆ cls0 c σ, (∀ x ∈ B, c x ∈ B) ∧ B.card = m * 2 := by
  have hcl : ∀ x ∈ cls0 c σ, ({x, c x} : Finset α) ⊆ cls0 c σ := by
    intro x hx w hw
    have hx' := mem_cls0.1 hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hx
    · rw [mem_cls0]
      grind
  have hcard : ∀ x ∈ cls0 c σ, ({x, c x} : Finset α).card = 2 := fun x hx =>
    Finset.card_pair (ne_comm.1 (mem_cls0.1 hx).1)
  obtain ⟨hd, hsel⟩ := exists_orbit_union (fun x => ({x, c x} : Finset α)) 2
    (fun x => by simp) (pair_orbit_sub hcc) _ (cls0 c σ) rfl hcl hcard
  refine ⟨hd, fun m hm => ?_⟩
  obtain ⟨B, hB, hcl', hcard'⟩ := hsel m hm
  exact ⟨B, hB, fun x hx => hcl' x hx (by simp), hcard'⟩

theorem cls1_orbit {c σ : Perm α} (hcc : ∀ x, c (c x) = x) (hcσ : ∀ x, σ (c x) = c (σ x)) :
    2 ∣ (cls1 c σ).card ∧ ∀ m, m * 2 ≤ (cls1 c σ).card →
      ∃ B ⊆ cls1 c σ, (∀ x ∈ B, c x ∈ B) ∧ B.card = m * 2 := by
  have hcl : ∀ x ∈ cls1 c σ, ({x, c x} : Finset α) ⊆ cls1 c σ := by
    intro x hx w hw
    have hx' := mem_cls1.1 hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hx
    · rw [mem_cls1]
      grind
  have hcard : ∀ x ∈ cls1 c σ, ({x, c x} : Finset α).card = 2 := fun x hx =>
    Finset.card_pair (ne_comm.1 (mem_cls1.1 hx).1)
  obtain ⟨hd, hsel⟩ := exists_orbit_union (fun x => ({x, c x} : Finset α)) 2
    (fun x => by simp) (pair_orbit_sub hcc) _ (cls1 c σ) rfl hcl hcard
  refine ⟨hd, fun m hm => ?_⟩
  obtain ⟨B, hB, hcl', hcard'⟩ := hsel m hm
  exact ⟨B, hB, fun x hx => hcl' x hx (by simp), hcard'⟩

theorem cls2_orbit {c σ : Perm α} (hcc : ∀ x, c (c x) = x) (hσσ : ∀ x, σ (σ x) = x)
    (hcσ : ∀ x, σ (c x) = c (σ x)) :
    4 ∣ (cls2 c σ).card ∧ ∀ m, m * 4 ≤ (cls2 c σ).card →
      ∃ B ⊆ cls2 c σ, (∀ x ∈ B, c x ∈ B ∧ σ x ∈ B) ∧ B.card = m * 4 := by
  have hcl : ∀ x ∈ cls2 c σ, ({x, c x, σ x, c (σ x)} : Finset α) ⊆ cls2 c σ := by
    intro x hx w hw
    have hx' := mem_cls2.1 hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact hx
    · rw [mem_cls2]
      grind
    · rw [mem_cls2]
      grind
    · rw [mem_cls2]
      grind
  have hcard : ∀ x ∈ cls2 c σ, ({x, c x, σ x, c (σ x)} : Finset α).card = 4 := by
    intro x hx
    have hx' := mem_cls2.1 hx
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair] <;>
      (try simp only [Finset.mem_insert, Finset.mem_singleton]) <;> grind
  obtain ⟨hd, hsel⟩ := exists_orbit_union (fun x => ({x, c x, σ x, c (σ x)} : Finset α)) 4
    (fun x => by simp) (quad_orbit_sub hcc hσσ hcσ) _ (cls2 c σ) rfl hcl hcard
  refine ⟨hd, fun m hm => ?_⟩
  obtain ⟨B, hB, hcl', hcard'⟩ := hsel m hm
  exact ⟨B, hB, fun x hx => ⟨hcl' x hx (by simp), hcl' x hx (by simp)⟩, hcard'⟩

end Classes

section Partner

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem exists_partner_build {c σ : Perm α} (hcc : ∀ x, c (c x) = x)
    (hσσ : ∀ x, σ (σ x) = x) (hcσ : ∀ x, σ (c x) = c (σ x)) {m₀ m₁ m₂ : ℕ}
    (h₀ : m₀ * 2 ≤ (cls0 c σ).card) (h₁ : m₁ * 2 ≤ (cls1 c σ).card)
    (h₂ : m₂ * 4 ≤ (cls2 c σ).card) (hsum : m₀ + m₁ + 2 * m₂ = 4) :
    ∃ τ : Perm α, (∀ x, τ x = x ∨ (c x ≠ x ∧ τ x = c x)) ∧ (∀ x, τ (τ x) = x) ∧
      (∀ x, σ (τ x) = τ (σ x)) ∧ τ.support.card = 8 ∧
      (σ * τ).support.card + 2 * m₁ = σ.support.card + 2 * m₀ := by
  classical
  obtain ⟨B₀, hB₀X, hB₀c, hB₀n⟩ := (cls0_orbit hcc hcσ).2 m₀ h₀
  obtain ⟨B₁, hB₁X, hB₁c, hB₁n⟩ := (cls1_orbit hcc hcσ).2 m₁ h₁
  obtain ⟨B₂, hB₂X, hB₂c, hB₂n⟩ := (cls2_orbit hcc hσσ hcσ).2 m₂ h₂
  have hdis01 : Disjoint B₀ B₁ :=
    Finset.disjoint_of_subset_left hB₀X
      (Finset.disjoint_of_subset_right hB₁X (disjoint_cls01 c σ))
  have hdis02 : Disjoint B₀ B₂ :=
    Finset.disjoint_of_subset_left hB₀X
      (Finset.disjoint_of_subset_right hB₂X (disjoint_cls02 c σ))
  have hdis12 : Disjoint B₁ B₂ :=
    Finset.disjoint_of_subset_left hB₁X
      (Finset.disjoint_of_subset_right hB₂X (disjoint_cls12 c σ))
  set B : Finset α := B₀ ∪ B₁ ∪ B₂ with hB
  have hBcard : B.card = 8 := by
    rw [hB, Finset.card_union_of_disjoint (Finset.disjoint_union_left.2 ⟨hdis02, hdis12⟩),
      Finset.card_union_of_disjoint hdis01]
    omega
  have hmemB : ∀ x, x ∈ B ↔ x ∈ B₀ ∨ x ∈ B₁ ∨ x ∈ B₂ := by
    intro x
    simp [hB, or_assoc]
  have hBne : ∀ x ∈ B, c x ≠ x := by
    intro x hx
    rcases (hmemB x).1 hx with h | h | h
    · exact (mem_cls0.1 (hB₀X h)).1
    · exact (mem_cls1.1 (hB₁X h)).1
    · exact (mem_cls2.1 (hB₂X h)).1
  have hBc : ∀ x ∈ B, c x ∈ B := by
    intro x hx
    rcases (hmemB x).1 hx with h | h | h
    · exact (hmemB _).2 (Or.inl (hB₀c x h))
    · exact (hmemB _).2 (Or.inr (Or.inl (hB₁c x h)))
    · exact (hmemB _).2 (Or.inr (Or.inr (hB₂c x h).1))
  have hBσ : ∀ x ∈ B, σ x ∈ B := by
    intro x hx
    rcases (hmemB x).1 hx with h | h | h
    · have := (mem_cls0.1 (hB₀X h)).2
      rw [this]
      exact hx
    · have := (mem_cls1.1 (hB₁X h)).2
      rw [this]
      exact hBc x hx
    · exact (hmemB _).2 (Or.inr (Or.inr (hB₂c x h).2))
  have hBσ' : ∀ x, σ x ∈ B → x ∈ B := fun x hx => by
    have := hBσ _ hx
    rwa [hσσ] at this
  obtain ⟨τ, hτB, hτ0, hτi⟩ := exists_partialInvol c hcc B hBc
  have hτ1 : ∀ x, τ x = x ∨ (c x ≠ x ∧ τ x = c x) := by
    intro x
    by_cases hx : x ∈ B
    · exact Or.inr ⟨hBne x hx, hτB x hx⟩
    · exact Or.inl (hτ0 x hx)
  have hτ2 : ∀ x, σ (τ x) = τ (σ x) := by
    intro x
    by_cases hx : x ∈ B
    · rw [hτB x hx, hcσ x, hτB (σ x) (hBσ x hx)]
    · have hx' : σ x ∉ B := fun h => hx (hBσ' x h)
      rw [hτ0 x hx, hτ0 (σ x) hx']
  have hsupp : τ.support = B := by
    ext x
    rw [Perm.mem_support]
    constructor
    · intro h
      by_contra hx
      exact h (hτ0 x hx)
    · intro hx
      rw [hτB x hx]
      exact hBne x hx
  refine ⟨τ, hτ1, hτi, hτ2, by rw [hsupp, hBcard], ?_⟩
  have key := card_support_mul_add hcc hcσ B hτB hτ0
  have hf1 : B.filter (fun x => σ x = c x) = B₁ := by
    ext x
    simp only [Finset.mem_filter, hmemB]
    constructor
    · rintro ⟨h | h | h, hσx⟩
      · have := mem_cls0.1 (hB₀X h)
        exact absurd (this.2.symm.trans hσx) (Ne.symm this.1)
      · exact h
      · exact absurd hσx (mem_cls2.1 (hB₂X h)).2.2
    · intro h
      exact ⟨Or.inr (Or.inl h), (mem_cls1.1 (hB₁X h)).2⟩
  have hf0 : B.filter (fun x => σ x = x) = B₀ := by
    ext x
    simp only [Finset.mem_filter, hmemB]
    constructor
    · rintro ⟨h | h | h, hσx⟩
      · exact h
      · have := mem_cls1.1 (hB₁X h)
        exact absurd (this.2.symm.trans hσx) this.1
      · exact absurd hσx (mem_cls2.1 (hB₂X h)).2.1
    · intro h
      exact ⟨Or.inl h, (mem_cls0.1 (hB₀X h)).2⟩
  rw [hf1, hf0, hB₁n, hB₀n] at key
  omega

theorem exists_partner_swap {c σ : Perm α} (hcc : ∀ x, c (c x) = x) (hσσ : ∀ x, σ (σ x) = x)
    (hcσ : ∀ x, σ (c x) = c (σ x)) (hsupp : 12 ≤ c.support.card) (h8 : 8 ∣ σ.support.card) :
    ∃ τ : Perm α, (∀ x, τ x = x ∨ (c x ≠ x ∧ τ x = c x)) ∧ (∀ x, τ (τ x) = x) ∧
      (∀ x, σ (τ x) = τ (σ x)) ∧ τ.support.card = 8 ∧ 8 ∣ (σ * τ).support.card ∧
      σ * τ ≠ 1 := by
  obtain ⟨⟨p₀, hp₀⟩, -⟩ := cls0_orbit hcc hcσ
  obtain ⟨⟨p₁, hp₁⟩, -⟩ := cls1_orbit hcc hcσ
  obtain ⟨⟨q, hq⟩, -⟩ := cls2_orbit hcc hσσ hcσ
  have hpart := card_cls c σ
  have hsuppσ := card_cls_le c σ
  have build : ∀ m₀ m₁ m₂ : ℕ, m₀ ≤ p₀ → m₁ ≤ p₁ → m₂ ≤ q → m₀ + m₁ + 2 * m₂ = 4 →
      ∃ τ : Perm α, (∀ x, τ x = x ∨ (c x ≠ x ∧ τ x = c x)) ∧ (∀ x, τ (τ x) = x) ∧
        (∀ x, σ (τ x) = τ (σ x)) ∧ τ.support.card = 8 ∧
        (σ * τ).support.card + 2 * m₁ = σ.support.card + 2 * m₀ :=
    fun m₀ m₁ m₂ h₀ h₁ h₂ hsum =>
      exists_partner_build hcc hσσ hcσ (by omega) (by omega) (by omega) hsum
  have hne1 : ∀ τ : Perm α, ∀ m₀ m₁ : ℕ,
      (σ * τ).support.card + 2 * m₁ = σ.support.card + 2 * m₀ →
      (σ.support.card + 2 * m₀ ≠ 2 * m₁) → σ * τ ≠ 1 := by
    intro τ m₀ m₁ h hne h1
    have h0 : (σ * τ).support.card = 0 := by rw [h1]; simp
    omega
  by_cases A : 4 ≤ p₀
  · obtain ⟨τ, h1, h1', h2, h3, h4⟩ := build 4 0 0 A (Nat.zero_le _) (Nat.zero_le _) rfl
    exact ⟨τ, h1, h1', h2, h3, by omega, hne1 τ 4 0 h4 (by omega)⟩
  by_cases C : 2 ≤ p₀ ∧ 2 ≤ p₁
  · obtain ⟨τ, h1, h1', h2, h3, h4⟩ := build 2 2 0 C.1 C.2 (Nat.zero_le _) rfl
    exact ⟨τ, h1, h1', h2, h3, by omega, hne1 τ 2 2 h4 (by omega)⟩
  by_cases D : 2 ≤ q
  · obtain ⟨τ, h1, h1', h2, h3, h4⟩ := build 0 0 2 (Nat.zero_le _) (Nat.zero_le _) D rfl
    exact ⟨τ, h1, h1', h2, h3, by omega, hne1 τ 0 0 h4 (by omega)⟩
  by_cases G : 1 ≤ p₀ ∧ 1 ≤ p₁ ∧ 1 ≤ q
  · obtain ⟨τ, h1, h1', h2, h3, h4⟩ := build 1 1 1 G.1 G.2.1 G.2.2 rfl
    exact ⟨τ, h1, h1', h2, h3, by omega, hne1 τ 1 1 h4 (by omega)⟩
  have hp1 : 4 ≤ p₁ := by omega
  obtain ⟨τ, h1, h1', h2, h3, h4⟩ := build 0 4 0 (Nat.zero_le _) hp1 (Nat.zero_le _) rfl
  exact ⟨τ, h1, h1', h2, h3, by omega, hne1 τ 0 4 h4 (by omega)⟩

end Partner

section Normal

variable {α : Type*} [Fintype α] [DecidableEq α]

@[expose] def pairSwapGroup (c : Perm α) (hcc : ∀ x, c (c x) = x) : Subgroup (Perm α) where
  carrier := {g | (∀ x, g x = x ∨ (c x ≠ x ∧ g x = c x)) ∧ sign g = 1}
  mul_mem' := by
    rintro g h ⟨hg, hgs⟩ ⟨hh, hhs⟩
    refine ⟨fun x => ?_, by rw [map_mul, hgs, hhs]; rfl⟩
    rw [Perm.mul_apply]
    rcases hh x with h1 | ⟨h1, h2⟩
    · rw [h1]
      exact hg x
    · rw [h2]
      rcases hg (c x) with h3 | ⟨h3, h4⟩
      · exact Or.inr ⟨h1, h3⟩
      · exact Or.inl (by rw [h4, hcc])
  one_mem' := ⟨fun x => Or.inl rfl, map_one _⟩
  inv_mem' := by
    rintro g ⟨hg, hgs⟩
    refine ⟨fun x => ?_, by rw [map_inv, hgs]; rfl⟩
    obtain ⟨y, hy⟩ : ∃ y, g y = x := ⟨g⁻¹ x, by simp⟩
    have hyx : g⁻¹ x = y := by rw [← hy]; simp
    rw [hyx]
    rcases hg y with h1 | ⟨h1, h2⟩
    · exact Or.inl (h1.symm.trans hy)
    · have hxc : x = c y := hy.symm.trans h2
      have hcx : c x = y := by rw [hxc, hcc]
      refine Or.inr ⟨?_, hcx.symm⟩
      intro h
      apply h1
      calc c y = x := hxc.symm
        _ = c x := h.symm
        _ = y := hcx

theorem pairSwapGroup_mem {c : Perm α} {hcc : ∀ x, c (c x) = x} {g : Perm α} :
    g ∈ pairSwapGroup c hcc ↔ (∀ x, g x = x ∨ (c x ≠ x ∧ g x = c x)) ∧ sign g = 1 := Iff.rfl

theorem pairSwapGroup_isPGroup (c : Perm α) (hcc : ∀ x, c (c x) = x) :
    IsPGroup 2 (pairSwapGroup c hcc) := by
  rintro ⟨g, hg, -⟩
  refine ⟨1, ?_⟩
  apply Subtype.ext
  ext x
  show g (g x) = x
  rcases hg x with h1 | ⟨h1, h2⟩
  · rw [h1, h1]
  · rw [h2]
    rcases hg (c x) with h3 | ⟨h3, h4⟩
    · exact absurd (g.injective (h3.trans h2.symm)) h1
    · rw [h4, hcc]

theorem pairSwapGroup_le {S : Subgroup (Perm α)} (hSA : S ≤ alternatingGroup α)
    (hS2 : IsPGroup 2 S)
    (hmax : ∀ S' : Subgroup (Perm α), S' ≤ alternatingGroup α → IsPGroup 2 S' → S ≤ S' →
      S' = S)
    {c : Perm α} (hcc : ∀ x, c (c x) = x) (hSc : ∀ s ∈ S, ∀ x, s (c x) = c (s x)) :
    pairSwapGroup c hcc ≤ S := by
  have hconj : ∀ s ∈ S, ∀ g ∈ pairSwapGroup c hcc, s * g * s⁻¹ ∈ pairSwapGroup c hcc := by
    intro s hs g hg
    obtain ⟨hg1, hg2⟩ := pairSwapGroup_mem.1 hg
    refine pairSwapGroup_mem.2 ⟨fun x => ?_, ?_⟩
    · obtain ⟨y, hy⟩ : ∃ y, s y = x := ⟨s⁻¹ x, by simp⟩
      have hyx : s⁻¹ x = y := by rw [← hy]; simp
      simp only [Perm.mul_apply, hyx]
      rcases hg1 y with h1 | ⟨h1, h2⟩
      · left
        rw [h1, hy]
      · right
        refine ⟨?_, ?_⟩
        · intro h
          apply h1
          apply s.injective
          rw [hSc s hs y, hy, h]
        · rw [h2, hSc s hs y, hy]
    · rw [map_mul, map_mul, map_inv, hg2]
      simp
  have hnorm : S ≤ normalizer ((pairSwapGroup c hcc : Subgroup (Perm α)) : Set (Perm α)) := by
    intro s hs
    rw [mem_normalizer_iff]
    intro g
    constructor
    · exact fun h => hconj s hs g h
    · intro h
      have := hconj s⁻¹ (S.inv_mem hs) _ h
      simpa [mul_assoc] using this
  have hP : IsPGroup 2 (S ⊔ pairSwapGroup c hcc : Subgroup (Perm α)) :=
    hS2.to_sup_of_normal_right' (pairSwapGroup_isPGroup c hcc) hnorm
  have hle : S ⊔ pairSwapGroup c hcc ≤ alternatingGroup α :=
    sup_le hSA (fun g hg => Perm.mem_alternatingGroup.2 (pairSwapGroup_mem.1 hg).2)
  have heq := hmax _ hle hP le_sup_left
  exact heq ▸ le_sup_right

end Normal

section Hub

theorem factorial_two_mul_odd (k : ℕ) :
    ∃ u : ℕ, Odd u ∧ (2 * k).factorial = 2 ^ k * k.factorial * u := by
  induction k with
  | zero => exact ⟨1, odd_one, by simp⟩
  | succ k ih =>
    obtain ⟨u, hu, h⟩ := ih
    refine ⟨(2 * k + 1) * u, (odd_two_mul_add_one k).mul hu, ?_⟩
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ, h,
      Nat.factorial_succ]
    ring

theorem factorial_eq_two_pow_mul_odd (n : ℕ) :
    ∃ u : ℕ, Odd u ∧ n.factorial = 2 ^ (n / 2) * (n / 2).factorial * u := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨u, hu, h⟩ := factorial_two_mul_odd k
    refine ⟨u, hu, ?_⟩
    have : 2 * k / 2 = k := by omega
    rw [this, h]
  · obtain ⟨u, hu, h⟩ := factorial_two_mul_odd k
    refine ⟨(2 * k + 1) * u, (odd_two_mul_add_one k).mul hu, ?_⟩
    rw [Nat.factorial_succ, h]
    have : (2 * k + 1) / 2 = k := by omega
    rw [this]
    ring

theorem odd_card_class (n : ℕ) (hn : 2 ≤ n) (c₀ : Perm (Fin n))
    (hc₀ : c₀.cycleType = Multiset.replicate (n / 2) 2) :
    Odd (Nat.card {h : Perm (Fin n) | IsConj c₀ h}) := by
  have h := Equiv.Perm.card_isConj_mul_eq c₀
  rw [hc₀] at h
  have hk : n / 2 ≠ 0 := by omega
  simp only [Fintype.card_fin, Multiset.sum_replicate, Multiset.prod_replicate, smul_eq_mul,
    Multiset.toFinset_replicate, hk, if_false, Finset.prod_singleton,
    Multiset.count_replicate_self] at h
  obtain ⟨u, hu, hfac⟩ := factorial_eq_two_pow_mul_odd n
  have h1 : (n - n / 2 * 2).factorial = 1 := by
    have : n - n / 2 * 2 = 0 ∨ n - n / 2 * 2 = 1 := by omega
    rcases this with h0 | h0 <;> rw [h0] <;> rfl
  rw [h1, hfac] at h
  have hpos : 0 < 2 ^ (n / 2) * (n / 2).factorial := by positivity
  have : Nat.card {h : Perm (Fin n) | IsConj c₀ h} = u := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [mul_comm u]
    calc Nat.card {h : Perm (Fin n) | IsConj c₀ h} * (2 ^ (n / 2) * (n / 2).factorial)
        = Nat.card {h : Perm (Fin n) | IsConj c₀ h} *
            (1 * 2 ^ (n / 2) * (n / 2).factorial) := by ring
      _ = 2 ^ (n / 2) * (n / 2).factorial * u := h
  rw [this]
  exact hu

theorem exists_hub (n : ℕ) (hn : 2 ≤ n) (S : Subgroup (Perm (Fin n))) (hS : IsPGroup 2 S) :
    ∃ c : Perm (Fin n), (∀ x, c (c x) = x) ∧ c.support.card = 2 * (n / 2) ∧
      ∀ s ∈ S, ∀ x, s (c x) = c (s x) := by
  classical
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : Perm (Fin n), c₀.cycleType = Multiset.replicate (n / 2) 2 := by
    rw [Equiv.Perm.exists_with_cycleType_iff]
    refine ⟨?_, ?_⟩
    · simp only [Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin]
      omega
    · intro a ha
      rw [Multiset.eq_of_mem_replicate ha]
  have hodd := odd_card_class n hn c₀ hc₀
  letI : MulAction S {h : Perm (Fin n) | IsConj c₀ h} :=
    { smul := fun s y => ⟨(s : Perm (Fin n)) * y.1 * (s : Perm (Fin n))⁻¹,
        y.2.trans (isConj_iff.2 ⟨s, rfl⟩)⟩
      one_smul := fun y => Subtype.ext (by
        show ((1 : S) : Perm (Fin n)) * y.1 * ((1 : S) : Perm (Fin n))⁻¹ = y.1
        simp)
      mul_smul := fun s t y => Subtype.ext (by
        show ((s * t : S) : Perm (Fin n)) * y.1 * ((s * t : S) : Perm (Fin n))⁻¹ =
          (s : Perm (Fin n)) * ((t : Perm (Fin n)) * y.1 * (t : Perm (Fin n))⁻¹) *
            (s : Perm (Fin n))⁻¹
        simp [mul_assoc]) }
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨c, hc⟩, hfix⟩ := hS.nonempty_fixed_point_of_prime_not_dvd_card
    {h : Perm (Fin n) | IsConj c₀ h}
    (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 hodd)
  have hcyc : c.cycleType = Multiset.replicate (n / 2) 2 := by
    rw [← hc₀]
    exact (isConj_iff_cycleType_eq.1 hc).symm
  have hc2 : c ^ 2 = 1 := by
    refine Perm.pow_prime_eq_one_iff.2 ?_
    intro i hi
    rw [hcyc] at hi
    exact Multiset.eq_of_mem_replicate hi
  refine ⟨c, fun x => ?_, ?_, fun s hs x => ?_⟩
  · have := congrArg (fun p : Perm (Fin n) => p x) hc2
    simpa [pow_two] using this
  · rw [← Perm.sum_cycleType, hcyc, Multiset.sum_replicate, smul_eq_mul]
    ring
  · have h1 := MulAction.mem_fixedPoints.1 hfix ⟨s, hs⟩
    have h2 : s * c * s⁻¹ = c := congrArg Subtype.val h1
    have h3 : s * c = c * s := mul_inv_eq_iff_eq_mul.1 h2
    have h4 := congrArg (fun p : Perm (Fin n) => p x) h3
    simpa [Perm.mul_apply] using h4

end Hub

theorem exists_partner_of_sylow {n : ℕ} (hn : 12 ≤ n) {S : Subgroup (Perm (Fin n))}
    (hSA : S ≤ alternatingGroup (Fin n)) (hS2 : IsPGroup 2 S)
    (hmax : ∀ S' : Subgroup (Perm (Fin n)), S' ≤ alternatingGroup (Fin n) → IsPGroup 2 S' →
      S ≤ S' → S' = S)
    {σ : Perm (Fin n)} (hσS : σ ∈ S) (hσ2 : ∀ x, σ (σ x) = x) (h8 : 8 ∣ σ.support.card) :
    ∃ τ ∈ S, (∀ x, τ (τ x) = x) ∧ (∀ x, σ (τ x) = τ (σ x)) ∧ τ.support.card = 8 ∧
      8 ∣ (σ * τ).support.card ∧ σ * τ ≠ 1 := by
  obtain ⟨c, hcc, hcsupp, hSc⟩ := exists_hub n (by omega) S hS2
  have hcσ : ∀ x, σ (c x) = c (σ x) := hSc σ hσS
  obtain ⟨τ, h1, h1', h2, h3, h4, h5⟩ :=
    exists_partner_swap hcc hσ2 hcσ (by rw [hcsupp]; omega) h8
  have hτmem : τ ∈ pairSwapGroup c hcc :=
    pairSwapGroup_mem.2 ⟨h1, sign_eq_one_of_card_eight h1' h3⟩
  exact ⟨τ, pairSwapGroup_le hSA hS2 hmax hcc hSc hτmem, h1', h2, h3, h4, h5⟩

end CFSG.OddStandard.Solomon75.FourPartner
