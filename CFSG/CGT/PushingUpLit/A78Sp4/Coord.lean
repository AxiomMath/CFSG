module

public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.CGT.PushingUpLit.A78Sp4

open scoped commutatorElement

variable {K : Type*} [Field K]

@[expose] def beta (x y : K × K) : K × K :=
  (x.1 * y.2 + y.1 * x.2, x.1 ^ 2 * y.2 + y.1 ^ 2 * x.2)

theorem beta_fst_zero (r s s' : K) : beta (r, s) (0, s') = (r * s', r ^ 2 * s') := by
  simp [beta]

theorem beta_snd_zero (r s r' : K) : beta (r, s) (r', 0) = (r' * s, r' ^ 2 * s) := by
  simp [beta]

section CharTwo

variable [CharP K 2]

theorem charTwo_two_eq_zero : (2 : K) = 0 := by
  have := CharP.cast_eq_zero K 2
  simpa using this

theorem exists_line_sum {r r' : K} (hr : r ≠ 0) (hr' : r' ≠ 0) (hrr : r ≠ r') (T W : K) :
    ∃ s₁ s₂ : K, (r * s₁ + r' * s₂, r ^ 2 * s₁ + r' ^ 2 * s₂) = (T, W) := by
  have h2 : (2 : K) = 0 := charTwo_two_eq_zero
  have hs : r + r' ≠ 0 := by
    intro h
    apply hrr
    have : r = -r' := eq_neg_of_add_eq_zero_left h
    rw [this]
    have : (-r' : K) = r' := by
      have : r' + r' = 0 := by linear_combination r' * h2
      exact neg_eq_of_add_eq_zero_right this
    exact this
  refine ⟨(T + r' * ((W + r * T) / (r' * (r + r')))) / r, (W + r * T) / (r' * (r + r')), ?_⟩
  ext
  · simp only
    field_simp
    linear_combination (T * r + W) * h2
  · simp only
    field_simp
    linear_combination (r * T * r' + r ^ 2 * T) * h2

theorem exists_sq_eq [Finite K] (c : K) : ∃ u : K, u ^ 2 = c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective (frobenius K 2) := frobenius_inj K 2
  obtain ⟨u, hu⟩ := Finite.surjective_of_injective hinj c
  exact ⟨u, by simpa [frobenius_def] using hu⟩

theorem exists_line_sum' [Finite K] {s s' : K} (hs : s ≠ 0) (hs' : s' ≠ 0) (hss : s ≠ s')
    (T W : K) : ∃ u v : K, (u * s + v * s', u ^ 2 * s + v ^ 2 * s') = (T, W) := by
  have h2 : (2 : K) = 0 := charTwo_two_eq_zero
  have hsum : s + s' ≠ 0 := by
    intro h
    apply hss
    have : s' + s' = 0 := by linear_combination s' * h2
    have h3 : s = -s' := eq_neg_of_add_eq_zero_left h
    rw [h3]; exact neg_eq_of_add_eq_zero_right this
  obtain ⟨u, hu⟩ := exists_sq_eq ((W * s' + T ^ 2) / (s * (s + s')))
  refine ⟨u, (T + u * s) / s', ?_⟩
  have hu' : u ^ 2 * (s * (s + s')) = W * s' + T ^ 2 := by
    rw [hu]; field_simp
  ext
  · simp only
    field_simp
    linear_combination (u * s) * h2
  · simp only
    field_simp
    linear_combination hu' + (T * u * s + T ^ 2) * h2

omit [CharP K 2] in
theorem exists_two_ne_zero [Finite K] {S : Set K} (h : 2 < S.ncard) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b := by
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff (Set.toFinite S)).1 h
  by_cases h1 : a = 0
  · exact ⟨b, hb, c, hc, fun h => hab (h1.trans h.symm), fun h => hac (h1.trans h.symm), hbc⟩
  by_cases h2 : b = 0
  · exact ⟨a, ha, c, hc, h1, fun h => hbc (h2.trans h.symm), hac⟩
  · exact ⟨a, ha, b, hb, h1, h2, hab⟩

theorem polar_span_eq_top [Finite K] (B : Set (K × K)) (hB : 4 < B.ncard) :
    AddSubgroup.closure {z | ∃ x ∈ B, ∃ y, z = beta x y} = ⊤ := by
  rw [eq_top_iff]
  intro ⟨T, W⟩ _
  set P := AddSubgroup.closure {z | ∃ x ∈ B, ∃ y, z = beta x y} with hP
  have hmem : ∀ x ∈ B, ∀ y, beta x y ∈ P := fun x hx y =>
    AddSubgroup.subset_closure ⟨x, hx, y, rfl⟩
  have hsub : B ⊆ (Prod.fst '' B) ×ˢ (Prod.snd '' B) := fun x hx =>
    ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩
  have hle : B.ncard ≤ (Prod.fst '' B).ncard * (Prod.snd '' B).ncard := by
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [Set.ncard_prod] at this
  have h3 : 2 < (Prod.fst '' B).ncard ∨ 2 < (Prod.snd '' B).ncard := by
    by_contra hcon
    push Not at hcon
    have := Nat.mul_le_mul hcon.1 hcon.2
    omega
  rcases h3 with h3 | h3
  · obtain ⟨a, ⟨⟨a0, a1⟩, hxa, rfl⟩, b, ⟨⟨b0, b1⟩, hxb, rfl⟩, ha, hb, hab⟩ :=
      exists_two_ne_zero h3
    obtain ⟨s₁, s₂, hs⟩ := exists_line_sum (r := a0) (r' := b0) ha hb hab T W
    have e1 := hmem _ hxa (0, s₁)
    have e2 := hmem _ hxb (0, s₂)
    rw [beta_fst_zero] at e1 e2
    have := P.add_mem e1 e2
    rwa [Prod.mk_add_mk, hs] at this
  · obtain ⟨a, ⟨⟨a0, a1⟩, hxa, rfl⟩, b, ⟨⟨b0, b1⟩, hxb, rfl⟩, ha, hb, hab⟩ :=
      exists_two_ne_zero h3
    obtain ⟨u, v, hs⟩ := exists_line_sum' (s := a1) (s' := b1) ha hb hab T W
    have e1 := hmem _ hxa (u, 0)
    have e2 := hmem _ hxb (v, 0)
    rw [beta_snd_zero] at e1 e2
    have := P.add_mem e1 e2
    rwa [Prod.mk_add_mk, hs] at this

end CharTwo

variable {G : Type*} [Group G] {J : Subgroup G}

structure Cls2Coord (K : Type*) [Field K] {G : Type*} [Group G] (J : Subgroup G) where
  π : G → K × K
  ζ : G → K × K
  π_mul : ∀ x ∈ J, ∀ y ∈ J, π (x * y) = π x + π y
  π_surj : ∀ w : K × K, ∃ x ∈ J, π x = w
  ζ_mul : ∀ x ∈ J, π x = 0 → ∀ y ∈ J, π y = 0 → ζ (x * y) = ζ x + ζ y
  ζ_inj : ∀ x ∈ J, π x = 0 → ∀ y ∈ J, π y = 0 → ζ x = ζ y → x = y
  ζ_surj : ∀ w : K × K, ∃ x ∈ J, π x = 0 ∧ ζ x = w
  comm : ∀ x ∈ J, ∀ y ∈ J, π ⁅x, y⁆ = 0 ∧ ζ ⁅x, y⁆ = beta (π x) (π y)

namespace Cls2Coord

variable (c : Cls2Coord K J)

theorem π_one : c.π 1 = 0 := by
  have := c.π_mul 1 J.one_mem 1 J.one_mem
  simpa using this

theorem ζ_one : c.ζ 1 = 0 := by
  have := c.ζ_mul 1 J.one_mem c.π_one 1 J.one_mem c.π_one
  simpa using this

theorem π_inv {x : G} (hx : x ∈ J) : c.π x⁻¹ = - c.π x := by
  have := c.π_mul x hx x⁻¹ (J.inv_mem hx)
  rw [mul_inv_cancel, c.π_one] at this
  exact eq_neg_of_add_eq_zero_right this.symm

theorem ζ_inv {x : G} (hx : x ∈ J) (h0 : c.π x = 0) : c.ζ x⁻¹ = - c.ζ x := by
  have h0' : c.π x⁻¹ = 0 := by rw [c.π_inv hx, h0, neg_zero]
  have := c.ζ_mul x hx h0 x⁻¹ (J.inv_mem hx) h0'
  rw [mul_inv_cancel, c.ζ_one] at this
  exact eq_neg_of_add_eq_zero_right this.symm

theorem ker_central {x : G} (hx : x ∈ J) (h0 : c.π x = 0) {y : G} (hy : y ∈ J) :
    x * y = y * x := by
  have hc : ⁅x, y⁆ ∈ J :=
    J.mul_mem (J.mul_mem (J.mul_mem hx hy) (J.inv_mem hx)) (J.inv_mem hy)
  obtain ⟨h1, h2⟩ := c.comm x hx y hy
  have h3 : c.ζ ⁅x, y⁆ = c.ζ 1 := by rw [h2, h0, c.ζ_one]; simp [beta]
  have h4 := c.ζ_inj _ hc h1 1 J.one_mem c.π_one h3
  exact commutatorElement_eq_one_iff_mul_comm.1 h4

end Cls2Coord

@[expose] def commSet (c : Cls2Coord K J) (s : G) : Set (K × K) := {w | ∃ y ∈ J, c.π ⁅s, y⁆ = w}

end CFSG.CGT.PushingUpLit.A78Sp4
