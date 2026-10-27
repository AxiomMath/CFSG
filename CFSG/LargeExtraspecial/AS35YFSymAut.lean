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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LargeExtraspecial.AS35YF

open Equiv Equiv.Perm

variable {n : ℕ}

theorem swap_apply_ne_self_iff {a b x : Fin n} (hab : a ≠ b) :
    swap a b x ≠ x ↔ x = a ∨ x = b := by
  constructor
  · intro h
    by_contra h'
    push Not at h'
    exact h (swap_apply_of_ne_of_ne h'.1 h'.2)
  · rintro (rfl | rfl)
    · rw [swap_apply_left]
      exact fun h => hab h.symm
    · rw [swap_apply_right]
      exact hab

theorem swap_comm_of_disjoint {a b c d : Fin n} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) : swap a b * swap c d = swap c d * swap a b := by
  refine Equiv.ext fun x => ?_
  simp only [Perm.mul_apply]
  by_cases hxa : x = a
  · subst hxa
    rw [swap_apply_of_ne_of_ne hac had, swap_apply_left, swap_apply_of_ne_of_ne hbc hbd]
  by_cases hxb : x = b
  · subst hxb
    rw [swap_apply_of_ne_of_ne hbc hbd, swap_apply_right, swap_apply_of_ne_of_ne hac had]
  by_cases hxc : x = c
  · subst hxc
    rw [swap_apply_left, swap_apply_of_ne_of_ne hxa hxb,
      swap_apply_of_ne_of_ne (Ne.symm had) (Ne.symm hbd), swap_apply_left]
  by_cases hxd : x = d
  · subst hxd
    rw [swap_apply_right, swap_apply_of_ne_of_ne hxa hxb,
      swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc), swap_apply_right]
  rw [swap_apply_of_ne_of_ne hxc hxd, swap_apply_of_ne_of_ne hxa hxb,
    swap_apply_of_ne_of_ne hxc hxd]

theorem swap_not_comm {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    swap a b * swap a c ≠ swap a c * swap a b := by
  intro h
  have := congrArg (fun σ : Perm (Fin n) => σ a) h
  simp only [Perm.mul_apply, swap_apply_left] at this
  rw [swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc).symm.symm] at this
  · rw [swap_apply_of_ne_of_ne (Ne.symm hab) hbc] at this
    exact hbc this.symm

theorem eq_or_eq_of_swap_eq {a b c d : Fin n} (hab : a ≠ b) (h : swap a b = swap c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hcd : c ≠ d := by
    rintro rfl
    rw [swap_self] at h
    have := congrArg (fun σ : Perm (Fin n) => σ a) h
    simp only [swap_apply_left, Equiv.refl_apply] at this
    exact hab this.symm
  have h1 : swap c d a ≠ a := by rw [← h, swap_apply_left]; exact fun e => hab e.symm
  have h2 : swap c d b ≠ b := by rw [← h, swap_apply_right]; exact hab
  rcases (swap_apply_ne_self_iff hcd).1 h1 with rfl | rfl <;>
    rcases (swap_apply_ne_self_iff hcd).1 h2 with h3 | h3
  · exact absurd h3.symm hab
  · exact Or.inl ⟨rfl, h3⟩
  · exact Or.inr ⟨rfl, h3⟩
  · exact absurd h3.symm hab

theorem eq_swap_of_moves {u v x y : Fin n} (huv : u ≠ v) (hxy : x ≠ y) (hx : swap u v x ≠ x)
    (hy : swap u v y ≠ y) : swap u v = swap x y := by
  rcases (swap_apply_ne_self_iff huv).1 hx with rfl | rfl <;>
    rcases (swap_apply_ne_self_iff huv).1 hy with rfl | rfl
  · exact absurd rfl hxy
  · rfl
  · exact swap_comm _ _
  · exact absurd rfl hxy

theorem exists_eq_swap_of_moves {σ : Perm (Fin n)} (hσ : σ.IsSwap) {c : Fin n} (hc : σ c ≠ c) :
    ∃ x, x ≠ c ∧ σ = swap c x := by
  obtain ⟨u, v, huv, rfl⟩ := hσ
  rcases (swap_apply_ne_self_iff huv).1 hc with rfl | rfl
  · exact ⟨v, huv.symm, rfl⟩
  · exact ⟨u, huv, swap_comm _ _⟩

theorem exists_common_of_not_comm {σ τ : Perm (Fin n)} (hσ : σ.IsSwap) (hτ : τ.IsSwap)
    (h : σ * τ ≠ τ * σ) : ∃ p, σ p ≠ p ∧ τ p ≠ p := by
  obtain ⟨u, v, huv, rfl⟩ := hσ
  obtain ⟨u', v', huv', rfl⟩ := hτ
  by_contra hall
  push Not at hall
  have hu : swap u v u ≠ u := by rw [swap_apply_left]; exact fun e => huv e.symm
  have hv : swap u v v ≠ v := by rw [swap_apply_right]; exact huv
  refine h (swap_comm_of_disjoint ?_ ?_ ?_ ?_)
  · rintro rfl
    exact (by rw [swap_apply_left]; exact fun e => huv' e.symm : swap u v' u ≠ u) (hall u hu)
  · rintro rfl
    exact (by rw [swap_apply_right]; exact huv' : swap u' u u ≠ u) (hall u hu)
  · rintro rfl
    exact (by rw [swap_apply_left]; exact fun e => huv' e.symm : swap v v' v ≠ v) (hall v hv)
  · rintro rfl
    exact (by rw [swap_apply_right]; exact huv' : swap u' v v ≠ v) (hall v hv)

theorem common_point_of_four {σ₁ σ₂ σ₃ σ₄ : Perm (Fin n)} (h₁ : σ₁.IsSwap) (h₂ : σ₂.IsSwap)
    (h₃ : σ₃.IsSwap) (h₄ : σ₄.IsSwap) (h12 : σ₁ * σ₂ ≠ σ₂ * σ₁) (h13 : σ₁ * σ₃ ≠ σ₃ * σ₁)
    (h14 : σ₁ * σ₄ ≠ σ₄ * σ₁) (h23 : σ₂ * σ₃ ≠ σ₃ * σ₂) (h24 : σ₂ * σ₄ ≠ σ₄ * σ₂)
    (h34 : σ₃ * σ₄ ≠ σ₄ * σ₃) {c : Fin n} (hc₁ : σ₁ c ≠ c) (hc₂ : σ₂ c ≠ c) :
    σ₃ c ≠ c := by
  have hne : ∀ {σ τ : Perm (Fin n)}, σ * τ ≠ τ * σ → σ ≠ τ := fun h e => h (by rw [e])
  obtain ⟨x, hxc, rfl⟩ := exists_eq_swap_of_moves h₁ hc₁
  obtain ⟨y, hyc, rfl⟩ := exists_eq_swap_of_moves h₂ hc₂
  have hxy : x ≠ y := fun e => hne h12 (by rw [e])
  have key : ∀ {τ : Perm (Fin n)}, τ.IsSwap → swap c x * τ ≠ τ * swap c x →
      swap c y * τ ≠ τ * swap c y → τ c = c → τ = swap x y := by
    intro τ hτ ht1 ht2 htc
    obtain ⟨p, hp1, hp2⟩ := exists_common_of_not_comm (⟨c, x, hxc.symm, rfl⟩) hτ ht1
    obtain ⟨q, hq1, hq2⟩ := exists_common_of_not_comm (⟨c, y, hyc.symm, rfl⟩) hτ ht2
    have hpx : p = x := by
      rcases (swap_apply_ne_self_iff hxc.symm).1 hp1 with rfl | rfl
      · exact absurd htc hp2
      · rfl
    have hqy : q = y := by
      rcases (swap_apply_ne_self_iff hyc.symm).1 hq1 with rfl | rfl
      · exact absurd htc hq2
      · rfl
    subst hpx hqy
    obtain ⟨u, v, huv, rfl⟩ := hτ
    exact eq_swap_of_moves huv hxy hp2 hq2
  intro h3c
  have hσ₃ := key h₃ h13 h23 h3c
  subst hσ₃
  by_cases h4c : σ₄ c = c
  · exact hne h34 (key h₄ h14 h24 h4c).symm
  · obtain ⟨z, hzc, rfl⟩ := exists_eq_swap_of_moves h₄ h4c
    obtain ⟨p, hp1, hp2⟩ := exists_common_of_not_comm (⟨x, y, hxy, rfl⟩) h₄ h34
    have hp : p = x ∨ p = y := (swap_apply_ne_self_iff hxy).1 hp1
    rcases (swap_apply_ne_self_iff hzc.symm).1 hp2 with rfl | rfl
    · rcases hp with rfl | rfl
      · exact hxc rfl
      · exact hyc rfl
    · rcases hp with rfl | rfl
      · exact hne h14 rfl
      · exact hne h24 rfl

@[expose] def T6 : List (Perm (Fin 6)) :=
  [1, swap 0 1, swap 2 3 * swap 4 5, swap 2 4 * swap 3 5, swap 2 5 * swap 3 4,
    swap 0 1 * (swap 2 3 * swap 4 5), swap 0 1 * (swap 2 4 * swap 3 5),
    swap 0 1 * (swap 2 5 * swap 3 4)]

set_option maxRecDepth 100000 in
theorem t6_check : ∀ x : Perm (Fin 6), x * swap 0 1 = swap 0 1 * x → x ∉ T6 →
    ∃ c : Perm (Fin 6), c * swap 0 1 = swap 0 1 * c ∧
      (x⁻¹ * (c * x * c⁻¹)) * (x⁻¹ * (c * x * c⁻¹)) * (x⁻¹ * (c * x * c⁻¹)) = 1 ∧
      x⁻¹ * (c * x * c⁻¹) ≠ 1 := by
  decide

set_option maxRecDepth 100000 in
theorem t6_comm : ∀ a ∈ T6, ∀ b ∈ T6, a * b = b * a := by
  decide

theorem eq_one_of_two_of_cube {X : Type*} [Monoid X] {y : X} (h2 : ∃ k : ℕ, y ^ 2 ^ k = 1)
    (h3 : y * y * y = 1) : y = 1 := by
  obtain ⟨k, hk⟩ := h2
  have h3' : y ^ 3 = 1 := by rw [pow_three, ← mul_assoc]; exact h3
  have hcop : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
  have h := pow_gcd_eq_one.mpr ⟨hk, h3'⟩
  rwa [hcop, pow_one] at h

theorem mem_T6_of_normal {N : Subgroup (Perm (Fin 6))} (hN2 : IsPGroup 2 N)
    (hNC : ∀ x ∈ N, x * swap 0 1 = swap 0 1 * x)
    (hNn : ∀ c : Perm (Fin 6), c * swap 0 1 = swap 0 1 * c → ∀ x ∈ N, c * x * c⁻¹ ∈ N)
    {x : Perm (Fin 6)} (hx : x ∈ N) : x ∈ T6 := by
  by_contra hxT
  obtain ⟨c, hc, hc3, hc1⟩ := t6_check x (hNC x hx) hxT
  have hy : x⁻¹ * (c * x * c⁻¹) ∈ N := mul_mem (inv_mem hx) (hNn c hc x hx)
  refine hc1 (eq_one_of_two_of_cube ?_ hc3)
  obtain ⟨k, hk⟩ := hN2 ⟨_, hy⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem exists_ne_three (hn : 5 ≤ n) (a b c d : Fin n) : ∃ x, x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {a, b, c, d} := fun x _ => by
    by_cases ha : x = a
    · simp [ha]
    by_cases hb : x = b
    · simp [hb]
    by_cases hc : x = c
    · simp [hc]
    simp [h x ha hb hc]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have h2 : ({a, b, c, d} : Finset (Fin n)).card ≤ 4 := Finset.card_le_four
  omega

variable (β : MulAut (Perm (Fin n))) (hβ : ∀ σ : Perm (Fin n), σ.IsSwap → (β σ).IsSwap)
include hβ

omit hβ in
theorem aut_not_comm {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    β (swap i j) * β (swap i k) ≠ β (swap i k) * β (swap i j) := by
  rw [← map_mul, ← map_mul]
  exact fun h => swap_not_comm hij hik hjk (β.injective h)

theorem exists_star_point (hn : 5 ≤ n) (i : Fin n) :
    ∃ c, ∀ j, j ≠ i → β (swap i j) c ≠ c := by
  obtain ⟨j₁, hj₁, -⟩ := exists_ne_three hn i i i i
  obtain ⟨j₂, hj₂i, hj₂j₁, -⟩ := exists_ne_three hn i j₁ i i
  have hsw : ∀ j, j ≠ i → (β (swap i j)).IsSwap := fun j hj => hβ _ ⟨i, j, hj.symm, rfl⟩
  obtain ⟨c, hc1, hc2⟩ := exists_common_of_not_comm (hsw j₁ hj₁) (hsw j₂ hj₂i)
    (aut_not_comm β hj₁.symm hj₂i.symm hj₂j₁.symm)
  refine ⟨c, fun j hj => ?_⟩
  by_cases h1 : j = j₁
  · rw [h1]
    exact hc1
  by_cases h2 : j = j₂
  · rw [h2]
    exact hc2
  obtain ⟨j', hj'i, hj'1, hj'2, hj'j⟩ := exists_ne_three hn i j₁ j₂ j
  exact common_point_of_four (hsw j₁ hj₁) (hsw j₂ hj₂i) (hsw j hj) (hsw j' hj'i)
    (aut_not_comm β hj₁.symm hj₂i.symm hj₂j₁.symm) (aut_not_comm β hj₁.symm hj.symm (Ne.symm h1))
    (aut_not_comm β hj₁.symm hj'i.symm hj'1.symm) (aut_not_comm β hj₂i.symm hj.symm (Ne.symm h2))
    (aut_not_comm β hj₂i.symm hj'i.symm hj'2.symm) (aut_not_comm β hj.symm hj'i.symm hj'j.symm)
    hc1 hc2

theorem perm_aut_eq_conj_of_isSwap (hn : 5 ≤ n) :
    ∃ π : Perm (Fin n), ∀ σ, β σ = π * σ * π⁻¹ := by
  choose c hc using exists_star_point β hβ hn
  have hinj : Function.Injective c := by
    intro i i' hii'
    by_contra hne
    obtain ⟨j, hji, hji', -⟩ := exists_ne_three hn i i' i i
    have m1 : β (swap i i') (c i) ≠ c i := hc i i' (Ne.symm hne)
    have m2 : β (swap i' j) (c i) ≠ c i := by rw [hii']; exact hc i' j hji'
    have m3 : β (swap i j) (c i) ≠ c i := hc i j hji
    obtain ⟨x, hx, e1⟩ := exists_eq_swap_of_moves (hβ _ ⟨i, i', hne, rfl⟩) m1
    obtain ⟨y, hy, e2⟩ := exists_eq_swap_of_moves (hβ _ ⟨i', j, hji'.symm, rfl⟩) m2
    obtain ⟨z, hz, e3⟩ := exists_eq_swap_of_moves (hβ _ ⟨i, j, hji.symm, rfl⟩) m3
    have hxy : x ≠ y := by
      intro hxy
      rw [hxy, ← e2] at e1
      rcases eq_or_eq_of_swap_eq hne (β.injective e1) with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hne h1
      · exact hji h1.symm
    have hrel : swap i j = swap i i' * swap i' j * (swap i i')⁻¹ := by
      rw [← swap_apply_apply, swap_apply_right, swap_apply_of_ne_of_ne hji hji']
    have h1 := congrArg β hrel
    rw [map_mul, map_mul, map_inv, e1, e2, e3, ← swap_apply_apply, swap_apply_left,
      swap_apply_of_ne_of_ne hy (Ne.symm hxy)] at h1
    rcases eq_or_eq_of_swap_eq hz.symm h1 with ⟨h2, -⟩ | ⟨h2, -⟩
    · exact hx h2.symm
    · exact hy h2.symm
  set π : Perm (Fin n) := Equiv.ofBijective c (Finite.injective_iff_bijective.mp hinj) with hπ
  have hπc : ∀ i, π i = c i := fun i => rfl
  have hsw : ∀ σ : Perm (Fin n), σ.IsSwap → β σ = π * σ * π⁻¹ := by
    rintro _ ⟨i, j, hij, rfl⟩
    rw [← swap_apply_apply, hπc, hπc]
    obtain ⟨u, v, huv, huv'⟩ := hβ _ ⟨i, j, hij, rfl⟩
    have h1 := hc i j hij.symm
    have h2 := hc j i hij
    rw [swap_comm j i] at h2
    rw [huv'] at h1 h2 ⊢
    exact eq_swap_of_moves huv (hinj.ne hij) h1 h2
  refine ⟨π, fun σ => ?_⟩
  have h := MonoidHom.eq_of_eqOn_dense (Equiv.Perm.closure_isSwap (α := Fin n))
    (f := β.toMonoidHom) (g := (MulAut.conj π).toMonoidHom) fun τ hτ => hsw τ hτ
  exact congrArg (fun f : Perm (Fin n) →* Perm (Fin n) => f σ) h

end CFSG.LargeExtraspecial.AS35YF
