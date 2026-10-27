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
public import Mathlib.GroupTheory.GroupAction.Jordan
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

namespace CFSG.CGT.PushingUpLit.CGT6

open Equiv MulAction

theorem cycleType_of_orderOf_nine_perm9 {σ : Perm (Fin 9)} (h : orderOf σ = 9) : σ.cycleType = {9} := by
  have h9 : 9 ∈ σ.cycleType := by
    by_contra hno
    have hall : ∀ m ∈ σ.cycleType, m = 3 := by
      intro m hm
      have h1 : m ∣ 9 := h ▸ Perm.dvd_of_mem_cycleType hm
      have h2 : 2 ≤ m := Perm.two_le_of_mem_cycleType hm
      have h3 : m ≠ 9 := fun h' => hno (h' ▸ hm)
      have : m ∣ 3 ^ 2 := by simpa using h1
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp this
      interval_cases k
      · omega
      · simp [hk']
      · exact absurd hk' h3
    have : σ.cycleType.lcm ∣ 3 := by
      rw [Multiset.lcm_dvd]
      intro m hm
      rw [hall m hm]
    rw [Perm.lcm_cycleType, h] at this
    omega
  exact Perm.cycleType_of_card_le_mem_cycleType_add_two (by simp) h9

@[expose] def alt9c0 : Perm (Fin 9) := ⟨![1, 2, 3, 4, 5, 6, 7, 8, 0], ![8, 0, 1, 2, 3, 4, 5, 6, 7], by decide, by decide⟩
@[expose] def alt9b0 : Perm (Fin 9) := alt9c0 ^ 3
@[expose] def alt9h0 : Perm (Fin 9) := ⟨![1, 2, 0, 4, 5, 3, 7, 8, 6], ![2, 0, 1, 5, 3, 4, 8, 6, 7], by decide, by decide⟩
@[expose] def alt9g1 : Perm (Fin 9) := ⟨![0, 8, 4, 1, 6, 5, 2, 7, 3], ![0, 3, 6, 8, 2, 5, 4, 7, 1], by decide, by decide⟩
@[expose] def alt9g2 : Perm (Fin 9) := ⟨![0, 1, 2, 4, 5, 3, 8, 6, 7], ![0, 1, 2, 5, 3, 4, 7, 8, 6], by decide, by decide⟩
@[expose] def alt9g3 : Perm (Fin 9) := ⟨![0, 1, 2, 5, 3, 4, 7, 8, 6], ![0, 1, 2, 4, 5, 3, 8, 6, 7], by decide, by decide⟩

theorem orderOf_alt9c0 : orderOf alt9c0 = 9 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  intro m hm hm0
  interval_cases m <;> decide

theorem alt9h0_pow : alt9h0 ^ 3 = 1 := by decide
theorem alt9b0_comm_h0 : alt9b0 * alt9h0 = alt9h0 * alt9b0 := by decide
theorem alt9g1_conj : alt9g1 * alt9b0 * alt9g1⁻¹ = alt9h0 := by decide
theorem alt9g2_conj : alt9g2 * alt9b0 * alt9g2⁻¹ = alt9b0 * alt9h0 := by decide
theorem alt9g3_conj : alt9g3 * alt9b0 * alt9g3⁻¹ = alt9b0 * alt9h0 ^ 2 := by decide
theorem sign_alt9h0 : Perm.sign alt9h0 = 1 := by decide
theorem sign_alt9g1 : Perm.sign alt9g1 = 1 := by decide
theorem sign_alt9g2 : Perm.sign alt9g2 = 1 := by decide
theorem sign_alt9g3 : Perm.sign alt9g3 = 1 := by decide

theorem sign_conj_perm9 (π f : Perm (Fin 9)) : Perm.sign (π * f * π⁻¹) = Perm.sign f := by
  rw [map_mul, map_mul, map_inv, mul_comm (Perm.sign π) (Perm.sign f), mul_assoc, mul_inv_cancel,
    mul_one]

theorem exists_e9_alt9 (c : alternatingGroup (Fin 9)) (hc : orderOf c = 9) :
    ∃ x g₁ g₂ g₃ : alternatingGroup (Fin 9), x ^ 3 = 1 ∧ c ^ 3 * x = x * c ^ 3 ∧
      x = g₁ * c ^ 3 * g₁⁻¹ ∧ c ^ 3 * x = g₂ * c ^ 3 * g₂⁻¹ ∧ c ^ 3 * x ^ 2 = g₃ * c ^ 3 * g₃⁻¹ := by
  have hc' : orderOf (c : Perm (Fin 9)) = 9 := by rw [Subgroup.orderOf_coe]; exact hc
  have hconj : IsConj alt9c0 (c : Perm (Fin 9)) := by
    rw [Perm.isConj_iff_cycleType_eq, cycleType_of_orderOf_nine_perm9 hc', cycleType_of_orderOf_nine_perm9 orderOf_alt9c0]
  obtain ⟨π, hπ⟩ := isConj_iff.mp hconj
  have hcube : (c : Perm (Fin 9)) ^ 3 = π * alt9b0 * π⁻¹ := by
    rw [← hπ, alt9b0, conj_pow]
  have hmem : ∀ f : Perm (Fin 9), Perm.sign f = 1 → π * f * π⁻¹ ∈ alternatingGroup (Fin 9) := by
    intro f hf
    rw [Perm.mem_alternatingGroup, sign_conj_perm9, hf]
  refine ⟨⟨π * alt9h0 * π⁻¹, hmem _ sign_alt9h0⟩, ⟨π * alt9g1 * π⁻¹, hmem _ sign_alt9g1⟩,
    ⟨π * alt9g2 * π⁻¹, hmem _ sign_alt9g2⟩, ⟨π * alt9g3 * π⁻¹, hmem _ sign_alt9g3⟩, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    show (π * alt9h0 * π⁻¹) ^ 3 = 1
    rw [conj_pow, alt9h0_pow]; simp
  · apply Subtype.ext
    show (c : Perm (Fin 9)) ^ 3 * (π * alt9h0 * π⁻¹) = (π * alt9h0 * π⁻¹) * (c : Perm (Fin 9)) ^ 3
    rw [hcube]
    calc π * alt9b0 * π⁻¹ * (π * alt9h0 * π⁻¹) = π * (alt9b0 * alt9h0) * π⁻¹ := by group
      _ = π * (alt9h0 * alt9b0) * π⁻¹ := by rw [alt9b0_comm_h0]
      _ = _ := by group
  · apply Subtype.ext
    show π * alt9h0 * π⁻¹ = π * alt9g1 * π⁻¹ * (c : Perm (Fin 9)) ^ 3 * (π * alt9g1 * π⁻¹)⁻¹
    rw [hcube, ← alt9g1_conj]; group
  · apply Subtype.ext
    show (c : Perm (Fin 9)) ^ 3 * (π * alt9h0 * π⁻¹) =
      π * alt9g2 * π⁻¹ * (c : Perm (Fin 9)) ^ 3 * (π * alt9g2 * π⁻¹)⁻¹
    rw [hcube]
    have : π * alt9g2 * π⁻¹ * (π * alt9b0 * π⁻¹) * (π * alt9g2 * π⁻¹)⁻¹ = π * (alt9g2 * alt9b0 * alt9g2⁻¹) * π⁻¹ := by group
    rw [this, alt9g2_conj]; group
  · apply Subtype.ext
    show (c : Perm (Fin 9)) ^ 3 * (π * alt9h0 * π⁻¹) ^ 2 =
      π * alt9g3 * π⁻¹ * (c : Perm (Fin 9)) ^ 3 * (π * alt9g3 * π⁻¹)⁻¹
    rw [hcube]
    have : π * alt9g3 * π⁻¹ * (π * alt9b0 * π⁻¹) * (π * alt9g3 * π⁻¹)⁻¹ = π * (alt9g3 * alt9b0 * alt9g3⁻¹) * π⁻¹ := by group
    rw [this, alt9g3_conj, conj_pow]; group


theorem perm9_exists_three_points : ∀ p : Fin 9, ∃ p' x : Fin 9, p' ≠ p ∧ x ≠ p ∧ x ≠ p' := by decide

theorem exists_gen_alt9 (E : Subgroup (Perm (Fin 9))) (hEalt : E ≤ alternatingGroup (Fin 9))
    (p : Fin 9) (hfix : ∀ a ∈ E, a p = p)
    (hreg : ∀ q q' : Fin 9, q ≠ p → q' ≠ p → ∃ a ∈ E, a q = q')
    (hinv : ∀ a ∈ E, a * a = 1) :
    ∃ g ∈ alternatingGroup (Fin 9),
      E ⊔ E.map (MulAut.conj g).toMonoidHom = alternatingGroup (Fin 9) := by
  classical
  obtain ⟨p', x, hp'p, hxp, hxp'⟩ := perm9_exists_three_points p
  set g : Perm (Fin 9) := swap p x * swap p p' with hg
  have hg3 : g.IsThreeCycle := Perm.isThreeCycle_swap_mul_swap_same hxp.symm hp'p.symm hxp'
  have hgalt : g ∈ alternatingGroup (Fin 9) := by
    rw [Perm.mem_alternatingGroup]; exact hg3.sign
  have hg1 : g p = p' := by
    simp [hg, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hp'p hxp'.symm]
  obtain ⟨e, heE, hep'⟩ := hreg p' x hp'p hxp
  have hex : e x = p' := by
    have := hinv e heE
    have h2 := congrArg (fun f : Perm (Fin 9) => f p') this
    simp only [Perm.mul_apply, Perm.one_apply, hep'] at h2
    exact h2
  have hep := hfix e heE
  have hconj : e * g * e⁻¹ = g⁻¹ := by
    have h1 : e * (swap p x * swap p p') * e⁻¹ = (e * swap p x * e⁻¹) * (e * swap p p' * e⁻¹) := by
      group
    rw [hg, h1, ← swap_apply_apply, ← swap_apply_apply, hep, hex, hep', mul_inv_rev, swap_inv,
      swap_inv]
  have hg3one : g ^ 3 = 1 := by
    rw [← hg3.orderOf]; exact pow_orderOf_eq_one g
  set E' : Subgroup (Perm (Fin 9)) := E.map (MulAut.conj g).toMonoidHom with hE'
  set M : Subgroup (Perm (Fin 9)) := E ⊔ E' with hM
  have hEM : E ≤ M := le_sup_left
  have hgM : g ∈ M := by
    have h1 : g * e⁻¹ * g⁻¹ ∈ E' := ⟨e⁻¹, E.inv_mem heE, by simp [MulAut.conj_apply]⟩
    have h2 : g = e * (g * e⁻¹ * g⁻¹) := by
      calc g = g⁻¹ * g⁻¹ := by
            calc g = g ^ 3 * g⁻¹ * g⁻¹ := by group
              _ = g⁻¹ * g⁻¹ := by rw [hg3one, one_mul]
        _ = (e * g * e⁻¹) * g⁻¹ := by rw [hconj]
        _ = e * (g * e⁻¹ * g⁻¹) := by group
    rw [h2]
    exact M.mul_mem (hEM heE) ((le_sup_right : E' ≤ M) h1)
  have hMalt : M ≤ alternatingGroup (Fin 9) := by
    refine sup_le hEalt ?_
    rintro _ ⟨a, ha, rfl⟩
    rw [Perm.mem_alternatingGroup]
    have := Perm.mem_alternatingGroup.mp (hEalt ha)
    show Perm.sign (g * a * g⁻¹) = 1
    rw [map_mul, map_mul, map_inv, this, mul_one, mul_inv_cancel]
  have hreach : ∀ q : Fin 9, ∃ m ∈ M, m p = q := by
    intro q
    by_cases hq : q = p
    · exact ⟨1, M.one_mem, by simp [hq]⟩
    · obtain ⟨a, haE, ha⟩ := hreg p' q hp'p hq
      exact ⟨a * g, M.mul_mem (hEM haE) hgM, by simp [Perm.mul_apply, hg1, ha]⟩
  have h2 : IsMultiplyPretransitive ↥M (Fin 9) 2 := by
    rw [is_two_pretransitive_iff]
    intro a b c d hab hcd
    obtain ⟨u0, hu0M, hu0⟩ := hreach a
    obtain ⟨v0, hv0M, hv0⟩ := hreach c
    have hub : u0⁻¹ b ≠ p := by
      intro h
      apply hab
      have h1 : u0⁻¹ b = u0⁻¹ a := by rw [h, ← hu0]; simp
      exact (u0⁻¹).injective h1 |>.symm
    have hvd : v0⁻¹ d ≠ p := by
      intro h
      apply hcd
      have h1 : v0⁻¹ d = v0⁻¹ c := by rw [h, ← hv0]; simp
      exact (v0⁻¹).injective h1 |>.symm
    obtain ⟨e', he'E, he'⟩ := hreg (u0⁻¹ b) (v0⁻¹ d) hub hvd
    refine ⟨⟨v0 * e' * u0⁻¹, M.mul_mem (M.mul_mem hv0M (hEM he'E)) (M.inv_mem hu0M)⟩, ?_, ?_⟩
    · show (v0 * e' * u0⁻¹) a = c
      have ha : u0⁻¹ a = p := by rw [← hu0]; simp
      simp [Perm.mul_apply, ha, hfix e' he'E, hv0]
    · show (v0 * e' * u0⁻¹) b = d
      have h3 : (v0 * e' * u0⁻¹) b = v0 (e' (u0⁻¹ b)) := rfl
      rw [h3, he']; simp
  have hprim : IsPreprimitive ↥M (Fin 9) := isPreprimitive_of_is_two_pretransitive h2
  exact ⟨g, hgalt, le_antisymm hMalt
    (Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim hg3 hgM)⟩


theorem card_fixed_involution_alt9 {a : Perm (Fin 9)} (ha : a ∈ alternatingGroup (Fin 9))
    (hsq : a * a = 1) (h1 : a ≠ 1) :
    (Finset.univ.filter fun q : Fin 9 => a q = q).card = 1 ∨
      (Finset.univ.filter fun q : Fin 9 => a q = q).card = 5 := by
  classical
  have ha2 : a ^ 2 = 1 := by rw [sq]; exact hsq
  have hev : 2 ∣ a.support.card := Perm.two_dvd_card_support ha2
  have hnz : a.support.card ≠ 0 := fun h => h1 (Perm.card_support_eq_zero.mp h)
  have hle : a.support.card ≤ 9 := by
    have := Finset.card_le_univ a.support; simpa using this
  have hfix : (Finset.univ.filter fun q : Fin 9 => a q = q).card = 9 - a.support.card := by
    have : (Finset.univ.filter fun q : Fin 9 => a q = q) = a.supportᶜ := by
      ext q; simp [Perm.mem_support]
    rw [this, Finset.card_compl]; simp
  have hfp : Fintype.card (Function.fixedPoints a) = 9 - a.support.card := by
    rw [Perm.card_fixedPoints, Perm.sum_cycleType]; simp
  have hsign := Perm.sign_of_pow_two_eq_one ha2
  rw [Perm.mem_alternatingGroup.mp ha, hfp] at hsign
  have h3 : (-1 : ℤˣ) ^ (a.support.card / 2) = 1 := by
    have : (Fintype.card (Fin 9) - (9 - a.support.card)) / 2 = a.support.card / 2 := by
      simp; congr 1; omega
    rw [this] at hsign
    exact hsign.symm
  have h4 : Even (a.support.card / 2) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    rw [hodd.neg_one_pow] at h3
    exact absurd h3 (by decide)
  rw [hfix]
  obtain ⟨k, hk⟩ := hev
  obtain ⟨m, hm⟩ := h4
  have : a.support.card = 2 * (m + m) := by
    have : a.support.card / 2 = k := by omega
    omega
  omega

theorem exists_regular_alt9 (E : Subgroup (Perm (Fin 9))) (hEalt : E ≤ alternatingGroup (Fin 9))
    (hcard : Nat.card E = 8) (hinv : ∀ a ∈ E, a * a = 1)
    (hconj : ∀ x ∈ E, x ≠ 1 → ∀ y ∈ E, y ≠ 1 → ∃ π ∈ alternatingGroup (Fin 9), π * x * π⁻¹ = y) :
    ∃ p : Fin 9, (∀ a ∈ E, a p = p) ∧
      ∀ q q' : Fin 9, q ≠ p → q' ≠ p → ∃ a ∈ E, a q = q' := by
  classical
  let fx : Perm (Fin 9) → ℕ := fun a => (Finset.univ.filter fun q : Fin 9 => a q = q).card
  have hfx : ∀ a : Perm (Fin 9), fx a = 9 - a.support.card := by
    intro a
    have : (Finset.univ.filter fun q : Fin 9 => a q = q) = a.supportᶜ := by
      ext q; simp [Perm.mem_support]
    simp only [fx]
    rw [this, Finset.card_compl]; simp
  have hnt : 1 < Nat.card E := by rw [hcard]; norm_num
  obtain ⟨a₀, ha₀E, ha₀1⟩ : ∃ a ∈ E, a ≠ 1 := by
    have := Finite.one_lt_card_iff_nontrivial.mp hnt
    obtain ⟨⟨a, haE⟩, h⟩ := exists_ne (1 : E)
    exact ⟨a, haE, fun h' => h (Subtype.ext h')⟩
  have hf : ∀ a ∈ E, a ≠ 1 → fx a = fx a₀ := by
    intro a haE ha1
    obtain ⟨π, -, hπ⟩ := hconj a₀ ha₀E ha₀1 a haE ha1
    rw [hfx, hfx, ← hπ, Perm.card_support_conj]
  have hf15 : fx a₀ = 1 ∨ fx a₀ = 5 :=
    card_fixed_involution_alt9 (hEalt ha₀E) (hinv a₀ ha₀E) ha₀1
  have hE8 : Fintype.card E = 8 := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have hburn : 8 ∣ ∑ a : E, fx (a : Perm (Fin 9)) := by
    have := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (G := ↥E) (X := Fin 9)
    have h2 : ∀ g : E, Fintype.card (MulAction.fixedBy (Fin 9) g) = fx (g : Perm (Fin 9)) := by
      intro g
      rw [Fintype.card_subtype]
      simp [fx, MulAction.mem_fixedBy, Subgroup.smul_def, Perm.smul_def]
    simp only [h2] at this
    rw [this, hE8]
    exact dvd_mul_left _ _
  have hsum : ∑ a : E, fx (a : Perm (Fin 9)) = 9 + 7 * fx a₀ := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (1 : E))]
    have h1 : fx ((1 : E) : Perm (Fin 9)) = 9 := by
      simp [fx]
    have h2 : ∑ a ∈ Finset.univ.erase (1 : E), fx (a : Perm (Fin 9)) = 7 * fx a₀ := by
      rw [Finset.sum_congr rfl (g := fun _ => fx a₀)]
      · rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hE8]
        simp
      · intro a ha
        have hne : a ≠ 1 := Finset.ne_of_mem_erase ha
        exact hf a a.2 (fun h => hne (Subtype.ext h))
    rw [h1, h2]
  have hf1 : fx a₀ = 1 := by
    rw [hsum] at hburn
    rcases hf15 with h | h
    · exact h
    · rw [h] at hburn; omega
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hf1
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    have hab : (a * b) * (a * b) = 1 := hinv _ (E.mul_mem ha hb)
    have h1 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab
    have h2 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hinv a ha)
    have h3 : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hinv b hb)
    calc a * b = (a * b)⁻¹ := h1.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [h2, h3]
  have hpfix : ∀ q : Fin 9, a₀ q = q ↔ q = p := by
    intro q
    have : q ∈ Finset.univ.filter (fun q : Fin 9 => a₀ q = q) ↔ q ∈ ({p} : Finset (Fin 9)) := by
      rw [hp]
    simpa using this
  have hEp : ∀ a ∈ E, a p = p := by
    intro a ha
    have h1 : a₀ (a p) = a p := by
      have := congrArg (fun f : Perm (Fin 9) => f p) (hcomm a₀ ha₀E a ha)
      simp only [Perm.mul_apply] at this
      have h0 : a₀ p = p := (hpfix p).mpr rfl
      rw [h0] at this
      exact this
    exact (hpfix _).mp h1
  have hfree : ∀ a ∈ E, a ≠ 1 → ∀ q : Fin 9, q ≠ p → a q ≠ q := by
    intro a haE ha1 q hq hqa
    have hfa : fx a = 1 := (hf a haE ha1).trans hf1
    have hsub : ({p} : Finset (Fin 9)) ⊆ Finset.univ.filter (fun q : Fin 9 => a q = q) := by
      intro r hr
      rw [Finset.mem_singleton] at hr
      simp [hr, hEp a haE]
    have hcard1 : ({p} : Finset (Fin 9)).card = (Finset.univ.filter fun q : Fin 9 => a q = q).card := by
      rw [Finset.card_singleton]; exact hfa.symm
    have heq := Finset.eq_of_subset_of_card_le hsub hcard1.ge
    have : q ∈ Finset.univ.filter (fun q : Fin 9 => a q = q) := by simp [hqa]
    rw [← heq] at this
    exact hq (Finset.mem_singleton.mp this)
  refine ⟨p, hEp, ?_⟩
  intro q q' hq hq'
  let φ : E → {x : Fin 9 // x ≠ p} := fun a => ⟨(a : Perm (Fin 9)) q, by
    intro h
    apply hq
    have : (a : Perm (Fin 9)) q = (a : Perm (Fin 9)) p := by rw [h, hEp a a.2]
    exact (a : Perm (Fin 9)).injective this⟩
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h1 : (a : Perm (Fin 9)) q = (b : Perm (Fin 9)) q := congrArg Subtype.val hab
    have h2 : ((b : Perm (Fin 9))⁻¹ * (a : Perm (Fin 9))) q = q := by
      simp only [Perm.mul_apply, h1]
      exact Equiv.symm_apply_apply (b : Perm (Fin 9)) q
    by_contra hne
    have hne' : (b : Perm (Fin 9))⁻¹ * (a : Perm (Fin 9)) ≠ 1 := by
      intro h
      apply hne
      have : (a : Perm (Fin 9)) = b := by
        have := congrArg (fun f => (b : Perm (Fin 9)) * f) h
        simpa using this
      exact Subtype.ext this
    exact hfree _ (E.mul_mem (E.inv_mem b.2) a.2) hne' q hq h2
  have hcardsub : Nat.card {x : Fin 9 // x ≠ p} = 8 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]; simp
  have hbij : Function.Bijective φ :=
    hφinj.bijective_of_nat_card_le (by rw [hcardsub, hcard])
  obtain ⟨a, ha⟩ := hbij.2 ⟨q', hq'⟩
  exact ⟨a, a.2, congrArg Subtype.val ha⟩


end CFSG.CGT.PushingUpLit.CGT6
