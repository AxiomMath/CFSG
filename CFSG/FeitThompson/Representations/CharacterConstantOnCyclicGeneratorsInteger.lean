module

import CFSG.FeitThompson.Representations.RationalAlgebraicIntegerIsInteger
import CFSG.FeitThompson.Representations.CharacterValuesAlgebraicIntegers
import CFSG.FeitThompson.Representations.CliffordIsotypicDecomposition
public import CFSG.FeitThompson.Representations.VirtualCharacterNormCyclicGenerators
import Mathlib.MeasureTheory.Integral.Bochner.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Finset Module

theorem sum_divisors_moebius (n : ℕ) :
    ∑ d ∈ n.divisors, ArithmeticFunction.moebius d = if n = 1 then 1 else 0 := by
  have h := congrArg (fun F : ArithmeticFunction ℤ => F n)
    ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  rw [h]

theorem sum_moebius_filter_dvd {N : ℕ} (hN : N ≠ 0) (a : ℕ) :
    ∑ d ∈ {d ∈ N.divisors | d ∣ a}, ArithmeticFunction.moebius d
      = if a.Coprime N then 1 else 0 := by
  classical
  have h1 : {d ∈ N.divisors | d ∣ a} = (Nat.gcd a N).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · intro h; exact ⟨⟨h.2, h.1.1⟩, Nat.gcd_ne_zero_right hN⟩
    · intro h; exact ⟨⟨h.1.2, hN⟩, h.1.1⟩
  rw [h1, sum_divisors_moebius]

theorem coprimeIndices_eq_filter (N : ℕ) :
    coprimeIndices N = {a ∈ Finset.Icc 1 N | a.Coprime N} := by
  classical
  ext a
  simp only [mem_coprimeIndices, Finset.mem_filter, Finset.mem_Icc]
  tauto

theorem sum_coprimeIndices_eq {N : ℕ} (hN : N ≠ 0) (F : ℕ → ℂ) :
    ∑ a ∈ coprimeIndices N, F a
      = ∑ d ∈ N.divisors, (ArithmeticFunction.moebius d : ℂ) *
          ∑ a ∈ {a ∈ Finset.Icc 1 N | d ∣ a}, F a := by
  classical
  have key : ∀ a : ℕ, ∑ d ∈ N.divisors, (if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0)
      = if a.Coprime N then (1 : ℂ) else 0 := by
    intro a
    rw [← Finset.sum_filter]
    have h := sum_moebius_filter_dvd hN a
    calc (∑ d ∈ {d ∈ N.divisors | d ∣ a}, (ArithmeticFunction.moebius d : ℂ))
        = ((∑ d ∈ {d ∈ N.divisors | d ∣ a}, ArithmeticFunction.moebius d : ℤ) : ℂ) := by
          push_cast; rfl
      _ = if a.Coprime N then (1 : ℂ) else 0 := by rw [h]; split <;> simp
  calc ∑ a ∈ coprimeIndices N, F a
      = ∑ a ∈ Finset.Icc 1 N, (if a.Coprime N then (1 : ℂ) else 0) * F a := by
        rw [coprimeIndices_eq_filter, Finset.sum_filter]
        exact Finset.sum_congr rfl fun a _ => by split <;> simp
    _ = ∑ a ∈ Finset.Icc 1 N, ∑ d ∈ N.divisors,
          (if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0) * F a :=
        Finset.sum_congr rfl fun a _ => by rw [← Finset.sum_mul, key a]
    _ = ∑ d ∈ N.divisors, ∑ a ∈ Finset.Icc 1 N,
          (if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0) * F a := Finset.sum_comm
    _ = ∑ d ∈ N.divisors, (ArithmeticFunction.moebius d : ℂ) *
          ∑ a ∈ {a ∈ Finset.Icc 1 N | d ∣ a}, F a := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.mul_sum, Finset.sum_filter]
        exact Finset.sum_congr rfl fun a _ => by split <;> simp

theorem sum_filter_dvd_Icc {M : Type*} [AddCommMonoid M] {N d : ℕ} (hN : N ≠ 0) (hd : d ∣ N)
    (F : ℕ → M) :
    ∑ a ∈ {a ∈ Finset.Icc 1 N | d ∣ a}, F a = ∑ t ∈ Finset.Icc 1 (N / d), F (d * t) := by
  classical
  have hd0 : 0 < d := Nat.pos_of_ne_zero fun h => hN (by simpa [h] using hd)
  refine (Finset.sum_nbij' (i := fun t => d * t) (j := fun a => a / d) ?_ ?_ ?_ ?_ ?_).symm
  · intro t ht
    simp only [Finset.mem_Icc] at ht
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hd0.ne' (by omega)), ?_⟩, Dvd.intro t rfl⟩
    calc d * t ≤ d * (N / d) := Nat.mul_le_mul_left _ ht.2
      _ = N := Nat.mul_div_cancel' hd
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha
    obtain ⟨⟨h1, h2⟩, h3⟩ := ha
    simp only [Finset.mem_Icc]
    exact ⟨(Nat.one_le_div_iff hd0).2 (Nat.le_of_dvd h1 h3), Nat.div_le_div_right h2⟩
  · intro t _; exact Nat.mul_div_cancel_left t hd0
  · intro a ha
    simp only [Finset.mem_filter] at ha
    exact Nat.mul_div_cancel' ha.2
  · intro t _; rfl

variable {G : Type*} [Group G]

theorem exists_int_sum_subgroup_of_mem_Irr [Finite G] (K : Subgroup G) [Fintype K] {χ : G → ℂ}
    (hχ : χ ∈ Irr G) : ∃ n : ℤ, ∑ x : K, χ x = n := by
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨V, -, rfl⟩ := mem_Irr.1 hχ
  have hne : ((Nat.card K : ℂ)) ≠ 0 := by simp
  have : Invertible ((Nat.card K : ℂ)) := invertibleOfNonzero hne
  refine ⟨Nat.card K * finrank ℂ (Representation.invariants (resSubgroup V.ρ K)), ?_⟩
  have h := Representation.card_inv_mul_sum_char_eq_finrank (resSubgroup V.ρ K)
  have h2 : ∀ x : K, (resSubgroup V.ρ K).character x = FDRep.character V x := fun x => by
    simp [Representation.character, resSubgroup_apply, FDRep.character]
  simp only [h2] at h
  field_simp at h
  push_cast
  rw [h]

theorem exists_int_sum_subgroup [Finite G] (K : Subgroup G) [Fintype K] {f : G → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr G)) : ∃ n : ℤ, ∑ x : K, f x = n := by
  induction hf using Submodule.span_induction with
  | mem x hx => exact exists_int_sum_subgroup_of_mem_Irr K hx
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨n, hn⟩ := hx
      obtain ⟨m, hm⟩ := hy
      refine ⟨n + m, ?_⟩
      simp only [Pi.add_apply, Finset.sum_add_distrib, hn, hm]
      push_cast
      ring
  | smul c x _ hx =>
      obtain ⟨n, hn⟩ := hx
      refine ⟨c * n, ?_⟩
      simp only [Pi.smul_apply, zsmul_eq_mul, ← Finset.mul_sum, hn]
      push_cast
      ring

theorem sum_range_orderOf_eq_sum_zpowers {f : G → ℂ} {y : G} (hy : IsOfFinOrder y)
    [Fintype (Subgroup.zpowers y)] :
    ∑ t ∈ Finset.range (orderOf y), f (y ^ t) = ∑ x : Subgroup.zpowers y, f x := by
  rw [← Fin.sum_univ_eq_sum_range (fun t => f (y ^ t)) (orderOf y)]
  exact Fintype.sum_equiv (finEquivZPowers hy) _ _ fun i => by rw [finEquivZPowers_apply hy]

theorem sum_Icc_orderOf_eq_sum_zpowers {f : G → ℂ} {y : G} (hy : IsOfFinOrder y)
    [Fintype (Subgroup.zpowers y)] :
    ∑ t ∈ Finset.Icc 1 (orderOf y), f (y ^ t) = ∑ x : Subgroup.zpowers y, f x := by
  have hM : 0 < orderOf y := hy.orderOf_pos
  rw [← sum_range_orderOf_eq_sum_zpowers (f := f) hy, ← Finset.Ico_add_one_right_eq_Icc,
    Finset.sum_Ico_succ_top hM, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hM]
  simp [pow_orderOf_eq_one]
  ring

theorem exists_int_sum_Icc_orderOf [Finite G] {f : G → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr G)) (y : G) :
    ∃ n : ℤ, ∑ t ∈ Finset.Icc 1 (orderOf y), f (y ^ t) = n := by
  have hy : IsOfFinOrder y := isOfFinOrder_of_finite y
  have : Fintype (Subgroup.zpowers y) := Fintype.ofFinite _
  obtain ⟨n, hn⟩ := exists_int_sum_subgroup (Subgroup.zpowers y) hf
  exact ⟨n, by rw [sum_Icc_orderOf_eq_sum_zpowers hy, hn]⟩

theorem isIntegral_of_mem_span_Irr [Finite G] {f : G → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr G)) (x : G) : IsIntegral ℤ (f x) := by
  have h : f ∈ Submodule.comap (LinearMap.proj x (R := ℤ) (φ := fun _ : G => ℂ))
      ((integralClosure ℤ ℂ).toSubmodule.restrictScalars ℤ) := by
    refine Submodule.span_le.2 ?_ hf
    rintro χ hχ
    obtain ⟨V, -, rfl⟩ := mem_Irr.1 hχ
    exact FDRep.isIntegral_character V x
  exact h

private def intSubring : Subring ℂ := (Int.castRingHom ℂ).range

private theorem mem_intSubring {z : ℂ} : z ∈ intSubring ↔ ∃ n : ℤ, z = n :=
  ⟨fun ⟨n, hn⟩ => ⟨n, hn.symm⟩, fun ⟨n, hn⟩ => ⟨n, hn.symm⟩⟩

theorem exists_int_apply_of_apply_pow_eq [Finite G] {f : G → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr G)) (g : G)
    (hconst : ∀ a ∈ coprimeIndices (orderOf g), f (g ^ a) = f g) :
    ∃ n : ℤ, f g = n := by
  classical
  set N := orderOf g with hNdef
  have hg : IsOfFinOrder g := isOfFinOrder_of_finite g
  have hN : N ≠ 0 := hg.orderOf_pos.ne'
  have hsum : ∑ a ∈ coprimeIndices N, f (g ^ a) ∈ intSubring := by
    rw [sum_coprimeIndices_eq hN (fun a => f (g ^ a))]
    refine Subring.sum_mem _ fun d hd => ?_
    have hdN : d ∣ N := (Nat.mem_divisors.1 hd).1
    have hd0 : d ≠ 0 := fun h => hN (by simpa [h] using hdN)
    refine Subring.mul_mem _ (mem_intSubring.2 ⟨ArithmeticFunction.moebius d, rfl⟩) ?_
    rw [sum_filter_dvd_Icc hN hdN]
    obtain ⟨n, hn⟩ := exists_int_sum_Icc_orderOf hf (g ^ d)
    rw [orderOf_pow_of_dvd hd0 hdN] at hn
    refine mem_intSubring.2 ⟨n, ?_⟩
    rw [← hn]
    exact Finset.sum_congr rfl fun t _ => by rw [pow_mul]
  obtain ⟨m, hm⟩ := mem_intSubring.1 hsum
  have hsum2 : ∑ a ∈ coprimeIndices N, f (g ^ a) = (N.totient : ℂ) * f g := by
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, card_coprimeIndices, nsmul_eq_mul]
  have hφ : (N.totient : ℂ) ≠ 0 := by
    simpa using (Nat.totient_pos.2 (Nat.pos_of_ne_zero hN)).ne'
  have hval : f g = ((m : ℚ) / (N.totient : ℚ) : ℚ) := by
    push_cast
    rw [eq_div_iff hφ, mul_comm, ← hsum2, hm]
  exact (Complex.isIntegral_int_iff_exists_int_of_exists_rat ⟨_, hval⟩).1
    (isIntegral_of_mem_span_Irr hf g)

theorem exists_int_apply_of_eqOn_cyclicGenerators [Finite G] {f : G → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr G)) (g : G)
    (hconst : ∀ y ∈ cyclicGenerators (Subgroup.zpowers g), f y = f g) :
    ∃ n : ℤ, f g = n := by
  refine exists_int_apply_of_apply_pow_eq hf g fun a ha => hconst _ ?_
  rw [cyclicGenerators_eq_image (isOfFinOrder_of_finite g)]
  exact ⟨a, ha, rfl⟩

end CFSG.FeitThompson
