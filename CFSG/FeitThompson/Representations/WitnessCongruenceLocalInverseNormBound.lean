module

public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms
import CFSG.FeitThompson.Representations.CharacterConstantOutsideSubgroupIntegral
import CFSG.FeitThompson.Representations.CommutingCyclicAverageCharacterCongruence

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

section Norm

variable {α : Type*} [Fintype α]

theorem cfInner_self_eq_ofReal (f : α → ℂ) :
    cfInner f f = (((Nat.card α : ℝ)⁻¹ * ∑ a : α, ‖f a‖ ^ 2 : ℝ) : ℂ) := by
  rw [cfInner_self_eq_sum_norm_sq]; push_cast; ring

theorem cfInner_self_re (f : α → ℂ) :
    (cfInner f f).re = (Nat.card α : ℝ)⁻¹ * ∑ a : α, ‖f a‖ ^ 2 := by
  rw [cfInner_self_eq_ofReal, Complex.ofReal_re]

end Norm

theorem sq_sub_one_le_sq_of_dvd_sub {p n e : ℤ} (he : 1 ≤ e) (hpe : 2 * e ≤ p + 1)
    (h : p ∣ n - e) : (e - 1) ^ 2 ≤ n ^ 2 := by
  obtain ⟨t, ht⟩ := h
  have hp1 : 1 ≤ p := by linarith
  have he0 : (0 : ℤ) ≤ e - 1 := by linarith
  rcases lt_trichotomy t 0 with hneg | hzero | hpos
  · have ht1 : t ≤ -1 := by omega
    have hpt : p * t ≤ -p := by nlinarith
    have h1 : n ≤ -(e - 1) := by linarith
    nlinarith
  · subst hzero
    have hne : n = e := by omega
    subst hne
    nlinarith
  · have hpt : p ≤ p * t := by nlinarith
    have h1 : e - 1 ≤ n := by linarith
    nlinarith

variable {G : Type*} [Group G]

theorem card_filter_coe_mem {M : Subgroup G} [Fintype M] (K : Subgroup G) (hKM : K ≤ M)
    [DecidablePred fun m : M => (m : G) ∈ K] :
    ({m : M | (m : G) ∈ K} : Finset M).card = Nat.card K := by
  rw [show ({m : M | (m : G) ∈ K} : Finset M).card = Nat.card {m : M // (m : G) ∈ K} by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype],
    Nat.card_congr (Equiv.subtypeEquivRight fun m : M => Subgroup.mem_subgroupOf.symm),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]

theorem le_cfInner_self_re_of_le_norm_sq {M : Subgroup G} [Fintype M] {B K : Subgroup G}
    (hBK : B ≤ K) (hKM : K ≤ M) {f : M → ℂ} {r : ℝ}
    (hval : ∀ m : M, (m : G) ∈ K → (m : G) ∉ B → r ≤ ‖f m‖ ^ 2) :
    ((Nat.card K : ℝ) - Nat.card B) / Nat.card M * r ≤ (cfInner f f).re := by
  classical
  set FK : Finset M := {m : M | (m : G) ∈ K} with hFK
  set FB : Finset M := {m : M | (m : G) ∈ B} with hFB
  have hsub : FB ⊆ FK := by
    intro m hm
    simp only [hFB, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    simpa [hFK] using hBK hm
  have hcardK : FK.card = Nat.card K := card_filter_coe_mem K hKM
  have hcardB : FB.card = Nat.card B := card_filter_coe_mem B (hBK.trans hKM)
  have hcard : ((FK \ FB).card : ℝ) = (Nat.card K : ℝ) - Nat.card B := by
    have hsplit := Finset.card_sdiff_add_card_eq_card hsub
    rw [← hcardK, ← hcardB, ← hsplit]
    push_cast
    ring
  have hsum1 : ((FK \ FB).card : ℝ) * r ≤ ∑ m ∈ FK \ FB, ‖f m‖ ^ 2 := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun m hm => ?_
    simp only [Finset.mem_sdiff, hFK, hFB, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    exact hval m hm.1 hm.2
  have hsum2 : ∑ m ∈ FK \ FB, ‖f m‖ ^ 2 ≤ ∑ m : M, ‖f m‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun m _ _ => by positivity
  have hM : (0 : ℝ) < Nat.card M := by exact_mod_cast Nat.card_pos
  rw [cfInner_self_re, div_mul_eq_mul_div, div_le_iff₀ hM]
  calc ((Nat.card K : ℝ) - Nat.card B) * r = ((FK \ FB).card : ℝ) * r := by rw [hcard]
    _ ≤ ∑ m : M, ‖f m‖ ^ 2 := hsum1.trans hsum2
    _ = (Nat.card M : ℝ)⁻¹ * (∑ m : M, ‖f m‖ ^ 2) * Nat.card M := by field_simp

theorem card_sub_card_div_card_mul_sq_le_cfInner_self_re [Finite G] {B K M : Subgroup G}
    [Fintype M] (hBK : B < K) (hKM : K ≤ M)
    {Psi : G → ℂ} (hPsi : Psi ∈ Submodule.span ℤ (Irr G))
    {c : ℂ} (hc : ∀ k ∈ K, k ∉ B → Psi k = c)
    {f : M → ℂ} (hf : ∀ m : M, (m : G) ∈ K → (m : G) ∉ B → f m = Psi m)
    {p : ℕ} (hp : p.Prime) {e : ℤ} (he : 1 ≤ e) (hpe : 2 * e ≤ (p : ℤ) + 1)
    {x g : G} (hx : orderOf x = p) (hgK : g ∈ K) (hgB : g ∉ B) (hxg : Commute x g)
    {Θ : Subgroup.zpowers x → ℂ} (hΘ : Θ ∈ Submodule.span ℤ (Irr (Subgroup.zpowers x)))
    (heΘ : Θ 1 = (e : ℂ))
    (hmatch : ∀ a : ℕ, 1 ≤ a → a ≤ p - 1 →
      Psi (x ^ a * g) = Θ (⟨x, Subgroup.mem_zpowers x⟩ ^ a)) :
    ((Nat.card K : ℝ) - Nat.card B) / Nat.card M * ((e : ℝ) - 1) ^ 2 ≤ (cfInner f f).re := by
  obtain ⟨n, hn⟩ := exists_int_eq_of_mem_span_Irr_of_eq_of_notMem hBK hPsi hc
  have hPg : Psi g = (n : ℂ) := by rw [hc g hgK hgB, hn]
  have hdvd : (p : ℤ) ∣ n - e :=
    prime_dvd_sub_of_forall_apply_eq hp hx hxg hPsi hΘ hPg heΘ hmatch
  have hsq : (e - 1) ^ 2 ≤ n ^ 2 := sq_sub_one_le_sq_of_dvd_sub he hpe hdvd
  refine le_cfInner_self_re_of_le_norm_sq hBK.le hKM fun m hmK hmB => ?_
  have hfm : ‖f m‖ ^ 2 = ((n : ℝ)) ^ 2 := by
    rw [hf m hmK hmB, hc _ hmK hmB, hn, Complex.norm_intCast, sq_abs]
  rw [hfm]
  have : (((e - 1) ^ 2 : ℤ) : ℝ) ≤ ((n ^ 2 : ℤ) : ℝ) := Int.cast_le.2 hsq
  push_cast at this
  linarith

theorem card_sub_card_div_card_mul_sq_le_cfInner_self_re_classFun [Finite G] {B K M : Subgroup G}
    [Fintype M] (hBK : B < K) (hKM : K ≤ M)
    {Psi : G → ℂ} (hPsi : Psi ∈ Submodule.span ℤ (Irr G))
    {c : ℂ} (hc : ∀ k ∈ K, k ∉ B → Psi k = c)
    (f : classFun M) (hf : ∀ m : M, (m : G) ∈ K → (m : G) ∉ B → (f : M → ℂ) m = Psi m)
    {p : ℕ} (hp : p.Prime) {e : ℤ} (he : 1 ≤ e) (hpe : 2 * e ≤ (p : ℤ) + 1)
    {x g : G} (hx : orderOf x = p) (hgK : g ∈ K) (hgB : g ∉ B) (hxg : Commute x g)
    {Θ : Subgroup.zpowers x → ℂ} (hΘ : Θ ∈ Submodule.span ℤ (Irr (Subgroup.zpowers x)))
    (heΘ : Θ 1 = (e : ℂ))
    (hmatch : ∀ a : ℕ, 1 ≤ a → a ≤ p - 1 →
      Psi (x ^ a * g) = Θ (⟨x, Subgroup.mem_zpowers x⟩ ^ a)) :
    ((Nat.card K : ℝ) - Nat.card B) / Nat.card M * ((e : ℝ) - 1) ^ 2
      ≤ (cfInner (f : M → ℂ) (f : M → ℂ)).re :=
  card_sub_card_div_card_mul_sq_le_cfInner_self_re hBK hKM hPsi hc hf hp he hpe hx hgK hgB hxg
    hΘ heΘ hmatch

end CFSG.FeitThompson
