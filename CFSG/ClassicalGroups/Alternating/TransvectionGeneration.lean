module

public import CFSG.ClassicalGroups.Alternating.PointRadicalCard
public import Mathlib.FieldTheory.Finite.Basic
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.ClassicalGroups.Alternating

open Module Submodule
open LinearMap (BilinForm)
open CFSG.LocalAnalysis.ComponentInitial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : BilinForm K V}

private theorem gl_ext'' {g h : LinearMap.GeneralLinearGroup K V}
    (H : ∀ x, (g : V →ₗ[K] V) x = (h : V →ₗ[K] V) x) : g = h :=
  Units.ext (LinearMap.ext H)

theorem symplecticTransvection_comm (hB : B.IsAlt) {a b : V} (hab : B a b = 0) (c d : K) :
    symplecticTransvection B hB a c * symplecticTransvection B hB b d =
      symplecticTransvection B hB b d * symplecticTransvection B hB a c := by
  have hba : B b a = 0 := by rw [← hB.neg_eq a b, hab, neg_zero]
  refine gl_ext'' fun x => ?_
  simp only [Units.val_mul, Module.End.mul_apply, symplecticTransvection_apply, map_add,
    map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hab, hba, mul_zero,
    zero_smul, add_zero]
  module

theorem siegel_smul_eq_mul (h2 : (2 : K) = 0) (hB : B.IsAlt) {e w : V} (hew : B e w = 0)
    (c : K) :
    siegel B hB e (c • w) c =
      symplecticTransvection B hB (e + w) c * symplecticTransvection B hB w c := by
  have hwe : B w e = 0 := by rw [← hB.neg_eq e w, hew, neg_zero]
  have hcw : B e (c • w) = 0 := by rw [map_smul, hew, smul_zero]
  have h2w : (2 : K) • w = 0 := by rw [h2, zero_smul]
  refine gl_ext'' fun x => ?_
  rw [siegel_apply hB hcw]
  simp only [Units.val_mul, Module.End.mul_apply, symplecticTransvection_apply, map_add,
    map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hew, hwe,
    hB.self_eq_zero, mul_zero, zero_smul, add_zero]
  linear_combination (norm := module) (-(c * B x w)) • h2w

theorem siegel_add_smul_self_of_two_eq_zero (h2 : (2 : K) = 0) (hB : B.IsAlt) {v w : V}
    (hvw : B v w = 0) (t c : K) : siegel B hB v (w + t • v) c = siegel B hB v w c := by
  rw [siegel_add_smul_self hB hvw, h2, zero_mul, add_zero]

theorem siegel_zero_right (hB : B.IsAlt) (u : V) (c : K) :
    siegel B hB u 0 c = symplecticTransvection B hB u c := by
  refine gl_ext'' fun x => ?_
  rw [siegel_apply hB (map_zero (B u)), symplecticTransvection_apply]
  simp


theorem exists_mem_apply_eq_of_restrict_nondegenerate {W : Submodule K V}
    (hW : (B.restrict W).Nondegenerate) {w : V} (hw : w ∈ W) (hw0 : w ≠ 0) (t : K) :
    ∃ w' ∈ W, B w w' = t := by
  obtain ⟨y, hy⟩ : ∃ y : W, B w y ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 (congrArg Subtype.val (hW.1 ⟨w, hw⟩ fun y => h y))
  refine ⟨(t / B w y) • (y : V), W.smul_mem _ y.2, ?_⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hy]

theorem exists_ne_zero_ne_one_of_two_lt_card (hq : 2 < Nat.card K) : ∃ s : K, s ≠ 0 ∧ s ≠ 1 := by
  classical
  by_contra h
  push Not at h
  have hinj : Function.Injective (fun s : K => decide (s = 0)) := by
    intro a b hab
    by_cases ha : a = 0
    · by_cases hb : b = 0
      · rw [ha, hb]
      · simp [ha, hb] at hab
    · by_cases hb : b = 0
      · simp [ha, hb] at hab
      · rw [h a ha, h b hb]
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  omega


theorem apply_add_add_of_orthogonal (hB : B.IsAlt) {e u u' : V} (hu : B e u = 0)
    (hu' : B e u' = 0) : B (e + u) (e + u') = B u u' := by
  have hue : B u e = 0 := by rw [← hB.neg_eq, hu, neg_zero]
  simp only [map_add, LinearMap.add_apply, hB.self_eq_zero, hu', hue, zero_add]

section Step

variable [FiniteDimensional K V] [Finite K] [CharP K 2]

theorem le_of_generation_step (hq : 2 < Nat.card K) (hB : B.IsAlt) (hBn : B.Nondegenerate)
    {e f : V} (hef : B e f = 1) (H : Subgroup (LinearMap.GeneralLinearGroup K V))
    (hHle : H ≤ bilinIsometryGroup B)
    (hW : ∀ a ∈ B.orthogonal (span K {e, f}), ∀ c : K, symplecticTransvection B hB a c ∈ H)
    (hT : ∀ w ∈ B.orthogonal (span K {e, f}), ∀ w' ∈ B.orthogonal (span K {e, f}), w ≠ 0 →
      w' ≠ 0 → ∃ g ∈ H, (g : V →ₗ[K] V) e = e ∧ (g : V →ₗ[K] V) w = w')
    {w₀ : V} (hw₀ : w₀ ∈ B.orthogonal (span K {e, f})) (hw₀ne : w₀ ≠ 0)
    (h1 : symplecticTransvection B hB (e + w₀) 1 ∈ H)
    (h3 : symplecticTransvection B hB f 1 ∈ H) :
    bilinIsometryGroup B ≤ H := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [map_zero, LinearMap.zero_apply] at hef
    exact zero_ne_one hef
  obtain ⟨-, hsplit⟩ := alternating_hyperbolic_splitting hB hBn he0
  obtain ⟨-, -, -, hcompl, hWnd, -⟩ := hsplit f hef
  set W := B.orthogonal (span K {e, f}) with hWdef
  have hmem : ∀ {x : V}, x ∈ W → B e x = 0 ∧ B f x = 0 := fun hx =>
    (LinearMap.BilinForm.mem_orthogonal_span_pair_iff B).mp hx
  have hS1 : ∀ w ∈ W, w ≠ 0 → symplecticTransvection B hB (e + w) 1 ∈ H := by
    intro w hw hw0
    obtain ⟨g, hgH, hge, hgw⟩ := hT w₀ hw₀ w hw hw₀ne hw0
    have hgiso := mem_bilinIsometryGroup.mp (hHle hgH)
    have := SteinbergBQ.symplecticTransvection_conj hB hgiso (e + w₀) 1
    rw [map_add, hge, hgw] at this
    rw [← this]
    exact mul_mem (mul_mem hgH h1) (inv_mem hgH)
  have hS2 : ∀ w ∈ W, w ≠ 0 → ∀ c : K, symplecticTransvection B hB (e + w) c ∈ H := by
    intro w'' hw'' hw''0 c
    by_cases hc0 : c = 0
    · rw [hc0, symplecticTransvection_zero]
      exact one_mem _
    by_cases hc1 : c = 1
    · rw [hc1]
      exact hS1 w'' hw'' hw''0
    obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) c
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact hc0 (by rw [hs]; ring)
    have hs1 : s ≠ 1 := by
      rintro rfl
      exact hc1 (by rw [hs]; ring)
    have h1s : (1 + s) ≠ 0 := fun h => hs1 (by linear_combination h - h2)
    obtain ⟨w', hw', hpair⟩ := exists_mem_apply_eq_of_restrict_nondegenerate hWnd hw'' hw''0
      ((1 + s) / s)
    have hw'0 : w' ≠ 0 := by
      rintro rfl
      rw [map_zero] at hpair
      exact div_ne_zero h1s hs0 hpair.symm
    have hBw : B w'' (s • w'' + (1 + s) • w') = (1 + s) ^ 2 / s := by
      rw [map_add, map_smul, map_smul, hB.self_eq_zero, hpair, smul_eq_mul, smul_eq_mul,
        mul_zero, zero_add]
      field_simp
    have hw : s • w'' + (1 + s) • w' ∈ W := W.add_mem (W.smul_mem _ hw'') (W.smul_mem _ hw')
    have hw0 : s • w'' + (1 + s) • w' ≠ 0 := by
      intro h
      rw [h, map_zero] at hBw
      exact div_ne_zero (pow_ne_zero 2 h1s) hs0 hBw.symm
    have hz := hS1 _ hw hw0
    have hy := hS1 w' hw' hw'0
    have hgiso := mem_bilinIsometryGroup.mp (hHle hy)
    have hconj := SteinbergBQ.symplecticTransvection_conj hB hgiso
      (e + (s • w'' + (1 + s) • w')) 1
    have hBzy : B (e + (s • w'' + (1 + s) • w')) (e + w') = 1 + s := by
      rw [apply_add_add_of_orthogonal hB (hmem hw).1 (hmem hw').1, map_add, LinearMap.add_apply,
        map_smul, LinearMap.smul_apply, map_smul, LinearMap.smul_apply, hB.self_eq_zero, hpair,
        smul_eq_mul, smul_eq_mul, mul_zero, add_zero]
      field_simp
    have he2 : (2 : K) • e = 0 := by rw [h2, zero_smul]
    have hw'2 : (2 : K) • w' = 0 := by rw [h2, zero_smul]
    have himg : (symplecticTransvection B hB (e + w') 1 : V →ₗ[K] V)
        (e + (s • w'' + (1 + s) • w')) = s • (e + w'') := by
      rw [symplecticTransvection_apply, hBzy]
      linear_combination (norm := module) (1 : K) • he2 + (1 + s) • hw'2
    rw [himg, SteinbergBQ.symplecticTransvection_smul hB] at hconj
    have hc : s ^ 2 * 1 = c := by rw [hs]; ring
    rw [hc] at hconj
    rw [← hconj]
    exact mul_mem (mul_mem hy hz) (inv_mem hy)
  have hsig : ∀ w ∈ W, w ≠ 0 → ∀ c : K, siegel B hB e (c • w) c ∈ H := by
    intro w hw hw0 c
    rw [siegel_smul_eq_mul h2 hB (hmem hw).1 c]
    exact mul_mem (hS2 w hw hw0 c) (hW w hw c)
  obtain ⟨s₀, hs₀0, hs₀1⟩ := exists_ne_zero_ne_one_of_two_lt_card hq
  have h1s₀ : (1 + s₀) ≠ 0 := fun h => hs₀1 (by linear_combination h - h2)
  have hA : ∀ u ∈ W, u ≠ 0 → ∀ t : K, siegel B hB e u t ∈ H := by
    intro u hu hu0 t
    obtain ⟨u₀, hu₀, hpair⟩ := exists_mem_apply_eq_of_restrict_nondegenerate hWnd hu hu0 1
    set w₂ : V := (-t) • u₀ + s₀ • u with hw₂
    set w₁ : V := u + w₂ with hw₁
    have hw₂W : w₂ ∈ W := W.add_mem (W.smul_mem _ hu₀) (W.smul_mem _ hu)
    have hw₁W : w₁ ∈ W := W.add_mem hu hw₂W
    have hBw₂ : B w₂ u = t := by
      rw [← hB.neg_eq u w₂, hw₂, map_add, map_smul, map_smul, hB.self_eq_zero, hpair]
      simp
    have hBw₁ : B w₁ u = t := by
      rw [hw₁, map_add, LinearMap.add_apply, hB.self_eq_zero, zero_add, hBw₂]
    have hw₂0 : w₂ ≠ 0 := by
      intro h
      rw [h, map_zero, LinearMap.zero_apply] at hBw₂
      rw [← hBw₂, neg_zero, zero_smul, zero_add] at hw₂
      exact hs₀0 ((smul_eq_zero.mp (hw₂ ▸ h)).resolve_right hu0)
    have hw₁0 : w₁ ≠ 0 := by
      intro h
      rw [h, map_zero, LinearMap.zero_apply] at hBw₁
      rw [hw₁, hw₂, ← hBw₁, neg_zero, zero_smul, zero_add] at h
      have : (1 + s₀) • u = 0 := by rw [add_smul, one_smul]; exact h
      exact h1s₀ ((smul_eq_zero.mp this).resolve_right hu0)
    have m₁ := hsig w₁ hw₁W hw₁0 1
    have m₂ := hsig w₂ hw₂W hw₂0 1
    rw [one_smul] at m₁ m₂
    have hprod := siegel_mul hB (hmem hw₁W).1 (hmem hw₂W).1 1 1
    have hsum : w₁ + w₂ = u := by
      have h2w : (2 : K) • w₂ = 0 := by rw [h2, zero_smul]
      rw [hw₁, add_assoc, ← two_smul K w₂, h2w, add_zero]
    have hval : (1 : K) + 1 + B w₂ w₁ = t := by
      rw [hw₁, map_add, hB.self_eq_zero, add_zero, hBw₂]
      linear_combination h2
    rw [hsum, hval] at hprod
    rw [← hprod]
    exact mul_mem m₁ m₂
  have hC : ∀ u ∈ W, ∀ t : K, siegel B hB e u t ∈ H := by
    intro u hu t
    by_cases hu0 : u = 0
    · rw [hu0]
      have hprod := siegel_mul hB (hmem hw₀).1 (hmem hw₀).1 0 t
      have h0 : w₀ + w₀ = 0 := by rw [← two_smul K w₀, h2, zero_smul]
      rw [h0, hB.self_eq_zero, zero_add, add_zero] at hprod
      rw [← hprod]
      exact mul_mem (hA w₀ hw₀ hw₀ne 0) (hA w₀ hw₀ hw₀ne t)
    · exact hA u hu hu0 t
  have hD : pointRadical B hB e ≤ H := by
    rintro _ ⟨w, c, hew, rfl⟩
    have hw : w ∈ span K {e, f} ⊔ W := by rw [hcompl.sup_eq_top]; trivial
    obtain ⟨p, hp, u, hu, hpu⟩ := Submodule.mem_sup.mp hw
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hp
    have hb : b = 0 := by
      rw [← hpu, map_add, map_add, map_smul, map_smul, hB.self_eq_zero, hef, (hmem hu).1] at hew
      simpa using hew
    have hwu : w = u + a • e := by
      rw [← hpu, hb, zero_smul, add_zero, add_comm]
    rw [hwu, siegel_add_smul_self_of_two_eq_zero h2 hB (hmem hu).1 a c]
    exact hC u hu c
  have hsf : siegel B hB f 0 1 ∈ H := by
    rw [siegel_zero_right]
    exact h3
  have hBfe : B f e ≠ 0 := by
    rw [← hB.neg_eq e f, hef]
    simp
  have hgen := pointRadical_sup_zpowers_siegel h2 hB hBn (u := f) (v := e) (w := 0) (c := 1)
    hBfe (map_zero _) one_ne_zero
  rw [← hgen]
  exact sup_le hD (Subgroup.zpowers_le.mpr hsf)


theorem exists_eq_smul_of_apply_eq_zero (hB : B.IsAlt)
    (hBn : B.Nondegenerate) (hdim : finrank K V = 2) {z w : V} (hz : z ≠ 0) (hzw : B z w = 0) :
    ∃ t : K, w = t • z := by
  obtain ⟨⟨b, hb⟩, hsplit⟩ := alternating_hyperbolic_splitting hB hBn hz
  obtain ⟨hspan, -⟩ := hsplit b hb
  have htop : span K {z, b} = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hspan, hdim])
  have hw : w ∈ span K {z, b} := by rw [htop]; trivial
  obtain ⟨a, c, hac⟩ := Submodule.mem_span_pair.mp hw
  have hc : c = 0 := by
    rw [← hac, map_add, map_smul, map_smul, hB.self_eq_zero, hb] at hzw
    simpa using hzw
  exact ⟨a, by rw [← hac, hc, zero_smul, add_zero]⟩

theorem exists_card_le_three_closure_eq
    (hq : 2 < Nat.card K) (hB : B.IsAlt) (hBn : B.Nondegenerate) (hdim : finrank K V = 2) :
    ∃ s : Finset V, (∀ x ∈ s, x ≠ 0) ∧ s.card ≤ 3 ∧
      Subgroup.closure ((fun x => symplecticTransvection B hB x 1) '' (s : Set V)) =
        bilinIsometryGroup B := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  haveI : Nontrivial V := Module.finrank_pos_iff.mp (show 0 < finrank K V by omega)
  obtain ⟨e, he⟩ := exists_ne (0 : V)
  obtain ⟨⟨f, hef⟩, -⟩ := alternating_hyperbolic_splitting hB hBn he
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [map_zero] at hef
    exact zero_ne_one hef
  have hfe : B f e = -1 := by rw [← hB.neg_eq e f, hef]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  set lam : K := (g : K) with hlam
  have hlam0 : lam ≠ 0 := g.ne_zero
  have hlam1 : lam ≠ 1 := by
    intro h1
    have hg1 : g = 1 := Units.ext h1
    obtain ⟨s, hs0, hs1⟩ := exists_ne_zero_ne_one_of_two_lt_card hq
    have := hg (Units.mk0 s hs0)
    rw [hg1, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at this
    exact hs1 (congrArg Units.val this)
  obtain ⟨β, hβ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (lam + lam⁻¹)
  have hβ' : β * β * lam = lam * lam + 1 := by
    rw [← hβ]
    field_simp
  have hβ0 : β ≠ 0 := by
    rintro rfl
    have h0 : lam * lam + 1 = 0 := by rw [← hβ']; ring
    have h00 : (lam + 1) * (lam + 1) = 0 := by linear_combination h0 + lam * h2
    have h01 : lam + 1 = 0 := mul_self_eq_zero.mp h00
    exact hlam1 (by linear_combination h01 - h2)
  set y : V := β • f with hy
  set z : V := (1 + lam) • e + (β * β) • f with hz
  have hy0 : y ≠ 0 := smul_ne_zero hβ0 hf0
  have hBez : B e z = β * β := by
    rw [hz, map_add, map_smul, map_smul, hB.self_eq_zero, hef]
    simp
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, map_zero] at hBez
    exact mul_ne_zero hβ0 hβ0 hBez.symm
  set a := symplecticTransvection B hB e 1 with ha
  set b := symplecticTransvection B hB y 1 with hb
  have haS : a ∈ bilinIsometryGroup B := symplecticTransvection_mem_bilinIsometryGroup hB e 1
  have hbS : b ∈ bilinIsometryGroup B := symplecticTransvection_mem_bilinIsometryGroup hB y 1
  have hgmS : a * b ∈ bilinIsometryGroup B := mul_mem haS hbS
  have hgmz : ((a * b : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) z = lam • z := by
    rw [Units.val_mul, Module.End.mul_apply, ha, hb, symplecticTransvection_apply,
      symplecticTransvection_apply]
    simp only [hy, hz, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hB.self_eq_zero, hef, hfe]
    match_scalars
    · linear_combination (-1 : K) * hβ' - (lam * lam + β * β) * h2
    · linear_combination (β * β) * h2
  have hpow : ∀ k : ℕ, (((a * b) ^ k : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) z =
      lam ^ k • z := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Units.val_mul, Module.End.mul_apply, ih, map_smul, hgmz, smul_smul,
        pow_succ]
  set H : Subgroup (LinearMap.GeneralLinearGroup K V) :=
    Subgroup.closure
      ((fun x => symplecticTransvection B hB x 1) '' (({e, y, z} : Finset V) : Set V)) with hH
  have hmemH : ∀ x ∈ ({e, y, z} : Finset V), symplecticTransvection B hB x 1 ∈ H :=
    fun x hx => Subgroup.subset_closure ⟨x, hx, rfl⟩
  have haH : a ∈ H := hmemH e (by simp)
  have hbH : b ∈ H := hmemH y (by simp)
  have hzH : symplecticTransvection B hB z 1 ∈ H := hmemH z (by simp)
  have hHle : H ≤ bilinIsometryGroup B := by
    rw [hH, Subgroup.closure_le]
    rintro _ ⟨x, -, rfl⟩
    exact symplecticTransvection_mem_bilinIsometryGroup hB x 1
  have hroot : ∀ c : K, symplecticTransvection B hB z c ∈ H := by
    intro c
    by_cases hc0 : c = 0
    · rw [hc0, symplecticTransvection_zero]
      exact one_mem _
    obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) c
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hc0 (by rw [hr]; ring)
    obtain ⟨k, hk⟩ : (Units.mk0 r hr0) ∈ Submonoid.powers g := by
      rw [mem_powers_iff_mem_zpowers]
      exact hg _
    have hrk : r = lam ^ k := by
      have := congrArg Units.val hk
      simpa [hlam] using this.symm
    have hconj := SteinbergBQ.symplecticTransvection_conj hB
      (mem_bilinIsometryGroup.mp (pow_mem hgmS k)) z 1
    rw [hpow k, SteinbergBQ.symplecticTransvection_smul hB] at hconj
    have hc : (lam ^ k) ^ 2 * 1 = c := by rw [hr, hrk]; ring
    rw [hc] at hconj
    rw [← hconj]
    have hgH : (a * b) ^ k ∈ H := pow_mem (mul_mem haH hbH) k
    exact mul_mem (mul_mem hgH hzH) (inv_mem hgH)
  have hrad : pointRadical B hB z ≤ H := by
    rintro _ ⟨w, c, hzw, rfl⟩
    obtain ⟨t, rfl⟩ := exists_eq_smul_of_apply_eq_zero hB hBn hdim hz0 hzw
    have := siegel_add_smul_self_of_two_eq_zero h2 hB (v := z) (w := 0) (map_zero (B z)) t c
    rw [zero_add, siegel_zero_right] at this
    rw [this]
    exact hroot c
  have hBez0 : B e z ≠ 0 := by
    rw [hBez]
    exact mul_ne_zero hβ0 hβ0
  have hgen := pointRadical_sup_zpowers_siegel h2 hB hBn (u := e) (v := z) (w := 0) (c := 1)
    hBez0 (map_zero _) one_ne_zero
  refine ⟨{e, y, z}, ?_, Finset.card_le_three, le_antisymm hHle ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · rw [← hgen]
    refine sup_le hrad (Subgroup.zpowers_le.mpr ?_)
    rw [siegel_zero_right]
    exact haH

end Step

section Extension

variable {H W : Submodule K V}

private noncomputable def extendEquiv' (h : IsCompl H W) (φ : W ≃ₗ[K] W) : V ≃ₗ[K] V :=
  (Submodule.prodEquivOfIsCompl H W h).symm ≪≫ₗ ((LinearEquiv.refl K H).prodCongr φ) ≪≫ₗ
    Submodule.prodEquivOfIsCompl H W h

private theorem extendEquiv'_apply_left (h : IsCompl H W) (φ : W ≃ₗ[K] W) {x : V}
    (hx : x ∈ H) : extendEquiv' h φ x = x := by
  rw [extendEquiv', LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    show x = ((⟨x, hx⟩ : H) : V) from rfl, Submodule.prodEquivOfIsCompl_symm_apply_left,
    LinearEquiv.prodCongr_apply, map_zero, LinearEquiv.refl_apply,
    Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, add_zero]

private theorem extendEquiv'_apply_right (h : IsCompl H W) (φ : W ≃ₗ[K] W) (w : W) :
    extendEquiv' h φ w = φ w := by
  rw [extendEquiv', LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    Submodule.prodEquivOfIsCompl_symm_apply_right, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, zero_add]

private noncomputable def extendGL' (h : IsCompl H W) :
    LinearMap.GeneralLinearGroup K W →* LinearMap.GeneralLinearGroup K V where
  toFun φ := LinearMap.GeneralLinearGroup.ofLinearEquiv (extendEquiv' h φ.toLinearEquiv)
  map_one' := Units.ext <| LinearMap.ext_on_codisjoint h.codisjoint
    (fun x hx => extendEquiv'_apply_left h _ hx)
    (fun x hx => extendEquiv'_apply_right h _ ⟨x, hx⟩)
  map_mul' φ ψ := Units.ext <| LinearMap.ext_on_codisjoint h.codisjoint
    (fun x hx => by
      change extendEquiv' h _ x = extendEquiv' h _ (extendEquiv' h _ x)
      rw [extendEquiv'_apply_left h _ hx, extendEquiv'_apply_left h _ hx,
        extendEquiv'_apply_left h _ hx])
    (fun x hx => by
      change extendEquiv' h _ ((⟨x, hx⟩ : W) : V) =
        extendEquiv' h _ (extendEquiv' h _ ((⟨x, hx⟩ : W) : V))
      rw [extendEquiv'_apply_right, extendEquiv'_apply_right, extendEquiv'_apply_right]
      rfl)

private theorem extendGL'_apply_left (h : IsCompl H W) (φ : LinearMap.GeneralLinearGroup K W)
    {x : V} (hx : x ∈ H) : (extendGL' h φ : V →ₗ[K] V) x = x :=
  extendEquiv'_apply_left h _ hx

private theorem extendGL'_apply_right (h : IsCompl H W) (φ : LinearMap.GeneralLinearGroup K W)
    (w : W) : (extendGL' h φ : V →ₗ[K] V) w = (φ : W →ₗ[K] W) w :=
  extendEquiv'_apply_right h _ w

private theorem extendGL'_symplecticTransvection (hB : B.IsAlt) (h : IsCompl H W)
    (hHW : ∀ x ∈ H, ∀ y ∈ W, B x y = 0) (w : W) (c : K) :
    extendGL' h (symplecticTransvection (B.restrict W) (isAlt_restrict hB W) w c) =
      symplecticTransvection B hB w c :=
  Units.ext <| LinearMap.ext_on_codisjoint h.codisjoint
    (fun x hx => by
      rw [extendGL'_apply_left h _ hx, symplecticTransvection_apply, hHW x hx w w.2, mul_zero,
        zero_smul, add_zero])
    (fun x hx => by
      change (extendGL' h _ : V →ₗ[K] V) ((⟨x, hx⟩ : W) : V) =
        (symplecticTransvection B hB w c : V →ₗ[K] V) x
      rw [extendGL'_apply_right, symplecticTransvection_apply, symplecticTransvection_apply]
      rfl)

end Extension

universe u v

private theorem exists_card_le_closure_eq_aux {K : Type u} [Field K] [Finite K] [CharP K 2]
    (hq : 2 < Nat.card K) (m : ℕ) :
    ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (B : BilinForm K V)
      (hB : B.IsAlt), B.Nondegenerate → finrank K V = m →
      ∃ s : Finset V, (∀ x ∈ s, x ≠ 0) ∧ s.card ≤ m + 1 ∧
        Subgroup.closure ((fun x => symplecticTransvection B hB x 1) '' (s : Set V)) =
          bilinIsometryGroup B := by
  classical
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro V _ _ _ B hB hBn hm
  rcases subsingleton_or_nontrivial V with hV | hV
  · refine ⟨∅, by simp, by simp, ?_⟩
    have h1 : ∀ g : LinearMap.GeneralLinearGroup K V, g = 1 := fun g =>
      Units.ext (LinearMap.ext fun x => Subsingleton.elim _ _)
    rw [Finset.coe_empty, Set.image_empty, Subgroup.closure_empty]
    ext g
    rw [h1 g]
    simp only [Subgroup.mem_bot]
    exact ⟨fun _ => one_mem _, fun _ => trivial⟩
  obtain ⟨e, he⟩ := exists_ne (0 : V)
  obtain ⟨⟨f, hef⟩, hsplit⟩ := alternating_hyperbolic_splitting hB hBn he
  obtain ⟨hspan, -, -, hcompl, hWnd, hWdim⟩ := hsplit f hef
  have hm2 : 2 ≤ m := by
    rw [← hm, ← hspan]
    exact Submodule.finrank_le _
  by_cases hm2' : m = 2
  · subst hm2'
    obtain ⟨s, hs0, hs, hsc⟩ := exists_card_le_three_closure_eq hq hB hBn hm
    exact ⟨s, hs0, hs, hsc⟩
  set W := B.orthogonal (span K {e, f}) with hWdef
  have hWm : finrank K W = m - 2 := by rw [hWdim, hm]
  obtain ⟨sW, hsW0, hsWc, hsWgen⟩ := ih (m - 2) (by omega) W (B.restrict W)
    (isAlt_restrict hB W) hWnd hWm
  have hHW : ∀ x ∈ span K {e, f}, ∀ y ∈ W, B x y = 0 := fun x hx y hy => hy x hx
  haveI : Nontrivial W := Module.finrank_pos_iff.mp (show 0 < finrank K W by omega)
  obtain ⟨w₀, hw₀ne⟩ := exists_ne (0 : W)
  have hw₀ : (w₀ : V) ∈ W := w₀.2
  have hw₀0 : (w₀ : V) ≠ 0 := fun h => hw₀ne (Subtype.ext h)
  let sW' : Finset V := sW.map ⟨Subtype.val, Subtype.val_injective⟩
  let s : Finset V := insert ((e + w₀ : V)) (insert f sW')
  have hmemS : ∀ x ∈ sW, ((x : W) : V) ∈ s := fun x hx =>
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨x, hx, rfl⟩))
  set H : Subgroup (LinearMap.GeneralLinearGroup K V) :=
    Subgroup.closure ((fun x => symplecticTransvection B hB x 1) '' (s : Set V)) with hH
  have hHle : H ≤ bilinIsometryGroup B := by
    rw [hH, Subgroup.closure_le]
    rintro _ ⟨x, -, rfl⟩
    exact symplecticTransvection_mem_bilinIsometryGroup hB x 1
  have hext : ∀ g ∈ bilinIsometryGroup (B.restrict W), extendGL' hcompl g ∈ H := by
    intro g hg
    rw [← hsWgen] at hg
    have hmap := Subgroup.mem_map_of_mem (extendGL' hcompl) hg
    rw [MonoidHom.map_closure] at hmap
    refine Subgroup.closure_mono ?_ hmap
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨((x : W) : V), hmemS x hx, (extendGL'_symplecticTransvection hB hcompl hHW x 1).symm⟩
  have hW : ∀ a ∈ W, ∀ c : K, symplecticTransvection B hB a c ∈ H := by
    intro a ha c
    have := hext _ (symplecticTransvection_mem_bilinIsometryGroup (isAlt_restrict hB W)
      (⟨a, ha⟩ : W) c)
    rwa [extendGL'_symplecticTransvection hB hcompl hHW] at this
  have hT : ∀ w ∈ W, ∀ w' ∈ W, w ≠ 0 → w' ≠ 0 →
      ∃ g ∈ H, (g : V →ₗ[K] V) e = e ∧ (g : V →ₗ[K] V) w = w' := by
    intro w hw w' hw' hw0 hw'0
    obtain ⟨g, hg, hgw⟩ := (alternating_transvection_vector_transitivity
      (isAlt_restrict hB W) hWnd).2 ⟨w, hw⟩ ⟨w', hw'⟩ (fun h => hw0 (congrArg Subtype.val h))
      (fun h => hw'0 (congrArg Subtype.val h))
    have hgS := closure_symplecticTransvection_le_bilinIsometryGroup (isAlt_restrict hB W) hg
    refine ⟨extendGL' hcompl g, hext g hgS, extendGL'_apply_left hcompl g
      (Submodule.subset_span (by simp)), ?_⟩
    rw [extendGL'_apply_right hcompl g ⟨w, hw⟩]
    exact congrArg Subtype.val hgw
  have h1 : symplecticTransvection B hB (e + (w₀ : V)) 1 ∈ H :=
    Subgroup.subset_closure ⟨_, Finset.mem_insert_self _ _, rfl⟩
  have h3 : symplecticTransvection B hB f 1 ∈ H :=
    Subgroup.subset_closure ⟨_, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), rfl⟩
  have hge := le_of_generation_step hq hB hBn hef H hHle hW hT hw₀ hw₀0 h1 h3
  refine ⟨s, ?_, ?_, le_antisymm hHle hge⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · intro h
      have hfw := ((LinearMap.BilinForm.mem_orthogonal_span_pair_iff B).mp hw₀).2
      have h0 : B f (e + (w₀ : V)) = 0 := by rw [h, map_zero]
      rw [map_add, hfw, add_zero, ← hB.neg_eq e f, hef] at h0
      simp at h0
    rcases Finset.mem_insert.mp hx with rfl | hx
    · intro h
      rw [h, map_zero] at hef
      exact zero_ne_one hef
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact fun h => hsW0 y hy (Subtype.ext h)
  · calc s.card ≤ (insert f sW').card + 1 := Finset.card_insert_le _ _
      _ ≤ sW'.card + 1 + 1 := by gcongr; exact Finset.card_insert_le _ _
      _ = sW.card + 2 := by rw [Finset.card_map]
      _ ≤ m + 1 := by omega

theorem exists_card_le_closure_symplecticTransvection_eq {K : Type u} {V : Type v} [Field K]
    [Finite K] [CharP K 2] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {B : BilinForm K V} (hq : 2 < Nat.card K) (hB : B.IsAlt) (hBn : B.Nondegenerate) :
    ∃ s : Finset V, (∀ x ∈ s, x ≠ 0) ∧ s.card ≤ finrank K V + 1 ∧
      Subgroup.closure ((fun x => symplecticTransvection B hB x 1) '' (s : Set V)) =
        bilinIsometryGroup B :=
  exists_card_le_closure_eq_aux hq _ V B hB hBn rfl

theorem exists_card_le_closure_conj_eq_top {K : Type u} {V : Type v} [Field K]
    [Finite K] [CharP K 2] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {B : BilinForm K V} (hq : 2 < Nat.card K) (hB : B.IsAlt) (hBn : B.Nondegenerate) {v : V}
    (hv : v ≠ 0) {c : K} (hc : c ≠ 0) :
    ∃ s : Finset (bilinIsometryGroup B), s.card ≤ finrank K V + 1 ∧
      Subgroup.closure ((fun g : bilinIsometryGroup B =>
        g * (⟨symplecticTransvection B hB v c,
          symplecticTransvection_mem_bilinIsometryGroup hB v c⟩ : bilinIsometryGroup B) * g⁻¹) ''
          (s : Set (bilinIsometryGroup B))) = ⊤ := by
  classical
  obtain ⟨s₀, hs₀0, hcard, hgen⟩ := exists_card_le_closure_symplecticTransvection_eq hq hB hBn
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) c
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hc (by rw [hr]; ring)
  have hmove : ∀ x ∈ s₀, ∃ g : bilinIsometryGroup B,
      ((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v = r⁻¹ • x := by
    intro x hx
    obtain ⟨g, hg, hgv⟩ := (alternating_transvection_vector_transitivity hB hBn).2 v (r⁻¹ • x) hv
      (smul_ne_zero (inv_ne_zero hr0) (hs₀0 x hx))
    exact ⟨⟨g, closure_symplecticTransvection_le_bilinIsometryGroup hB hg⟩, hgv⟩
  choose! G hG using hmove
  set a : bilinIsometryGroup B := ⟨symplecticTransvection B hB v c,
    symplecticTransvection_mem_bilinIsometryGroup hB v c⟩ with ha
  have hconj : ∀ x ∈ s₀, ((G x * a * (G x)⁻¹ : bilinIsometryGroup B) :
      LinearMap.GeneralLinearGroup K V) = symplecticTransvection B hB x 1 := by
    intro x hx
    have h1 := SteinbergBQ.symplecticTransvection_conj hB
      (mem_bilinIsometryGroup.mp (G x).2) v c
    rw [hG x hx, SteinbergBQ.symplecticTransvection_smul hB] at h1
    have hc1 : (r⁻¹) ^ 2 * c = 1 := by
      rw [hr]
      field_simp
    rw [hc1] at h1
    exact h1
  refine ⟨s₀.image G, (Finset.card_image_le).trans hcard, ?_⟩
  rw [eq_top_iff]
  intro g _
  have hle : Subgroup.closure ((fun x => symplecticTransvection B hB x 1) '' (s₀ : Set V)) ≤
      Subgroup.map (bilinIsometryGroup B).subtype
        (Subgroup.closure ((fun g : bilinIsometryGroup B => g * a * g⁻¹) ''
          ((s₀.image G : Finset (bilinIsometryGroup B)) : Set (bilinIsometryGroup B)))) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨G x * a * (G x)⁻¹, Subgroup.subset_closure
      ⟨G x, Finset.mem_coe.mpr (Finset.mem_image_of_mem G hx), rfl⟩, ?_⟩
    exact hconj x hx
  have hg : (g : LinearMap.GeneralLinearGroup K V) ∈
      Subgroup.closure ((fun x => symplecticTransvection B hB x 1) '' (s₀ : Set V)) := by
    rw [hgen]
    exact g.2
  obtain ⟨h, hh, hhg⟩ := hle hg
  have : h = g := Subtype.ext hhg
  rw [← this]
  exact hh

end CFSG.ClassicalGroups.Alternating
