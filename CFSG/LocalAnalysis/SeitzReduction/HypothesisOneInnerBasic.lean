module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneExceptionalBasic

public section

namespace CFSG.SeitzReduction

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem eq_one_of_odd_orderOf_of_isPGroup {A : Type*} [Group A] (hA : IsPGroup 2 A) {φ : A}
    (hφ : Odd (orderOf φ)) : φ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hA φ
  rcases k with _ | k
  · rwa [pow_zero, orderOf_eq_one_iff] at hk
  · exfalso
    rw [hk, pow_succ] at hφ
    exact Nat.not_even_iff_odd.2 hφ (even_two.mul_left _)

theorem mem_centralizer_of_odd_orderOf_of_forall {X : Type*} [Group X] {B : Subgroup X}
    [B.Normal] (hB : ∀ φ : MulAut B, Odd (orderOf φ) → φ = 1) {g : X}
    (hg : Odd (orderOf g)) : g ∈ centralizer (B : Set X) := by
  have hφ : (MulAut.conjNormal (H := B) g) = 1 := hB _ (hg.of_dvd_nat (orderOf_map_dvd _ g))
  rw [mem_centralizer_iff]
  intro b hb
  have h : g * b * g⁻¹ = b := by
    have := congrArg (fun φ : MulAut B => ((φ ⟨b, hb⟩ : B) : X)) hφ
    simpa only [MulAut.conjNormal_apply, MulAut.one_apply] using this
  calc b * g = g * b * g⁻¹ * g := by rw [h]
    _ = g * b := by group

theorem mem_centralizer_of_odd_orderOf {X : Type*} [Group X] {B : Subgroup X} [B.Normal]
    (hB : IsPGroup 2 (MulAut B)) {g : X} (hg : Odd (orderOf g)) :
    g ∈ centralizer (B : Set X) :=
  mem_centralizer_of_odd_orderOf_of_forall (fun _ hφ => eq_one_of_odd_orderOf_of_isPGroup hB hφ) hg

theorem closure_odd_orderOf_le_centralizer {X : Type*} [Group X] {B : Subgroup X} [B.Normal]
    (hB : IsPGroup 2 (MulAut B)) : closure {g : X | Odd (orderOf g)} ≤ centralizer (B : Set X) :=
  (closure_le _).2 fun _ hg => mem_centralizer_of_odd_orderOf hB hg

theorem le_centralizer_closure_odd_orderOf {X : Type*} [Group X] {B : Subgroup X} [B.Normal]
    (hB : IsPGroup 2 (MulAut B)) : B ≤ centralizer (closure {g : X | Odd (orderOf g)} : Set X) :=
  le_centralizer_iff.2 (closure_odd_orderOf_le_centralizer hB)

theorem zmodFour_eq_pow (w : Multiplicative (ZMod 4)) :
    w = Multiplicative.ofAdd (1 : ZMod 4) ^ (Multiplicative.toAdd w).val := by
  revert w
  decide

theorem pow_two_eq_one_mulAut_zmodFour (φ : MulAut (Multiplicative (ZMod 4))) : φ ^ 2 = 1 := by
  have hφ : ∀ w, φ w = φ (Multiplicative.ofAdd 1) ^ (Multiplicative.toAdd w).val := fun w => by
    conv_lhs => rw [zmodFour_eq_pow w]
    rw [map_pow]
  have hy : φ (Multiplicative.ofAdd 1) ^ 2 ≠ 1 := by
    intro h
    have h' : φ (Multiplicative.ofAdd (1 : ZMod 4) ^ 2) = φ 1 := by rw [map_pow, h, map_one]
    exact absurd (φ.injective h') (by decide)
  have hsq : ∀ y : Multiplicative (ZMod 4), y ^ 2 ≠ 1 →
      y ^ (Multiplicative.toAdd y).val = Multiplicative.ofAdd 1 := by decide
  refine MulEquiv.ext fun w => ?_
  rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
  conv_rhs => rw [zmodFour_eq_pow w]
  rw [hφ w, map_pow, hφ (φ (Multiplicative.ofAdd 1)), hsq _ hy]

theorem isPGroup_two_mulAut_zmodFour : IsPGroup 2 (MulAut (Multiplicative (ZMod 4))) :=
  fun φ => ⟨1, by rw [pow_one]; exact pow_two_eq_one_mulAut_zmodFour φ⟩

theorem zmodTwoProdFour_eq_mul_pow (w : Multiplicative (ZMod 2) × Multiplicative (ZMod 4)) :
    w = (Multiplicative.ofAdd (1 : ZMod 2), (1 : Multiplicative (ZMod 4))) ^
        (Multiplicative.toAdd w.1).val *
      ((1 : Multiplicative (ZMod 2)), Multiplicative.ofAdd (1 : ZMod 4)) ^
        (Multiplicative.toAdd w.2).val := by
  revert w
  decide

theorem map_zmodTwoProdFour {M F : Type*} [Monoid M]
    [FunLike F (Multiplicative (ZMod 2) × Multiplicative (ZMod 4)) M]
    [MonoidHomClass F (Multiplicative (ZMod 2) × Multiplicative (ZMod 4)) M] (ψ : F)
    (w : Multiplicative (ZMod 2) × Multiplicative (ZMod 4)) :
    ψ w = ψ (Multiplicative.ofAdd (1 : ZMod 2), 1) ^ (Multiplicative.toAdd w.1).val *
      ψ (1, Multiplicative.ofAdd (1 : ZMod 4)) ^ (Multiplicative.toAdd w.2).val := by
  conv_lhs => rw [zmodTwoProdFour_eq_mul_pow w]
  rw [map_mul, map_pow, map_pow]

theorem pow_four_eq_one_mulAut_zmodTwoProdFour
    (φ : MulAut (Multiplicative (ZMod 2) × Multiplicative (ZMod 4))) : φ ^ 4 = 1 := by
  have hC : ∀ y : Multiplicative (ZMod 2) × Multiplicative (ZMod 4), y ^ 2 ≠ 1 →
      y ^ 2 = ((1 : Multiplicative (ZMod 2)), Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 := by
    decide
  have hD : ∀ x : Multiplicative (ZMod 2) × Multiplicative (ZMod 4), x ^ 2 = 1 → x ≠ 1 →
      x ≠ ((1 : Multiplicative (ZMod 2)), Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 →
      x = (Multiplicative.ofAdd (1 : ZMod 2), (1 : Multiplicative (ZMod 4))) ∨
        x = (Multiplicative.ofAdd (1 : ZMod 2), (1 : Multiplicative (ZMod 4))) *
          ((1 : Multiplicative (ZMod 2)), Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 := by
    decide
  have hE : ∀ z : Multiplicative (ZMod 2) × Multiplicative (ZMod 4), z ^ 2 ≠ 1 →
      (Multiplicative.ofAdd (1 : ZMod 2), (1 : Multiplicative (ZMod 4))) ^
          (Multiplicative.toAdd z.1).val * z ^ (Multiplicative.toAdd z.2).val =
        ((1 : Multiplicative (ZMod 2)), Multiplicative.ofAdd (1 : ZMod 4)) := by
    decide
  have hab : (Multiplicative.ofAdd (1 : ZMod 2), (1 : Multiplicative (ZMod 4))) *
      ((1 : Multiplicative (ZMod 2)), Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 *
      ((1 : Multiplicative (ZMod 2)), Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 =
      (Multiplicative.ofAdd (1 : ZMod 2), (1 : Multiplicative (ZMod 4))) := by decide
  set a : Multiplicative (ZMod 2) × Multiplicative (ZMod 4) :=
    (Multiplicative.ofAdd (1 : ZMod 2), (1 : Multiplicative (ZMod 4))) with ha
  set b : Multiplicative (ZMod 2) × Multiplicative (ZMod 4) :=
    ((1 : Multiplicative (ZMod 2)), Multiplicative.ofAdd (1 : ZMod 4)) with hb
  have ha1 : a ≠ 1 := by rw [ha]; decide
  have ha2 : a ^ 2 = 1 := by rw [ha]; decide
  have hab2 : a ≠ b ^ 2 := by rw [ha, hb]; decide
  have hb2 : b ^ 2 ≠ 1 := by rw [hb]; decide
  have hsq : ∀ (θ : MulAut (Multiplicative (ZMod 2) × Multiplicative (ZMod 4))) y, y ^ 2 ≠ 1 →
      θ y ^ 2 ≠ 1 := fun θ y hy h => hy (θ.injective (by rw [map_pow, h, map_one]))
  have hφb2 : φ (b ^ 2) = b ^ 2 := by rw [map_pow]; exact hC _ (hsq φ b hb2)
  have hφφa : φ (φ a) = a := by
    have hx2 : φ a ^ 2 = 1 := by rw [← map_pow, ha2, map_one]
    have hx1 : φ a ≠ 1 := fun h => ha1 (φ.injective (by rw [h, map_one]))
    have hxb : φ a ≠ b ^ 2 := fun h => hab2 (φ.injective (by rw [h, hφb2]))
    rcases hD _ hx2 hx1 hxb with h | h
    · rw [h, h]
    · rw [h, map_mul, h, hφb2]
      exact hab
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = φ * φ := ⟨_, rfl⟩
  have hψa : ψ a = a := by rw [hψ, MulAut.mul_apply]; exact hφφa
  have hψψb : ψ (ψ b) = b := by
    rw [map_zmodTwoProdFour ψ (ψ b), hψa]
    exact hE _ (hsq ψ b hb2)
  refine MulEquiv.ext fun w => ?_
  have h4 : φ ^ 4 = ψ * ψ := by rw [hψ, ← sq, ← sq, ← pow_mul]
  rw [h4, MulAut.one_apply, map_zmodTwoProdFour (ψ * ψ) w, MulAut.mul_apply, MulAut.mul_apply,
    hψa, hψa, hψψb]
  exact (zmodTwoProdFour_eq_mul_pow w).symm

theorem isPGroup_two_mulAut_zmodTwoProdFour :
    IsPGroup 2 (MulAut (Multiplicative (ZMod 2) × Multiplicative (ZMod 4))) :=
  fun φ => ⟨2, by rw [show 2 ^ 2 = 4 by norm_num]; exact pow_four_eq_one_mulAut_zmodTwoProdFour φ⟩

theorem isPGroup_two_mulAut_of_Z4_or_Z2xZ4 {B : Type*} [Group B]
    (hiso : Nonempty (B ≃* Multiplicative (ZMod 4)) ∨
      Nonempty (B ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 4))) :
    IsPGroup 2 (MulAut B) := by
  rcases hiso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact isPGroup_two_mulAut_zmodFour.of_equiv (MulAut.congr e).symm
  · exact isPGroup_two_mulAut_zmodTwoProdFour.of_equiv (MulAut.congr e).symm

theorem exists_orderOf_eq_four_of_Z4_or_Z2xZ4 {B : Type*} [Group B]
    (hiso : Nonempty (B ≃* Multiplicative (ZMod 4)) ∨
      Nonempty (B ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 4))) :
    ∃ b : B, orderOf b = 4 := by
  rcases hiso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · refine ⟨e.symm (Multiplicative.ofAdd 1), ?_⟩
    rw [MulEquiv.orderOf_eq]
    exact (orderOf_eq_iff (by norm_num)).2 (by decide)
  · refine ⟨e.symm (1, Multiplicative.ofAdd 1), ?_⟩
    rw [MulEquiv.orderOf_eq]
    exact (orderOf_eq_iff (by norm_num)).2 (by decide)

theorem mem_centralizer_of_odd_orderOf_of_Z4_or_Z2xZ4 {X : Type*} [Group X] {B : Subgroup X}
    (hB : B.Normal) (hiso : Nonempty (B ≃* Multiplicative (ZMod 4)) ∨
      Nonempty (B ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 4))) {g : X}
    (hg : Odd (orderOf g)) : g ∈ centralizer (B : Set X) :=
  mem_centralizer_of_odd_orderOf (isPGroup_two_mulAut_of_Z4_or_Z2xZ4 hiso) hg

theorem noNormalZ4OrZ2xZ4_of_forall_commute {X : Type*} [Group X] {S : Set X}
    (hS : ∀ s ∈ S, Odd (orderOf s))
    (h : ∀ β : X, (∀ s ∈ S, β * s = s * β) → orderOf β ≠ 4) : NoNormalZ4OrZ2xZ4 X := by
  intro B hB hiso
  obtain ⟨b, hb⟩ := exists_orderOf_eq_four_of_Z4_or_Z2xZ4 hiso
  refine h b (fun s hs => ?_) ((Subgroup.orderOf_coe b).trans hb)
  exact mem_centralizer_iff.1 (mem_centralizer_of_odd_orderOf_of_Z4_or_Z2xZ4 hB hiso (hS s hs)) b
    b.2

@[expose] def InnerCentralizerCriterion {C : Type*} [Group C] (t : C) : Prop :=
  ∀ β : MulAut C, β * MulAut.conj t = MulAut.conj t * β →
    (∀ c : C, c * t = t * c → Odd (orderOf c) → β * MulAut.conj c = MulAut.conj c * β) →
    orderOf β ≠ 4

theorem noNormalZ4OrZ2xZ4_inf_centralizer_conj {C : Type*} [Group C] {t : C}
    (h : InnerCentralizerCriterion t) {H : Subgroup (MulAut C)} (hH : inner C ≤ H) :
    NoNormalZ4OrZ2xZ4 ↥(H ⊓ centralizer ({MulAut.conj t} : Set (MulAut C))) := by
  have hmem : ∀ c : C, c * t = t * c →
      MulAut.conj c ∈ H ⊓ centralizer ({MulAut.conj t} : Set (MulAut C)) := fun c hc =>
    mem_inf.2 ⟨hH ⟨c, rfl⟩, mem_centralizer_singleton_iff.2 (by rw [← map_mul, ← map_mul, hc])⟩
  refine noNormalZ4OrZ2xZ4_of_forall_commute
    (S := {x | ∃ c : C, c * t = t * c ∧ Odd (orderOf c) ∧ (x : MulAut C) = MulAut.conj c}) ?_ ?_
  · rintro x ⟨c, -, hc, hx⟩
    rw [← Subgroup.orderOf_coe, hx]
    exact hc.of_dvd_nat (orderOf_map_dvd _ c)
  · intro β hβ
    rw [← Subgroup.orderOf_coe]
    refine h β (mem_centralizer_singleton_iff.1 (mem_inf.1 β.2).2) fun c hct hc => ?_
    exact congrArg Subtype.val (hβ ⟨MulAut.conj c, hmem c hct⟩ ⟨c, hct, hc, rfl⟩)

theorem mul_conj_mul_inv_eq_conj {C : Type*} [Group C] (ψ : MulAut C) (c : C) :
    ψ * MulAut.conj c * ψ⁻¹ = MulAut.conj (ψ c) := by
  ext x
  simp [MulAut.conj_apply]

theorem InnerCentralizerCriterion.map {C : Type*} [Group C] {t : C}
    (h : InnerCentralizerCriterion t) (ψ : MulAut C) : InnerCentralizerCriterion (ψ t) := by
  intro β hβt hβc hβ4
  have hconj : ∀ c : C, ψ⁻¹ * β * ψ * MulAut.conj c = MulAut.conj c * (ψ⁻¹ * β * ψ) ↔
      β * MulAut.conj (ψ c) = MulAut.conj (ψ c) * β := by
    intro c
    rw [← mul_conj_mul_inv_eq_conj]
    constructor
    · intro hc
      calc β * (ψ * MulAut.conj c * ψ⁻¹) = ψ * (ψ⁻¹ * β * ψ * MulAut.conj c) * ψ⁻¹ := by group
        _ = ψ * (MulAut.conj c * (ψ⁻¹ * β * ψ)) * ψ⁻¹ := by rw [hc]
        _ = ψ * MulAut.conj c * ψ⁻¹ * β := by group
    · intro hc
      calc ψ⁻¹ * β * ψ * MulAut.conj c = ψ⁻¹ * (β * (ψ * MulAut.conj c * ψ⁻¹)) * ψ := by group
        _ = ψ⁻¹ * ((ψ * MulAut.conj c * ψ⁻¹) * β) * ψ := by rw [hc]
        _ = MulAut.conj c * (ψ⁻¹ * β * ψ) := by group
  refine h (ψ⁻¹ * β * ψ) ((hconj t).2 hβt) (fun c hct hc => (hconj c).2 (hβc (ψ c) ?_ ?_)) ?_
  · rw [← map_mul, ← map_mul, hct]
  · rwa [MulEquiv.orderOf_eq]
  · rw [show ψ⁻¹ * β * ψ = MulAut.conj ψ⁻¹ β by rw [MulAut.conj_apply, inv_inv],
      MulEquiv.orderOf_eq, hβ4]

theorem innerCentralizerCriterion_of_fix {C : Type*} [Group C]
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {t : C}
    (h : ∀ β : MulAut C, β t = t → (∀ c : C, c * t = t * c → Odd (orderOf c) → β c = c) →
      β ^ 2 = 1) : InnerCentralizerCriterion t := by
  intro β hβt hβc hβ4
  have hfix : ∀ c : C, β * MulAut.conj c = MulAut.conj c * β → β c = c := fun c hc =>
    hinj (by rw [← mul_conj_mul_inv_eq_conj, hc, mul_inv_cancel_right])
  have hdvd : orderOf β ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (h β (hfix t hβt) fun c hct hc => hfix c (hβc c hct hc))
  rw [hβ4] at hdvd
  exact absurd hdvd (by norm_num)

theorem innerCentralizerCriterion_of_pointwise {C : Type*} [Group C]
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {t : C} {V : Subgroup C}
    (hodd : V ≤ closure {c : C | c * t = t * c ∧ Odd (orderOf c)})
    (hpt : ∀ β : MulAut C, (∀ v ∈ V, β v = v) → ∃ z : C, MulAut.conj z = β ∧
      ((∀ c : C, c * t = t * c → Odd (orderOf c) → z * c = c * z) → z ^ 2 = 1)) :
    InnerCentralizerCriterion t := by
  refine innerCentralizerCriterion_of_fix hinj fun β _ hβc => ?_
  have hfixC : ∀ x ∈ closure {c : C | c * t = t * c ∧ Odd (orderOf c)}, β x = x := by
    intro x hx
    induction hx using closure_induction with
    | mem c hc => exact hβc c hc.1 hc.2
    | one => exact map_one β
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
    | inv x _ hx => rw [map_inv, hx]
  obtain ⟨z, rfl, hz⟩ := hpt β fun v hv => hfixC v (hodd hv)
  have hz2 : z ^ 2 = 1 := hz fun c hct hc => by
    have h := hβc c hct hc
    rw [MulAut.conj_apply] at h
    calc z * c = z * c * z⁻¹ * z := by group
      _ = c * z := by rw [h]
  rw [← map_pow, hz2, map_one]

theorem innerInvolution_noNormalZ4OrZ2xZ4_of_forall {C : Type*} [Group C]
    (h : ∀ t : C, orderOf (MulAut.conj t) = 2 → InnerCentralizerCriterion t) :
    ∀ H : Subgroup (MulAut C), inner C ≤ H → ∀ α ∈ inner C, orderOf α = 2 →
      NoNormalZ4OrZ2xZ4 ↥(H ⊓ centralizer ({α} : Set (MulAut C))) := by
  rintro H hH _ ⟨t, rfl⟩ hα
  exact noNormalZ4OrZ2xZ4_inf_centralizer_conj (h t hα) hH

theorem innerInvolution_noNormalZ4OrZ2xZ4_of_representatives {C : Type*} [Group C] {T : Set C}
    (hT : ∀ s ∈ T, InnerCentralizerCriterion s)
    (hrep : ∀ t : C, orderOf (MulAut.conj t) = 2 → ∃ ψ : MulAut C, ∃ s ∈ T, ψ s = t) :
    ∀ H : Subgroup (MulAut C), inner C ≤ H → ∀ α ∈ inner C, orderOf α = 2 →
      NoNormalZ4OrZ2xZ4 ↥(H ⊓ centralizer ({α} : Set (MulAut C))) :=
  innerInvolution_noNormalZ4OrZ2xZ4_of_forall fun t ht => by
    obtain ⟨ψ, s, hs, rfl⟩ := hrep t ht
    exact (hT s hs).map ψ

end CFSG.SeitzReduction
