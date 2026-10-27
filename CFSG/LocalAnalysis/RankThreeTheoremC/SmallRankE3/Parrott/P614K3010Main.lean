module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K3010Real
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K3010Core

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open Subgroup

namespace P614K3010

theorem exists_inverting_of_surjective {A : Type} [Group A] {W K : Subgroup A} {X : Type*}
    [Group X] (hreal : ∀ g : X, orderOf g = 3 → ∃ h, h * g * h⁻¹ = g⁻¹) (f : ↥K →* X)
    (hfs : Function.Surjective f) (hfk : ∀ k : ↥K, f k = 1 → ∀ w ∈ W, (k : A) * w = w * k)
    {y : A} (hy : y ∈ K) (hy3 : orderOf y = 3) {w₀ : A} (hw₀ : w₀ ∈ W)
    (hyw₀ : y * w₀ ≠ w₀ * y) :
    ∃ k ∈ K, ∀ w ∈ W, k⁻¹ * y * k * y * w = w * (k⁻¹ * y * k * y) := by
  set y' : ↥K := ⟨y, hy⟩ with hy'
  have hfy1 : f y' ≠ 1 := fun h => hyw₀ (hfk y' h w₀ hw₀)
  have hfy3 : orderOf (f y') = 3 := by
    have hdvd : orderOf (f y') ∣ 3 := by
      have := orderOf_map_dvd f y'
      rwa [hy', Subgroup.orderOf_mk, hy3] at this
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hfy1
    · exact h
  obtain ⟨h, hh⟩ := hreal (f y') hfy3
  obtain ⟨k, hk⟩ := hfs h⁻¹
  refine ⟨k, k.2, fun w hw => ?_⟩
  have h1 : f (k⁻¹ * y' * k * y') = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, hk, inv_inv, hh, inv_mul_cancel]
  exact hfk _ h1 w hw

@[expose] def conjAdd {A : Type} [Group A] (W : Subgroup A) {a : A}
    (ha : a ∈ normalizer (W : Set A)) : Additive ↥W →+ Additive ↥W where
  toFun x := Additive.ofMul ⟨a * (Additive.toMul x).1 * a⁻¹,
    (mem_normalizer_iff.1 ha _).1 (Additive.toMul x).2⟩
  map_zero' := by
    apply Additive.toMul.injective
    apply Subtype.ext
    simp
  map_add' x x' := by
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [toMul_ofMul, toMul_add, Subgroup.coe_mul]
    group

theorem conjAdd_ofMul {A : Type} [Group A] (W : Subgroup A) {a : A}
    (ha : a ∈ normalizer (W : Set A)) {w : A} (hw : w ∈ W) :
    conjAdd W ha (Additive.ofMul ⟨w, hw⟩) =
      Additive.ofMul ⟨a * w * a⁻¹, (mem_normalizer_iff.1 ha w).1 hw⟩ := rfl

theorem ofMul_mk_eq_iff {A : Type} [Group A] {W : Subgroup A} {u u' : A} (hu : u ∈ W)
    (hu' : u' ∈ W) : Additive.ofMul (⟨u, hu⟩ : ↥W) = Additive.ofMul ⟨u', hu'⟩ ↔ u = u' := by
  simp

end P614K3010

open P614K3010 in
open scoped IsMulCommutative in
theorem kFact3010_holds : KFact3010 := by
  intro A _ _ W K y b hW hKW hf hirr hy hy3 hidx hb hcomm
  by_contra hcon
  push Not at hcon
  obtain ⟨w₁, hw₁, hbw₁⟩ := hcon
  have hU : K ≤ normalizer ((W ⊓ centralizer {b} : Subgroup A) : Set A) := by
    intro k hk
    have hkW := hKW hk
    rw [mem_normalizer_iff]
    intro h
    simp only [SetLike.mem_coe, mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hhW, hhb⟩
      refine ⟨(mem_normalizer_iff.1 hkW h).1 hhW, ?_⟩
      have e1 : b * h * b⁻¹ = h := by rw [← hhb, mul_inv_cancel_right]
      have e2 := hcomm k hk h hhW
      rw [e1] at e2
      exact (mul_inv_eq_iff_eq_mul.1 e2).symm
    · rintro ⟨hhW, hhb⟩
      have hhW' : h ∈ W := (mem_normalizer_iff.1 hkW h).2 hhW
      refine ⟨hhW', ?_⟩
      have e1 : b * (k * h * k⁻¹) * b⁻¹ = k * h * k⁻¹ := by rw [← hhb, mul_inv_cancel_right]
      have e2 := hcomm k hk h hhW'
      rw [e1] at e2
      have e3 : b * h * b⁻¹ = h := by
        have := congrArg (fun z => k⁻¹ * z * k) e2
        simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at this
        rw [← mul_assoc] at this
        exact this.symm
      exact (mul_inv_eq_iff_eq_mul.1 e3).symm
  have hfix : ∀ w ∈ W, b * w * b⁻¹ = w → w = 1 := by
    rcases hirr _ inf_le_left hU with hbot | htop
    · intro w hw hbw
      have hmem : w ∈ W ⊓ centralizer {b} :=
        ⟨hw, mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 hbw).symm⟩
      rw [hbot] at hmem
      exact hmem
    · exfalso
      have hmem : w₁ ∈ W ⊓ centralizer {b} := by
        rw [htop]
        exact hw₁
      exact hbw₁ (mem_centralizer_singleton_iff.1 hmem.2).symm
  obtain ⟨w₀, hw₀, hyw₀⟩ : ∃ w₀ ∈ W, y * w₀ ≠ w₀ * y := by
    by_contra h
    push Not at h
    have hle : W ≤ centralizer {y} := fun w hw =>
      mem_centralizer_singleton_iff.2 (h w hw).symm
    rw [relIndex_eq_one.2 hle] at hidx
    norm_num at hidx
  obtain ⟨k, hk, hkc⟩ : ∃ k ∈ K, ∀ w ∈ W, k⁻¹ * y * k * y * w = w * (k⁻¹ * y * k * y) := by
    rcases hf with ⟨f, hfs, hfk⟩ | ⟨f, hfs, hfk⟩
    · exact exists_inverting_of_surjective (fun g hg => alternatingGroup_five_exists_conj_eq_inv hg)
        f hfs hfk hy hy3 hw₀ hyw₀
    · exact exists_inverting_of_surjective (fun g hg => GL_three_two_exists_conj_eq_inv hg)
        f hfs hfk hy hy3 hw₀ hyw₀
  haveI : IsMulCommutative ↥W := hW.1
  have hyN := hKW hy
  have hkN := hKW hk
  set Y := conjAdd W hyN with hY
  set Φ := conjAdd W hb with hΦ
  set κ := conjAdd W hkN with hκ
  have hy3' : y ^ 3 = 1 := hy3 ▸ pow_orderOf_eq_one y
  have h2 : ∀ x : Additive ↥W, x + x = 0 := by
    intro x
    obtain ⟨⟨w, hw⟩, rfl⟩ := Additive.ofMul.surjective x
    rw [← ofMul_mul, ← ofMul_one]
    congr 1
    exact Subtype.ext ((pow_two w).symm.trans (hW.2 w hw))
  have hY3 : ∀ x, Y (Y (Y x)) = x := by
    intro x
    obtain ⟨⟨w, hw⟩, rfl⟩ := Additive.ofMul.surjective x
    simp only [hY, conjAdd_ofMul, ofMul_mk_eq_iff]
    calc y * (y * (y * w * y⁻¹) * y⁻¹) * y⁻¹ = y ^ 3 * w * (y ^ 3)⁻¹ := by
          simp only [pow_three, mul_inv_rev, mul_assoc]
      _ = w := by rw [hy3', one_mul, inv_one, mul_one]
  have hinj : ∀ {a : A} (ha : a ∈ normalizer (W : Set A)), Function.Injective (conjAdd W ha) := by
    intro a ha x x'
    obtain ⟨⟨w, hw⟩, rfl⟩ := Additive.ofMul.surjective x
    obtain ⟨⟨w', hw'⟩, rfl⟩ := Additive.ofMul.surjective x'
    simp only [conjAdd_ofMul, ofMul_mk_eq_iff]
    intro h
    simpa using h
  have hΦfp : ∀ x, Φ x = x → x = 0 := by
    intro x
    obtain ⟨⟨w, hw⟩, rfl⟩ := Additive.ofMul.surjective x
    simp only [hΦ, conjAdd_ofMul, ofMul_mk_eq_iff]
    intro h
    obtain rfl := hfix w hw h
    rfl
  have hYΦ : ∀ x, Y (Φ x) = Φ (Y x) := by
    intro x
    obtain ⟨⟨w, hw⟩, rfl⟩ := Additive.ofMul.surjective x
    simp only [hY, hΦ, conjAdd_ofMul, ofMul_mk_eq_iff]
    exact (hcomm y hy w hw).symm
  have hκΦ : ∀ x, κ (Φ x) = Φ (κ x) := by
    intro x
    obtain ⟨⟨w, hw⟩, rfl⟩ := Additive.ofMul.surjective x
    simp only [hκ, hΦ, conjAdd_ofMul, ofMul_mk_eq_iff]
    exact (hcomm k hk w hw).symm
  have hκY : ∀ x, Y (κ (Y x)) = κ x := by
    intro x
    obtain ⟨⟨w, hw⟩, rfl⟩ := Additive.ofMul.surjective x
    simp only [hY, hκ, conjAdd_ofMul, ofMul_mk_eq_iff]
    calc y * (k * (y * w * y⁻¹) * k⁻¹) * y⁻¹
        = k * (k⁻¹ * y * k * y * w) * (k⁻¹ * y * k * y)⁻¹ * k⁻¹ := by group
      _ = k * (w * (k⁻¹ * y * k * y)) * (k⁻¹ * y * k * y)⁻¹ * k⁻¹ := by rw [hkc w hw]
      _ = k * w * k⁻¹ := by group
  have hcard : Nat.card (Additive ↥W) = 4 * Nat.card {x : Additive ↥W // Y x = x} := by
    have e : {x : Additive ↥W // Y x = x} ≃ ↥((centralizer {y}).subgroupOf W) :=
      Equiv.subtypeEquiv Additive.toMul fun x => by
        obtain ⟨⟨w, hw⟩, rfl⟩ := Additive.ofMul.surjective x
        simp only [hY, conjAdd_ofMul, ofMul_mk_eq_iff, toMul_ofMul, mem_subgroupOf,
          mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
        exact eq_comm
    rw [Nat.card_congr e, Nat.card_congr (Additive.toMul : Additive ↥W ≃ ↥W),
      ← card_mul_index ((centralizer {y}).subgroupOf W)]
    change Nat.card _ * (centralizer {y}).relIndex W = _
    rw [hidx, mul_comm]
  have hx₀ : Y (Additive.ofMul ⟨w₀, hw₀⟩) ≠ Additive.ofMul ⟨w₀, hw₀⟩ := by
    intro h
    simp only [hY, conjAdd_ofMul, ofMul_mk_eq_iff] at h
    exact hyw₀ (mul_inv_eq_iff_eq_mul.1 h)
  exact false_of_inverted h2 Y Φ κ hY3 (hinj hb) (hinj hkN) hΦfp hYΦ hκΦ hκY hcard hx₀

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
