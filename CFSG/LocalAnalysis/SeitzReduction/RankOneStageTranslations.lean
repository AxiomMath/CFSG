module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneStage

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.SteinbergBV CFSG.LocalAnalysis.SteinbergBX

namespace SmallRootStage

variable {D : Type*} [Group D] [Finite D] {R X U P : Subgroup D} {n : ℕ}

omit [Finite D] in
theorem translations_inf_normalizer (h : SmallRootStage R X U P n) :
    normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D) ⊓
        normalizer (R : Set D) = U ⊔ R := by
  have hC := h.normalizer_inf_centralizer
  refine le_antisymm (fun x hx => ?_) (le_inf (le_inf le_normalizer fun v hv =>
    mem_centralizer_iff.mpr fun u hu => gms_comm_V h.1 u (mem_sup_left hu) v hv) ?_)
  · rw [← hC]
    exact mem_inf.mpr ⟨(mem_inf.mp hx).2, (mem_inf.mp (mem_inf.mp hx).1).2⟩
  · intro v hv
    have hv' : v ∈ normalizer (R : Set D) ⊓ centralizer (U : Set D) := by rw [hC]; exact hv
    exact (mem_inf.mp hv').1

theorem comm_eq_one_iff_mem (h : SmallRootStage R X U P n) {t : D}
    (hS : GMS28.Setup R R X U P n t) {w : D}
    (hw : w ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D)) :
    w * t * w⁻¹ * t = 1 ↔ w ∈ U ⊔ R := by
  rw [hS.comm_eq_one_iff]
  constructor
  · intro hwt
    rw [← h.translations_inf_normalizer]
    refine mem_inf.mpr ⟨hw, ?_⟩
    rw [hS.eq_zpowers]
    refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun r hr => ?_)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hr
    exact ((Commute.zpow_right (show Commute w t from hwt) k).eq).symm
  · intro hwV
    exact hS.commute_V hwV hS.t_mem_V

theorem card_translations (h : SmallRootStage R X U P n) {t : D}
    (hS : GMS28.Setup R R X U P n t)
    (htr : ∀ u ∈ U, ∃ τ ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D),
      τ * t * τ⁻¹ = u * t) :
    Nat.card (normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D) :
      Subgroup D) = 2 * 2 ^ n * 2 ^ n := by
  set W := normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D) with hW
  obtain ⟨-, -, -, -, ⟨-, -, -, hUcard⟩, -⟩ := h.1
  let φ : W →* U :=
    { toFun := fun w => ⟨(w : D) * t * (w : D)⁻¹ * t, hS.comm_mem w.2⟩
      map_one' := Subtype.ext (by simp [hS.mul_self_t])
      map_mul' := fun a b => Subtype.ext (hS.comm_mul a.2 b.2) }
  have hsurj : Function.Surjective φ := fun u => by
    obtain ⟨τ, hτ, hτt⟩ := htr u u.2
    refine ⟨⟨τ, hτ⟩, Subtype.ext ?_⟩
    change τ * t * τ⁻¹ * t = u
    rw [hτt, mul_assoc, hS.mul_self_t, mul_one]
  have hker : φ.ker = (U ⊔ R).subgroupOf W := by
    ext w
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← h.comm_eq_one_iff_mem hS w.2]
    constructor
    · intro h1
      exact congrArg Subtype.val h1
    · intro h1
      exact Subtype.ext h1
  have hVW : U ⊔ R ≤ W := hS.V_le_tr
  have hVcard : Nat.card (U ⊔ R : Subgroup D) = 2 ^ n * 2 := by
    rw [SteinbergBT.card_sup_of_centralizes (gms_R_le_centralizer_U h.1) hS.inf_eq_bot, hUcard,
      h.card_eq_two]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv, hker,
    Nat.card_congr (subgroupOfEquivOfLe hVW).toEquiv, hUcard, hVcard] at h1
  rw [h1]
  ring

theorem normalizer_V_eq_sup {t : D} (hS : GMS28.Setup R R X U P n t)
    (htr : ∀ u ∈ U, ∃ τ ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D),
      τ * t * τ⁻¹ = u * t) :
    normalizer ((U ⊔ R : Subgroup D) : Set D) =
      (normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D)) ⊔
        (normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ normalizer (R : Set D)) := by
  refine le_antisymm (fun x hx => ?_) (sup_le inf_le_left inf_le_left)
  obtain ⟨τ, hτ, hτt⟩ := htr _ (hS.conj_t_mul_mem hx)
  have hτx : τ * t * τ⁻¹ = x * t * x⁻¹ := by
    rw [hτt, mul_assoc _ t t, hS.mul_self_t, mul_one]
  have hyt : τ⁻¹ * x * t = t * (τ⁻¹ * x) := by
    calc τ⁻¹ * x * t = τ⁻¹ * (x * t * x⁻¹) * x := by group
      _ = τ⁻¹ * (τ * t * τ⁻¹) * x := by rw [hτx]
      _ = t * (τ⁻¹ * x) := by group
  have hyR : τ⁻¹ * x ∈ normalizer (R : Set D) := by
    rw [hS.eq_zpowers]
    refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun r hr => ?_)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hr
    exact ((Commute.zpow_right (show Commute (τ⁻¹ * x) t from hyt) k).eq).symm
  have hyV : τ⁻¹ * x ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) :=
    mul_mem (inv_mem (mem_inf.mp hτ).1) hx
  have e : x = τ * (τ⁻¹ * x) := by group
  rw [e]
  exact mul_mem (mem_sup_left hτ) (mem_sup_right (mem_inf.mpr ⟨hyV, hyR⟩))

end SmallRootStage

variable {D : Type*} [Group D] [Finite D] {R X U P : Subgroup D} {n : ℕ}

theorem smallRoot_translations (h : SmallRootStage R X U P n)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) (hE : GMSHasRegularNormal U R) :
    let V := U ⊔ R
    let W := normalizer (V : Set D) ⊓ centralizer (U : Set D)
    let Y := normalizer (V : Set D) ⊓ normalizer (R : Set D)
    IsPGroup 2 W ∧ Nat.card W = 2 * 2 ^ n * 2 ^ n ∧ V ≤ W ∧
    (W.subgroupOf (normalizer (V : Set D))).Normal ∧
    normalizer (V : Set D) ≤ normalizer (U : Set D) ∧
    W ⊓ normalizer (R : Set D) = V ∧ normalizer (V : Set D) = W ⊔ Y ∧
    ∀ r ∈ R, r ≠ 1 →
      (∀ w ∈ W, w * r * w⁻¹ * r⁻¹ ∈ U) ∧
      (∀ w ∈ W, ∀ w' ∈ W, (w * w') * r * (w * w')⁻¹ * r⁻¹ =
        (w * r * w⁻¹ * r⁻¹) * (w' * r * w'⁻¹ * r⁻¹)) ∧
      (∀ w ∈ W, w * r * w⁻¹ * r⁻¹ = 1 ↔ w ∈ V) ∧
      (∀ u ∈ U, ∃ w ∈ W, w * r * w⁻¹ * r⁻¹ = u) := by
  intro V W Y
  obtain ⟨E, hEN, hEn, hreg⟩ := hE
  obtain ⟨t, htR, ht1⟩ := h.exists_ne_one
  have hS := h.setup h3 htR ht1
  have htr := hS.exists_tr_conj_eq E hEN hEn hreg
  have hcard : Nat.card W = 2 * 2 ^ n * 2 ^ n := h.card_translations hS htr
  refine ⟨IsPGroup.of_card (n := 2 * n + 1) (by rw [hcard]; ring), hcard, hS.V_le_tr,
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      hS.normalizer_V_le_normalizer_tr, hS.normalizer_V_le, h.translations_inf_normalizer,
    SmallRootStage.normalizer_V_eq_sup hS htr, fun r hr hr1 => ?_⟩
  have hSr := h.setup h3 hr hr1
  have htrr := hSr.exists_tr_conj_eq E hEN hEn hreg
  rw [hSr.inv_t]
  refine ⟨fun w hw => hSr.comm_mem hw, fun w hw w' hw' => hSr.comm_mul hw hw',
    fun w hw => h.comm_eq_one_iff_mem hSr hw, fun u hu => ?_⟩
  obtain ⟨τ, hτ, hτt⟩ := htrr u hu
  refine ⟨τ, hτ, ?_⟩
  rw [hτt, mul_assoc, hSr.mul_self_t, mul_one]

end CFSG.SeitzReduction.RankOne
