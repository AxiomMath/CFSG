module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L56B

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G]

structure WreathCfg (T X X' : Subgroup G) (x a s : G) : Prop where
  isPGroup : IsPGroup 2 T
  XT : X ≤ T
  X'T : X' ≤ T
  comm : ∀ c ∈ X, ∀ d ∈ X', c * d = d * c
  bot : X ⊓ X' = ⊥
  card : Nat.card X = 8
  xX : x ∈ X
  x2 : x * x = 1
  x1 : x ≠ 1
  xZ : ∀ d ∈ X, d * x = x * d
  aX : a ∈ X
  a2 : a * a = 1
  anc : ∃ d ∈ X, d * a ≠ a * d
  Cx : ∀ y ∈ T, y * x = x * y → y ∈ X ⊔ X'
  sT : s ∈ T
  s2 : s * s = 1
  sX : ∀ c ∈ X, s * c * s ∈ X'
  sX' : ∀ c ∈ X', s * c * s ∈ X

namespace WreathCfg

variable {T X X' : Subgroup G} {x a s : G} (h : WreathCfg T X X' x a s)
include h

theorem s_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_right h.s2

theorem conj_conj (c : G) : s * (s * c * s) * s = c := by
  calc s * (s * c * s) * s = (s * s) * c * (s * s) := by group
    _ = c := by rw [h.s2, one_mul, mul_one]

theorem le_T : X ⊔ X' ≤ T := sup_le h.XT h.X'T

theorem conj_mem_S {y : G} (hy : y ∈ X ⊔ X') : s * y * s ∈ X ⊔ X' := by
  obtain ⟨q₁, hq₁, q₂, hq₂, rfl⟩ := exists_mul_of_mem_sup_commute h.comm hy
  rw [show s * (q₁ * q₂) * s = (s * q₁ * s) * (s * q₂ * s) by
    calc s * (q₁ * q₂) * s = s * q₁ * (s * s) * q₂ * s := by rw [h.s2]; group
      _ = (s * q₁ * s) * (s * q₂ * s) := by group]
  exact mul_mem (mem_sup_right (h.sX q₁ hq₁)) (mem_sup_left (h.sX' q₂ hq₂))

theorem s_mem_normalizer : s ∈ normalizer ((X ⊔ X' : Subgroup G) : Set G) :=
  mem_normalizer_iff.mpr fun y => ⟨fun hy => by rw [h.s_inv]; exact h.conj_mem_S hy,
    fun hy => by
      rw [h.s_inv] at hy
      have h1 := h.conj_mem_S hy
      rwa [h.conj_conj] at h1⟩

theorem x_center {y : G} (hy : y ∈ X ⊔ X') : y * x = x * y := by
  obtain ⟨q₁, hq₁, q₂, hq₂, rfl⟩ := exists_mul_of_mem_sup_commute h.comm hy
  rw [mul_assoc, ← h.comm x h.xX q₂ hq₂, ← mul_assoc, h.xZ q₁ hq₁, mul_assoc]

theorem x'_center {y : G} (hy : y ∈ X ⊔ X') : y * (s * x * s) = s * x * s * y := by
  have h1 := h.x_center (h.conj_mem_S hy)
  rw [show s * y * s = s⁻¹ * y * s by rw [h.s_inv]] at h1
  rw [show s * x * s = s * x * s⁻¹ by rw [h.s_inv]]
  calc y * (s * x * s⁻¹) = s * ((s⁻¹ * y * s) * x) * s⁻¹ := by group
    _ = s * (x * (s⁻¹ * y * s)) * s⁻¹ := by rw [h1]
    _ = s * x * s⁻¹ * y := by group

theorem s_not_mem : s ∉ X ⊔ X' := by
  intro hs
  obtain ⟨q₁, hq₁, q₂, hq₂, hsq⟩ := exists_mul_of_mem_sup_commute h.comm hs
  have h1 : s * x * s = x := by
    calc s * x * s = s * x * s⁻¹ := by rw [h.s_inv]
      _ = q₁ * (q₂ * x * q₂⁻¹) * q₁⁻¹ := by rw [hsq]; group
      _ = q₁ * x * q₁⁻¹ := by rw [← h.comm x h.xX q₂ hq₂, mul_inv_cancel_right]
      _ = x := by rw [h.xZ q₁ hq₁, mul_inv_cancel_right]
  have h2 : x ∈ X ⊓ X' := mem_inf.mpr ⟨h.xX, h1 ▸ h.sX x h.xX⟩
  rw [h.bot, mem_bot] at h2
  exact h.x1 h2

theorem X'_eq : X' = conjugate X s := by
  ext c
  rw [mem_conjugate_iff, h.s_inv]
  exact ⟨fun hc => h.sX' c hc, fun hc => by
    have h1 := h.sX _ hc
    rwa [h.conj_conj] at h1⟩

theorem card_X' : Nat.card X' = 8 := by
  rw [h.X'_eq, card_conjugate_eq_card, h.card]

theorem card_S : Nat.card ↥(X ⊔ X') = 64 := by
  have h1 := GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer X X'
    (le_normalizer_of_commute h.comm) (disjoint_iff.mpr h.bot)
  rw [h1, h.card, h.card_X']

theorem eq_of_mem_center_X' [Finite G] {c : G} (hcX' : c ∈ X')
    (hcZ : ∀ d ∈ X', d * c = c * d) : c = 1 ∨ c = s * x * s := by
  have hna : ∃ c ∈ X, ∃ d ∈ X, c * d ≠ d * c := by
    obtain ⟨d, hd, hda⟩ := h.anc
    exact ⟨d, hd, a, h.aX, hda⟩
  have hsc : ∀ d ∈ X, d * (s * c * s) = s * c * s * d := by
    intro d hd
    have h1 := hcZ _ (h.sX d hd)
    rw [show s * d * s = s⁻¹ * d * s by rw [h.s_inv]] at h1
    rw [show s * c * s = s * c * s⁻¹ by rw [h.s_inv]]
    calc d * (s * c * s⁻¹) = s * ((s⁻¹ * d * s) * c) * s⁻¹ := by group
      _ = s * (c * (s⁻¹ * d * s)) * s⁻¹ := by rw [h1]
      _ = s * c * s⁻¹ * d := by group
  rcases eq_one_or_eq_of_mem_center_eight h.card hna h.xX h.x1 h.xZ (h.sX' c hcX') hsc
    with h1 | h1
  · left
    calc c = s * (s * c * s) * s := (h.conj_conj c).symm
      _ = s * 1 * s := by rw [h1]
      _ = 1 := by rw [mul_one, h.s2]
  · right
    calc c = s * (s * c * s) * s := (h.conj_conj c).symm
      _ = s * x * s := by rw [h1]

theorem S_le_normalizer_X : X ⊔ X' ≤ normalizer (X : Set G) :=
  sup_le le_normalizer (le_normalizer_of_commute h.comm)

theorem S_le_normalizer_X' : X ⊔ X' ≤ normalizer (X' : Set G) :=
  sup_le (le_normalizer_of_commute fun c hc d hd => (h.comm d hd c hc).symm) le_normalizer

theorem eq_of_mem_zpowers {w : G} (hw : w ∈ zpowers s) : w = 1 ∨ w = s := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [show m + m = 2 * m by ring, zpow_mul, zpow_two, h.s2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, h.s2, one_zpow, one_mul, zpow_one]

theorem mem_or_mul_mem_of_mem_N {y : G} (hy : y ∈ X ⊔ X' ⊔ zpowers s) :
    y ∈ X ⊔ X' ∨ y * s ∈ X ⊔ X' := by
  have h1 : y ∈ (((X ⊔ X' : Subgroup G) : Set G) * (zpowers s : Set G)) := by
    rw [← coe_mul_of_right_le_normalizer_left (X ⊔ X') (zpowers s)
      (zpowers_le.mpr h.s_mem_normalizer)]
    exact hy
  obtain ⟨c, hc, w, hw, hcw⟩ := h1
  have hcw' : c * w = y := hcw
  rw [← hcw']
  rcases h.eq_of_mem_zpowers hw with hw1 | hw1 <;> rw [hw1]
  · left
    rw [mul_one]
    exact hc
  · right
    rw [mul_assoc, h.s2, mul_one]
    exact hc

theorem card_N : Nat.card ↥(X ⊔ X' ⊔ zpowers s) = 128 := by
  have hs1 : s ≠ 1 := fun h1 => h.s_not_mem (h1 ▸ one_mem _)
  have hdisj : Disjoint (X ⊔ X') (zpowers s) := by
    rw [disjoint_iff, eq_bot_iff]
    intro w hw
    rcases h.eq_of_mem_zpowers (mem_inf.mp hw).2 with rfl | rfl
    · exact one_mem _
    · exact absurd (mem_inf.mp hw).1 h.s_not_mem
  have h1 := GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer (X ⊔ X') (zpowers s)
    (zpowers_le.mpr h.s_mem_normalizer) hdisj
  rw [h1, h.card_S, Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact h.s2) hs1]

theorem card_le_two_mul_inf {K : Subgroup G} (hK : K ≤ X ⊔ X' ⊔ zpowers s) :
    Nat.card K ≤ 2 * Nat.card ↥((X ⊔ X') ⊓ K) := by
  have h1 := relIndex_mul_card (X ⊔ X') K
  have h2 := relIndex_mul_card (X ⊔ X') (X ⊔ X' ⊔ zpowers s)
  rw [inf_of_le_left le_sup_left, h.card_N, h.card_S] at h2
  have h3 : (X ⊔ X').relIndex (X ⊔ X' ⊔ zpowers s) = 2 := by omega
  have h4 := relIndex_le_of_le_right hK (by rw [h3]; norm_num)
  rw [h3] at h4
  rw [← h1]
  exact Nat.mul_le_mul_right _ h4

end WreathCfg

end CFSG.ComponentClassification.Foote5
