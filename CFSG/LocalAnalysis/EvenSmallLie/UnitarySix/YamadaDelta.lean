module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaWeak

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.UnitarySix.Yamada

open Subgroup CFSG.Quasithin CFSG.Sporadic.Schreier

section G

variable {G : Type} [Group G] {L : Subgroup G}

@[expose] def toddK (D : ToddParabolic L) : Subgroup G := D.K.map L.subtype

theorem toddK_le (D : ToddParabolic L) : toddK D ≤ L := map_subtype_le _

theorem conjClass_toddK (D : ToddParabolic L) (a : L) :
    conjClass (toddK D) (a : G) = L.subtype '' conjClass D.K a := by
  ext y
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k * a * k⁻¹, ⟨k, hk, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, ⟨k, hk, rfl⟩, by simp⟩

theorem ncard_conjClass_toddK (D : ToddParabolic L) (a : L) :
    (conjClass (toddK D) (a : G)).ncard = (conjClass D.K a).ncard := by
  rw [conjClass_toddK, Set.ncard_image_of_injective _ L.subtype_injective]

theorem conjClass_toddK_subset (D : ToddParabolic L) {a : L} (ha : a ∈ D.A) :
    conjClass (toddK D) (a : G) ⊆ toddA D := by
  rw [conjClass_toddK]
  rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  exact ⟨_, (mem_normalizer_iff.1 (D.K_le_normalizer hk) a).1 ha, rfl⟩

theorem conj_mem_toddA (D : ToddParabolic L) {k a : G} (hk : k ∈ toddK D) (ha : a ∈ toddA D) :
    k * a * k⁻¹ ∈ toddA D := by
  obtain ⟨k, hk, rfl⟩ := hk
  obtain ⟨a, ha, rfl⟩ := ha
  exact ⟨_, (mem_normalizer_iff.1 (D.K_le_normalizer hk) a).1 ha, by simp⟩

theorem conj_mem_conjClass {K : Subgroup G} {x y c : G} (hc : c ∈ K) (hy : y ∈ conjClass K x) :
    c * y * c⁻¹ ∈ conjClass K x := by
  obtain ⟨d, hd, rfl⟩ := hy
  exact ⟨c * d, mul_mem hc hd, by group⟩

theorem self_mem_conjClass (K : Subgroup G) (x : G) : x ∈ conjClass K x :=
  ⟨1, one_mem K, by group⟩

theorem conjClass_eq_of_mem {K : Subgroup G} {x y : G} (hy : y ∈ conjClass K x) :
    conjClass K y = conjClass K x := by
  obtain ⟨d, hd, rfl⟩ := hy
  ext z
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c * d, mul_mem hc hd, by group⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c * d⁻¹, mul_mem hc (inv_mem hd), by group⟩

theorem invariant_diff {K : Subgroup G} {S : Set G} (hS : ∀ c ∈ K, ∀ y ∈ S, c * y * c⁻¹ ∈ S)
    (x : G) : ∀ c ∈ K, ∀ y ∈ S \ conjClass K x, c * y * c⁻¹ ∈ S \ conjClass K x := by
  rintro c hc y ⟨hyS, hyx⟩
  refine ⟨hS c hc y hyS, fun hcy => hyx ?_⟩
  have := conj_mem_conjClass (inv_mem hc) hcy
  rwa [show c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y by group] at this

open Classical in
theorem ncard_eq_add_of_invariant {K : Subgroup G} {S : Set G} (hSfin : S.Finite)
    (hS : ∀ c ∈ K, ∀ y ∈ S, c * y * c⁻¹ ∈ S) (x : G) :
    S.ncard = (if x ∈ S then (conjClass K x).ncard else 0) + (S \ conjClass K x).ncard := by
  split_ifs with hx
  · have hsub : conjClass K x ⊆ S := by
      rintro _ ⟨c, hc, rfl⟩
      exact hS c hc x hx
    rw [← Set.ncard_inter_add_ncard_sdiff_eq_ncard S (conjClass K x) hSfin,
      Set.inter_eq_right.2 hsub]
  · have hdisj : S \ conjClass K x = S := by
      refine Set.ext fun y => ⟨fun hy => hy.1, fun hyS => ⟨hyS, fun hyx => hx ?_⟩⟩
      obtain ⟨c, hc, rfl⟩ := hyx
      have := hS c⁻¹ (inv_mem hc) _ hyS
      rwa [show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at this
    rw [hdisj, zero_add]

end G

namespace Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {D : ToddParabolic L} {t : G}

theorem toddK_le_H (h : Setting G L D t) : toddK D ≤ centralizer ({t} : Set G) :=
  (toddK_le D).trans h.le_H

theorem comm_toddK (h : Setting G L D t) {k : G} (hk : k ∈ toddK D) : k * t = t * k :=
  h.comm (toddK_le D hk)

theorem conjClass_t (h : Setting G L D t) : conjClass (toddK D) t = {t} := by
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [h.comm_toddK hc, mul_inv_cancel_right]
  · rintro rfl
    exact self_mem_conjClass _ _

omit [Finite G] in
theorem conjClass_one (K : Subgroup G) : conjClass K (1 : G) = {1} := by
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨c, -, rfl⟩
    group
  · rintro rfl
    exact self_mem_conjClass _ _

theorem conjClass_mul_t (h : Setting G L D t) (a : G) :
    conjClass (toddK D) (a * t) = (· * t) '' conjClass (toddK D) a := by
  ext y
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c * a * c⁻¹, ⟨c, hc, rfl⟩, ?_⟩
    have := h.comm_toddK hc
    calc c * a * c⁻¹ * t = c * a * (c⁻¹ * (t * c)) * c⁻¹ := by group
      _ = c * (a * t) * c⁻¹ := by rw [← this]; group
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨c, hc, ?_⟩
    have := h.comm_toddK hc
    calc c * a * c⁻¹ * t = c * a * (c⁻¹ * (t * c)) * c⁻¹ := by group
      _ = c * (a * t) * c⁻¹ := by rw [← this]; group

theorem ncard_conjClass_mul_t (h : Setting G L D t) (a : G) :
    (conjClass (toddK D) (a * t)).ncard = (conjClass (toddK D) a).ncard := by
  rw [h.conjClass_mul_t, Set.ncard_image_of_injective _ (mul_left_injective t)]

omit [Finite G] in
theorem ncard_delta (D : ToddParabolic L) :
    (conjClass (toddK D) (D.a₁ : G)).ncard = 21 ∧ (conjClass (toddK D) (D.a₂ : G)).ncard = 210 ∧
      (conjClass (toddK D) (D.a₃ : G)).ncard = 280 := by
  simp only [ncard_conjClass_toddK]
  exact D.orbit_card

omit [Finite G] in
theorem mem_delta_of_mem (D : ToddParabolic L) {a : G} (ha : a ∈ toddA D) (ha1 : a ≠ 1) :
    a ∈ conjClass (toddK D) (D.a₁ : G) ∨ a ∈ conjClass (toddK D) (D.a₂ : G) ∨
      a ∈ conjClass (toddK D) (D.a₃ : G) := by
  obtain ⟨a, haA, rfl⟩ := ha
  have ha1' : a ≠ 1 := fun h1 => ha1 (by rw [h1]; rfl)
  simp only [conjClass_toddK]
  rcases D.orbits a haA ha1' with h1 | h1 | h1
  · exact Or.inl ⟨a, h1, rfl⟩
  · exact Or.inr (Or.inl ⟨a, h1, rfl⟩)
  · exact Or.inr (Or.inr ⟨a, h1, rfl⟩)

omit [Finite G] in
theorem a_ne_one (D : ToddParabolic L) :
    (D.a₁ : G) ≠ 1 ∧ (D.a₂ : G) ≠ 1 ∧ (D.a₃ : G) ≠ 1 := by
  obtain ⟨n₁, n₂, n₃⟩ := ncard_delta D (G := G)
  refine ⟨fun h1 => ?_, fun h1 => ?_, fun h1 => ?_⟩
  · rw [h1, conjClass_one, Set.ncard_singleton] at n₁
    exact absurd n₁ (by norm_num)
  · rw [h1, conjClass_one, Set.ncard_singleton] at n₂
    exact absurd n₂ (by norm_num)
  · rw [h1, conjClass_one, Set.ncard_singleton] at n₃
    exact absurd n₃ (by norm_num)

omit [Finite G] in
theorem a_not_mem_delta (D : ToddParabolic L) :
    (D.a₂ : G) ∉ conjClass (toddK D) (D.a₁ : G) ∧ (D.a₃ : G) ∉ conjClass (toddK D) (D.a₁ : G) ∧
      (D.a₃ : G) ∉ conjClass (toddK D) (D.a₂ : G) := by
  obtain ⟨h12, h13, h23⟩ := D.not_isConj
  have key : ∀ x y : L, ¬ IsConj x y → (y : G) ∉ conjClass (toddK D) (x : G) := by
    intro x y hxy hy
    rw [conjClass_toddK] at hy
    obtain ⟨z, ⟨k, -, rfl⟩, hz⟩ := hy
    exact hxy (isConj_iff.2 ⟨k, L.subtype_injective hz⟩)
  exact ⟨key _ _ h12, key _ _ h13, key _ _ h23⟩

open Classical in
theorem ncard_eq_of_invariant (h : Setting G L D t) {S : Set G} (hSE : S ⊆ toddE D t)
    (hS : ∀ c ∈ toddK D, ∀ y ∈ S, c * y * c⁻¹ ∈ S) :
    S.ncard = (if (1 : G) ∈ S then 1 else 0) + (if (D.a₁ : G) ∈ S then 21 else 0) +
      (if (D.a₂ : G) ∈ S then 210 else 0) + (if (D.a₃ : G) ∈ S then 280 else 0) +
      (if t ∈ S then 1 else 0) + (if (D.a₁ : G) * t ∈ S then 21 else 0) +
      (if (D.a₂ : G) * t ∈ S then 210 else 0) + (if (D.a₃ : G) * t ∈ S then 280 else 0) := by
  set K := toddK D with hK
  obtain ⟨n₁, n₂, n₃⟩ := ncard_delta D (G := G)
  obtain ⟨o₁, o₂, o₃⟩ := a_ne_one D (G := G)
  obtain ⟨d₁₂, d₁₃, d₂₃⟩ := a_not_mem_delta D (G := G)
  have hA : ∀ a : L, a ∈ D.A → conjClass K (a : G) ⊆ toddA D := fun a ha =>
    conjClass_toddK_subset D ha
  obtain ⟨m₁, m₂, m₃⟩ := D.a_mem
  have htA : t ∉ toddA D := fun ht => h.t_not_mem (toddA_le D ht)
  have hatA : ∀ a ∈ toddA D, a * t ∉ toddA D := fun a ha hat => htA (by
    have := mul_mem (inv_mem ha) hat
    rwa [inv_mul_cancel_left] at this)
  have hat_ne : ∀ a : G, a ≠ 1 → a * t ≠ t := fun a ha hat => ha (by
    rwa [mul_eq_right] at hat)
  have hmt : ∀ a b : G, a * t ∈ conjClass K (b * t) → a ∈ conjClass K b := by
    intro a b hab
    rw [h.conjClass_mul_t] at hab
    obtain ⟨c, hc, hct⟩ := hab
    rwa [mul_left_injective t hct] at hc
  have hfin : ∀ T : Set G, T.Finite := fun T => Set.toFinite T
  have e0 := ncard_eq_add_of_invariant (hfin S) hS 1
  have i1 := invariant_diff hS 1
  have e1 := ncard_eq_add_of_invariant (hfin _) i1 (D.a₁ : G)
  have i2 := invariant_diff i1 (D.a₁ : G)
  have e2 := ncard_eq_add_of_invariant (hfin _) i2 (D.a₂ : G)
  have i3 := invariant_diff i2 (D.a₂ : G)
  have e3 := ncard_eq_add_of_invariant (hfin _) i3 (D.a₃ : G)
  have i4 := invariant_diff i3 (D.a₃ : G)
  have e4 := ncard_eq_add_of_invariant (hfin _) i4 t
  have i5 := invariant_diff i4 t
  have e5 := ncard_eq_add_of_invariant (hfin _) i5 ((D.a₁ : G) * t)
  have i6 := invariant_diff i5 ((D.a₁ : G) * t)
  have e6 := ncard_eq_add_of_invariant (hfin _) i6 ((D.a₂ : G) * t)
  have i7 := invariant_diff i6 ((D.a₂ : G) * t)
  have e7 := ncard_eq_add_of_invariant (hfin _) i7 ((D.a₃ : G) * t)
  set O₀ := conjClass K 1 with hO₀
  set O₁ := conjClass K (D.a₁ : G) with hO₁
  set O₂ := conjClass K (D.a₂ : G) with hO₂
  set O₃ := conjClass K (D.a₃ : G) with hO₃
  set O₄ := conjClass K t with hO₄
  set O₅ := conjClass K ((D.a₁ : G) * t) with hO₅
  set O₆ := conjClass K ((D.a₂ : G) * t) with hO₆
  set O₇ := conjClass K ((D.a₃ : G) * t) with hO₇
  have hempty : ((((((((S \ O₀) \ O₁) \ O₂) \ O₃) \ O₄) \ O₅) \ O₆) \ O₇) = ∅ := by
    ext y
    simp only [Set.mem_sdiff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨⟨⟨⟨⟨⟨⟨hyS, hy0⟩, hy1⟩, hy2⟩, hy3⟩, hy4⟩, hy5⟩, hy6⟩, hy7⟩
    obtain ⟨a, ha, hya | hya⟩ := h.eq_or_eq_mul_of_mem_toddE (hSE hyS) <;> subst y
    · by_cases ha1 : a = 1
      · exact hy0 (by rw [ha1, hO₀, conjClass_one]; rfl)
      rcases mem_delta_of_mem D ha ha1 with h1 | h1 | h1
      · exact hy1 h1
      · exact hy2 h1
      · exact hy3 h1
    · by_cases ha1 : a = 1
      · exact hy4 (by rw [ha1, one_mul]; exact self_mem_conjClass _ _)
      rcases mem_delta_of_mem D ha ha1 with h1 | h1 | h1
      · exact hy5 (by rw [hO₅, h.conjClass_mul_t]; exact ⟨a, h1, rfl⟩)
      · exact hy6 (by rw [hO₆, h.conjClass_mul_t]; exact ⟨a, h1, rfl⟩)
      · exact hy7 (by rw [hO₇, h.conjClass_mul_t]; exact ⟨a, h1, rfl⟩)
  rw [hempty, Set.ncard_empty, add_zero] at e7
  rw [e0, e1, e2, e3, e4, e5, e6, e7]
  have hO₀' : O₀ = {1} := by rw [hO₀, conjClass_one]
  have hO₄' : O₄ = {t} := by rw [hO₄, h.conjClass_t]
  have sA₁ : O₁ ⊆ toddA D := hA _ m₁
  have sA₂ : O₂ ⊆ toddA D := hA _ m₂
  have sA₃ : O₃ ⊆ toddA D := hA _ m₃
  have mA₁ : (D.a₁ : G) ∈ toddA D := ⟨_, m₁, rfl⟩
  have mA₂ : (D.a₂ : G) ∈ toddA D := ⟨_, m₂, rfl⟩
  have mA₃ : (D.a₃ : G) ∈ toddA D := ⟨_, m₃, rfl⟩
  have ka : ∀ a : G, a ≠ 1 → a ∉ O₀ := fun a ha h1 => ha (by rw [hO₀'] at h1; exact h1)
  have kt : ∀ O ⊆ (toddA D : Set G), t ∉ O := fun O hO h1 => htA (hO h1)
  have kat : ∀ a ∈ toddA D, ∀ O ⊆ (toddA D : Set G), a * t ∉ O := fun a ha O hO h1 =>
    hatA a ha (hO h1)
  have k0 : ∀ a ∈ toddA D, a * t ∉ O₀ := fun a ha h1 =>
    hatA a ha (by rw [hO₀'] at h1; rw [Set.mem_singleton_iff.1 h1]; exact one_mem _)
  have k4 : ∀ a : G, a ≠ 1 → a * t ∉ O₄ := fun a ha h1 =>
    hat_ne a ha (by rw [hO₄'] at h1; exact h1)
  have k56 : (D.a₂ : G) * t ∉ O₅ := fun h1 => d₁₂ (hmt _ _ h1)
  have k57 : (D.a₃ : G) * t ∉ O₅ := fun h1 => d₁₃ (hmt _ _ h1)
  have k67 : (D.a₃ : G) * t ∉ O₆ := fun h1 => d₂₃ (hmt _ _ h1)
  have kt0 : t ∉ O₀ := ka t h.t_ne_one
  simp only [Set.mem_sdiff, ka _ o₁, ka _ o₂, ka _ o₃, d₁₂, d₁₃, d₂₃, kt0, kt O₁ sA₁, kt O₂ sA₂,
    kt O₃ sA₃, k0 _ mA₁, k0 _ mA₂, k0 _ mA₃, kat _ mA₁ O₁ sA₁, kat _ mA₁ O₂ sA₂,
    kat _ mA₁ O₃ sA₃, kat _ mA₂ O₁ sA₁, kat _ mA₂ O₂ sA₂, kat _ mA₂ O₃ sA₃, kat _ mA₃ O₁ sA₁,
    kat _ mA₃ O₂ sA₂, kat _ mA₃ O₃ sA₃, k4 _ o₁, k4 _ o₂, k4 _ o₃, k56, k57, k67,
    not_false_eq_true, and_true]
  rw [hO₀', hO₄', Set.ncard_singleton, Set.ncard_singleton, n₁, n₂, n₃, hO₅, hO₆, hO₇,
    h.ncard_conjClass_mul_t, h.ncard_conjClass_mul_t, h.ncard_conjClass_mul_t, ← hO₁, ← hO₂,
    ← hO₃, n₁, n₂, n₃]
  ring

omit [Finite G] in
theorem card_eq_ncard (B : Subgroup G) : Nat.card B = (B : Set G).ncard :=
  Nat.card_coe_set_eq _

theorem eq_toddA_of_invariant (h : Setting G L D t) {B : Subgroup G} (hBA : B ≤ toddA D)
    (hB : ∀ k ∈ toddK D, ∀ b ∈ B, k * b * k⁻¹ ∈ B) (hB1 : B ≠ ⊥) : B = toddA D := by
  classical
  have hc := h.ncard_eq_of_invariant (S := (B : Set G))
    (fun x hx => toddA_le_toddE D t (hBA hx)) hB
  have htA : t ∉ toddA D := fun ht => h.t_not_mem (toddA_le D ht)
  have htB : t ∉ B := fun ht => htA (hBA ht)
  simp only [SetLike.mem_coe, htB, ite_false, one_mem, ite_true, add_zero] at hc
  have hdvd : Nat.card B ∣ 2 ^ 9 := card_toddA D ▸ Subgroup.card_dvd_of_le hBA
  have hB1' : Nat.card B ≠ 1 := fun h1 => hB1 (Subgroup.card_eq_one.1 h1)
  rw [card_eq_ncard, hc] at hdvd hB1'
  have h9 : Nat.card B = 2 ^ 9 := by
    rw [card_eq_ncard, hc]
    revert hdvd hB1'
    split_ifs <;> decide
  exact eq_of_le_of_card_ge hBA (by rw [card_toddA, h9])

end Setting

end CFSG.EvenSmallLie.UnitarySix.Yamada
