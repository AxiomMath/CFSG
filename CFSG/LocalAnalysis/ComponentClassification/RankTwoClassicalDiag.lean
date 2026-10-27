module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderBasic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup

variable {G : Type} [Group G]

@[expose] def diagSet (J U W : Subgroup G) : Set G := {j | j ∈ J ∧ j ∉ U ∧ j ∉ W}

theorem exists_ne_ne_of_three_le {H : Subgroup G} (h : 3 ≤ Nat.card H) (x y : G) :
    ∃ z ∈ H, z ≠ x ∧ z ≠ y := by
  by_contra hne
  push Not at hne
  have hsub : (H : Set G) ⊆ {x, y} := by
    intro z hz
    by_cases hzx : z = x
    · exact Or.inl hzx
    · exact Or.inr (hne z hz hzx)
  have h1 : (H : Set G).ncard ≤ ({x, y} : Set G).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({x, y} : Set G).ncard ≤ 2 := by
    have := Set.ncard_insert_le x {y}
    rwa [Set.ncard_singleton] at this
  have h3 : Nat.card H = (H : Set G).ncard := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
  omega

structure DiagData (A J U W : Subgroup G) (p y₁ y₂ : G) : Prop where
  J_eq : J = U ⊔ W
  inf_eq : U ⊓ W = ⊥
  three_le_U : 3 ≤ Nat.card U
  three_le_W : 3 ≤ Nat.card W
  p_mem : p ∈ diagSet J U W
  trans : ∀ j ∈ diagSet J U W, ∃ a ∈ A ⊓ normalizer (J : Set G), a * p * a⁻¹ = j
  free : ∀ a ∈ A ⊓ normalizer (J : Set G), ∀ j ∈ diagSet J U W, a * j * a⁻¹ = j →
    a ∈ centralizer (J : Set G)
  y₁_mem : y₁ ∈ A ⊓ normalizer (J : Set G)
  y₂_mem : y₂ ∈ A ⊓ normalizer (J : Set G)
  y₁_cent : y₁ ∈ centralizer (U : Set G)
  y₂_cent : y₂ ∈ centralizer (W : Set G)
  gen : ∀ a ∈ A ⊓ normalizer (J : Set G), ∃ k₁ k₂ : ℕ,
    (y₁ ^ k₁ * y₂ ^ k₂)⁻¹ * a ∈ centralizer (J : Set G)
  sep : ∀ a ∈ A, ∀ x ∈ J, x ≠ 1 → a * x * a⁻¹ ∈ J →
    ((x ∈ U ↔ a * x * a⁻¹ ∈ U) ∧ (x ∈ W ↔ a * x * a⁻¹ ∈ W))

namespace DiagData

variable {A J U W : Subgroup G} {p y₁ y₂ : G} (h : DiagData A J U W p y₁ y₂)
include h

theorem U_le : U ≤ J := h.J_eq ▸ le_sup_left

theorem W_le : W ≤ J := h.J_eq ▸ le_sup_right

theorem mul_mem_diagSet {u w : G} (hu : u ∈ U) (hu1 : u ≠ 1) (hw : w ∈ W) (hw1 : w ≠ 1) :
    u * w ∈ diagSet J U W := by
  refine ⟨mul_mem (h.U_le hu) (h.W_le hw), fun huw => hw1 ?_, fun huw => hu1 ?_⟩
  · have hw' : w ∈ U ⊓ W := mem_inf.mpr ⟨by simpa using mul_mem (inv_mem hu) huw, hw⟩
    rwa [h.inf_eq, mem_bot] at hw'
  · have hu' : u ∈ U ⊓ W := mem_inf.mpr ⟨hu, by simpa using mul_mem huw (inv_mem hw)⟩
    rwa [h.inf_eq, mem_bot] at hu'

theorem mul_mem_diagSet' {u w : G} (hu : u ∈ U) (hu1 : u ≠ 1) (hw : w ∈ W) (hw1 : w ≠ 1) :
    w * u ∈ diagSet J U W := by
  refine ⟨mul_mem (h.W_le hw) (h.U_le hu), fun hwu => hw1 ?_, fun hwu => hu1 ?_⟩
  · have hw' : w ∈ U ⊓ W := mem_inf.mpr ⟨by simpa using mul_mem hwu (inv_mem hu), hw⟩
    rwa [h.inf_eq, mem_bot] at hw'
  · have hu' : u ∈ U ⊓ W := mem_inf.mpr ⟨hu, by simpa using mul_mem (inv_mem hw) hwu⟩
    rwa [h.inf_eq, mem_bot] at hu'

theorem eq_of_mul_eq {u u' w w' : G} (hu : u ∈ U) (hu' : u' ∈ U) (hw : w ∈ W) (hw' : w' ∈ W)
    (he : u * w = u' * w') : u = u' ∧ w = w' := by
  have h1 : u'⁻¹ * u = w' * w⁻¹ := by
    calc u'⁻¹ * u = u'⁻¹ * (u * w) * w⁻¹ := by group
      _ = w' * w⁻¹ := by rw [he]; group
  have h2 : u'⁻¹ * u ∈ U ⊓ W :=
    mem_inf.mpr ⟨mul_mem (inv_mem hu') hu, h1 ▸ mul_mem hw' (inv_mem hw)⟩
  rw [h.inf_eq, mem_bot] at h2
  have hu'' : u = u' := by
    calc u = u' * (u'⁻¹ * u) := by group
      _ = u' := by rw [h2, mul_one]
  refine ⟨hu'', ?_⟩
  rw [h2] at h1
  calc w = (w' * w⁻¹)⁻¹ * w' := by group
    _ = w' := by rw [← h1, inv_one, one_mul]

theorem normalizer_le_U : A ⊓ normalizer (J : Set G) ≤ normalizer (U : Set G) := by
  have key : ∀ a ∈ A ⊓ normalizer (J : Set G), ∀ u ∈ U, a * u * a⁻¹ ∈ U := by
    intro a ha u hu
    by_cases hu1 : u = 1
    · rw [hu1, mul_one, mul_inv_cancel]
      exact one_mem _
    have haJ := (mem_normalizer_iff.mp (mem_inf.mp ha).2 u).mp (h.U_le hu)
    exact ((h.sep a (mem_inf.mp ha).1 u (h.U_le hu) hu1 haJ).1).mp hu
  intro a ha
  rw [mem_normalizer_iff]
  intro u
  refine ⟨key a ha u, fun hu => ?_⟩
  have ha' : a⁻¹ ∈ A ⊓ normalizer (J : Set G) :=
    mem_inf.mpr ⟨inv_mem (mem_inf.mp ha).1, inv_mem (mem_inf.mp ha).2⟩
  have := key a⁻¹ ha' _ hu
  simpa [mul_assoc] using this

theorem normalizer_le_W : A ⊓ normalizer (J : Set G) ≤ normalizer (W : Set G) := by
  have key : ∀ a ∈ A ⊓ normalizer (J : Set G), ∀ w ∈ W, a * w * a⁻¹ ∈ W := by
    intro a ha w hw
    by_cases hw1 : w = 1
    · rw [hw1, mul_one, mul_inv_cancel]
      exact one_mem _
    have haJ := (mem_normalizer_iff.mp (mem_inf.mp ha).2 w).mp (h.W_le hw)
    exact ((h.sep a (mem_inf.mp ha).1 w (h.W_le hw) hw1 haJ).2).mp hw
  intro a ha
  rw [mem_normalizer_iff]
  intro w
  refine ⟨key a ha w, fun hw => ?_⟩
  have ha' : a⁻¹ ∈ A ⊓ normalizer (J : Set G) :=
    mem_inf.mpr ⟨inv_mem (mem_inf.mp ha).1, inv_mem (mem_inf.mp ha).2⟩
  have := key a⁻¹ ha' _ hw
  simpa [mul_assoc] using this

theorem le_closure : J ≤ closure (diagSet J U W) := by
  have hU : U ≤ closure (diagSet J U W) := by
    intro u hu
    by_cases hu1 : u = 1
    · rw [hu1]
      exact one_mem _
    obtain ⟨u₁, hu₁, hu₁1, hu₁u⟩ := exists_ne_ne_of_three_le h.three_le_U 1 u
    obtain ⟨w, hw, hw1, -⟩ := exists_ne_ne_of_three_le h.three_le_W 1 1
    have h1 : u₁ * w ∈ diagSet J U W := h.mul_mem_diagSet hu₁ hu₁1 hw hw1
    have h2 : w⁻¹ * (u₁⁻¹ * u) ∈ diagSet J U W := by
      refine h.mul_mem_diagSet' (mul_mem (inv_mem hu₁) hu) ?_ (inv_mem hw) (inv_ne_one.mpr hw1)
      intro h3
      apply hu₁u
      calc u₁ = u₁ * (u₁⁻¹ * u)⁻¹ * u₁⁻¹ * u := by group
        _ = u := by rw [h3]; group
    have h3 : u = (u₁ * w) * (w⁻¹ * (u₁⁻¹ * u)) := by group
    rw [h3]
    exact mul_mem (subset_closure h1) (subset_closure h2)
  have hW : W ≤ closure (diagSet J U W) := by
    intro w hw
    by_cases hw1 : w = 1
    · rw [hw1]
      exact one_mem _
    obtain ⟨w₁, hw₁, hw₁1, hw₁w⟩ := exists_ne_ne_of_three_le h.three_le_W 1 w
    obtain ⟨u, hu, hu1, -⟩ := exists_ne_ne_of_three_le h.three_le_U 1 1
    have h1 : w₁ * u ∈ diagSet J U W := h.mul_mem_diagSet' hu hu1 hw₁ hw₁1
    have h2 : u⁻¹ * (w₁⁻¹ * w) ∈ diagSet J U W := by
      refine h.mul_mem_diagSet (inv_mem hu) (inv_ne_one.mpr hu1) (mul_mem (inv_mem hw₁) hw) ?_
      intro h3
      apply hw₁w
      calc w₁ = w₁ * (w₁⁻¹ * w)⁻¹ * w₁⁻¹ * w := by group
        _ = w := by rw [h3]; group
    have h3 : w = (w₁ * u) * (u⁻¹ * (w₁⁻¹ * w)) := by group
    rw [h3]
    exact mul_mem (subset_closure h1) (subset_closure h2)
  exact h.J_eq.le.trans (sup_le hU hW)

theorem trans_W {w w' : G} (hw : w ∈ W) (hw1 : w ≠ 1) (hw' : w' ∈ W) (hw'1 : w' ≠ 1) :
    ∃ a ∈ zpowers y₁, a⁻¹ * w * a = w' := by
  obtain ⟨u, hu, hu1, -⟩ := exists_ne_ne_of_three_le h.three_le_U 1 1
  obtain ⟨a₁, ha₁, he₁⟩ := h.trans _ (h.mul_mem_diagSet hu hu1 hw hw1)
  obtain ⟨a₂, ha₂, he₂⟩ := h.trans _ (h.mul_mem_diagSet hu hu1 hw' hw'1)
  set a := a₂ * a₁⁻¹ with hadef
  have ha : a ∈ A ⊓ normalizer (J : Set G) := mul_mem ha₂ (inv_mem ha₁)
  have hauw : a * (u * w) * a⁻¹ = u * w' := by
    rw [← he₁, ← he₂, hadef]
    group
  obtain ⟨k₁, k₂, hc⟩ := h.gen a ha
  set c := (y₁ ^ k₁ * y₂ ^ k₂)⁻¹ * a with hcdef
  have hac : a = y₁ ^ k₁ * y₂ ^ k₂ * c := by rw [hcdef]; group
  have hcuw : c * (u * w) * c⁻¹ = u * w := by
    have := (mem_centralizer_iff.mp hc) (u * w) (mul_mem (h.U_le hu) (h.W_le hw))
    rw [← this]
    group
  have hy₂w : y₂ ^ k₂ * w * (y₂ ^ k₂)⁻¹ = w := by
    have := (mem_centralizer_iff.mp (pow_mem h.y₂_cent k₂)) w hw
    rw [← this]
    group
  have hy₁u : y₁ ^ k₁ * (y₂ ^ k₂ * u * (y₂ ^ k₂)⁻¹) * (y₁ ^ k₁)⁻¹ =
      y₂ ^ k₂ * u * (y₂ ^ k₂)⁻¹ := by
    have hu₂ : y₂ ^ k₂ * u * (y₂ ^ k₂)⁻¹ ∈ U :=
      (mem_normalizer_iff.mp (pow_mem (h.normalizer_le_U h.y₂_mem) k₂) u).mp hu
    have := (mem_centralizer_iff.mp (pow_mem h.y₁_cent k₁)) _ hu₂
    rw [← this]
    group
  have hu₂ : y₂ ^ k₂ * u * (y₂ ^ k₂)⁻¹ ∈ U :=
    (mem_normalizer_iff.mp (pow_mem (h.normalizer_le_U h.y₂_mem) k₂) u).mp hu
  have hw₂ : y₁ ^ k₁ * w * (y₁ ^ k₁)⁻¹ ∈ W :=
    (mem_normalizer_iff.mp (pow_mem (h.normalizer_le_W h.y₁_mem) k₁) w).mp hw
  have hcalc : a * (u * w) * a⁻¹ =
      (y₂ ^ k₂ * u * (y₂ ^ k₂)⁻¹) * (y₁ ^ k₁ * w * (y₁ ^ k₁)⁻¹) := by
    calc a * (u * w) * a⁻¹ = y₁ ^ k₁ * y₂ ^ k₂ * (c * (u * w) * c⁻¹) * (y₂ ^ k₂)⁻¹ *
          (y₁ ^ k₁)⁻¹ := by rw [hac]; group
      _ = y₁ ^ k₁ * ((y₂ ^ k₂ * u * (y₂ ^ k₂)⁻¹) * (y₂ ^ k₂ * w * (y₂ ^ k₂)⁻¹)) *
          (y₁ ^ k₁)⁻¹ := by rw [hcuw]; group
      _ = (y₁ ^ k₁ * (y₂ ^ k₂ * u * (y₂ ^ k₂)⁻¹) * (y₁ ^ k₁)⁻¹) *
          (y₁ ^ k₁ * w * (y₁ ^ k₁)⁻¹) := by rw [hy₂w]; group
      _ = _ := by rw [hy₁u]
  rw [hauw] at hcalc
  have he := (h.eq_of_mul_eq hu hu₂ hw' hw₂ hcalc).2
  refine ⟨(y₁ ^ k₁)⁻¹, inv_mem (pow_mem (mem_zpowers y₁) k₁), ?_⟩
  rw [inv_inv, he]

theorem trans_U {u u' : G} (hu : u ∈ U) (hu1 : u ≠ 1) (hu' : u' ∈ U) (hu'1 : u' ≠ 1) :
    ∃ a ∈ zpowers y₂, a⁻¹ * u * a = u' := by
  obtain ⟨w, hw, hw1, -⟩ := exists_ne_ne_of_three_le h.three_le_W 1 1
  obtain ⟨a₁, ha₁, he₁⟩ := h.trans _ (h.mul_mem_diagSet hu hu1 hw hw1)
  obtain ⟨a₂, ha₂, he₂⟩ := h.trans _ (h.mul_mem_diagSet hu' hu'1 hw hw1)
  set a := a₂ * a₁⁻¹ with hadef
  have ha : a ∈ A ⊓ normalizer (J : Set G) := mul_mem ha₂ (inv_mem ha₁)
  have hauw : a * (u * w) * a⁻¹ = u' * w := by
    rw [← he₁, ← he₂, hadef]
    group
  obtain ⟨k₁, k₂, hc⟩ := h.gen a ha
  set c := (y₁ ^ k₁ * y₂ ^ k₂)⁻¹ * a with hcdef
  have hac : a = y₁ ^ k₁ * y₂ ^ k₂ * c := by rw [hcdef]; group
  have hcuw : c * (u * w) * c⁻¹ = u * w := by
    have := (mem_centralizer_iff.mp hc) (u * w) (mul_mem (h.U_le hu) (h.W_le hw))
    rw [← this]
    group
  have hy₂w : y₂ ^ k₂ * w * (y₂ ^ k₂)⁻¹ = w := by
    have := (mem_centralizer_iff.mp (pow_mem h.y₂_cent k₂)) w hw
    rw [← this]
    group
  have hu₂ : y₂ ^ k₂ * u * (y₂ ^ k₂)⁻¹ ∈ U :=
    (mem_normalizer_iff.mp (pow_mem (h.normalizer_le_U h.y₂_mem) k₂) u).mp hu
  have hy₁u : y₁ ^ k₁ * (y₂ ^ k₂ * u * (y₂ ^ k₂)⁻¹) * (y₁ ^ k₁)⁻¹ =
      y₂ ^ k₂ * u * (y₂ ^ k₂)⁻¹ := by
    have := (mem_centralizer_iff.mp (pow_mem h.y₁_cent k₁)) _ hu₂
    rw [← this]
    group
  have hw₂ : y₁ ^ k₁ * w * (y₁ ^ k₁)⁻¹ ∈ W :=
    (mem_normalizer_iff.mp (pow_mem (h.normalizer_le_W h.y₁_mem) k₁) w).mp hw
  have hcalc : a * (u * w) * a⁻¹ =
      (y₂ ^ k₂ * u * (y₂ ^ k₂)⁻¹) * (y₁ ^ k₁ * w * (y₁ ^ k₁)⁻¹) := by
    calc a * (u * w) * a⁻¹ = y₁ ^ k₁ * y₂ ^ k₂ * (c * (u * w) * c⁻¹) * (y₂ ^ k₂)⁻¹ *
          (y₁ ^ k₁)⁻¹ := by rw [hac]; group
      _ = y₁ ^ k₁ * ((y₂ ^ k₂ * u * (y₂ ^ k₂)⁻¹) * (y₂ ^ k₂ * w * (y₂ ^ k₂)⁻¹)) *
          (y₁ ^ k₁)⁻¹ := by rw [hcuw]; group
      _ = (y₁ ^ k₁ * (y₂ ^ k₂ * u * (y₂ ^ k₂)⁻¹) * (y₁ ^ k₁)⁻¹) *
          (y₁ ^ k₁ * w * (y₁ ^ k₁)⁻¹) := by rw [hy₂w]; group
      _ = _ := by rw [hy₁u]
  rw [hauw] at hcalc
  have he := (h.eq_of_mul_eq hu' hu₂ hw hw₂ hcalc).1
  refine ⟨(y₂ ^ k₂)⁻¹, inv_mem (pow_mem (mem_zpowers y₂) k₂), ?_⟩
  rw [inv_inv, he]

end DiagData

theorem le_of_forall_ne {U Q : Subgroup G} (hU : 3 ≤ Nat.card U) {z₀ : G}
    (hQ : ∀ z ∈ U, z ≠ z₀ → z ∈ Q) : U ≤ Q := by
  intro z hz
  by_cases hz0 : z = z₀
  · obtain ⟨v, hv, hv1, hvz⟩ := exists_ne_ne_of_three_le hU 1 z₀
    have h1 : v ∈ Q := hQ v hv hvz
    have h2 : v⁻¹ * z ∈ Q := by
      refine hQ _ (mul_mem (inv_mem hv) hz) fun h3 => hv1 ?_
      rw [hz0] at h3
      have h4 : v⁻¹ = 1 := by
        calc v⁻¹ = v⁻¹ * z₀ * z₀⁻¹ := by group
          _ = 1 := by rw [h3]; group
      exact inv_eq_one.mp h4
    have h3 : z = v * (v⁻¹ * z) := by group
    rw [h3]
    exact mul_mem h1 h2
  · exact hQ z hz hz0

theorem le_of_forall_conj_le {U W Q : Subgroup G} {y₁ y₂ τ u w : G}
    (hcomm : ∀ x ∈ U, ∀ z ∈ W, x * z = z * x) (hu : u ∈ U) (hw : w ∈ W)
    (hU3 : 3 ≤ Nat.card U) (hW3 : 3 ≤ Nat.card W)
    (hy₁τ : y₁ * τ = τ * y₁) (hy₂τ : y₂ * τ = τ * y₂) (hy₁U : y₁ ∈ centralizer (U : Set G))
    (hy₂W : y₂ ∈ centralizer (W : Set G))
    (htU : ∀ u' ∈ U, u' ≠ 1 → ∃ a ∈ zpowers y₂, a⁻¹ * u * a = u')
    (htW : ∀ w' ∈ W, w' ≠ 1 → ∃ a ∈ zpowers y₁, a⁻¹ * w * a = w')
    (hrQ : τ * u * w ∈ Q)
    (hQ : ∀ a ∈ (zpowers y₁ : Set G) ∪ zpowers y₂, a⁻¹ * (τ * u * w) * a ∈ Q) :
    U ≤ Q ∧ W ≤ Q := by
  constructor
  · refine le_of_forall_ne hU3 (z₀ := u⁻¹) fun z hz hz0 => ?_
    have hz' : u * z ≠ 1 := fun h1 => hz0 (eq_inv_of_mul_eq_one_right h1)
    obtain ⟨a, ha, hau⟩ := htU (u * z) (mul_mem hu hz) hz'
    have haτ : a⁻¹ * τ * a = τ := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
      have hc : Commute (y₂ ^ k) τ := Commute.zpow_left hy₂τ k
      rw [mul_assoc, ← hc.eq]
      group
    have haw : a⁻¹ * w * a = w := by
      have hc := (mem_centralizer_iff.mp ((zpowers_le.mpr hy₂W) ha)) w hw
      calc a⁻¹ * w * a = a⁻¹ * (w * a) := by group
        _ = a⁻¹ * (a * w) := by rw [hc]
        _ = w := by group
    have h1 := hQ a (Or.inr ha)
    have h2 : a⁻¹ * (τ * u * w) * a = τ * (u * z) * w := by
      calc a⁻¹ * (τ * u * w) * a = (a⁻¹ * τ * a) * (a⁻¹ * u * a) * (a⁻¹ * w * a) := by group
        _ = τ * (u * z) * w := by rw [haτ, hau, haw]
    rw [h2] at h1
    have h3 : (τ * u * w)⁻¹ * (τ * (u * z) * w) = z := by
      have hzw : z * w = w * z := hcomm z hz w hw
      calc (τ * u * w)⁻¹ * (τ * (u * z) * w) = w⁻¹ * (z * w) := by group
        _ = z := by rw [hzw]; group
    rw [← h3]
    exact mul_mem (inv_mem hrQ) h1
  · refine le_of_forall_ne hW3 (z₀ := w⁻¹) fun z hz hz0 => ?_
    have hz' : w * z ≠ 1 := fun h1 => hz0 (eq_inv_of_mul_eq_one_right h1)
    obtain ⟨a, ha, haw⟩ := htW (w * z) (mul_mem hw hz) hz'
    have haτ : a⁻¹ * τ * a = τ := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
      have hc : Commute (y₁ ^ k) τ := Commute.zpow_left hy₁τ k
      rw [mul_assoc, ← hc.eq]
      group
    have hau : a⁻¹ * u * a = u := by
      have hc := (mem_centralizer_iff.mp ((zpowers_le.mpr hy₁U) ha)) u hu
      calc a⁻¹ * u * a = a⁻¹ * (u * a) := by group
        _ = a⁻¹ * (a * u) := by rw [hc]
        _ = u := by group
    have h1 := hQ a (Or.inl ha)
    have h2 : a⁻¹ * (τ * u * w) * a = τ * u * (w * z) := by
      calc a⁻¹ * (τ * u * w) * a = (a⁻¹ * τ * a) * (a⁻¹ * u * a) * (a⁻¹ * w * a) := by group
        _ = τ * u * (w * z) := by rw [haτ, hau, haw]
    rw [h2] at h1
    have h3 : (τ * u * w)⁻¹ * (τ * u * (w * z)) = z := by group
    rw [← h3]
    exact mul_mem (inv_mem hrQ) h1

end CFSG.ComponentClassification.RankTwoClassical
