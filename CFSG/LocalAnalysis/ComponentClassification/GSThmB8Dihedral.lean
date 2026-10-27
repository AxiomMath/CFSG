module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.ComponentClassification.GSThmB

open Subgroup

namespace Eight

theorem dihedral4_commutator_central : ∀ x y g : DihedralGroup 4,
    g * (x⁻¹ * y⁻¹ * x * y) = (x⁻¹ * y⁻¹ * x * y) * g := by decide

theorem dihedral4_involutions : ∀ x y : DihedralGroup 4, x * x = 1 → y * y = 1 → x * y = y * x →
    (∀ g : DihedralGroup 4, g * x = x * g) ∨ (∀ g : DihedralGroup 4, g * y = y * g) ∨
      ∀ g : DihedralGroup 4, g * (x⁻¹ * y) = (x⁻¹ * y) * g := by decide

variable {Y : Type*} [Group Y]

theorem commutator_central_of_dihedral {D : Subgroup Y} (e : ↥D ≃* DihedralGroup 4) {x y g : Y}
    (hx : x ∈ D) (hy : y ∈ D) (hg : g ∈ D) :
    g * (x⁻¹ * y⁻¹ * x * y) = (x⁻¹ * y⁻¹ * x * y) * g := by
  have h := dihedral4_commutator_central (e ⟨x, hx⟩) (e ⟨y, hy⟩) (e ⟨g, hg⟩)
  simp only [← map_inv, ← map_mul] at h
  exact congrArg Subtype.val (e.injective h)

theorem involutions_of_dihedral {D : Subgroup Y} (e : ↥D ≃* DihedralGroup 4) {x y : Y}
    (hx : x ∈ D) (hy : y ∈ D) (hx2 : x * x = 1) (hy2 : y * y = 1) (hxy : x * y = y * x) :
    (∀ g ∈ D, g * x = x * g) ∨ (∀ g ∈ D, g * y = y * g) ∨
      ∀ g ∈ D, g * (x⁻¹ * y) = (x⁻¹ * y) * g := by
  have hx2' : e ⟨x, hx⟩ * e ⟨x, hx⟩ = 1 := by
    rw [← map_mul, show (⟨x, hx⟩ : ↥D) * ⟨x, hx⟩ = 1 from Subtype.ext hx2, map_one]
  have hy2' : e ⟨y, hy⟩ * e ⟨y, hy⟩ = 1 := by
    rw [← map_mul, show (⟨y, hy⟩ : ↥D) * ⟨y, hy⟩ = 1 from Subtype.ext hy2, map_one]
  have hxy' : e ⟨x, hx⟩ * e ⟨y, hy⟩ = e ⟨y, hy⟩ * e ⟨x, hx⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext hxy)
  have key : ∀ (u : ↥D), (∀ g : DihedralGroup 4, g * e u = e u * g) → ∀ g ∈ D, g * u = u * g := by
    intro u hu g hg
    have := hu (e ⟨g, hg⟩)
    rw [← map_mul, ← map_mul] at this
    exact congrArg Subtype.val (e.injective this)
  rcases dihedral4_involutions _ _ hx2' hy2' hxy' with h1 | h1 | h1
  · exact Or.inl (key ⟨x, hx⟩ h1)
  · exact Or.inr (Or.inl (key ⟨y, hy⟩ h1))
  · refine Or.inr (Or.inr (key (⟨x, hx⟩⁻¹ * ⟨y, hy⟩) ?_))
    simpa only [map_mul, map_inv] using h1

theorem eq_of_mul_eq_mul {D₁ D₂ : Subgroup Y} (hD : D₁ ⊓ D₂ = ⊥) {a a' b b' : Y} (ha : a ∈ D₁)
    (ha' : a' ∈ D₁) (hb : b ∈ D₂) (hb' : b' ∈ D₂) (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ D₁ ⊓ D₂ :=
    Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem ha') ha, h1 ▸ mul_mem hb' (inv_mem hb)⟩
  rw [hD, mem_bot] at h2
  have h3 : a = a' := by
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' := by rw [h2, mul_one]
  subst h3
  exact ⟨rfl, mul_left_cancel h⟩

theorem components_mul_self {D₁ D₂ : Subgroup Y} (hD : D₁ ⊓ D₂ = ⊥)
    (hcomm : ∀ a ∈ D₁, ∀ b ∈ D₂, a * b = b * a) {a b : Y} (ha : a ∈ D₁) (hb : b ∈ D₂)
    (h : (a * b) * (a * b) = 1) : a * a = 1 ∧ b * b = 1 := by
  have h1 : (a * a) * (b * b) = 1 * 1 := by
    rw [mul_one, ← h]
    calc a * a * (b * b) = a * (a * b) * b := by group
      _ = a * (b * a) * b := by rw [hcomm a ha b hb]
      _ = a * b * (a * b) := by group
  exact eq_of_mul_eq_mul hD (mul_mem ha ha) (one_mem _) (mul_mem hb hb) (one_mem _) h1

theorem components_comm {D₁ D₂ : Subgroup Y} (hD : D₁ ⊓ D₂ = ⊥)
    (hcomm : ∀ a ∈ D₁, ∀ b ∈ D₂, a * b = b * a) {a b a' b' : Y} (ha : a ∈ D₁) (hb : b ∈ D₂)
    (ha' : a' ∈ D₁) (hb' : b' ∈ D₂) (h : (a * b) * (a' * b') = (a' * b') * (a * b)) :
    a * a' = a' * a ∧ b * b' = b' * b := by
  have h1 : (a * a') * (b * b') = (a' * a) * (b' * b) := by
    calc a * a' * (b * b') = a * (a' * b) * b' := by group
      _ = a * (b * a') * b' := by rw [hcomm a' ha' b hb]
      _ = a * b * (a' * b') := by group
      _ = a' * b' * (a * b) := h
      _ = a' * (b' * a) * b := by group
      _ = a' * (a * b') * b := by rw [hcomm a ha b' hb']
      _ = a' * a * (b' * b) := by group
  exact eq_of_mul_eq_mul hD (mul_mem ha ha') (mul_mem ha' ha) (mul_mem hb hb')
    (mul_mem hb' hb) h1

theorem exists_mul_of_mem_sup_comm {D₁ D₂ : Subgroup Y}
    (hcomm : ∀ a ∈ D₁, ∀ b ∈ D₂, a * b = b * a) {g : Y} (hg : g ∈ D₁ ⊔ D₂) :
    ∃ a ∈ D₁, ∃ b ∈ D₂, g = a * b := by
  let S : Subgroup Y :=
    { carrier := {g | ∃ a ∈ D₁, ∃ b ∈ D₂, g = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [hcomm a' ha' b hb]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, (mul_one 1).symm⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
        rw [mul_inv_rev, hcomm a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)] }
  have hle : D₁ ⊔ D₂ ≤ S := sup_le (fun a ha => ⟨a, ha, 1, one_mem _, (mul_one a).symm⟩)
    (fun b hb => ⟨1, one_mem _, b, hb, (one_mul b).symm⟩)
  exact hle hg

theorem exists_noncentral_commutator_le [Finite Y] {D₁ D₂ : Subgroup Y}
    (hD : D₁ ⊓ D₂ = ⊥) (hc : D₁ ≤ centralizer (D₂ : Set Y))
    (e₁ : ↥D₁ ≃* DihedralGroup 4) (e₂ : ↥D₂ ≃* DihedralGroup 4) {z₁ : Y}
    (hz₁ : center D₁ = (zpowers z₁).subgroupOf D₁) {A : Subgroup Y} (hA : A ≤ D₁ ⊔ D₂)
    (hA2 : ∀ y ∈ A, y * y = 1) (hA8 : 8 ≤ Nat.card A) {w : Y}
    (hAZ : ∀ y ∈ A, (∀ r ∈ D₁ ⊔ D₂, y * r = r * y) → y = 1 ∨ y = w) :
    ∃ y ∈ A, (∃ r ∈ D₁ ⊔ D₂, y * r ≠ r * y) ∧
      ∀ r ∈ D₁ ⊔ D₂, y⁻¹ * r⁻¹ * y * r ∈ zpowers z₁ := by
  have hcomm : ∀ a ∈ D₁, ∀ b ∈ D₂, a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.mp (hc ha) b hb).symm
  set Z₂ : Subgroup Y := (center ↥D₂).map D₂.subtype with hZ₂
  have hZ₂D : Z₂ ≤ D₂ := map_subtype_le _
  have hmemZ₂ : ∀ c ∈ D₂, (∀ g ∈ D₂, g * c = c * g) → c ∈ Z₂ := by
    intro c hc' hcen
    refine ⟨⟨c, hc'⟩, ?_, rfl⟩
    show (⟨c, hc'⟩ : ↥D₂) ∈ center ↥D₂
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (hcen g g.2)
  have hZ₂cen : ∀ c ∈ Z₂, ∀ g ∈ D₂, g * c = c * g := by
    rintro _ ⟨c, hc', rfl⟩ g hg
    exact congrArg Subtype.val (mem_center_iff.mp hc' ⟨g, hg⟩)
  have hcomm' : ∀ a ∈ D₁, ∀ b ∈ Z₂, a * b = b * a := fun a ha b hb => hcomm a ha b (hZ₂D hb)
  set A' : Subgroup Y := A ⊓ (D₁ ⊔ Z₂) with hA'
  have hAc : ∀ y ∈ A, ∀ y' ∈ A, y * y' = y' * y := by
    intro y hy y' hy'
    have h1 := hA2 _ (mul_mem hy hy')
    have h2 := hA2 _ hy
    have h3 := hA2 _ hy'
    rw [(inv_eq_of_mul_eq_one_right h1).symm, mul_inv_rev, inv_eq_of_mul_eq_one_right h2,
      inv_eq_of_mul_eq_one_right h3]
  have key : ∀ y ∈ A, y ∉ A' → ∀ y' ∈ A, y' ∉ A' → y * y' ∈ A' := by
    intro y hy hyA' y' hy' hyA''
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := exists_mul_of_mem_sup_comm hcomm (hA hy)
    obtain ⟨y₁', hy₁', y₂', hy₂', rfl⟩ := exists_mul_of_mem_sup_comm hcomm (hA hy')
    have hnc : ∀ {u v : Y}, u ∈ D₁ → v ∈ D₂ → u * v ∈ A → u * v ∉ A' →
        ¬ ∀ g ∈ D₂, g * v = v * g := by
      intro u v hu hv huv huvA hcen
      exact huvA ⟨huv, mul_mem_sup hu (hmemZ₂ v hv hcen)⟩
    have hsq := (components_mul_self hD hcomm hy₁ hy₂ (hA2 _ hy)).2
    have hsq' := (components_mul_self hD hcomm hy₁' hy₂' (hA2 _ hy')).2
    have hcm := (components_comm hD hcomm hy₁ hy₂ hy₁' hy₂' (hAc _ hy _ hy')).2
    rcases involutions_of_dihedral e₂ hy₂ hy₂' hsq hsq' hcm with h1 | h1 | h1
    · exact absurd h1 (hnc hy₁ hy₂ hy hyA')
    · exact absurd h1 (hnc hy₁' hy₂' hy' hyA'')
    · refine ⟨mul_mem hy hy', ?_⟩
      have hc2 : y₂⁻¹ * y₂' ∈ Z₂ := hmemZ₂ _ (mul_mem (inv_mem hy₂) hy₂') h1
      have hy2inv : y₂⁻¹ = y₂ := inv_eq_of_mul_eq_one_right hsq
      have : y₁ * y₂ * (y₁' * y₂') = (y₁ * y₁') * (y₂⁻¹ * y₂') := by
        rw [hy2inv]
        calc y₁ * y₂ * (y₁' * y₂') = y₁ * (y₂ * y₁') * y₂' := by group
          _ = y₁ * (y₁' * y₂) * y₂' := by rw [hcomm y₁' hy₁' y₂ hy₂]
          _ = y₁ * y₁' * (y₂ * y₂') := by group
      rw [this]
      exact mul_mem_sup (mul_mem hy₁ hy₁') hc2
  have hcard : Nat.card A ≤ 2 * Nat.card A' := by
    classical
    by_cases hex : ∃ y₀ ∈ A, y₀ ∉ A'
    · obtain ⟨y₀, hy₀, hy₀A'⟩ := hex
      let f : ↥A → Bool × ↥A' := fun y =>
        if hy : (y : Y) ∈ A' then (true, ⟨y, hy⟩)
        else (false, ⟨y₀ * y, key y₀ hy₀ hy₀A' y y.2 hy⟩)
      have hf : Function.Injective f := by
        intro u v huv
        simp only [f] at huv
        by_cases hu : (u : Y) ∈ A' <;> by_cases hv : (v : Y) ∈ A' <;>
          simp only [hu, hv, dite_true, dite_false, Prod.mk.injEq, Bool.false_eq_true,
            Bool.true_eq_false, false_and] at huv
        · have h1 := congrArg Subtype.val huv.2
          exact Subtype.ext h1
        · have h1 := congrArg Subtype.val huv.2
          exact Subtype.ext (mul_left_cancel h1)
      have := Nat.card_le_card_of_injective f hf
      rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
    · push Not at hex
      have hle : A ≤ A' := fun y hy => hex y hy
      calc Nat.card A ≤ Nat.card A' := card_le_of_le hle
        _ ≤ 2 * Nat.card A' := by omega
  have hex : ∃ y ∈ A', ∃ r ∈ D₁ ⊔ D₂, y * r ≠ r * y := by
    by_contra hall
    push Not at hall
    have hsub : (A' : Set Y) ⊆ {1, w} := fun y hy => hAZ y hy.1 (hall y hy)
    have h1 : Nat.card A' ≤ 2 := by
      calc Nat.card A' = (A' : Set Y).ncard := (Nat.card_coe_set_eq _).symm
        _ ≤ ({1, w} : Set Y).ncard := Set.ncard_le_ncard hsub
        _ ≤ ({w} : Set Y).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    omega
  obtain ⟨y, hy, hyr⟩ := hex
  refine ⟨y, hy.1, hyr, fun r hr => ?_⟩
  obtain ⟨y₁, hy₁, c, hc', rfl⟩ := exists_mul_of_mem_sup_comm hcomm' hy.2
  obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := exists_mul_of_mem_sup_comm hcomm hr
  have hk : y₁⁻¹ * r₁⁻¹ * y₁ * r₁ ∈ D₁ :=
    mul_mem (mul_mem (mul_mem (inv_mem hy₁) (inv_mem hr₁)) hy₁) hr₁
  have e1 : r₂ * y₁ = y₁ * r₂ := (hcomm y₁ hy₁ r₂ hr₂).symm
  have e2 : c * (y₁⁻¹ * r₁⁻¹ * y₁ * r₁) = (y₁⁻¹ * r₁⁻¹ * y₁ * r₁) * c := (hcomm' _ hk c hc').symm
  have e3 : r₂ * (y₁⁻¹ * r₁⁻¹ * y₁ * r₁) = (y₁⁻¹ * r₁⁻¹ * y₁ * r₁) * r₂ :=
    (hcomm _ hk r₂ hr₂).symm
  have e4 : r₂ * c = c * r₂ := hZ₂cen c hc' r₂ hr₂
  have e5 : r₁ * c = c * r₁ := hcomm' r₁ hr₁ c hc'
  have main : y₁ * c * (r₁ * r₂) = r₁ * r₂ * (y₁ * c) * (y₁⁻¹ * r₁⁻¹ * y₁ * r₁) := by
    have l1 : y₁ * c * (r₁ * r₂) = y₁ * r₁ * r₂ * c := by
      calc y₁ * c * (r₁ * r₂) = y₁ * (c * r₁) * r₂ := by group
        _ = y₁ * (r₁ * c) * r₂ := by rw [e5]
        _ = y₁ * r₁ * (c * r₂) := by group
        _ = y₁ * r₁ * (r₂ * c) := by rw [e4]
        _ = y₁ * r₁ * r₂ * c := by group
    have l2 : r₁ * r₂ * (y₁ * c) * (y₁⁻¹ * r₁⁻¹ * y₁ * r₁) = y₁ * r₁ * r₂ * c := by
      calc r₁ * r₂ * (y₁ * c) * (y₁⁻¹ * r₁⁻¹ * y₁ * r₁)
          = r₁ * (r₂ * y₁) * (c * (y₁⁻¹ * r₁⁻¹ * y₁ * r₁)) := by group
        _ = r₁ * (y₁ * r₂) * ((y₁⁻¹ * r₁⁻¹ * y₁ * r₁) * c) := by rw [e1, e2]
        _ = r₁ * y₁ * (r₂ * (y₁⁻¹ * r₁⁻¹ * y₁ * r₁)) * c := by group
        _ = r₁ * y₁ * ((y₁⁻¹ * r₁⁻¹ * y₁ * r₁) * r₂) * c := by rw [e3]
        _ = y₁ * r₁ * r₂ * c := by group
    rw [l1, l2]
  have hcomm_eq : (y₁ * c)⁻¹ * (r₁ * r₂)⁻¹ * (y₁ * c) * (r₁ * r₂) = y₁⁻¹ * r₁⁻¹ * y₁ * r₁ := by
    calc (y₁ * c)⁻¹ * (r₁ * r₂)⁻¹ * (y₁ * c) * (r₁ * r₂)
        = (y₁ * c)⁻¹ * (r₁ * r₂)⁻¹ * ((y₁ * c) * (r₁ * r₂)) := by group
      _ = (y₁ * c)⁻¹ * (r₁ * r₂)⁻¹ * (r₁ * r₂ * (y₁ * c) * (y₁⁻¹ * r₁⁻¹ * y₁ * r₁)) := by
          rw [main]
      _ = y₁⁻¹ * r₁⁻¹ * y₁ * r₁ := by group
  rw [hcomm_eq]
  have hcen : (⟨_, hk⟩ : ↥D₁) ∈ center D₁ := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (commutator_central_of_dihedral e₁ hy₁ hr₁ g.2)
  rw [hz₁] at hcen
  exact hcen

end Eight

end CFSG.ComponentClassification.GSThmB
