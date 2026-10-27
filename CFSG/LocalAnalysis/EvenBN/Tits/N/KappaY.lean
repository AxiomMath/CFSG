module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.KappaW

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits
open scoped Pointwise commutatorElement

namespace KappaY

section Abstract

variable {G : Type*} [Group G]

theorem inv_conj_of_conj {a b c : G} (h : a * b * a⁻¹ = c) : a⁻¹ * c * a = b := by
  rw [← h]; group

theorem comm_of_conj_eq {g g' a : G} (h : g * a * g⁻¹ = g' * a * g'⁻¹) :
    a * (g'⁻¹ * g) = g'⁻¹ * g * a := by
  calc a * (g'⁻¹ * g) = g'⁻¹ * (g' * a * g'⁻¹) * g := by group
    _ = g'⁻¹ * (g * a * g⁻¹) * g := by rw [h]
    _ = g'⁻¹ * g * a := by group

theorem conj_eq_of_comm {g g' a : G} (h : a * (g'⁻¹ * g) = g'⁻¹ * g * a) :
    g * a * g⁻¹ = g' * a * g'⁻¹ := by
  calc g * a * g⁻¹ = g' * (g'⁻¹ * g * a) * g⁻¹ := by group
    _ = g' * (a * (g'⁻¹ * g)) * g⁻¹ := by rw [h]
    _ = g' * a * g'⁻¹ := by group

theorem sq_mul_comm {j w c : G} (hc : c = w * j * w⁻¹ * j⁻¹) (hjc : j * c = c * j) :
    (j * w) * (j * w) = c * (j * j) * (w * w) := by
  have h1 : w * j = c * j * w := by rw [hc]; group
  calc (j * w) * (j * w) = j * (w * j) * w := by group
    _ = j * (c * j * w) * w := by rw [h1]
    _ = (j * c) * j * (w * w) := by group
    _ = (c * j) * j * (w * w) := by rw [hjc]
    _ = c * (j * j) * (w * w) := by group

theorem zpowers_cases {a x : G} (ha : a * a = 1) (hx : x ∈ zpowers a) : x = 1 ∨ x = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
  · left
    rw [zpow_mul]
    simp [zpow_ofNat, sq, ha]
  · right
    rw [zpow_add, zpow_mul]
    simp [zpow_ofNat, sq, ha]

theorem conj_g {x y u u' : G} (hu : y⁻¹ * u * y = u') (hx : x * u' = u' * x) :
    y * x * y⁻¹ * u * (y * x * y⁻¹)⁻¹ = u := by
  have hx' : x * u' * x⁻¹ = u' := by rw [hx]; group
  calc y * x * y⁻¹ * u * (y * x * y⁻¹)⁻¹ = y * (x * (y⁻¹ * u * y) * x⁻¹) * y⁻¹ := by group
    _ = y * (x * u' * x⁻¹) * y⁻¹ := by rw [hu]
    _ = y * u' * y⁻¹ := by rw [hx']
    _ = u := by rw [← hu]; group

theorem act_F (F : Subgroup G) (x y v11 z : G) (hyF : ∀ f ∈ F, y⁻¹ * f * y ∈ F)
    (hxF : ∀ f ∈ F, x * f * x⁻¹ = f ∨ x * f * x⁻¹ = v11 * f) (hyv : y * v11 * y⁻¹ = z) {f : G}
    (hf : f ∈ F) :
    y * x * y⁻¹ * f * (y * x * y⁻¹)⁻¹ = f ∨ y * x * y⁻¹ * f * (y * x * y⁻¹)⁻¹ = z * f := by
  have e : y * x * y⁻¹ * f * (y * x * y⁻¹)⁻¹ = y * (x * (y⁻¹ * f * y) * x⁻¹) * y⁻¹ := by group
  rw [e]
  rcases hxF _ (hyF f hf) with h | h
  · left
    rw [h]
    group
  · right
    rw [h]
    calc y * (v11 * (y⁻¹ * f * y)) * y⁻¹ = (y * v11 * y⁻¹) * f := by group
      _ = z * f := by rw [hyv]

theorem final_cases {v10 v11 z u w : G} (hz2 : z * z = 1) (hc : v10 * z = z * v10)
    (hne1 : v11 ≠ 1) (hnez : v11 ≠ z) (h10 : v10 ≠ v11) (h10' : v10 ≠ v11 * z)
    (hu : u = 1 ∨ u = z) (hw : w = 1 ∨ w = z ∨ w = v10 ∨ w = v10 * z) : v11 * z ≠ u * w := by
  intro h
  rcases hu with hu | hu <;> rcases hw with hw | hw | hw | hw <;> rw [hu, hw] at h
  ·
    apply hnez
    calc v11 = v11 * (z * z) := by rw [hz2, mul_one]
      _ = (v11 * z) * z := by group
      _ = z := by rw [h]; group
  ·
    exact hne1 (mul_right_cancel h)
  ·
    exact h10' (by rw [h]; group)
  ·
    exact h10 (mul_right_cancel (b := z) (by rw [h]; group)).symm
  ·
    apply hne1
    exact mul_right_cancel (b := z) (by rw [h]; group)
  ·
    exact hnez (mul_right_cancel h)
  ·
    exact h10 (mul_right_cancel (b := z) (by rw [h, hc])).symm
  ·
    apply h10'
    rw [h]
    symm
    calc z * (v10 * z) = (z * v10) * z := by group
      _ = (v10 * z) * z := by rw [← hc]
      _ = v10 * (z * z) := by group
      _ = v10 := by rw [hz2, mul_one]

theorem sq_cmp (F : Subgroup G) (t v10 z g g' : G) (hF2 : ∀ a ∈ F, a * a = 1)
    (hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) (ht2 : t * t = 1) (htF : ∀ a ∈ F, t * a = a * t)
    (hCB : ∀ h : G, (∀ a ∈ F, h * a = a * h) → h * t = t * h → h ∈ F ⊔ zpowers t)
    (hv10 : v10 ∈ F) (hz : z ∈ F) (hgt : g * t * g⁻¹ = t * v10)
    (hg't : g' * t * g'⁻¹ = t * v10) (hag : ∀ f ∈ F, g * f * g⁻¹ = g' * f * g'⁻¹)
    (hgF : ∀ f ∈ F, g * f * g⁻¹ = f ∨ g * f * g⁻¹ = z * f) (hg'z : g' * z * g'⁻¹ = z)
    (hg'10 : g' * v10 * g'⁻¹ = v10) :
    ∃ w, (w = 1 ∨ w = z ∨ w = v10 ∨ w = v10 * z) ∧ g * g = g' * g' * w := by
  have hz2 : z * z = 1 := hF2 z hz
  have h102 : v10 * v10 = 1 := hF2 v10 hv10
  have hg'z' : g'⁻¹ * z * g' = z := inv_conj_of_conj hg'z
  have hg'10' : g'⁻¹ * v10 * g' = v10 := inv_conj_of_conj hg'10
  have hg't' : g'⁻¹ * (t * v10) * g' = t := inv_conj_of_conj hg't
  have hg'ti : g'⁻¹ * t * g' = t * v10 := by
    calc g'⁻¹ * t * g' = g'⁻¹ * (t * v10) * g' * (g'⁻¹ * v10 * g') := by
          calc g'⁻¹ * t * g' = g'⁻¹ * (t * (v10 * v10)) * g' := by rw [h102, mul_one]
            _ = _ := by group
      _ = t * v10 := by rw [hg't', hg'10']
  obtain ⟨h, hh⟩ : ∃ h : G, h = g'⁻¹ * g := ⟨_, rfl⟩
  have hg : g = g' * h := by rw [hh]; group
  have hhF : ∀ a ∈ F, h * a = a * h := fun a ha => by
    rw [hh]
    exact (comm_of_conj_eq (hag a ha)).symm
  have hht : h * t = t * h := by
    calc h * t = g'⁻¹ * (g * t * g⁻¹) * g := by rw [hh]; group
      _ = g'⁻¹ * (t * v10) * g := by rw [hgt]
      _ = (g'⁻¹ * (t * v10) * g') * (g'⁻¹ * g) := by group
      _ = t * h := by rw [hg't', hh]
  obtain ⟨f, hf, hft⟩ := KappaW.mem_sup_zpowers_cases hF2 ht2 htF (hCB h hhF hht)
  have hconj : ∀ a ∈ F, g'⁻¹ * a * g' = a ∨ g'⁻¹ * a * g' = z * a := by
    intro a ha
    rcases hgF a ha with h1 | h1
    · left
      exact inv_conj_of_conj ((hag a ha).symm.trans h1)
    · right
      have h2 : g' * a * g'⁻¹ = z * a := (hag a ha).symm.trans h1
      have h3 : g'⁻¹ * (z * a) * g' = a := inv_conj_of_conj h2
      have h4 : z * (g'⁻¹ * a * g') = a := by
        calc z * (g'⁻¹ * a * g') = (g'⁻¹ * z * g') * (g'⁻¹ * a * g') := by rw [hg'z']
          _ = g'⁻¹ * (z * a) * g' := by group
          _ = a := h3
      calc g'⁻¹ * a * g' = z * (z * (g'⁻¹ * a * g')) := by rw [← mul_assoc, hz2, one_mul]
        _ = z * a := by rw [h4]
  have hsq : g * g = g' * g' * (g'⁻¹ * h * g' * h) := by rw [hg]; group
  rcases hft with hft | hft
  · rcases hconj f hf with h1 | h1
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [hsq, hft, h1, hF2 f hf]
    · refine ⟨z, Or.inr (Or.inl rfl), ?_⟩
      rw [hsq, hft, h1]
      calc g' * g' * (z * f * f) = g' * g' * (z * (f * f)) := by group
        _ = g' * g' * z := by rw [hF2 f hf, mul_one]
  · have hjt : g'⁻¹ * (f * t) * g' = (g'⁻¹ * f * g') * (t * v10) := by
      calc g'⁻¹ * (f * t) * g' = (g'⁻¹ * f * g') * (g'⁻¹ * t * g') := by group
        _ = _ := by rw [hg'ti]
    have key : f * (t * v10) * (f * t) = v10 := by
      have htv : t * v10 = v10 * t := htF v10 hv10
      have htf : t * f = f * t := htF f hf
      have hfv : f * v10 = v10 * f := hFc f hf v10 hv10
      calc f * (t * v10) * (f * t) = f * (v10 * t) * (f * t) := by rw [htv]
        _ = f * v10 * (t * f) * t := by group
        _ = f * v10 * (f * t) * t := by rw [htf]
        _ = (f * v10 * f) * (t * t) := by group
        _ = (v10 * f * f) * (t * t) := by rw [hfv]
        _ = v10 := by rw [mul_assoc v10 f f, hF2 f hf, mul_one, ht2, mul_one]
    rcases hconj f hf with h1 | h1
    · refine ⟨v10, Or.inr (Or.inr (Or.inl rfl)), ?_⟩
      rw [hsq, hft, hjt, h1, key]
    · refine ⟨v10 * z, Or.inr (Or.inr (Or.inr rfl)), ?_⟩
      have e2 : z * f * (t * v10) * (f * t) = v10 * z := by
        calc z * f * (t * v10) * (f * t) = z * (f * (t * v10) * (f * t)) := by group
          _ = z * v10 := by rw [key]
          _ = v10 * z := hFc z hz v10 hv10
      rw [hsq, hft, hjt, h1, e2]

theorem main (F E : Subgroup G) (t v7 v8 v9 v10 v11 z x y j : G)
    (hE2 : ∀ a ∈ E, a * a = 1) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (h8E : v8 ∈ E) (h9E : v9 ∈ E) (h10E : v10 ∈ E) (h11E : v11 ∈ E) (hzE : z ∈ E)
    (hxE : ∀ a ∈ E, x * a = a * x) (hF2 : ∀ a ∈ F, a * a = 1)
    (hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) (h7F : v7 ∈ F) (h9F : v9 ∈ F) (h10F : v10 ∈ F)
    (h11F : v11 ∈ F) (hzF : z ∈ F)
    (hFgen : ∀ S : Subgroup G, v7 ∈ S → v9 ∈ S → v10 ∈ S → v11 ∈ S → z ∈ S → F ≤ S)
    (hFx : ∀ f ∈ F, x * f * x⁻¹ = f ∨ x * f * x⁻¹ = v11 * f) (ht2 : t * t = 1)
    (htF : ∀ a ∈ F, t * a = a * t) (h8t : v8 * t = t * v8)
    (hCB : ∀ h : G, (∀ a ∈ F, h * a = a * h) → h * t = t * h → h ∈ F ⊔ zpowers t)
    (hyF : ∀ f ∈ F, y⁻¹ * f * y ∈ F) (hyt : y * t = t * y) (hy10 : y * v10 = v10 * y)
    (hy11 : y * v11 * y⁻¹ = z) (hyz : y * z * y⁻¹ = v11 * z)
    (hy9 : x * (y⁻¹ * v9 * y) * x⁻¹ = v11 * (y⁻¹ * v9 * y))
    (hxt : x * t * x⁻¹ = t * v10) (hx7 : x * v7 * x⁻¹ = v11 * v7) (hx2 : x * x = z)
    (hjt : j * t = t * j) (hj7 : j * v7 * j⁻¹ = v7 * v11) (hj9 : j * v9 * j⁻¹ = v9 * z)
    (hj8 : j * v8 = v8 * j) (hj10 : j * v10 = v10 * j) (hj11 : j * v11 = v11 * j)
    (hjz : j * z = z * j) (hj2 : j * j = v10 * v11 * z)
    (hc : x * j * x⁻¹ * j⁻¹ * (v11 * v10) ∈ zpowers z) (h87 : v8 * v7 * v8⁻¹ = z * v7)
    (hne1 : v11 ≠ 1) (hnez : v11 ≠ z) (h10 : v10 ≠ v11) (h10' : v10 ≠ v11 * z) : False := by
  have hz2 : z * z = 1 := hF2 z hzF
  have h102 : v10 * v10 = 1 := hF2 v10 h10F
  have h112 : v11 * v11 = 1 := hF2 v11 h11F
  have hv11v7 : v11 * (v7 * v11) = v7 := by
    calc v11 * (v7 * v11) = (v11 * v7) * v11 := by group
      _ = (v7 * v11) * v11 := by rw [hFc v11 h11F v7 h7F]
      _ = v7 * (v11 * v11) := by group
      _ = v7 := by rw [h112, mul_one]
  have hyt' : y⁻¹ * t * y = t := by
    calc y⁻¹ * t * y = y⁻¹ * (t * y) := by group
      _ = y⁻¹ * (y * t) := by rw [hyt]
      _ = t := by group
  have hyt'' : y * t * y⁻¹ = t := by rw [hyt]; group
  have hy10'' : y * v10 * y⁻¹ = v10 := by rw [hy10]; group
  have hy10' : y⁻¹ * v10 * y = v10 := inv_conj_of_conj hy10''
  have hyz' : y⁻¹ * z * y = v11 := inv_conj_of_conj hy11
  have hy11' : y⁻¹ * v11 * y = z * v11 := by
    have h1 : y⁻¹ * (v11 * z) * y = z := inv_conj_of_conj hyz
    have h2 : y⁻¹ * (v11 * z) * y = (y⁻¹ * v11 * y) * (y⁻¹ * z * y) := by group
    rw [h2, hyz'] at h1
    calc y⁻¹ * v11 * y = (y⁻¹ * v11 * y) * (v11 * v11) := by rw [h112, mul_one]
      _ = ((y⁻¹ * v11 * y) * v11) * v11 := by group
      _ = z * v11 := by rw [h1]
  have hg10 := conj_g (x := x) hy10' (hxE v10 h10E)
  have hg11 := conj_g (x := x) hy11' (hxE (z * v11) (mul_mem hzE h11E))
  have hgz := conj_g (x := x) hyz' (hxE v11 h11E)
  have hgt : y * x * y⁻¹ * t * (y * x * y⁻¹)⁻¹ = t * v10 := by
    calc y * x * y⁻¹ * t * (y * x * y⁻¹)⁻¹ = y * (x * (y⁻¹ * t * y) * x⁻¹) * y⁻¹ := by group
      _ = y * (x * t * x⁻¹) * y⁻¹ := by rw [hyt']
      _ = y * (t * v10) * y⁻¹ := by rw [hxt]
      _ = (y * t * y⁻¹) * (y * v10 * y⁻¹) := by group
      _ = t * v10 := by rw [hyt'', hy10'']
  have hg9 : y * x * y⁻¹ * v9 * (y * x * y⁻¹)⁻¹ = z * v9 := by
    calc y * x * y⁻¹ * v9 * (y * x * y⁻¹)⁻¹ = y * (x * (y⁻¹ * v9 * y) * x⁻¹) * y⁻¹ := by group
      _ = y * (v11 * (y⁻¹ * v9 * y)) * y⁻¹ := by rw [hy9]
      _ = (y * v11 * y⁻¹) * v9 := by group
      _ = z * v9 := by rw [hy11]
  have hgsq : (y * x * y⁻¹) * (y * x * y⁻¹) = v11 * z := by
    calc (y * x * y⁻¹) * (y * x * y⁻¹) = y * (x * x) * y⁻¹ := by group
      _ = y * z * y⁻¹ := by rw [hx2]
      _ = v11 * z := hyz
  have hgF : ∀ f ∈ F, y * x * y⁻¹ * f * (y * x * y⁻¹)⁻¹ = f ∨
      y * x * y⁻¹ * f * (y * x * y⁻¹)⁻¹ = z * f := fun f hf => act_F F x y v11 z hyF hFx hy11 hf
  have hjt' : j * t * j⁻¹ = t := by rw [hjt]; group
  have hj10' : j * v10 * j⁻¹ = v10 := by rw [hj10]; group
  have hj11' : j * v11 * j⁻¹ = v11 := by rw [hj11]; group
  have hjz' : j * z * j⁻¹ = z := by rw [hjz]; group
  have hxz' : x * z * x⁻¹ = z := by rw [hxE z hzE]; group
  obtain ⟨e, he, hv7e⟩ : ∃ e : G, (e = 1 ∨ e = v8) ∧
      j * (x * e) * v7 * (j * (x * e))⁻¹ = y * x * y⁻¹ * v7 * (y * x * y⁻¹)⁻¹ := by
    rcases hFx _ (hyF v7 h7F) with h | h
    · refine ⟨1, Or.inl rfl, ?_⟩
      have e1 : y * x * y⁻¹ * v7 * (y * x * y⁻¹)⁻¹ = v7 := by
        calc y * x * y⁻¹ * v7 * (y * x * y⁻¹)⁻¹ = y * (x * (y⁻¹ * v7 * y) * x⁻¹) * y⁻¹ := by
              group
          _ = y * (y⁻¹ * v7 * y) * y⁻¹ := by rw [h]
          _ = v7 := by group
      rw [e1]
      calc j * (x * 1) * v7 * (j * (x * 1))⁻¹ = j * (x * v7 * x⁻¹) * j⁻¹ := by group
        _ = j * (v11 * v7) * j⁻¹ := by rw [hx7]
        _ = (j * v11 * j⁻¹) * (j * v7 * j⁻¹) := by group
        _ = v11 * (v7 * v11) := by rw [hj11', hj7]
        _ = v7 := hv11v7
    · refine ⟨v8, Or.inr rfl, ?_⟩
      have e1 : y * x * y⁻¹ * v7 * (y * x * y⁻¹)⁻¹ = z * v7 := by
        calc y * x * y⁻¹ * v7 * (y * x * y⁻¹)⁻¹ = y * (x * (y⁻¹ * v7 * y) * x⁻¹) * y⁻¹ := by
              group
          _ = y * (v11 * (y⁻¹ * v7 * y)) * y⁻¹ := by rw [h]
          _ = (y * v11 * y⁻¹) * v7 := by group
          _ = z * v7 := by rw [hy11]
      rw [e1]
      calc j * (x * v8) * v7 * (j * (x * v8))⁻¹
          = j * (x * (v8 * v7 * v8⁻¹) * x⁻¹) * j⁻¹ := by group
        _ = j * (x * (z * v7) * x⁻¹) * j⁻¹ := by rw [h87]
        _ = j * ((x * z * x⁻¹) * (x * v7 * x⁻¹)) * j⁻¹ := by group
        _ = j * (z * (v11 * v7)) * j⁻¹ := by rw [hxz', hx7]
        _ = (j * z * j⁻¹) * (j * v11 * j⁻¹) * (j * v7 * j⁻¹) := by group
        _ = z * v11 * (v7 * v11) := by rw [hjz', hj11', hj7]
        _ = z * v7 := by rw [mul_assoc z v11, hv11v7]
  have heE : e ∈ E := by
    rcases he with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact h8E
  have he2 : e * e = 1 := hE2 e heE
  have het : e * t = t * e := by
    rcases he with h | h <;> rw [h]
    · simp
    · exact h8t
  have hej : e * j = j * e := by
    rcases he with h | h <;> rw [h]
    · simp
    · exact hj8.symm
  have hej' : e * j * e⁻¹ = j := by rw [hej]; group
  have hxe : x * e = e * x := hxE e heE
  have hg'E : ∀ u ∈ E, j * (x * e) * u * (j * (x * e))⁻¹ = j * u * j⁻¹ := by
    intro u hu
    have h1 : e * u * e⁻¹ = u := by rw [hEc e heE u hu]; group
    have h2 : x * u * x⁻¹ = u := by rw [hxE u hu]; group
    calc j * (x * e) * u * (j * (x * e))⁻¹ = j * (x * (e * u * e⁻¹) * x⁻¹) * j⁻¹ := by group
      _ = j * (x * u * x⁻¹) * j⁻¹ := by rw [h1]
      _ = j * u * j⁻¹ := by rw [h2]
  have hg't : j * (x * e) * t * (j * (x * e))⁻¹ = t * v10 := by
    have h1 : e * t * e⁻¹ = t := by rw [het]; group
    calc j * (x * e) * t * (j * (x * e))⁻¹ = j * (x * (e * t * e⁻¹) * x⁻¹) * j⁻¹ := by group
      _ = j * (x * t * x⁻¹) * j⁻¹ := by rw [h1]
      _ = j * (t * v10) * j⁻¹ := by rw [hxt]
      _ = (j * t * j⁻¹) * (j * v10 * j⁻¹) := by group
      _ = t * v10 := by rw [hjt', hj10']
  have hag : ∀ f ∈ F, y * x * y⁻¹ * f * (y * x * y⁻¹)⁻¹ =
      j * (x * e) * f * (j * (x * e))⁻¹ := by
    intro f hf
    have hS : F ≤ centralizer ({(j * (x * e))⁻¹ * (y * x * y⁻¹)} : Set G) := by
      refine hFgen _ ?_ ?_ ?_ ?_ ?_
      · rw [mem_centralizer_singleton_iff]
        exact comm_of_conj_eq hv7e.symm
      · rw [mem_centralizer_singleton_iff]
        apply comm_of_conj_eq
        rw [hg9, hg'E v9 h9E, hj9]
        exact hFc z hzF v9 h9F
      · rw [mem_centralizer_singleton_iff]
        apply comm_of_conj_eq
        rw [hg10, hg'E v10 h10E, hj10']
      · rw [mem_centralizer_singleton_iff]
        apply comm_of_conj_eq
        rw [hg11, hg'E v11 h11E, hj11']
      · rw [mem_centralizer_singleton_iff]
        apply comm_of_conj_eq
        rw [hgz, hg'E z hzE, hjz']
    exact conj_eq_of_comm (mem_centralizer_singleton_iff.1 (hS hf))
  have hg'z : j * (x * e) * z * (j * (x * e))⁻¹ = z := by rw [hg'E z hzE, hjz']
  have hg'10 : j * (x * e) * v10 * (j * (x * e))⁻¹ = v10 := by rw [hg'E v10 h10E, hj10']
  obtain ⟨w', hw', hsq⟩ := sq_cmp F t v10 z (y * x * y⁻¹) (j * (x * e)) hF2 hFc ht2 htF hCB
    h10F hzF hgt hg't hag hgF hg'z hg'10
  have h1v : v10 * v11 = v11 * v10 := hFc v10 h10F v11 h11F
  obtain ⟨u₀, hu₀, hcu⟩ : ∃ u₀ : G, (u₀ = 1 ∨ u₀ = z) ∧
      x * j * x⁻¹ * j⁻¹ = u₀ * (v10 * v11) := by
    refine ⟨x * j * x⁻¹ * j⁻¹ * (v11 * v10), zpowers_cases hz2 hc, ?_⟩
    have h4 : v11 * v10 * (v10 * v11) = 1 := by
      calc v11 * v10 * (v10 * v11) = v11 * (v10 * v10) * v11 := by group
        _ = 1 := by rw [h102, mul_one, h112]
    calc x * j * x⁻¹ * j⁻¹ = x * j * x⁻¹ * j⁻¹ * (v11 * v10 * (v10 * v11)) := by
          rw [h4, mul_one]
      _ = x * j * x⁻¹ * j⁻¹ * (v11 * v10) * (v10 * v11) := by group
  have hjc : j * (x * j * x⁻¹ * j⁻¹) = (x * j * x⁻¹ * j⁻¹) * j := by
    rw [hcu]
    have h1 : Commute j u₀ := by
      rcases hu₀ with h | h <;> rw [h]
      · exact Commute.one_right j
      · exact hjz
    have h2 : Commute j (v10 * v11) := Commute.mul_right hj10 hj11
    exact h1.mul_right h2
  have hcw : x * e * j * (x * e)⁻¹ * j⁻¹ = x * j * x⁻¹ * j⁻¹ := by
    calc x * e * j * (x * e)⁻¹ * j⁻¹ = x * (e * j * e⁻¹) * x⁻¹ * j⁻¹ := by group
      _ = x * j * x⁻¹ * j⁻¹ := by rw [hej']
  have hxe2 : x * e * (x * e) = z := by
    calc x * e * (x * e) = x * (e * x) * e := by group
      _ = x * (x * e) * e := by rw [← hxe]
      _ = (x * x) * (e * e) := by group
      _ = z := by rw [hx2, he2, mul_one]
  have hjsq := sq_mul_comm hcw.symm hjc
  have hsq' : j * (x * e) * (j * (x * e)) = u₀ := by
    rw [hjsq, hcu, hj2, hxe2]
    have h4 : (v10 * v11) * (v10 * v11) = 1 := by
      calc (v10 * v11) * (v10 * v11) = v10 * (v11 * v10) * v11 := by group
        _ = v10 * (v10 * v11) * v11 := by rw [← h1v]
        _ = (v10 * v10) * (v11 * v11) := by group
        _ = 1 := by rw [h102, h112, one_mul]
    calc u₀ * (v10 * v11) * (v10 * v11 * z) * z
        = u₀ * ((v10 * v11) * (v10 * v11)) * (z * z) := by group
      _ = u₀ := by rw [h4, hz2, mul_one, mul_one]
  have hfin : v11 * z = u₀ * w' := by rw [← hgsq, hsq, hsq']
  exact final_cases hz2 (hFc v10 h10F z hzF) hne1 hnez h10 h10' hu₀ hw' hfin

theorem kapJ_conj {x5 x6 x7 x8 x9 x10 x11 x12 : G} (s10 : x10 * x10 = 1) (s11 : x11 * x11 = 1)
    (s12 : x12 * x12 = 1) (q5 : x5 * x5 = x12) (q6 : x6 * x6 = x11)
    (z5 : x12 * x5 = x5 * x12) (z6 : x12 * x6 = x6 * x12) (z10 : x12 * x10 = x10 * x12)
    (z11 : x12 * x11 = x11 * x12) (c57 : x5 * x7 = x7 * x5 * x11)
    (c56 : x5 * x6 = x6 * x5 * x10) (c96 : x9 * x6 = x6 * x9 * x12) (m67 : x6 * x7 = x7 * x6)
    (m59 : x5 * x9 = x9 * x5) (m85 : x8 * x5 = x5 * x8) (m86 : x8 * x6 = x6 * x8)
    (m105 : x10 * x5 = x5 * x10) (m106 : x10 * x6 = x6 * x10) (m115 : x11 * x5 = x5 * x11)
    (m116 : x11 * x6 = x6 * x11) :
    x5 * x6 * x7 * (x5 * x6)⁻¹ = x7 * x11 ∧ x5 * x6 * x9 * (x5 * x6)⁻¹ = x9 * x12 ∧
      x5 * x6 * x8 = x8 * (x5 * x6) ∧ x5 * x6 * x10 = x10 * (x5 * x6) ∧
      x5 * x6 * x11 = x11 * (x5 * x6) ∧ x5 * x6 * x12 = x12 * (x5 * x6) ∧
      x5 * x6 * (x5 * x6) = x10 * x11 * x12 := by
  have i10 : x10⁻¹ = x10 := inv_eq_of_mul_eq_one_right s10
  have i12 : x12⁻¹ = x12 := inv_eq_of_mul_eq_one_right s12
  have c65 : x6 * x5 = x5 * x6 * x10 := by
    calc x6 * x5 = x6 * x5 * x10 * x10⁻¹ := by group
      _ = x5 * x6 * x10⁻¹ := by rw [← c56]
      _ = x5 * x6 * x10 := by rw [i10]
  have c69 : x6 * x9 = x9 * x6 * x12 := by
    calc x6 * x9 = x6 * x9 * x12 * x12⁻¹ := by group
      _ = x9 * x6 * x12⁻¹ := by rw [← c96]
      _ = x9 * x6 * x12 := by rw [i12]
  have comm2 : ∀ a : G, x5 * a = a * x5 → x6 * a = a * x6 → x5 * x6 * a = a * (x5 * x6) := by
    intro a h5 h6
    calc x5 * x6 * a = x5 * (x6 * a) := by group
      _ = x5 * (a * x6) := by rw [h6]
      _ = (x5 * a) * x6 := by group
      _ = (a * x5) * x6 := by rw [h5]
      _ = a * (x5 * x6) := by group
  have hW8 := comm2 x8 m85.symm m86.symm
  have hW10 := comm2 x10 m105.symm m106.symm
  have hW11 := comm2 x11 m115.symm m116.symm
  have hW12 := comm2 x12 z5.symm z6.symm
  refine ⟨?_, ?_, hW8, hW10, hW11, hW12, ?_⟩
  · apply KappaT.conj_eq_of_mul_eq'
    calc x5 * x6 * x7 = x5 * (x6 * x7) := by group
      _ = x5 * (x7 * x6) := by rw [m67]
      _ = (x5 * x7) * x6 := by group
      _ = (x7 * x5 * x11) * x6 := by rw [c57]
      _ = x7 * x5 * (x11 * x6) := by group
      _ = x7 * x5 * (x6 * x11) := by rw [m116]
      _ = x7 * ((x5 * x6) * x11) := by group
      _ = x7 * (x11 * (x5 * x6)) := by rw [hW11]
      _ = (x7 * x11) * (x5 * x6) := by group
  · apply KappaT.conj_eq_of_mul_eq'
    calc x5 * x6 * x9 = x5 * (x6 * x9) := by group
      _ = x5 * (x9 * x6 * x12) := by rw [c69]
      _ = (x5 * x9) * x6 * x12 := by group
      _ = (x9 * x5) * x6 * x12 := by rw [m59]
      _ = x9 * ((x5 * x6) * x12) := by group
      _ = x9 * (x12 * (x5 * x6)) := by rw [hW12]
      _ = (x9 * x12) * (x5 * x6) := by group
  · calc x5 * x6 * (x5 * x6) = x5 * (x6 * x5) * x6 := by group
      _ = x5 * (x5 * x6 * x10) * x6 := by rw [c65]
      _ = (x5 * x5) * (x6 * x10) * x6 := by group
      _ = x12 * (x6 * x10) * x6 := by rw [q5]
      _ = x12 * (x10 * x6) * x6 := by rw [← m106]
      _ = x12 * x10 * (x6 * x6) := by group
      _ = x12 * x10 * x11 := by rw [q6]
      _ = x10 * x12 * x11 := by rw [z10]
      _ = x10 * (x12 * x11) := by group
      _ = x10 * (x11 * x12) := by rw [z11]
      _ = x10 * x11 * x12 := by group

end Abstract

section Model

open Certificates.TitsAschbacherParrott


theorem kapJ_model :
    Model.parrottV 5 * Model.parrottV 6 * Model.parrottV 7 *
        (Model.parrottV 5 * Model.parrottV 6)⁻¹ = Model.parrottV 7 * Model.parrottV 11 ∧
      Model.parrottV 5 * Model.parrottV 6 * Model.parrottV 9 *
        (Model.parrottV 5 * Model.parrottV 6)⁻¹ = Model.parrottV 9 * Model.parrottV 12 ∧
      Model.parrottV 5 * Model.parrottV 6 * Model.parrottV 8 =
        Model.parrottV 8 * (Model.parrottV 5 * Model.parrottV 6) ∧
      Model.parrottV 5 * Model.parrottV 6 * Model.parrottV 10 =
        Model.parrottV 10 * (Model.parrottV 5 * Model.parrottV 6) ∧
      Model.parrottV 5 * Model.parrottV 6 * Model.parrottV 11 =
        Model.parrottV 11 * (Model.parrottV 5 * Model.parrottV 6) ∧
      Model.parrottV 5 * Model.parrottV 6 * Model.parrottV 12 =
        Model.parrottV 12 * (Model.parrottV 5 * Model.parrottV 6) ∧
      Model.parrottV 5 * Model.parrottV 6 * (Model.parrottV 5 * Model.parrottV 6) =
        Model.parrottV 10 * Model.parrottV 11 * Model.parrottV 12 := by
  obtain ⟨-, -, q5, q6, s⟩ := Model.parrott_squares
  have c57 := Model.parrottV_comm (r := (5, 7, [11])) (by decide)
  have c56 := Model.parrottV_comm (r := (5, 6, [10])) (by decide)
  have c96 := Model.parrottV_comm (r := (9, 6, [12])) (by decide)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at c57 c56 c96
  have z : ∀ j, 1 ≤ j → j ≤ 12 → Model.parrottV 12 * Model.parrottV j =
      Model.parrottV j * Model.parrottV 12 :=
    fun j h1 h2 => Model.parrottV_twelve_comm h1 h2
  have cm : ∀ {i j : ℕ}, 1 ≤ i → i ≤ 12 → 1 ≤ j → j ≤ 12 → listed i j = false →
      listed j i = false → Model.parrottV i * Model.parrottV j =
        Model.parrottV j * Model.parrottV i :=
    fun h1 h2 h3 h4 h5 h6 => Model.parrottV_commute h1 h2 h3 h4 h5 h6
  exact kapJ_conj (s 10 (by norm_num) (by norm_num) (by decide))
    (s 11 (by norm_num) (by norm_num) (by decide)) (s 12 (by norm_num) (by norm_num) (by decide))
    q5 q6 (z 5 (by norm_num) (by norm_num)) (z 6 (by norm_num) (by norm_num))
    (z 10 (by norm_num) (by norm_num)) (z 11 (by norm_num) (by norm_num)) c57 c56 c96
    (cm (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide))
    (cm (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide))
    (cm (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide))
    (cm (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide))
    (cm (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide))
    (cm (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide))
    (cm (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide))
    (cm (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide))

end Model

end KappaY


namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem kJ_mem_titsD : Model.parrottV 5 * Model.parrottV 6 ∈ titsD :=
  titsS_le_titsD (Model.parrottBlocks_subset (Or.inr ⟨5, by decide, 6, by decide, rfl⟩))

theorem kJ_mem_titsJ : Model.parrottV 5 * Model.parrottV 6 ∈ titsJ := by
  have hP : Model.parrottV 5 * Model.parrottV 6 ∈ CFSG.Quasithin.twoF4P := by
    rw [Model.twoF4P_eq_parrottU_three]
    exact mul_mem (subset_closure ⟨5, ⟨by norm_num, by norm_num⟩, rfl⟩)
      (subset_closure ⟨6, ⟨by norm_num, by norm_num⟩, rfl⟩)
  rw [← (Model.pCore_twoF4H).2.2.1]
  exact mem_inf.2 ⟨hP, kJ_mem_titsD⟩

@[expose] noncomputable def kJ (d : Data G) : G := d.lift (Model.parrottV 5 * Model.parrottV 6)

theorem kJ_mem_J (d : Data G) : d.kJ ∈ d.s56J := mem_liftSub.2 ⟨_, kJ_mem_titsJ, kJ_mem_titsD, rfl⟩

theorem kJ_comm_t (hd : d.Hyp) : d.kJ * d.t = d.t * d.kJ := hd.L_comm_t (d.lift_mem _)

theorem kJ_conj (d : Data G) :
    d.kJ * d.pv 7 * d.kJ⁻¹ = d.pv 7 * d.pv 11 ∧ d.kJ * d.pv 9 * d.kJ⁻¹ = d.pv 9 * d.z ∧
      d.kJ * d.pv 8 = d.pv 8 * d.kJ ∧ d.kJ * d.pv 10 = d.pv 10 * d.kJ ∧
      d.kJ * d.pv 11 = d.pv 11 * d.kJ ∧ d.kJ * d.z = d.z * d.kJ ∧
      d.kJ * d.kJ = d.pv 10 * d.pv 11 * d.z := by
  obtain ⟨m7, m9, m8, m10, m11, m12, msq⟩ := KappaY.kapJ_model
  have hδD : Model.parrottV 5 * Model.parrottV 6 ∈ titsD := kJ_mem_titsD
  have hD : ∀ {i : ℕ}, 7 ≤ i → i ≤ 12 → Model.parrottV i ∈ titsD := fun h7 h12 =>
    kappa_pv_mem_D h7 h12
  have hconj : ∀ x ∈ titsD, d.kJ * d.lift x * d.kJ⁻¹ =
      d.lift (Model.parrottV 5 * Model.parrottV 6 * x *
        (Model.parrottV 5 * Model.parrottV 6)⁻¹) := fun x hx =>
    (d.lift_conj hδD hx).symm
  have h12 := hD (i := 12) (by norm_num) (le_refl _)
  have h11 := hD (i := 11) (by norm_num) (by norm_num)
  have h10 := hD (i := 10) (by norm_num) (by norm_num)
  have h9 := hD (i := 9) (by norm_num) (by norm_num)
  have h8 := hD (i := 8) (by norm_num) (by norm_num)
  have h7 := hD (i := 7) (by norm_num) (by norm_num)
  have e12 : d.pv 12 = d.z := s56_pv12 d
  have e12' : d.lift (Model.parrottV 12) = d.z := e12
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show d.kJ * d.lift (Model.parrottV 7) * d.kJ⁻¹ =
      d.lift (Model.parrottV 7) * d.lift (Model.parrottV 11)
    rw [hconj _ h7, m7, d.lift_mul h7 h11]
  · show d.kJ * d.lift (Model.parrottV 9) * d.kJ⁻¹ = d.lift (Model.parrottV 9) * d.z
    rw [hconj _ h9, m9, d.lift_mul h9 h12, e12']
  · show d.lift (Model.parrottV 5 * Model.parrottV 6) * d.lift (Model.parrottV 8) =
      d.lift (Model.parrottV 8) * d.lift (Model.parrottV 5 * Model.parrottV 6)
    exact (d.lift_comm_iff hδD h8).2 m8
  · show d.lift (Model.parrottV 5 * Model.parrottV 6) * d.lift (Model.parrottV 10) =
      d.lift (Model.parrottV 10) * d.lift (Model.parrottV 5 * Model.parrottV 6)
    exact (d.lift_comm_iff hδD h10).2 m10
  · show d.lift (Model.parrottV 5 * Model.parrottV 6) * d.lift (Model.parrottV 11) =
      d.lift (Model.parrottV 11) * d.lift (Model.parrottV 5 * Model.parrottV 6)
    exact (d.lift_comm_iff hδD h11).2 m11
  · rw [← e12']
    show d.lift (Model.parrottV 5 * Model.parrottV 6) * d.lift (Model.parrottV 12) =
      d.lift (Model.parrottV 12) * d.lift (Model.parrottV 5 * Model.parrottV 6)
    exact (d.lift_comm_iff hδD h12).2 m12
  · show d.lift (Model.parrottV 5 * Model.parrottV 6) * d.lift (Model.parrottV 5 *
      Model.parrottV 6) = d.lift (Model.parrottV 10) * d.lift (Model.parrottV 11) * d.z
    rw [← d.lift_mul hδD hδD, msq, d.lift_mul (mul_mem h10 h11) h12, d.lift_mul h10 h11, e12']

theorem F_le_of_pv_mem {S : Subgroup G} (h : ∀ i ∈ ({7, 9, 10, 11, 12} : Set ℕ), d.pv i ∈ S) :
    d.F ≤ S := by
  intro f hf
  obtain ⟨x, hx, hxD, rfl⟩ := mem_liftSub.1 hf
  have hx' : x ∈ closure (Model.parrottV '' {7, 9, 10, 11, 12}) := hx
  refine (closure_induction (p := fun x _ => x ∈ titsD ∧ d.lift x ∈ S) ?_ ?_ ?_ ?_ hx').2
  · rintro _ ⟨i, hi, rfl⟩
    exact ⟨Model.parrottF_le_titsD (Model.parrottV_mem_parrottF hi), h i hi⟩
  · exact ⟨one_mem _, by rw [d.lift_one]; exact S.one_mem⟩
  · rintro x y _ _ ⟨hxD, hxS⟩ ⟨hyD, hyS⟩
    exact ⟨mul_mem hxD hyD, by rw [d.lift_mul hxD hyD]; exact S.mul_mem hxS hyS⟩
  · rintro x _ ⟨hxD, hxS⟩
    exact ⟨inv_mem hxD, by rw [d.lift_inv hxD]; exact S.inv_mem hxS⟩

theorem Hyp.kappa_hCB (hd : d.Hyp) {h : G} (hhF : ∀ a ∈ d.F, h * a = a * h)
    (hht : h * d.t = d.t * h) : h ∈ d.F ⊔ zpowers d.t := by
  have hle : d.B ≤ centralizer ({h} : Set G) :=
    sup_le (fun a ha => mem_centralizer_singleton_iff.2 (hhF a ha).symm)
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 hht.symm))
  have hhC : h ∈ centralizer (d.B : Set G) :=
    mem_centralizer_iff.2 fun b hb => mem_centralizer_singleton_iff.1 (hle hb)
  rw [hd.centralizer_B] at hhC
  exact hhC

theorem Hyp.kappaY_Fx_of_not_mem (hd : d.Hyp) {x : G} (hxV : x ∈ d.s56V)
    (hx7 : x * d.pv 7 * x⁻¹ = d.pv 11 * d.pv 7) {f : G} (hf : f ∈ d.F) (hfE : f ∉ d.E) :
    x * f * x⁻¹ = d.pv 11 * f := by
  have h7f : d.pv 7 * f ∈ d.E := (Hyp.s56_F_cases d hf).resolve_left hfE
  have hc : x * (d.pv 7 * f) * x⁻¹ = d.pv 7 * f := by rw [s56_V_comm_E hxV h7f]; group
  have h11 : d.pv 11 * d.pv 11 = 1 := hd.s56_F_sq (s56_U11_le_F d (s56_pv11_mem_U11 d))
  have hF11 : d.pv 11 ∈ d.F := s56_U11_le_F d (s56_pv11_mem_U11 d)
  have hcomm : d.pv 11 * d.pv 7 = d.pv 7 * d.pv 11 := hd.s56_F_comm hF11 hd.s56_pv7_mem_F
  have h2 : (d.pv 7 * d.pv 11) * (x * f * x⁻¹) = d.pv 7 * f := by
    calc (d.pv 7 * d.pv 11) * (x * f * x⁻¹) = (d.pv 11 * d.pv 7) * (x * f * x⁻¹) := by
          rw [hcomm]
      _ = (x * d.pv 7 * x⁻¹) * (x * f * x⁻¹) := by rw [hx7]
      _ = x * (d.pv 7 * f) * x⁻¹ := by group
      _ = d.pv 7 * f := hc
  have h3 : d.pv 11 * (x * f * x⁻¹) = f := by
    have h2' := h2
    rw [mul_assoc (d.pv 7) (d.pv 11)] at h2'
    exact mul_left_cancel h2'
  calc x * f * x⁻¹ = d.pv 11 * (d.pv 11 * (x * f * x⁻¹)) := by
        rw [← mul_assoc, h11, one_mul]
    _ = d.pv 11 * f := by rw [h3]

theorem Hyp.kappaY_Fx (hd : d.Hyp) {x : G} (hxV : x ∈ d.s56V)
    (hx7 : x * d.pv 7 * x⁻¹ = d.pv 11 * d.pv 7) {f : G} (hf : f ∈ d.F) :
    x * f * x⁻¹ = f ∨ x * f * x⁻¹ = d.pv 11 * f := by
  by_cases hfE : f ∈ d.E
  · left
    rw [s56_V_comm_E hxV hfE]
    group
  · exact Or.inr (hd.kappaY_Fx_of_not_mem hxV hx7 hf hfE)

theorem Hyp.kappaY_y9 (h49 : d.Thm49Statement) (hd : d.Hyp) {x : G} (hxV : x ∈ d.s56V)
    (hx7 : x * d.pv 7 * x⁻¹ = d.pv 11 * d.pv 7) :
    x * (d.s56Y⁻¹ * d.pv 9 * d.s56Y) * x⁻¹ = d.pv 11 * (d.s56Y⁻¹ * d.pv 9 * d.s56Y) := by
  obtain ⟨hyNt, -, -, -, -, -, -⟩ := hd.s56_Y_facts
  have hyN : d.s56Y ∈ d.N := (mem_inf.1 hyNt).1
  have hf'F : d.s56Y⁻¹ * d.pv 9 * d.s56Y ∈ d.F := by
    have := hd.s56_N_conj_F h49 (inv_mem hyN) (N.node09K_pv9_mem_F d)
    simpa [mul_assoc] using this
  refine hd.kappaY_Fx_of_not_mem hxV hx7 hf'F fun hf'E => ?_
  have hf'U : d.s56Y⁻¹ * d.pv 9 * d.s56Y ∉ d.s56U10 := fun h => N.node09K_pv9_not_mem_U10 d (by
    have := hd.s56_N_conj_U10 h49 hyN h
    simpa [mul_assoc] using this)
  have h9 : d.pv 9 ∈ d.E ⊓ d.F := mem_inf.2 ⟨N.node09K_pv9_mem_E d, N.node09K_pv9_mem_F d⟩
  have hU := hd.s56_mul_mem_U10_of_not_mem h9 (mem_inf.2 ⟨hf'E, hf'F⟩)
    (N.node09K_pv9_not_mem_U10 d) hf'U
  apply s56_Y_comm_not_mem hf'F hf'U
  have hsq := hd.s56_F_sq hf'F
  have hinv : (d.s56Y⁻¹ * d.pv 9 * d.s56Y)⁻¹ = d.s56Y⁻¹ * d.pv 9 * d.s56Y :=
    inv_eq_of_mul_eq_one_right hsq
  have e : d.s56Y * (d.s56Y⁻¹ * d.pv 9 * d.s56Y) * d.s56Y⁻¹ *
      (d.s56Y⁻¹ * d.pv 9 * d.s56Y)⁻¹ = d.pv 9 * (d.s56Y⁻¹ * d.pv 9 * d.s56Y) := by
    rw [hinv]; group
  rw [e]
  exact hU

theorem Hyp.kappaY (h49 : d.Thm49Statement) (hd : d.Hyp) {x : G} (hxV : x ∈ d.s56V)
    (hxε : d.s56Eps x = d.pv 10) (hτ : x * d.pv 7 * x⁻¹ * (d.pv 7)⁻¹ = d.pv 11)
    (hc : x * d.kJ * x⁻¹ * d.kJ⁻¹ * (d.pv 11 * d.pv 10) ∈ zpowers d.z) (hx2 : x * x = d.z) :
    False := by
  obtain ⟨hyNt, -, -, -, hy10, hy11, hyz⟩ := hd.s56_Y_facts
  have hyN : d.s56Y ∈ d.N := (mem_inf.1 hyNt).1
  have hyt : d.s56Y * d.t = d.t * d.s56Y := mem_centralizer_singleton_iff.1 (mem_inf.1 hyNt).2
  have hyF : ∀ f ∈ d.F, d.s56Y⁻¹ * f * d.s56Y ∈ d.F := fun f hf => by
    have := hd.s56_N_conj_F h49 (inv_mem hyN) hf
    simpa [mul_assoc] using this
  have hx7 : x * d.pv 7 * x⁻¹ = d.pv 11 * d.pv 7 := by
    calc x * d.pv 7 * x⁻¹ = (x * d.pv 7 * x⁻¹ * (d.pv 7)⁻¹) * d.pv 7 := by group
      _ = d.pv 11 * d.pv 7 := by rw [hτ]
  have hxt : x * d.t * x⁻¹ = d.t * d.pv 10 := by
    have h : d.t * (x * d.t * x⁻¹) = d.pv 10 := hxε
    calc x * d.t * x⁻¹ = d.t * (d.t * (x * d.t * x⁻¹)) := by
          rw [← mul_assoc, hd.t_mul_self, one_mul]
      _ = d.t * d.pv 10 := by rw [h]
  have hF11 : d.pv 11 ∈ d.F := s56_U11_le_F d (s56_pv11_mem_U11 d)
  have hz11 : d.pv 11 * d.z ∈ d.s56U11 := s56_mem_U11_iff.2 (Or.inr (Or.inr (Or.inr rfl)))
  obtain ⟨hj7, hj9, hj8, hj10, hj11, hjz, hj2⟩ := kJ_conj d
  have h87 : d.pv 8 * d.pv 7 * (d.pv 8)⁻¹ = d.z * d.pv 7 := by
    have h8 : d.pv 8 * d.pv 8 = 1 := hd.s56_E_sq (s56_pv8_mem_E d)
    have h8i : (d.pv 8)⁻¹ = d.pv 8 := inv_eq_of_mul_eq_one_right h8
    have h := s56_pv7_conj_pv8 d
    have h' : d.pv 7 * d.pv 8 = d.pv 8 * d.z * d.pv 7 := by
      calc d.pv 7 * d.pv 8 = d.pv 7 * d.pv 8 * (d.pv 7)⁻¹ * d.pv 7 := by group
        _ = d.pv 8 * d.z * d.pv 7 := by rw [h]
    rw [h8i]
    calc d.pv 8 * d.pv 7 * d.pv 8 = d.pv 8 * (d.pv 7 * d.pv 8) := by group
      _ = d.pv 8 * (d.pv 8 * d.z * d.pv 7) := by rw [h']
      _ = (d.pv 8 * d.pv 8) * d.z * d.pv 7 := by group
      _ = d.z * d.pv 7 := by rw [h8, one_mul]
  exact KappaY.main d.F d.E d.t (d.pv 7) (d.pv 8) (d.pv 9) (d.pv 10) (d.pv 11) d.z x d.s56Y d.kJ
    (fun a ha => hd.s56_E_sq ha) (fun a ha b hb => hd.s56_E_comm ha hb) (s56_pv8_mem_E d)
    (N.node09K_pv9_mem_E d) hd.s56_pv10_mem_E (s56_pv11_mem_E d) hd.s56_z_mem_E
    (fun a ha => s56_V_comm_E hxV ha) (fun a ha => hd.s56_F_sq ha)
    (fun a ha b hb => hd.s56_F_comm ha hb) hd.s56_pv7_mem_F (N.node09K_pv9_mem_F d)
    (s56_pv10_mem_F d) hF11 hd.s56_z_mem_F
    (fun S h7 h9 h10 h11 hz => F_le_of_pv_mem (fun i hi => by
      rcases hi with rfl | rfl | rfl | rfl | rfl
      exacts [h7, h9, h10, h11, by rw [s56_pv12 d]; exact hz]))
    (fun f hf => hd.kappaY_Fx hxV hx7 hf) hd.t_mul_self
    (fun a ha => (hd.L_comm_t (s56_F_le_L d ha)).symm) (hd.L_comm_t (d.lift_mem (Model.parrottV 8)))
    (fun h hhF hht => hd.kappa_hCB hhF hht) hyF hyt hy10 hy11 hyz
    (hd.kappaY_y9 h49 hxV hx7) hxt hx7 hx2 (kJ_comm_t hd) hj7 hj9 hj8 hj10 hj11 hjz hj2 hc h87
    (s56_pv11_ne_one d) (s56_pv11_ne_z d)
    (fun h => s56_pv10_not_mem_U11 d (by rw [h]; exact s56_pv11_mem_U11 d))
    (fun h => s56_pv10_not_mem_U11 d (by rw [h]; exact hz11))

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
