module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56StepKappa
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P09K

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits
open scoped Pointwise commutatorElement

namespace KappaW

theorem mem_sup_zpowers_cases {G : Type*} [Group G] {F : Subgroup G} {t : G}
    (hF2 : ∀ a ∈ F, a * a = 1) (ht2 : t * t = 1) (htF : ∀ a ∈ F, t * a = a * t) {x : G}
    (hx : x ∈ F ⊔ zpowers t) : ∃ f ∈ F, x = f ∨ x = f * t := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun x _ => ∃ f ∈ F, x = f ∨ x = f * t) ?_ ?_ ?_ ?_ hx
  · rintro x (hxF | hxt)
    · exact ⟨x, hxF, Or.inl rfl⟩
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxt
      rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
      · refine ⟨1, one_mem _, Or.inl ?_⟩
        rw [zpow_mul]
        simp [zpow_ofNat, sq, ht2]
      · refine ⟨1, one_mem _, Or.inr ?_⟩
        rw [zpow_add, zpow_mul]
        simp [zpow_ofNat, sq, ht2]
  · exact ⟨1, one_mem _, Or.inl rfl⟩
  · rintro x y _ _ ⟨f₁, hf₁, h₁⟩ ⟨f₂, hf₂, h₂⟩
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> rw [h₁, h₂]
    · exact ⟨f₁ * f₂, mul_mem hf₁ hf₂, Or.inl rfl⟩
    · exact ⟨f₁ * f₂, mul_mem hf₁ hf₂, Or.inr (by group)⟩
    · refine ⟨f₁ * f₂, mul_mem hf₁ hf₂, Or.inr ?_⟩
      calc f₁ * t * f₂ = f₁ * (t * f₂) := by group
        _ = f₁ * (f₂ * t) := by rw [htF f₂ hf₂]
        _ = f₁ * f₂ * t := by group
    · refine ⟨f₁ * f₂, mul_mem hf₁ hf₂, Or.inl ?_⟩
      calc f₁ * t * (f₂ * t) = f₁ * (t * f₂) * t := by group
        _ = f₁ * (f₂ * t) * t := by rw [htF f₂ hf₂]
        _ = f₁ * f₂ * (t * t) := by group
        _ = f₁ * f₂ := by rw [ht2, mul_one]
  · rintro x _ ⟨f, hf, h⟩
    have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right (hF2 f hf)
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    rcases h with h | h <;> rw [h]
    · exact ⟨f, hf, Or.inl hfi⟩
    · refine ⟨f, hf, Or.inr ?_⟩
      calc (f * t)⁻¹ = t⁻¹ * f⁻¹ := by group
        _ = t * f := by rw [htinv, hfi]
        _ = f * t := htF f hf

theorem core {G : Type*} [Group G] (F : Subgroup G) (t v10 y g : G)
    (hF2 : ∀ a ∈ F, a * a = 1) (hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (ht2 : t * t = 1) (htF : ∀ a ∈ F, t * a = a * t)
    (hCB : ∀ h : G, (∀ a ∈ F, h * a = a * h) → h * t = t * h → h ∈ F ⊔ zpowers t)
    (hv10 : v10 ∈ F) (hyF : y ∈ normalizer (F : Set G)) (hyt : y * t = t * y)
    (hy10 : y * v10 = v10 * y) (hgF : ∀ a ∈ F, g * a = a * g) (hgt : g * t * g⁻¹ = t * v10) :
    g * g ∈ F ⊔ zpowers t ∧
      (y * (g * g) * y⁻¹ = g * g ∨ y * (g * g) * y⁻¹ = v10 * (g * g)) := by
  have hv10c : g * v10 = v10 * g := hgF _ hv10
  have hgt' : g⁻¹ * t * g = t * v10 := by
    have h : g * (t * v10) * g⁻¹ = t := by
      calc g * (t * v10) * g⁻¹ = (g * t * g⁻¹) * (g * v10 * g⁻¹) := by group
        _ = (t * v10) * v10 := by rw [hgt, show g * v10 * g⁻¹ = v10 by rw [hv10c]; group]
        _ = t := by rw [mul_assoc, hF2 _ hv10, mul_one]
    calc g⁻¹ * t * g = g⁻¹ * (g * (t * v10) * g⁻¹) * g := by rw [h]
      _ = t * v10 := by group
  have hg2F : ∀ a ∈ F, (g * g) * a = a * (g * g) := by
    intro a ha
    calc g * g * a = g * (g * a) := by group
      _ = g * (a * g) := by rw [hgF a ha]
      _ = (g * a) * g := by group
      _ = (a * g) * g := by rw [hgF a ha]
      _ = a * (g * g) := by group
  have hg2t : (g * g) * t = t * (g * g) := by
    have h : g * g * t * (g * g)⁻¹ = t := by
      calc g * g * t * (g * g)⁻¹ = g * (g * t * g⁻¹) * g⁻¹ := by group
        _ = g * (t * v10) * g⁻¹ := by rw [hgt]
        _ = (g * t * g⁻¹) * (g * v10 * g⁻¹) := by group
        _ = (t * v10) * v10 := by rw [hgt, show g * v10 * g⁻¹ = v10 by rw [hv10c]; group]
        _ = t := by rw [mul_assoc, hF2 _ hv10, mul_one]
    calc g * g * t = (g * g * t * (g * g)⁻¹) * (g * g) := by group
      _ = t * (g * g) := by rw [h]
  refine ⟨hCB _ hg2F hg2t, ?_⟩
  set gy : G := y * g * y⁻¹ with hgy
  have hyF' : ∀ a, a ∈ F ↔ y * a * y⁻¹ ∈ F := fun a => mem_normalizer_iff.1 hyF a
  have hyFinv : ∀ a ∈ F, y⁻¹ * a * y ∈ F := fun a ha =>
    (hyF' (y⁻¹ * a * y)).2 (by simpa [mul_assoc] using ha)
  have hgyF : ∀ a ∈ F, gy * a = a * gy := by
    intro a ha
    have h1 := hgF _ (hyFinv a ha)
    calc gy * a = y * (g * (y⁻¹ * a * y)) * y⁻¹ := by simp only [hgy]; group
      _ = y * ((y⁻¹ * a * y) * g) * y⁻¹ := by rw [h1]
      _ = a * gy := by simp only [hgy]; group
  have hyt' : y * t * y⁻¹ = t := by rw [hyt]; group
  have hyt'' : y⁻¹ * t * y = t := by
    calc y⁻¹ * t * y = y⁻¹ * (t * y) := by group
      _ = y⁻¹ * (y * t) := by rw [hyt]
      _ = t := by group
  have hy10' : y * v10 * y⁻¹ = v10 := by rw [hy10]; group
  have hgyt : gy * t * gy⁻¹ = t * v10 := by
    calc gy * t * gy⁻¹ = y * (g * (y⁻¹ * t * y) * g⁻¹) * y⁻¹ := by simp only [hgy]; group
      _ = y * (g * t * g⁻¹) * y⁻¹ := by rw [hyt'']
      _ = y * (t * v10) * y⁻¹ := by rw [hgt]
      _ = (y * t * y⁻¹) * (y * v10 * y⁻¹) := by group
      _ = t * v10 := by rw [hyt', hy10']
  set h : G := gy * g⁻¹ with hh
  have hhF : ∀ a ∈ F, h * a = a * h := by
    intro a ha
    have e1 := hgyF a ha
    have e2 := hgF a ha
    calc h * a = gy * (g⁻¹ * a) := by simp only [hh]; group
      _ = gy * (a * g⁻¹) := by
        congr 1
        calc g⁻¹ * a = g⁻¹ * (a * g) * g⁻¹ := by group
          _ = g⁻¹ * (g * a) * g⁻¹ := by rw [e2]
          _ = a * g⁻¹ := by group
      _ = (gy * a) * g⁻¹ := by group
      _ = (a * gy) * g⁻¹ := by rw [e1]
      _ = a * h := by simp only [hh]; group
  have hht : h * t = t * h := by
    have hgyv : gy * v10 = v10 * gy := hgyF _ hv10
    have e : h * t * h⁻¹ = t := by
      calc h * t * h⁻¹ = gy * (g⁻¹ * t * g) * gy⁻¹ := by simp only [hh]; group
        _ = gy * (t * v10) * gy⁻¹ := by rw [hgt']
        _ = (gy * t * gy⁻¹) * (gy * v10 * gy⁻¹) := by group
        _ = (t * v10) * v10 := by
            rw [hgyt, show gy * v10 * gy⁻¹ = v10 by rw [hgyv]; group]
        _ = t := by rw [mul_assoc, hF2 _ hv10, mul_one]
    calc h * t = (h * t * h⁻¹) * h := by group
      _ = t * h := by rw [e]
  obtain ⟨f, hf, hft⟩ := mem_sup_zpowers_cases hF2 ht2 htF (hCB h hhF hht)
  have hgy_eq : gy = h * g := by simp only [hh]; group
  have hgsq : gy * gy = (h * (g * h * g⁻¹)) * (g * g) := by
    calc gy * gy = (h * g) * (h * g) := by rw [← hgy_eq]
      _ = (h * (g * h * g⁻¹)) * (g * g) := by group
  have hysq : gy * gy = y * (g * g) * y⁻¹ := by simp only [hgy]; group
  have hgf : g * f * g⁻¹ = f := by rw [hgF f hf]; group
  have hftc : t * f = f * t := htF f hf
  have hF2' := hF2 f hf
  rw [← hysq]
  rcases hft with hft | hft
  · left
    rw [hgsq, hft, hgf, hF2', one_mul]
  · right
    have hght : g * (f * t) * g⁻¹ = f * (t * v10) := by
      calc g * (f * t) * g⁻¹ = (g * f * g⁻¹) * (g * t * g⁻¹) := by group
        _ = f * (t * v10) := by rw [hgf, hgt]
    have hprod : (f * t) * (f * (t * v10)) = v10 := by
      have e1 : (f * t) * (f * (t * v10)) = f * (t * f) * (t * v10) := by group
      rw [e1, hftc]
      have e2 : f * (f * t) * (t * v10) = (f * f) * (t * t) * v10 := by group
      rw [e2, hF2', ht2]
      group
    rw [hgsq, hft, hght, hprod]

end KappaW

namespace KappaT

section Abstract

variable {P : Type*} [Group P]

theorem conj_eq_of_mul_eq' {a y y' : P} (h : a * y = y' * a) : a * y * a⁻¹ = y' := by
  rw [h, mul_inv_cancel_right]

theorem kapS_conj {x1 x4 x7 x9 x10 x11 x12 : P}
    (s10 : x10 * x10 = 1) (s11 : x11 * x11 = 1) (s12 : x12 * x12 = 1)
    (z1 : x12 * x1 = x1 * x12) (z4 : x12 * x4 = x4 * x12) (z10 : x12 * x10 = x10 * x12)
    (z11 : x12 * x11 = x11 * x12)
    (c111 : x11 * x1 = x1 * x11) (c114 : x11 * x4 = x4 * x11) (c1110 : x11 * x10 = x10 * x11)
    (c104 : x10 * x4 = x4 * x10 * x12) (c101 : x10 * x1 = x1 * x10 * x11)
    (c94 : x9 * x4 = x4 * x9) (c91 : x9 * x1 = x1 * x9 * (x10 * (x11 * x12)))
    (c74 : x7 * x4 = x4 * x7 * (x10 * (x11 * x12))) (c71 : x7 * x1 = x1 * x7) :
    x1 * x4 * x12 * (x1 * x4)⁻¹ = x12 ∧ x1 * x4 * x11 * (x1 * x4)⁻¹ = x11 ∧
      x1 * x4 * x10 * (x1 * x4)⁻¹ = x10 * x11 * x12 ∧
      x1 * x4 * x9 * (x1 * x4)⁻¹ = x9 * x10 * x12 ∧
      (x1 * x4)⁻¹ * x7 * (x1 * x4) = x7 * (x10 * (x11 * x12)) := by
  have i10 : x10⁻¹ = x10 := inv_eq_of_mul_eq_one_right s10
  have i11 : x11⁻¹ = x11 := inv_eq_of_mul_eq_one_right s11
  have i12 : x12⁻¹ = x12 := inv_eq_of_mul_eq_one_right s12
  have A1 : x4 * x10 = x10 * x12 * x4 := by
    have h : x4 * x10 * x12 = x10 * x4 := c104.symm
    calc x4 * x10 = x4 * x10 * x12 * x12⁻¹ := by group
      _ = x10 * x4 * x12⁻¹ := by rw [h]
      _ = x10 * x4 * x12 := by rw [i12]
      _ = x10 * (x4 * x12) := by group
      _ = x10 * (x12 * x4) := by rw [z4]
      _ = x10 * x12 * x4 := by group
  have A2 : x1 * x10 = x10 * x11 * x1 := by
    have h : x1 * x10 * x11 = x10 * x1 := c101.symm
    calc x1 * x10 = x1 * x10 * x11 * x11⁻¹ := by group
      _ = x10 * x1 * x11⁻¹ := by rw [h]
      _ = x10 * x1 * x11 := by rw [i11]
      _ = x10 * (x1 * x11) := by group
      _ = x10 * (x11 * x1) := by rw [c111]
      _ = x10 * x11 * x1 := by group
  have B11 : x1 * x11 = x11 * x1 := c111.symm
  have B12 : x1 * x12 = x12 * x1 := z1.symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply conj_eq_of_mul_eq'
    calc x1 * x4 * x12 = x1 * (x4 * x12) := by group
      _ = x1 * (x12 * x4) := by rw [z4]
      _ = (x1 * x12) * x4 := by group
      _ = (x12 * x1) * x4 := by rw [B12]
      _ = x12 * (x1 * x4) := by group
  · apply conj_eq_of_mul_eq'
    calc x1 * x4 * x11 = x1 * (x4 * x11) := by group
      _ = x1 * (x11 * x4) := by rw [c114]
      _ = (x1 * x11) * x4 := by group
      _ = (x11 * x1) * x4 := by rw [B11]
      _ = x11 * (x1 * x4) := by group
  · apply conj_eq_of_mul_eq'
    calc x1 * x4 * x10 = x1 * (x4 * x10) := by group
      _ = x1 * (x10 * x12 * x4) := by rw [A1]
      _ = (x1 * x10) * x12 * x4 := by group
      _ = (x10 * x11 * x1) * x12 * x4 := by rw [A2]
      _ = x10 * x11 * (x1 * x12) * x4 := by group
      _ = x10 * x11 * (x12 * x1) * x4 := by rw [B12]
      _ = x10 * x11 * x12 * (x1 * x4) := by group
  · have hw : x1 * (x10 * (x11 * x12)) = (x10 * x12) * x1 := by
      calc x1 * (x10 * (x11 * x12)) = (x1 * x10) * (x11 * x12) := by group
        _ = (x10 * x11 * x1) * (x11 * x12) := by rw [A2]
        _ = x10 * x11 * (x1 * x11) * x12 := by group
        _ = x10 * x11 * (x11 * x1) * x12 := by rw [B11]
        _ = x10 * (x11 * x11) * x1 * x12 := by group
        _ = x10 * x1 * x12 := by rw [s11]; group
        _ = x10 * (x1 * x12) := by group
        _ = x10 * (x12 * x1) := by rw [B12]
        _ = (x10 * x12) * x1 := by group
    have hw' : x1 * (x10 * (x11 * x12)) * x1⁻¹ = x10 * x12 := conj_eq_of_mul_eq' hw
    have h1 : x1 * x9 = x9 * x1 * (x10 * (x11 * x12))⁻¹ := by
      rw [c91]; group
    have h2 : x1 * x9 = x9 * (x10 * x12)⁻¹ * x1 := by
      calc x1 * x9 = x9 * x1 * (x10 * (x11 * x12))⁻¹ := h1
        _ = x9 * (x1 * (x10 * (x11 * x12)) * x1⁻¹)⁻¹ * x1 := by group
        _ = x9 * (x10 * x12)⁻¹ * x1 := by rw [hw']
    have hinv : (x10 * x12)⁻¹ = x10 * x12 := by
      calc (x10 * x12)⁻¹ = x12⁻¹ * x10⁻¹ := by group
        _ = x12 * x10 := by rw [i12, i10]
        _ = x10 * x12 := z10
    apply conj_eq_of_mul_eq'
    calc x1 * x4 * x9 = x1 * (x4 * x9) := by group
      _ = x1 * (x9 * x4) := by rw [c94]
      _ = (x1 * x9) * x4 := by group
      _ = (x9 * (x10 * x12)⁻¹ * x1) * x4 := by rw [h2]
      _ = x9 * x10 * x12 * (x1 * x4) := by rw [hinv]; group
  · have h7 : x7 * (x1 * x4) = (x1 * x4) * (x7 * (x10 * (x11 * x12))) := by
      calc x7 * (x1 * x4) = (x7 * x1) * x4 := by group
        _ = (x1 * x7) * x4 := by rw [c71]
        _ = x1 * (x7 * x4) := by group
        _ = x1 * (x4 * x7 * (x10 * (x11 * x12))) := by rw [c74]
        _ = (x1 * x4) * (x7 * (x10 * (x11 * x12))) := by group
    calc (x1 * x4)⁻¹ * x7 * (x1 * x4) = (x1 * x4)⁻¹ * (x7 * (x1 * x4)) := by group
      _ = (x1 * x4)⁻¹ * ((x1 * x4) * (x7 * (x10 * (x11 * x12)))) := by rw [h7]
      _ = x7 * (x10 * (x11 * x12)) := by group

end Abstract

section Model

open Certificates.TitsAschbacherParrott

theorem kapS_model :
    Model.parrottV 1 * Model.parrottV 4 * Model.parrottV 12 *
        (Model.parrottV 1 * Model.parrottV 4)⁻¹ = Model.parrottV 12 ∧
      Model.parrottV 1 * Model.parrottV 4 * Model.parrottV 11 *
        (Model.parrottV 1 * Model.parrottV 4)⁻¹ = Model.parrottV 11 ∧
      Model.parrottV 1 * Model.parrottV 4 * Model.parrottV 10 *
        (Model.parrottV 1 * Model.parrottV 4)⁻¹ =
        Model.parrottV 10 * Model.parrottV 11 * Model.parrottV 12 ∧
      Model.parrottV 1 * Model.parrottV 4 * Model.parrottV 9 *
        (Model.parrottV 1 * Model.parrottV 4)⁻¹ =
        Model.parrottV 9 * Model.parrottV 10 * Model.parrottV 12 ∧
      (Model.parrottV 1 * Model.parrottV 4)⁻¹ * Model.parrottV 7 *
        (Model.parrottV 1 * Model.parrottV 4) =
        Model.parrottV 7 * (Model.parrottV 10 * (Model.parrottV 11 * Model.parrottV 12)) := by
  obtain ⟨-, -, -, -, s⟩ := Model.parrott_squares
  have c104 := Model.parrottV_comm (r := (10, 4, [12])) (by decide)
  have c101 := Model.parrottV_comm (r := (10, 1, [11])) (by decide)
  have c91 := Model.parrottV_comm (r := (9, 1, [10, 11, 12])) (by decide)
  have c74 := Model.parrottV_comm (r := (7, 4, [10, 11, 12])) (by decide)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at c104 c101
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at c91 c74
  have z : ∀ j, 1 ≤ j → j ≤ 12 → Model.parrottV 12 * Model.parrottV j =
      Model.parrottV j * Model.parrottV 12 :=
    fun j h1 h2 => Model.parrottV_twelve_comm h1 h2
  have cm : ∀ {i j : ℕ}, 1 ≤ i → i ≤ 12 → 1 ≤ j → j ≤ 12 → listed i j = false →
      listed j i = false → Model.parrottV i * Model.parrottV j =
        Model.parrottV j * Model.parrottV i :=
    fun h1 h2 h3 h4 h5 h6 => Model.parrottV_commute h1 h2 h3 h4 h5 h6
  exact kapS_conj (s 10 (by norm_num) (by norm_num) (by decide))
    (s 11 (by norm_num) (by norm_num) (by decide)) (s 12 (by norm_num) (by norm_num) (by decide))
    (z 1 (by norm_num) (by norm_num)) (z 4 (by norm_num) (by norm_num))
    (z 10 (by norm_num) (by norm_num)) (z 11 (by norm_num) (by norm_num))
    (cm (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide))
    (cm (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide))
    (cm (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide)) c104 c101
    (cm (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide)) c91 c74
    (cm (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide))

end Model

end KappaT

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem Hyp.kappaW_sq_mem (h49 : d.Thm49Statement) (hd : d.Hyp) {g : G}
    (hgF : ∀ f ∈ d.F, g * f = f * g) (hgt : g * d.t * g⁻¹ = d.t * d.pv 10) :
    g * g ∈ d.B ∧ (d.s56Y * (g * g) * d.s56Y⁻¹ = g * g ∨
      d.s56Y * (g * g) * d.s56Y⁻¹ = g * g * d.pv 10) := by
  obtain ⟨hyNt, -, -, -, hy10, -, -⟩ := hd.s56_Y_facts
  have hyN : d.s56Y ∈ d.N := (mem_inf.1 hyNt).1
  have hyt : d.s56Y * d.t = d.t * d.s56Y := mem_centralizer_singleton_iff.1 (mem_inf.1 hyNt).2
  have hyF : d.s56Y ∈ normalizer (d.F : Set G) := by
    rw [mem_normalizer_iff]
    intro a
    refine ⟨fun ha => hd.s56_N_conj_F h49 hyN ha, fun ha => ?_⟩
    have := hd.s56_N_conj_F h49 (inv_mem hyN) ha
    simpa [mul_assoc] using this
  have hF2 : ∀ a ∈ d.F, a * a = 1 := fun a ha => hd.s56_F_sq ha
  have hFc : ∀ a ∈ d.F, ∀ b ∈ d.F, a * b = b * a := fun a ha b hb => hd.s56_F_comm ha hb
  have htF : ∀ a ∈ d.F, d.t * a = a * d.t := fun a ha =>
    (hd.L_comm_t (s56_F_le_L d ha)).symm
  have hCB : ∀ h : G, (∀ a ∈ d.F, h * a = a * h) → h * d.t = d.t * h →
      h ∈ d.F ⊔ zpowers d.t := by
    intro h hhF hht
    have hle : d.B ≤ centralizer ({h} : Set G) :=
      sup_le (fun a ha => mem_centralizer_singleton_iff.2 (hhF a ha).symm)
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 hht.symm))
    have hhC : h ∈ centralizer (d.B : Set G) :=
      mem_centralizer_iff.2 fun b hb => mem_centralizer_singleton_iff.1 (hle hb)
    rw [hd.centralizer_B] at hhC
    exact hhC
  obtain ⟨hB, hsq⟩ := KappaW.core d.F d.t (d.pv 10) d.s56Y g hF2 hFc hd.t_mul_self htF hCB
    (s56_pv10_mem_F d) hyF hyt hy10 hgF hgt
  refine ⟨hB, ?_⟩
  have hcomm : d.pv 10 * (g * g) = g * g * d.pv 10 := by
    have hv10c : g * d.pv 10 = d.pv 10 * g := hgF _ (s56_pv10_mem_F d)
    calc d.pv 10 * (g * g) = (d.pv 10 * g) * g := by group
      _ = (g * d.pv 10) * g := by rw [hv10c]
      _ = g * (d.pv 10 * g) := by group
      _ = g * (g * d.pv 10) := by rw [hv10c]
      _ = g * g * d.pv 10 := by group
  rcases hsq with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans hcomm)

theorem kappa_pv_mem_D {i : ℕ} (h7 : 7 ≤ i) (h12 : i ≤ 12) : Model.parrottV i ∈ titsD :=
  (Model.parrottV_mem_titsD_iff h12).2 (by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega)

theorem kS_mem_titsD : Model.parrottV 1 * Model.parrottV 4 ∈ titsD := by
  have h := Model.kWords_mem_titsK [1, 4] (by decide)
  simpa using titsK_le_titsD h

@[expose] noncomputable def kS (d : Data G) : G := d.lift (Model.parrottV 1 * Model.parrottV 4)

theorem kS_mem_K (d : Data G) : d.kS ∈ d.s56K := by
  have h := s56_kword_prod_mem (d := d) (w := [1, 4]) (by decide)
  simpa [kS] using h

theorem kS_conj (d : Data G) :
    d.kS * d.z * d.kS⁻¹ = d.z ∧ d.kS * d.pv 11 * d.kS⁻¹ = d.pv 11 ∧
      d.kS * d.pv 10 * d.kS⁻¹ = d.pv 10 * d.pv 11 * d.z ∧
      d.kS * d.pv 9 * d.kS⁻¹ = d.pv 9 * d.pv 10 * d.z ∧
      d.kS⁻¹ * d.pv 7 * d.kS = d.pv 7 * (d.pv 10 * (d.pv 11 * d.z)) := by
  obtain ⟨m12, m11, m10, m9, m7⟩ := KappaT.kapS_model
  have hδD : Model.parrottV 1 * Model.parrottV 4 ∈ titsD := kS_mem_titsD
  have hD : ∀ {i : ℕ}, 7 ≤ i → i ≤ 12 → Model.parrottV i ∈ titsD := fun h7 h12 =>
    kappa_pv_mem_D h7 h12
  have hconj : ∀ x ∈ titsD, d.kS * d.lift x * d.kS⁻¹ =
      d.lift (Model.parrottV 1 * Model.parrottV 4 * x *
        (Model.parrottV 1 * Model.parrottV 4)⁻¹) := fun x hx =>
    (d.lift_conj hδD hx).symm
  have hconj' : ∀ x ∈ titsD, d.kS⁻¹ * d.lift x * d.kS =
      d.lift ((Model.parrottV 1 * Model.parrottV 4)⁻¹ * x *
        (Model.parrottV 1 * Model.parrottV 4)) := fun x hx => by
    have h := d.lift_conj (inv_mem hδD) hx
    rw [inv_inv, d.lift_inv hδD, inv_inv] at h
    exact h.symm
  have h12 := hD (i := 12) (by norm_num) (le_refl _)
  have h11 := hD (i := 11) (by norm_num) (by norm_num)
  have h10 := hD (i := 10) (by norm_num) (by norm_num)
  have h9 := hD (i := 9) (by norm_num) (by norm_num)
  have h7 := hD (i := 7) (by norm_num) (by norm_num)
  have e12 : d.pv 12 = d.z := s56_pv12 d
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← e12]
    show d.kS * d.lift (Model.parrottV 12) * d.kS⁻¹ = d.lift (Model.parrottV 12)
    rw [hconj _ h12, m12]
  · show d.kS * d.lift (Model.parrottV 11) * d.kS⁻¹ = d.lift (Model.parrottV 11)
    rw [hconj _ h11, m11]
  · show d.kS * d.lift (Model.parrottV 10) * d.kS⁻¹ = d.lift (Model.parrottV 10) *
      d.lift (Model.parrottV 11) * d.z
    rw [hconj _ h10, m10, d.lift_mul (mul_mem h10 h11) h12, d.lift_mul h10 h11,
      show d.lift (Model.parrottV 12) = d.z from e12]
  · show d.kS * d.lift (Model.parrottV 9) * d.kS⁻¹ = d.lift (Model.parrottV 9) *
      d.lift (Model.parrottV 10) * d.z
    rw [hconj _ h9, m9, d.lift_mul (mul_mem h9 h10) h12, d.lift_mul h9 h10,
      show d.lift (Model.parrottV 12) = d.z from e12]
  · show d.kS⁻¹ * d.lift (Model.parrottV 7) * d.kS = d.lift (Model.parrottV 7) *
      (d.lift (Model.parrottV 10) * (d.lift (Model.parrottV 11) * d.z))
    rw [hconj' _ h7, m7, d.lift_mul h7 (mul_mem h10 (mul_mem h11 h12)),
      d.lift_mul h10 (mul_mem h11 h12), d.lift_mul h11 h12,
      show d.lift (Model.parrottV 12) = d.z from e12]

@[expose] noncomputable def kTau (d : Data G) (x : G) : G := x * d.pv 7 * x⁻¹ * (d.pv 7)⁻¹

theorem Hyp.kTau_mul (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) {a b : G}
    (ha : a ∈ d.s56V) (hb : b ∈ d.s56V) : d.kTau (a * b) = d.kTau a * d.kTau b :=
  hd.s56_V_comm_pv7_hom h49 hz ha hb

theorem Hyp.kTau_E (hd : d.Hyp) {e : G} (he : e ∈ d.E) : d.kTau e ∈ zpowers d.z := by
  have h := inv_mem (hd.s56_pv7_conj_E he)
  have e' : (d.pv 7 * e * (d.pv 7)⁻¹ * e⁻¹)⁻¹ = d.kTau e := by
    rw [kTau]; group
  rwa [e'] at h

theorem Hyp.kTau_z0 (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) :
    d.kTau z₀ = 1 := by
  have h : d.pv 7 * z₀ = z₀ * d.pv 7 := hz.comm_Q _ (hd.s56_F_le_Q h49 hd.s56_pv7_mem_F)
  rw [kTau]
  calc z₀ * d.pv 7 * z₀⁻¹ * (d.pv 7)⁻¹ = (z₀ * d.pv 7) * z₀⁻¹ * (d.pv 7)⁻¹ := by group
    _ = (d.pv 7 * z₀) * z₀⁻¹ * (d.pv 7)⁻¹ := by rw [h]
    _ = 1 := by group

theorem Hyp.zpowers_z_cases (hd : d.Hyp) {a : G} (ha : a ∈ zpowers d.z) : a = 1 ∨ a = d.z := by
  have hz2 : d.z * d.z = 1 := hd.s56_E_sq hd.s56_z_mem_E
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
  · left
    rw [zpow_mul]
    simp [zpow_ofNat, sq, hz2]
  · right
    rw [zpow_add, zpow_mul]
    simp [zpow_ofNat, sq, hz2]

theorem Hyp.kappa_V_eps_eq (h49 : d.Thm49Statement) (hd : d.Hyp) {a b : G} (ha : a ∈ d.s56V)
    (hb : b ∈ d.s56V) (h : d.s56Eps a = d.s56Eps b) : ∃ e ∈ d.E, a = e * b := by
  have heV : a * b⁻¹ ∈ d.s56V := mul_mem ha (inv_mem hb)
  have hε : d.s56Eps (a * b⁻¹) = 1 := by
    rw [hd.s56_eps_mul_Q2' ha.2 (inv_mem hb).2, hd.s56_eps_inv_Q2 hb.2, h]
    exact hd.s56_E_sq (hd.s56_V_eps_mem_E hb)
  exact ⟨a * b⁻¹, (hd.s56_V_eps_eq_one_iff h49 heV).1 hε, by group⟩

theorem kS_conj_U11 (d : Data G) {u : G} (hu : u ∈ d.s56U11) : d.kS * u * d.kS⁻¹ = u := by
  obtain ⟨-, h11, -⟩ := kS_conj d
  obtain ⟨hz, -⟩ := kS_conj d
  rcases s56_mem_U11_iff.1 hu with rfl | rfl | rfl | rfl
  · group
  · exact h11
  · exact hz
  · have e : d.kS * (d.pv 11 * d.z) * d.kS⁻¹ =
        (d.kS * d.pv 11 * d.kS⁻¹) * (d.kS * d.z * d.kS⁻¹) := by group
    rw [e, h11, hz]

theorem E_ident {A : Subgroup G} (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    {a v10 u v11 z : G} (ha : a ∈ A) (h10 : v10 ∈ A) (hu : u ∈ A) (h11 : v11 ∈ A) (hz : z ∈ A)
    (ha2 : a * a = 1) : (a * (v10 * u)) * (a * v11 * z) = (v10 * v11 * z) * u := by
  haveI : IsMulCommutative A := ⟨⟨fun x y => Subtype.ext (hc x.1 x.2 y.1 y.2)⟩⟩
  have key : ((⟨a, ha⟩ : A) * ((⟨v10, h10⟩ : A) * ⟨u, hu⟩)) * ((⟨a, ha⟩ : A) * ⟨v11, h11⟩ * ⟨z, hz⟩)
      = ((⟨v10, h10⟩ : A) * ⟨v11, h11⟩ * ⟨z, hz⟩) * ⟨u, hu⟩ := by
    have h2 : (⟨a, ha⟩ : A) * ⟨a, ha⟩ = 1 := Subtype.ext ha2
    calc ((⟨a, ha⟩ : A) * ((⟨v10, h10⟩ : A) * ⟨u, hu⟩)) * ((⟨a, ha⟩ : A) * ⟨v11, h11⟩ * ⟨z, hz⟩)
        = ((⟨a, ha⟩ : A) * ⟨a, ha⟩) * (((⟨v10, h10⟩ : A) * ⟨v11, h11⟩ * ⟨z, hz⟩) * ⟨u, hu⟩) := by
          ac_rfl
      _ = ((⟨v10, h10⟩ : A) * ⟨v11, h11⟩ * ⟨z, hz⟩) * ⟨u, hu⟩ := by rw [h2, one_mul]
  exact congrArg Subtype.val key

theorem Hyp.kappaT_comm_pv7 (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    (hκ : ¬ d.S56KappaBit) {x : G} (hxV : x ∈ d.s56V) (hxε : d.s56Eps x = d.pv 10) :
    x * d.pv 7 * x⁻¹ * (d.pv 7)⁻¹ = d.pv 11 ∨
      x * d.pv 7 * x⁻¹ * (d.pv 7)⁻¹ = d.pv 11 * d.z := by
  classical
  have hv7F : d.pv 7 ∈ d.F := hd.s56_pv7_mem_F
  have hzE : d.z ∈ d.E := hd.s56_z_mem_E
  have hz2 : d.z * d.z = 1 := hd.s56_E_sq hzE
  have hv10E : d.pv 10 ∈ d.E := hd.s56_pv10_mem_E
  have hU11E : d.s56U11 ≤ d.E := s56_U11_le_E d hd
  have hv11E : d.pv 11 ∈ d.E := hU11E (s56_pv11_mem_U11 d)
  have hEV : d.E ≤ d.s56V := hd.s56_E_le_V h49
  have hEc : ∀ a ∈ d.E, ∀ b ∈ d.E, a * b = b * a := fun a ha b hb => hd.s56_E_comm ha hb
  obtain ⟨x₉, hx₉V, hx₉ε⟩ := hd.s56_V_eps_surj h49 hz (d.pv 9) (N.node09K_pv9_mem_E d)
  have hx₉Q0 : x₉ ∈ d.s56Q0 := hd.s56_Q_le_Q0 hx₉V.1
  have hx₉N : x₉ ∈ d.N :=
    (hd.s56_mem_N_iff_eps h49 hx₉Q0).2 (by rw [hx₉ε]; exact N.node09K_pv9_mem_F d)
  have hx₉P0 : x₉ ∈ d.s56P0 := hd.s56_Q2_inf_N_le_P0 h49 hx₉V.2 hx₉N
  have hτ₉U10 : d.kTau x₉ ∈ d.s56U10 := hd.s56_P0_comm_F_le_U10 h49 hx₉P0 hv7F
  have hτ₉U11 : d.kTau x₉ ∉ d.s56U11 := fun h =>
    hκ ⟨x₉, mem_inf.2 ⟨hx₉V, hx₉N⟩, by rw [hx₉ε]; exact N.node09K_pv9_not_mem_U10 d, h⟩
  obtain ⟨u, huU, hτ₉⟩ : ∃ u ∈ d.s56U11, d.kTau x₉ = d.pv 10 * u := by
    rcases s56_U10_cases hτ₉U10 with h | h
    · exact absurd h hτ₉U11
    · exact h
  have hsK : d.kS ∈ d.s56K := kS_mem_K d
  have hsC : d.kS ∈ centralizer ({d.t} : Set G) := (mem_inf.1 (hd.s56_K_le_CNt hsK)).2
  have hst : d.kS * d.t = d.t * d.kS := mem_centralizer_singleton_iff.1 hsC
  have hsM : d.kS ∈ d.M := hd.s56_CP0t_le_M (hd.s56_K_le_P0 h49 hsK) hsC
  obtain ⟨cz, c11, c10, c9, c7⟩ := kS_conj d
  have hx₉'V : d.kS * x₉ * d.kS⁻¹ ∈ d.s56V := hd.s56_V_conj_mem h49 hsM hx₉V
  have hε₉' : d.s56Eps (d.kS * x₉ * d.kS⁻¹) = d.pv 9 * d.pv 10 * d.z := by
    rw [hd.s56_eps_conj hst, hx₉ε, c9]
  have hz₀V : z₀ ∈ d.s56V := mem_inf.2 ⟨hz.mem_Q, hz.mem_Q2⟩
  have hcV : x₉ * x * z₀ ∈ d.s56V := mul_mem (mul_mem hx₉V hxV) hz₀V
  have hεc : d.s56Eps (x₉ * x * z₀) = d.pv 9 * d.pv 10 * d.z := by
    rw [hd.s56_eps_mul_Q2' (mul_mem hx₉V.2 hxV.2) hz₀V.2, hd.s56_eps_mul_Q2' hx₉V.2 hxV.2, hx₉ε,
      hxε, hz.eps]
  obtain ⟨e, heE, hec⟩ := hd.kappa_V_eps_eq h49 hx₉'V hcV (hε₉'.trans hεc.symm)
  have hτ1 : d.kTau (d.kS * x₉ * d.kS⁻¹) = d.kTau e * (d.kTau x₉ * d.kTau x) := by
    rw [hec, hd.kTau_mul h49 hz (hEV heE) hcV, hd.kTau_mul h49 hz (mul_mem hx₉V hxV) hz₀V,
      hd.kTau_mul h49 hz hx₉V hxV, hd.kTau_z0 h49 hz, mul_one]
  have hwE : d.pv 10 * (d.pv 11 * d.z) ∈ d.E := mul_mem hv10E (mul_mem hv11E hzE)
  have hxw : x₉ * (d.pv 10 * (d.pv 11 * d.z)) = (d.pv 10 * (d.pv 11 * d.z)) * x₉ :=
    s56_V_comm_E hx₉V hwE
  have hτ2 : d.kTau (d.kS * x₉ * d.kS⁻¹) = d.kS * d.kTau x₉ * d.kS⁻¹ := by
    have e1 : x₉ * (d.pv 10 * (d.pv 11 * d.z)) * x₉⁻¹ = d.pv 10 * (d.pv 11 * d.z) := by
      rw [hxw]; group
    have e2 : x₉ * d.pv 7 * x₉⁻¹ = d.kTau x₉ * d.pv 7 := by simp only [kTau]; group
    calc d.kTau (d.kS * x₉ * d.kS⁻¹)
        = d.kS * x₉ * (d.kS⁻¹ * d.pv 7 * d.kS) * x₉⁻¹ * d.kS⁻¹ * (d.pv 7)⁻¹ := by
          simp only [kTau]; group
      _ = d.kS * x₉ * (d.pv 7 * (d.pv 10 * (d.pv 11 * d.z))) * x₉⁻¹ * d.kS⁻¹ * (d.pv 7)⁻¹ := by
          rw [c7]
      _ = d.kS * (x₉ * d.pv 7 * x₉⁻¹) * (x₉ * (d.pv 10 * (d.pv 11 * d.z)) * x₉⁻¹) * d.kS⁻¹ *
            (d.pv 7)⁻¹ := by group
      _ = d.kS * (d.kTau x₉ * d.pv 7) * (d.pv 10 * (d.pv 11 * d.z)) * d.kS⁻¹ * (d.pv 7)⁻¹ := by
          rw [e1, e2]
      _ = d.kS * d.kTau x₉ * (d.pv 7 * (d.pv 10 * (d.pv 11 * d.z))) * d.kS⁻¹ * (d.pv 7)⁻¹ := by
          group
      _ = d.kS * d.kTau x₉ * (d.kS⁻¹ * d.pv 7 * d.kS) * d.kS⁻¹ * (d.pv 7)⁻¹ := by rw [c7]
      _ = d.kS * d.kTau x₉ * d.kS⁻¹ := by group
  have hsτ9 : d.kS * d.kTau x₉ * d.kS⁻¹ = (d.pv 10 * d.pv 11 * d.z) * u := by
    rw [hτ₉]
    have e : d.kS * (d.pv 10 * u) * d.kS⁻¹ =
        (d.kS * d.pv 10 * d.kS⁻¹) * (d.kS * u * d.kS⁻¹) := by group
    rw [e, c10, kS_conj_U11 d huU]
  have hEq : (d.pv 10 * d.pv 11 * d.z) * u = d.kTau e * (d.pv 10 * u * d.kTau x) := by
    calc (d.pv 10 * d.pv 11 * d.z) * u = d.kS * d.kTau x₉ * d.kS⁻¹ := hsτ9.symm
      _ = d.kTau (d.kS * x₉ * d.kS⁻¹) := hτ2.symm
      _ = d.kTau e * (d.kTau x₉ * d.kTau x) := hτ1
      _ = d.kTau e * (d.pv 10 * u * d.kTau x) := by rw [hτ₉]
  have huE : u ∈ d.E := hU11E huU
  have key : ∀ a : G, a ∈ d.E → a * a = 1 → d.kTau e = a → d.kTau x = a * d.pv 11 * d.z := by
    intro a haE ha2 hae
    rw [hae] at hEq
    have hid := E_ident hEc haE hv10E huE hv11E hzE ha2
    have h2 : (a * (d.pv 10 * u)) * d.kTau x = (a * (d.pv 10 * u)) * (a * d.pv 11 * d.z) := by
      calc (a * (d.pv 10 * u)) * d.kTau x = a * (d.pv 10 * u * d.kTau x) := by group
        _ = (d.pv 10 * d.pv 11 * d.z) * u := hEq.symm
        _ = (a * (d.pv 10 * u)) * (a * d.pv 11 * d.z) := hid.symm
    exact mul_left_cancel h2
  rcases hd.zpowers_z_cases (hd.kTau_E heE) with h | h
  · right
    have := key 1 (one_mem _) (mul_one 1) h
    rwa [one_mul] at this
  · left
    have := key d.z hzE hz2 h
    rw [show d.z * d.pv 11 * d.z = d.pv 11 by
      rw [hEc d.z hzE (d.pv 11) hv11E, mul_assoc, hz2, mul_one]] at this
    exact this

theorem Hyp.kappaW (h49 : d.Thm49Statement) (hd : d.Hyp) {g : G}
    (hgF : ∀ f ∈ d.F, g * f = f * g) (hgt : g * d.t * g⁻¹ = d.t * d.pv 10)
    (hg2 : g * g = d.z) : False := by
  obtain ⟨-, h⟩ := hd.kappaW_sq_mem h49 hgF hgt
  obtain ⟨-, -, -, -, -, -, hyz⟩ := hd.s56_Y_facts
  rw [hg2, hyz] at h
  rcases h with h | h
  · exact s56_pv11_ne_one d (mul_eq_right.1 h)
  · have hc : d.z * d.pv 10 = d.pv 10 * d.z := hd.s56_F_comm hd.s56_z_mem_F (s56_pv10_mem_F d)
    rw [hc] at h
    have h11 : d.pv 11 = d.pv 10 := mul_right_cancel h
    exact s56_pv10_not_mem_U11 d (h11 ▸ s56_pv11_mem_U11 d)

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
