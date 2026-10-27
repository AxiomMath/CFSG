module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp

public section

namespace CFSG.LieType.SeitzGeneration

namespace RootPairOrth

section Core

variable {ι K : Type} [Field K]

def SigmaRel (σ : K →+* K) (κ : K) (u w : ι → K) : Prop :=
  ∀ r s, σ (u r * w s - u s * w r) = κ * (u r * w s - u s * w r)

theorem SigmaRel.self (σ : K →+* K) (κ : K) (u : ι → K) : SigmaRel σ κ u u := fun r s => by
  have : u r * u s - u s * u r = 0 := by ring
  rw [this]
  simp

theorem SigmaRel.add_left {σ : K →+* K} {κ : K} {u u' w : ι → K} (h : SigmaRel σ κ u w)
    (h' : SigmaRel σ κ u' w) : SigmaRel σ κ (u + u') w := fun r s => by
  have e : (u + u') r * w s - (u + u') s * w r =
      (u r * w s - u s * w r) + (u' r * w s - u' s * w r) := by
    simp only [Pi.add_apply]; ring
  rw [e, map_add, h r s, h' r s]
  ring

theorem SigmaRel.exists_combo {σ : K →+* K} {κ : K} (hκ : κ ≠ 0) {u w : ι → K}
    (h : SigmaRel σ κ u w) {a b : ι} (hab : u a * w b - u b * w a ≠ 0) :
    ∃ α β : K, ∀ r, σ (u r) = α * u r + β * w r := by
  set p := u a * w b - u b * w a with hp
  refine ⟨(σ (u a) * w b - σ (u b) * w a) / p, (σ (u b) * u a - σ (u a) * u b) / p, fun r => ?_⟩
  have e : u r * p = u a * (u r * w b - u b * w r) + u b * (u a * w r - u r * w a) := by
    rw [hp]; ring
  have h1 := congrArg σ e
  have hp' : σ p = κ * p := h a b
  rw [map_mul, map_add, map_mul, map_mul, hp', h r b, h a r] at h1
  have h2 : σ (u r) * p = σ (u a) * (u r * w b - u b * w r) +
      σ (u b) * (u a * w r - u r * w a) := by
    apply mul_left_cancel₀ hκ
    linear_combination h1
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hab]
  linear_combination h2

theorem exists_minor_ne_zero [Fintype ι] {u w : ι → K}
    (hind : ∀ a b : K, a • u + b • w = 0 → a = 0 ∧ b = 0) :
    ∃ a b, u a * w b - u b * w a ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hu : u ≠ 0 := fun h => by
    have := (hind 1 0 (by simp [h])).1
    exact one_ne_zero this
  obtain ⟨r₀, hr₀⟩ := Function.ne_iff.mp hu
  have hr₀' : u r₀ ≠ 0 := hr₀
  have := hind (w r₀ / u r₀) (-1) (by
    funext r
    have h3 := hcon r₀ r
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    field_simp
    linear_combination -h3)
  exact absurd this.2 (by norm_num)

theorem SigmaRel.line [Fintype ι] {σ : K →+* K} {κ : K} (hκ : κ ≠ 0) {u w z : ι → K}
    (hw : SigmaRel σ κ u w) (hz : SigmaRel σ κ u z)
    (hind : ∀ a b c : K, a • u + b • w + c • z = 0 → a = 0 ∧ b = 0 ∧ c = 0) :
    ∃ α : K, ∀ r, σ (u r) = α * u r := by
  obtain ⟨a, b, hab⟩ := exists_minor_ne_zero (u := u) (w := w) fun x y hxy =>
    (let h := hind x y 0 (by simpa using hxy); ⟨h.1, h.2.1⟩)
  obtain ⟨a', b', hab'⟩ := exists_minor_ne_zero (u := u) (w := z) fun x y hxy =>
    (let h := hind x 0 y (by simpa using hxy); ⟨h.1, h.2.2⟩)
  obtain ⟨α, β, h1⟩ := hw.exists_combo hκ hab
  obtain ⟨α', β', h2⟩ := hz.exists_combo hκ hab'
  have h3 : (α - α') • u + β • w + (-β') • z = 0 := by
    funext r
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    linear_combination (h1 r).symm.trans (h2 r)
  have h4 := hind _ _ _ h3
  refine ⟨α, fun r => ?_⟩
  rw [h1 r, h4.2.1]
  ring

theorem cols_indep3 [Fintype ι] [DecidableEq ι] {g : Matrix ι ι K} (hg : g.det ≠ 0)
    {c₀ c₁ c₂ : ι} (h01 : c₀ ≠ c₁) (h02 : c₀ ≠ c₂) (h12 : c₁ ≠ c₂) (a b c : K)
    (h : a • (fun r => g r c₀) + b • (fun r => g r c₁) + c • (fun r => g r c₂) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hli := Matrix.linearIndependent_cols_of_det_ne_zero hg
  have hsum : ∑ i, ((if i = c₀ then a else 0) + (if i = c₁ then b else 0) +
      (if i = c₂ then c else 0)) • g.col i = 0 := by
    simp only [add_smul, ite_smul, zero_smul, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    exact h
  have key := Fintype.linearIndependent_iff.mp hli _ hsum
  refine ⟨?_, ?_, ?_⟩
  · have := key c₀
    simpa [h01, h02] using this
  · have := key c₁
    simpa [h01.symm, h12] using this
  · have := key c₂
    simpa [h02.symm, h12.symm] using this

theorem exists_two_ne [Fintype ι] (hι : 3 ≤ Fintype.card ι) (c : ι) :
    ∃ c' c'' : ι, c' ≠ c ∧ c'' ≠ c ∧ c' ≠ c'' := by
  classical
  have h2 : 1 < (Finset.univ.erase c).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ]
    omega
  obtain ⟨c', hc', c'', hc'', hne⟩ := Finset.one_lt_card.mp h2
  exact ⟨c', c'', (Finset.mem_erase.mp hc').1, (Finset.mem_erase.mp hc'').1, hne⟩

theorem exists_ne_two [Fintype ι] [DecidableEq ι] (hι : 3 ≤ Fintype.card ι) (c c' : ι) :
    ∃ c'' : ι, c'' ≠ c ∧ c'' ≠ c' := by
  by_contra hcon
  push Not at hcon
  have : (Finset.univ : Finset ι) ⊆ {c, c'} := fun x _ => by
    by_cases h : x = c
    · simp [h]
    · simp [hcon x h]
  have := Finset.card_le_card this
  rw [Finset.card_univ] at this
  have h2 := Finset.card_le_two (a := c) (b := c')
  omega

theorem rational_of_minors [Fintype ι] [DecidableEq ι] (hι : 3 ≤ Fintype.card ι) {σ : K →+* K}
    {k : Subfield K} (hσ : ∀ x, σ x = x ↔ x ∈ k) {μ : K} (hμ : μ ≠ 0) {g : Matrix ι ι K}
    (hg : g.det ≠ 0) (hmin : ∀ r s c c', μ⁻¹ * (g r c * g s c' - g r c' * g s c) ∈ k) :
    ∃ a : K, a ≠ 0 ∧ ∀ r c, σ (g r c) = a * g r c := by
  set κ := σ μ / μ with hκdef
  have hσμ : σ μ ≠ 0 := (map_ne_zero σ).mpr hμ
  have hκ : κ ≠ 0 := div_ne_zero hσμ hμ
  have hrel : ∀ c c', SigmaRel σ κ (fun r => g r c) (fun r => g r c') := by
    intro c c' r s
    have hq := (hσ _).mpr (hmin r s c c')
    rw [map_mul, map_inv₀] at hq
    have e : g r c * g s c' - g s c * g r c' = g r c * g s c' - g r c' * g s c := by ring
    show σ (g r c * g s c' - g s c * g r c') = κ * (g r c * g s c' - g s c * g r c')
    rw [e, hκdef]
    field_simp
    field_simp at hq
    linear_combination hq
  have hpair : ∀ c c', c ≠ c' → ∃ a : K, (∀ r, σ (g r c) = a * g r c) ∧
      (∀ r, σ (g r c') = a * g r c') := by
    intro c c' hcc'
    obtain ⟨c'', h1, h2⟩ := exists_ne_two hι c c'
    have hc1 : c ≠ c'' := h1.symm
    have hc2 : c' ≠ c'' := h2.symm
    obtain ⟨a₁, ha₁⟩ := SigmaRel.line hκ (hrel c c') (hrel c c'')
      (fun a b d h => cols_indep3 hg hcc' hc1 hc2 a b d h)
    obtain ⟨a₂, ha₂⟩ := SigmaRel.line hκ (hrel c' c) (hrel c' c'')
      (fun a b d h => cols_indep3 hg hcc'.symm hc2 hc1 a b d h)
    have hw : SigmaRel σ κ (fun r => g r c + g r c') (fun r => g r c') :=
      (hrel c c').add_left (SigmaRel.self σ κ _)
    have hz : SigmaRel σ κ (fun r => g r c + g r c') (fun r => g r c'') :=
      (hrel c c'').add_left (hrel c' c'')
    obtain ⟨a₃, ha₃⟩ := SigmaRel.line hκ hw hz (fun a b d h => by
      have h' := cols_indep3 hg hcc' hc1 hc2 a (a + b) d (by
        funext r
        have := congrFun h r
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
        linear_combination this)
      exact ⟨h'.1, by linear_combination h'.2.1 - h'.1, h'.2.2⟩)
    have h4 : (a₁ - a₃) • (fun r => g r c) + (a₂ - a₃) • (fun r => g r c') +
        (0 : K) • (fun r => g r c'') = 0 := by
      funext r
      have h5 := ha₃ r
      simp only [map_add, ha₁ r, ha₂ r] at h5
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_mul, add_zero]
      linear_combination h5
    have h6 := cols_indep3 hg hcc' hc1 hc2 _ _ _ h4
    refine ⟨a₃, fun r => ?_, fun r => ?_⟩
    · rw [ha₁ r, sub_eq_zero.mp h6.1]
    · rw [ha₂ r, sub_eq_zero.mp h6.2.1]
  have hne : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hg0 : g ≠ 0 := fun h => hg (by rw [h]; exact Matrix.det_zero)
  obtain ⟨r₀, c₀, hrc⟩ : ∃ r c, g r c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hg0 (Matrix.ext hcon)
  obtain ⟨c₁, -, hc₁, -⟩ := exists_two_ne hι c₀
  obtain ⟨a₀, ha₀, -⟩ := hpair c₀ c₁ hc₁.symm
  have hall : ∀ r c, σ (g r c) = a₀ * g r c := by
    intro r c
    by_cases hc : c = c₀
    · rw [hc]; exact ha₀ r
    · obtain ⟨a, ha, hac⟩ := hpair c₀ c (Ne.symm hc)
      have : a = a₀ := by
        have h1 := (ha r₀).symm.trans (ha₀ r₀)
        exact mul_right_cancel₀ hrc h1
      rw [hac r, this]
  have hl : σ (g r₀ c₀) = a₀ * g r₀ c₀ := hall r₀ c₀
  exact ⟨a₀, fun h => (map_ne_zero σ |>.mpr hrc) (by rw [hl, h, zero_mul]), hall⟩

end Core

end RootPairOrth

end CFSG.LieType.SeitzGeneration
