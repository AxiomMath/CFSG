module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.AutCenter

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section ModZ

theorem miyamotoA2_le_gramSU' : miyamotoA2 h ≤ gramSU h (miyamotoJ4 K) :=
  miyamotoUnipotent_le_SU h false true

theorem miyamotoZ_le_A2' : miyamotoZ h ≤ miyamotoA2 h := by
  have : CharP K 2 := h.charP
  exact (miyamotoZ_le_Z2 h).trans (miyamotoZ2_le_A2 h)

theorem fixes_Z_of_fixes_mod_Z {α : MulAut (gramSU h (miyamotoJ4 K))}
    (hα : ∀ g : gramSU h (miyamotoJ4 K), (g : GL (Fin 4) K) ∈ miyamotoA2 h →
      (g : GL (Fin 4) K)⁻¹ * (α g : GL (Fin 4) K) ∈ miyamotoZ h)
    (g : gramSU h (miyamotoJ4 K)) (hg : (g : GL (Fin 4) K) ∈ miyamotoZ h) : α g = g := by
  have : CharP K 2 := h.charP
  set Fix : Subgroup (GL (Fin 4) K) :=
    (MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id _)).map (gramSU h (miyamotoJ4 K)).subtype
    with hFix
  have hcomm : ⁅miyamotoA2 h, miyamotoA2 h⁆ ≤ Fix := by
    rw [commutator_le]
    intro x hx y hy
    set x' : gramSU h (miyamotoJ4 K) := ⟨x, miyamotoA2_le_gramSU' h hx⟩
    set y' : gramSU h (miyamotoJ4 K) := ⟨y, miyamotoA2_le_gramSU' h hy⟩
    refine ⟨⁅x', y'⁆, ?_, rfl⟩
    change α ⁅x', y'⁆ = ⁅x', y'⁆
    have hz1 := hα x' hx
    have hz2 := hα y' hy
    set z1 := (x : GL (Fin 4) K)⁻¹ * (α x' : GL (Fin 4) K) with hz1def
    set z2 := (y : GL (Fin 4) K)⁻¹ * (α y' : GL (Fin 4) K) with hz2def
    have ex : (α x' : GL (Fin 4) K) = x * z1 := by rw [hz1def]; group
    have ey : (α y' : GL (Fin 4) K) = y * z2 := by rw [hz2def]; group
    have c1 := miyamotoA2_commute_Z h hx hz1
    have c2 := miyamotoA2_commute_Z h hy hz1
    have c3 := miyamotoA2_commute_Z h hx hz2
    have c4 := miyamotoA2_commute_Z h hy hz2
    have c5 := miyamotoA2_commute_Z h (miyamotoZ_le_A2' h hz1) hz2
    apply Subtype.ext
    rw [map_commutatorElement, commutatorElement_def, commutatorElement_def, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, ex, ey,
      Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv]
    change x * z1 * (y * z2) * (x * z1)⁻¹ * (y * z2)⁻¹ = x * y * x⁻¹ * y⁻¹
    calc x * z1 * (y * z2) * (x * z1)⁻¹ * (y * z2)⁻¹ =
        x * (z1 * y) * z2 * z1⁻¹ * x⁻¹ * z2⁻¹ * y⁻¹ := by group
      _ = x * y * (z1 * z2) * z1⁻¹ * x⁻¹ * z2⁻¹ * y⁻¹ := by rw [← c2]; group
      _ = x * y * z2 * x⁻¹ * z2⁻¹ * y⁻¹ := by rw [c5]; group
      _ = x * y * x⁻¹ * y⁻¹ := by
          rw [show x * y * z2 * x⁻¹ * z2⁻¹ * y⁻¹ = x * y * (z2 * x⁻¹) * z2⁻¹ * y⁻¹ by group,
            show z2 * x⁻¹ = x⁻¹ * z2 by
              rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← c3, ← mul_assoc, inv_mul_cancel, one_mul]]
          group
  rw [commutator_miyamotoA2] at hcomm
  obtain ⟨g', hg', e⟩ := hcomm hg
  have : g' = g := Subtype.ext e
  rw [← this]
  exact hg'

theorem levi_mod_Z_entries {b : Kˣ} (hb : h.norm (b : K) = 1) {m : SpecialLinearGroup (Fin 2)
    h.fixedField} {φ : K ≃+* K} {a' c' d' e : K}
    (hD : miyamotoI2Hom h b * ((Units.map (miyamotoN2Mat K)).comp (SpecialLinearGroup.toGL.comp
      (SpecialLinearGroup.map (h.fixedField.subtype : h.fixedField →+* K)))) m *
        glAut φ (miyamotoXGL h a' 0 c' d') = miyamotoXGL h a' 0 c' d' * miyamotoXGL h 0 0 0 e *
          (miyamotoI2Hom h b * ((Units.map (miyamotoN2Mat K)).comp (SpecialLinearGroup.toGL.comp
            (SpecialLinearGroup.map (h.fixedField.subtype : h.fixedField →+* K)))) m)) :
    ((m : Matrix (Fin 2) (Fin 2) h.fixedField) 0 0 : K) * φ a' +
        ((m : Matrix (Fin 2) (Fin 2) h.fixedField) 0 1 : K) * φ c' = ((b : K) ^ 2) ^ 2 * a' ∧
      ((m : Matrix (Fin 2) (Fin 2) h.fixedField) 1 0 : K) * φ a' +
        ((m : Matrix (Fin 2) (Fin 2) h.fixedField) 1 1 : K) * φ c' = ((b : K) ^ 2) ^ 2 * c' := by
  have hb0 : (b : K) ≠ 0 := b.ne_zero
  have hM := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) hD
  simp only [Units.val_mul, coe_glAut, coe_miyamotoXGL, coe_miyamotoI2Hom_of_norm h hb] at hM
  have E10 := congrFun (congrFun hM 1) 0
  have E20 := congrFun (congrFun hM 2) 0
  simp [Matrix.mul_apply, Fin.sum_univ_four, miyamotoX, miyamotoN2Mat, diagonal] at E10 E20
  constructor
  · field_simp at E10
    linear_combination E10
  · field_simp at E20
    linear_combination E20

theorem fixes_mod_Z_iff (α : MulAut (gramSU h (miyamotoJ4 K))) :
    (∀ g : gramSU h (miyamotoJ4 K), (g : GL (Fin 4) K) ∈ miyamotoA2 h →
      (g : GL (Fin 4) K)⁻¹ * (α g : GL (Fin 4) K) ∈ miyamotoZ h) ↔
      ∃ a : gramSU h (miyamotoJ4 K), (a : GL (Fin 4) K) ∈ miyamotoA2 h ∧ α = MulAut.conj a := by
  have : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  constructor
  · intro hα
    obtain ⟨s, ⟨a, ha, i, hi, n, hn, hs⟩, φ, hφ, hαs⟩ :=
      (fixes_miyamotoZ_iff h α).mp (fixes_Z_of_fixes_mod_Z h hα)
    obtain ⟨b, hb, rfl⟩ := (mem_miyamotoI2Norm1 h).mp hi
    obtain ⟨m, rfl⟩ := hn
    set D := miyamotoI2Hom h b * ((Units.map (miyamotoN2Mat K)).comp (SpecialLinearGroup.toGL.comp
      (SpecialLinearGroup.map (h.fixedField.subtype : h.fixedField →+* K)))) m with hDdef
    have key : ∀ a' c' d' : K, miyamotoXGL h a' 0 c' d' ∈ miyamotoA2 h →
        ∃ e : K, D * glAut φ (miyamotoXGL h a' 0 c' d') =
          miyamotoXGL h a' 0 c' d' * miyamotoXGL h 0 0 0 e * D := by
      intro a' c' d' hg
      set g := miyamotoXGL h a' 0 c' d' with hgdef
      have hz := hα ⟨g, miyamotoA2_le_gramSU' h hg⟩ hg
      set z := g⁻¹ * (α ⟨g, miyamotoA2_le_gramSU' h hg⟩ : GL (Fin 4) K) with hzdef
      have hαg : (α ⟨g, miyamotoA2_le_gramSU' h hg⟩ : GL (Fin 4) K) =
          a * D * glAut φ g * (a * D)⁻¹ := by
        rw [hαs]
        simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
          coe_miyamotoFieldAut_apply]
        rw [hs, hDdef]
      have hza : a⁻¹ * z * a = z := by
        rw [mul_assoc, ← miyamotoA2_commute_Z h ha hz]; group
      have hz' : g⁻¹ * (D * glAut φ g * D⁻¹) ∈ miyamotoZ h := by
        have e2 : g⁻¹ * (D * glAut φ g * D⁻¹) = ⁅g⁻¹, a⁻¹⁆ * (a⁻¹ * z * a) := by
          rw [hzdef, hαg, commutatorElement_def]
          group
        rw [e2, hza]
        refine mul_mem ?_ hz
        rw [← commutator_miyamotoA2]
        exact commutator_mem_commutator (inv_mem hg) (inv_mem ha)
      obtain ⟨e, -, he⟩ := (mem_Z h).mp hz'
      refine ⟨e, ?_⟩
      rw [← he]
      group
    have hl0 : ((b : K) ^ 2) ≠ 0 := pow_ne_zero 2 b.ne_zero
    have hA2 : ∀ c : K, miyamotoXGL h c 0 0 0 ∈ miyamotoA2 h := fun c =>
      (miyamotoXGL_mem_A2 h).mpr ⟨rfl, by simp⟩
    have hA2' : miyamotoXGL h 0 0 1 0 ∈ miyamotoA2 h := (miyamotoXGL_mem_A2 h).mpr ⟨rfl, by simp⟩
    obtain ⟨e₁, he₁⟩ := key 1 0 0 (hA2 1)
    obtain ⟨e₂, he₂⟩ := key 0 1 0 hA2'
    obtain ⟨E1, E2⟩ := levi_mod_Z_entries h hb he₁
    obtain ⟨E3, E4⟩ := levi_mod_Z_entries h hb he₂
    simp only [map_one, map_zero, mul_one, mul_zero, add_zero, zero_add] at E1 E2 E3 E4
    have hφ1 : φ = RingEquiv.refl K := RingEquiv.ext fun c => by
      obtain ⟨e₃, he₃⟩ := key c 0 0 (hA2 c)
      obtain ⟨E5, -⟩ := levi_mod_Z_entries h hb he₃
      simp only [map_zero, mul_zero, add_zero, E1] at E5
      exact mul_left_cancel₀ (pow_ne_zero 2 hl0) E5
    have hdetm : ((m : Matrix (Fin 2) (Fin 2) h.fixedField) 0 0 : K) *
        ((m : Matrix (Fin 2) (Fin 2) h.fixedField) 1 1 : K) -
        ((m : Matrix (Fin 2) (Fin 2) h.fixedField) 0 1 : K) *
          ((m : Matrix (Fin 2) (Fin 2) h.fixedField) 1 0 : K) = 1 := by
      have e : (m : Matrix (Fin 2) (Fin 2) h.fixedField).det = 1 := m.2
      rw [Matrix.det_fin_two] at e
      have := congrArg (fun x : h.fixedField => (x : K)) e
      simpa using this
    rw [E1, E4, E3, E2] at hdetm
    have hl1 : (b : K) ^ 2 = 1 := eq_one_of_pow_four_eq_one (by linear_combination hdetm)
    have hb1 : b = 1 := Units.ext (eq_of_sq_eq_sq (by rw [hl1, Units.val_one, one_pow]))
    have hm1 : m = 1 := Subtype.ext (Matrix.ext fun k l => Subtype.ext (by
      fin_cases k <;> fin_cases l <;> simp [E1, E2, E3, E4, hl1]))
    refine ⟨⟨a, miyamotoA2_le_gramSU' h ha⟩, ha, ?_⟩
    rw [hαs, hφ1, miyamotoFieldAut_refl, mul_one]
    congr 1
    apply Subtype.ext
    rw [hs, hDdef, hb1, hm1, map_one, map_one, mul_one, mul_one]
  · rintro ⟨a, ha, rfl⟩ g hg
    have hc : (g : GL (Fin 4) K)⁻¹ * (MulAut.conj a g : GL (Fin 4) K) =
        ⁅(g : GL (Fin 4) K)⁻¹, (a : GL (Fin 4) K)⁆ := by
      rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        commutatorElement_def, inv_inv]
      group
    rw [hc, ← commutator_miyamotoA2]
    exact commutator_mem_commutator (inv_mem hg) ha

end ModZ

section ModA1

theorem miyamotoP_rows {g : GL (Fin 4) K} (hg : g ∈ miyamotoP h) :
    (g : Matrix (Fin 4) (Fin 4) K) 0 0 = 1 ∧ (g : Matrix (Fin 4) (Fin 4) K) 0 1 = 0 ∧
      (g : Matrix (Fin 4) (Fin 4) K) 0 2 = 0 ∧ (g : Matrix (Fin 4) (Fin 4) K) 0 3 = 0 ∧
      (g : Matrix (Fin 4) (Fin 4) K) 1 1 = 1 ∧ (g : Matrix (Fin 4) (Fin 4) K) 1 2 = 0 ∧
      (g : Matrix (Fin 4) (Fin 4) K) 1 3 = 0 := by
  obtain ⟨a, b, c, d, -, -, rfl⟩ := (mem_P h).mp hg
  simp [miyamotoX]

theorem miyamotoP_mul_coord {g k : GL (Fin 4) K} (hg : g ∈ miyamotoP h) (hk : k ∈ miyamotoP h) :
    ((g * k : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 0 =
      (g : Matrix (Fin 4) (Fin 4) K) 1 0 + (k : Matrix (Fin 4) (Fin 4) K) 1 0 := by
  obtain ⟨-, -, -, -, g11, g12, g13⟩ := miyamotoP_rows h hg
  obtain ⟨k00, -, -, -, -, -, -⟩ := miyamotoP_rows h hk
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_four, g11, g12, g13, k00]
  ring

theorem miyamotoP_inv_coord {g : GL (Fin 4) K} (hg : g ∈ miyamotoP h) :
    ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 0 =
      -(g : Matrix (Fin 4) (Fin 4) K) 1 0 := by
  have e := miyamotoP_mul_coord h hg (inv_mem hg)
  rw [mul_inv_cancel, Units.val_one, Matrix.one_apply_ne (by decide)] at e
  linear_combination -e

theorem mem_A1_of_mem_P_of_coord {g : GL (Fin 4) K} (hg : g ∈ miyamotoP h)
    (h10 : (g : Matrix (Fin 4) (Fin 4) K) 1 0 = 0) : g ∈ miyamotoA1 h := by
  have : CharP K 2 := h.charP
  obtain ⟨a, b, c, d, hb, hd, rfl⟩ := (mem_P h).mp hg
  simp only [coe_miyamotoXGL, miyamotoX_one_zero] at h10
  subst h10
  refine (miyamotoXGL_mem_A1 h).mpr ⟨rfl, hb, (add_bar_eq_zero_iff h).mp ?_⟩
  simpa using hd

theorem miyamotoI1_conj_P {i g : GL (Fin 4) K} (hi : i ∈ miyamotoI1 h) (hg : g ∈ miyamotoP h) :
    i * g * i⁻¹ ∈ miyamotoP h ∧ ((i * g * i⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 0 =
      (g : Matrix (Fin 4) (Fin 4) K) 1 0 := by
  have : CharP K 2 := h.charP
  obtain ⟨t, ht, rfl⟩ := (mem_miyamotoI1 h).mp hi
  obtain ⟨a, b, c, d, hb, hd, rfl⟩ := (mem_P h).mp hg
  have e : miyamotoIHom h (t, t) * miyamotoXGL h a b c d * (miyamotoIHom h (t, t))⁻¹ =
      (miyamotoIHom h (t⁻¹, t⁻¹))⁻¹ * miyamotoXGL h a b c d * miyamotoIHom h (t⁻¹, t⁻¹) := by
    rw [← map_inv, ← map_inv (miyamotoIHom h) (t⁻¹, t⁻¹), Prod.inv_mk, Prod.inv_mk, inv_inv]
  rw [e, miyamotoIHom_conj]
  have hbt : h.bar ((t⁻¹ : Kˣ) : K) = ((t⁻¹ : Kˣ) : K) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact congrArg _ ht
  have hbb := h.bar_bar
  refine ⟨(miyamotoXGL_mem_P h).mpr ⟨?_, ?_⟩, ?_⟩
  · dsimp only
    rw [map_mul, map_mul, hbt, hb, hbt]
  · dsimp only
    have ht' : h.bar (t : K) = t := ht
    have ht0 : (t : K) ≠ 0 := t.ne_zero
    simp only [map_mul, map_inv₀, Units.val_inv_eq_inv_val, inv_inv, ht']
    field_simp
    linear_combination hd
  · simp only [coe_miyamotoXGL, miyamotoX_one_zero]
    rw [mul_inv_cancel₀ (Units.ne_zero _), one_mul]

theorem miyamotoP_conj_P {p y : GL (Fin 4) K} (hp : p ∈ miyamotoP h) (hy : y ∈ miyamotoP h) :
    p * y * p⁻¹ ∈ miyamotoP h ∧ ((p * y * p⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 0 =
      (y : Matrix (Fin 4) (Fin 4) K) 1 0 := by
  refine ⟨mul_mem (mul_mem hp hy) (inv_mem hp), ?_⟩
  rw [miyamotoP_mul_coord h (mul_mem hp hy) (inv_mem hp), miyamotoP_mul_coord h hp hy,
    miyamotoP_inv_coord h hp]
  ring

theorem conj_P_of_mem_P_I1 {p i y : GL (Fin 4) K} (hp : p ∈ miyamotoP h) (hi : i ∈ miyamotoI1 h)
    (hy : y ∈ miyamotoP h) : p * i * y * (p * i)⁻¹ ∈ miyamotoP h ∧
      ((p * i * y * (p * i)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 0 =
        (y : Matrix (Fin 4) (Fin 4) K) 1 0 := by
  obtain ⟨hiy, hiyc⟩ := miyamotoI1_conj_P h hi hy
  have e : p * i * y * (p * i)⁻¹ = p * (i * y * i⁻¹) * p⁻¹ := by group
  rw [e]
  obtain ⟨h1, h2⟩ := miyamotoP_conj_P h hp hiy
  exact ⟨h1, h2.trans hiyc⟩

theorem inv_eq_mul_of_mem_P_I1 {p i : GL (Fin 4) K} (hp : p ∈ miyamotoP h)
    (hi : i ∈ miyamotoI1 h) : ∃ p' ∈ miyamotoP h, ∃ i' ∈ miyamotoI1 h, (p * i)⁻¹ = p' * i' := by
  refine ⟨i⁻¹ * p⁻¹ * i⁻¹⁻¹, (miyamotoI1_conj_P h (inv_mem hi) (inv_mem hp)).1, i⁻¹,
    inv_mem hi, by group⟩

theorem levi_mod_A1_entries {t : Kˣ} {m : SpecialLinearGroup (Fin 2) K} {φ : K ≃+* K} {c : K}
    {a₂ : GL (Fin 4) K} (ha₂ : a₂ ∈ miyamotoA1 h)
    (e : miyamotoI1Hom t * ((Units.map (miyamotoN1Mat h)).comp SpecialLinearGroup.toGL) m *
      glAut φ (miyamotoXGL h c 0 0 0) = miyamotoXGL h c 0 0 0 * a₂ *
        (miyamotoI1Hom t * ((Units.map (miyamotoN1Mat h)).comp SpecialLinearGroup.toGL) m)) :
    (m : Matrix (Fin 2) (Fin 2) K) 0 1 * φ c = 0 ∧
      (m : Matrix (Fin 2) (Fin 2) K) 1 1 * φ c = c * (m : Matrix (Fin 2) (Fin 2) K) 0 0 := by
  have : CharP K 2 := h.charP
  obtain ⟨b, c', d, -, -, rfl⟩ := (mem_A1 h).mp ha₂
  have ht0 : (t : K) ≠ 0 := t.ne_zero
  have hM := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) e
  simp only [Units.val_mul, coe_glAut, coe_miyamotoXGL, coe_miyamotoI1Hom,
    coe_miyamotoN1_elem] at hM
  have E00 := congrFun (congrFun hM 0) 0
  have E10 := congrFun (congrFun hM 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_four, miyamotoX, miyamotoN1Mat, diagonal] at E00 E10
  refine ⟨?_, ?_⟩
  · rcases E00 with E00 | E00
    · rw [E00, zero_mul]
    · rw [E00, map_zero, mul_zero]
  · have e3 : (t : K) * ((m : Matrix (Fin 2) (Fin 2) K) 1 1 * φ c) =
        (t : K) * (c * (m : Matrix (Fin 2) (Fin 2) K) 0 0) := by linear_combination E10
    exact mul_left_cancel₀ ht0 e3

theorem stabilizes_A1_and_fixes_mod_A1_iff (α : MulAut (gramSU h (miyamotoJ4 K))) :
    ((∀ g : gramSU h (miyamotoJ4 K),
        ((α g : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) ∈ miyamotoA1 h ↔
          (g : GL (Fin 4) K) ∈ miyamotoA1 h) ∧
      ∀ g : gramSU h (miyamotoJ4 K), (g : GL (Fin 4) K) ∈ miyamotoP h →
        (g : GL (Fin 4) K)⁻¹ * (α g : GL (Fin 4) K) ∈ miyamotoA1 h) ↔
      ∃ s : gramSU h (miyamotoJ4 K), (∃ p ∈ miyamotoP h, ∃ i ∈ miyamotoI1 h,
        (s : GL (Fin 4) K) = p * i) ∧ α = MulAut.conj s := by
  have : CharP K 2 := h.charP
  have hcoordA1 : ∀ g : GL (Fin 4) K, g ∈ miyamotoA1 h → (g : Matrix (Fin 4) (Fin 4) K) 1 0 = 0 :=
    fun g hg => by
      obtain ⟨b, c, d, -, -, rfl⟩ := (mem_A1 h).mp hg
      rfl
  constructor
  · rintro ⟨hA, hP⟩
    obtain ⟨s, ⟨a₀, ha₀, i, hi, n, hn, hs⟩, φ, hαs⟩ := (stabilizes_A1_iff h α).mp hA
    obtain ⟨t, ht, rfl⟩ := (mem_miyamotoI1' h).mp hi
    obtain ⟨m, rfl⟩ := hn
    set D := miyamotoI1Hom t * ((Units.map (miyamotoN1Mat h)).comp SpecialLinearGroup.toGL) m
      with hDdef
    have key : ∀ c : K, ∃ a₂ ∈ miyamotoA1 h, D * glAut φ (miyamotoXGL h c 0 0 0) =
        miyamotoXGL h c 0 0 0 * a₂ * D := by
      intro c
      have hgP : miyamotoXGL h c 0 0 0 ∈ miyamotoP h :=
        (miyamotoXGL_mem_P h).mpr ⟨map_zero _, by simp⟩
      have hgS := miyamotoUnipotent_le_SU h false false hgP
      have ha₁ := hP ⟨_, hgS⟩ hgP
      have hαg : (α ⟨_, hgS⟩ : GL (Fin 4) K) =
          a₀ * D * glAut φ (miyamotoXGL h c 0 0 0) * (a₀ * D)⁻¹ := by
        rw [hαs]
        simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
          coe_miyamotoFieldAut_apply]
        rw [hs, hDdef]
      refine ⟨(miyamotoXGL h c 0 0 0)⁻¹ * (D * glAut φ (miyamotoXGL h c 0 0 0) * D⁻¹), ?_,
        by group⟩
      have e2 : (miyamotoXGL h c 0 0 0)⁻¹ * (D * glAut φ (miyamotoXGL h c 0 0 0) * D⁻¹) =
          ((miyamotoXGL h c 0 0 0)⁻¹ * a₀⁻¹ * (miyamotoXGL h c 0 0 0)⁻¹⁻¹) *
            ((miyamotoXGL h c 0 0 0)⁻¹ * (α ⟨_, hgS⟩ : GL (Fin 4) K)) * a₀ := by
        rw [hαg]
        group
      rw [e2]
      refine mul_mem (mul_mem ?_ ha₁) ha₀
      obtain ⟨h1, h2⟩ := miyamotoP_conj_P h (inv_mem hgP) (inv_mem (miyamotoA1_le_P h ha₀))
      refine mem_A1_of_mem_P_of_coord h h1 ?_
      rw [h2, miyamotoP_inv_coord h (miyamotoA1_le_P h ha₀), hcoordA1 a₀ ha₀, neg_zero]
    obtain ⟨a₂, ha₂, e₁⟩ := key 1
    obtain ⟨E1, E2⟩ := levi_mod_A1_entries h ha₂ e₁
    simp only [map_one, mul_one, one_mul] at E1 E2
    have hdetm : (m : Matrix (Fin 2) (Fin 2) K) 0 0 * (m : Matrix (Fin 2) (Fin 2) K) 1 1 -
        (m : Matrix (Fin 2) (Fin 2) K) 0 1 * (m : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
      rw [← Matrix.det_fin_two]; exact m.2
    rw [E1, E2, zero_mul, sub_zero] at hdetm
    have hm00 : (m : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 :=
      eq_of_sq_eq_sq (by rw [one_pow, sq]; exact hdetm)
    have hφ1 : φ = RingEquiv.refl K := RingEquiv.ext fun c => by
      obtain ⟨a₃, ha₃, e₃⟩ := key c
      obtain ⟨-, E4⟩ := levi_mod_A1_entries h ha₃ e₃
      rw [E2, hm00, one_mul, mul_one] at E4
      exact E4
    set r := (m : Matrix (Fin 2) (Fin 2) K) 1 0 with hr
    have hnx : ((Units.map (miyamotoN1Mat h)).comp SpecialLinearGroup.toGL) m =
        miyamotoXGL h r 0 0 0 := by
      apply Units.ext
      rw [coe_miyamotoN1_elem, coe_miyamotoXGL]
      ext k l
      fin_cases k <;> fin_cases l <;> simp [miyamotoN1Mat, miyamotoX, E1, E2, hm00, ← hr]
    have hnP : miyamotoXGL h r 0 0 0 ∈ miyamotoP h :=
      (miyamotoXGL_mem_P h).mpr ⟨map_zero _, by simp⟩
    have hcomm := miyamotoN1_commute_I1 h ⟨m, rfl⟩ ((mem_miyamotoI1' h).mpr ⟨t, ht, rfl⟩)
    refine ⟨s, ⟨a₀ * miyamotoXGL h r 0 0 0, mul_mem (miyamotoA1_le_P h ha₀) hnP,
      miyamotoI1Hom t, (mem_miyamotoI1' h).mpr ⟨t, ht, rfl⟩, ?_⟩, ?_⟩
    · rw [hs, hDdef, ← hcomm, hnx]
      group
    · rw [hαs, hφ1, miyamotoFieldAut_refl, mul_one]
  · rintro ⟨s, ⟨p, hp, i, hi, hs⟩, rfl⟩
    obtain ⟨p', hp', i', hi', hinv⟩ := inv_eq_mul_of_mem_P_I1 h hp hi
    have hconj : ∀ g : gramSU h (miyamotoJ4 K),
        ((MulAut.conj s g : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) =
          p * i * g * (p * i)⁻¹ := fun g => by
      rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hs]
    refine ⟨fun g => ⟨fun hg => ?_, fun hg => ?_⟩, fun g hg => ?_⟩
    ·
      rw [hconj] at hg
      have e : (g : GL (Fin 4) K) = p' * i' * (p * i * g * (p * i)⁻¹) * (p' * i')⁻¹ := by
        rw [← hinv]; group
      obtain ⟨h1, h2⟩ := conj_P_of_mem_P_I1 h hp' hi' (miyamotoA1_le_P h hg)
      rw [e]
      exact mem_A1_of_mem_P_of_coord h h1 (by rw [h2, hcoordA1 _ hg])
    · rw [hconj]
      obtain ⟨h1, h2⟩ := conj_P_of_mem_P_I1 h hp hi (miyamotoA1_le_P h hg)
      exact mem_A1_of_mem_P_of_coord h h1 (by rw [h2, hcoordA1 _ hg])
    · rw [hconj]
      obtain ⟨h1, h2⟩ := conj_P_of_mem_P_I1 h hp hi hg
      refine mem_A1_of_mem_P_of_coord h (mul_mem (inv_mem hg) h1) ?_
      rw [miyamotoP_mul_coord h (inv_mem hg) h1, miyamotoP_inv_coord h hg, h2]
      ring

end ModA1

end CFSG.LocalAnalysis.EvenBN.U4
