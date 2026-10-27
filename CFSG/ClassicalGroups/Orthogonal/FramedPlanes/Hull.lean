module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.FieldTheory.Finite.Basic
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.QuadraticForm.Radical

public section

namespace CFSG.ClassicalGroups.Orthogonal.FramedPlanes

open Module QuadraticMap

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

@[expose] noncomputable def hullDim (Q : QuadraticForm F V) (U : Submodule F V) : ℕ :=
  finrank F U + finrank F ↥(U ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) U)

variable [Module.Finite F V] {Q : QuadraticForm F V}

private lemma add_self_eq_zero_char_two [CharP F 2] (a : F) : a + a = 0 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [← two_mul, h2, zero_mul]

omit [Module.Finite F V] in
private lemma polar_self_eq_zero [CharP F 2] (x : V) : polar Q x x = 0 := by
  rw [QuadraticMap.polar_self, two_nsmul, add_self_eq_zero_char_two]

private lemma finrank_rad_sup_le (U W : Submodule F V) :
    finrank F ↥((U ⊔ W) ⊓
        LinearMap.BilinForm.orthogonal (polarBilin Q) (U ⊔ W)) ≤
      finrank F W +
        finrank F ↥(U ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) U) := by
  set R : Submodule F V :=
    (U ⊔ W) ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) (U ⊔ W) with hR
  have hRU : R ≤ U ⊔ W := inf_le_left
  have hRorth : R ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) U :=
    inf_le_right.trans (LinearMap.BilinForm.orthogonal_le le_sup_left)
  have hinf : R ⊓ U ≤ U ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) U :=
    le_inf inf_le_right (inf_le_left.trans hRorth)
  have h1 : finrank F ↥(R ⊔ U) + finrank F ↥(R ⊓ U) =
      finrank F R + finrank F U :=
    Submodule.finrank_sup_add_finrank_inf_eq R U
  have h2 : finrank F ↥(R ⊔ U) ≤ finrank F ↥(U ⊔ W) :=
    Submodule.finrank_mono (sup_le hRU le_sup_left)
  have h3 : finrank F ↥(R ⊓ U) ≤
      finrank F ↥(U ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) U) :=
    Submodule.finrank_mono hinf
  have h4 : finrank F ↥(U ⊔ W) + finrank F ↥(U ⊓ W) =
      finrank F U + finrank F W :=
    Submodule.finrank_sup_add_finrank_inf_eq U W
  omega

theorem hullDim_sup_le (U W : Submodule F V) :
    hullDim Q (U ⊔ W) ≤ hullDim Q U + 2 * finrank F W := by
  rw [hullDim, hullDim]
  have h := finrank_rad_sup_le (Q := Q) U W
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq U W
  omega

omit [Module.Finite F V] in
private lemma rad_sup_le_sup_rad {U W : Submodule F V}
    (hW : W ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) U) :
    (U ⊔ W) ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) (U ⊔ W) ≤
      (U ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) U) ⊔
        (W ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) W) := by
  intro x hx
  obtain ⟨hxU, hxO⟩ := Submodule.mem_inf.mp hx
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hxU
  have hx0 : ∀ y ∈ U ⊔ W, polar Q y x = 0 := fun y hy =>
    (LinearMap.BilinForm.mem_orthogonal_iff.mp hxO) y hy
  have hu_rad : u ∈ U ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) U := by
    refine Submodule.mem_inf.mpr ⟨hu, ?_⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u' hu'
    have h1 : polar Q u' x = 0 := hx0 u' (Submodule.mem_sup_left hu')
    have h2 : polar Q u' w = 0 := by
      simpa only [QuadraticMap.polarBilin_apply_apply] using hW hw u' hu'
    have hux : u = x - w := by rw [← huw]; abel
    rw [hux, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_sub_right, h1, h2,
      sub_zero]
  have hw_rad : w ∈ W ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) W := by
    refine Submodule.mem_inf.mpr ⟨hw, ?_⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w' hw'
    have h1 : polar Q w' x = 0 := hx0 w' (Submodule.mem_sup_right hw')
    have h2 : polar Q w' u = 0 := by
      rw [polar_comm Q w' u]
      simpa only [QuadraticMap.polarBilin_apply_apply] using hW hw' u hu
    have hwx : w = x - u := by rw [← huw]; abel
    rw [hwx, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_sub_right, h1, h2,
      sub_zero]
  exact Submodule.mem_sup.mpr ⟨u, hu_rad, w, hw_rad, huw⟩

theorem hullDim_sup_le_of_le_orthogonal {U W : Submodule F V}
    (h : W ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) U) :
    hullDim Q (U ⊔ W) ≤ hullDim Q U + hullDim Q W := by
  rw [hullDim, hullDim, hullDim]
  have hrad := Submodule.finrank_mono (rad_sup_le_sup_rad (Q := Q) h)
  have hsup : finrank F ↥((U ⊔ W) ⊓
      LinearMap.BilinForm.orthogonal (polarBilin Q) (U ⊔ W)) ≤
        finrank F ↥(U ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) U) +
          finrank F ↥(W ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) W) := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq
      (U ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) U)
      (W ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) W)
    omega
  have h2 : finrank F ↥(U ⊔ W) ≤ finrank F U + finrank F W := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq U W
    omega
  omega

omit [Module.Finite F V] in
theorem hullDim_span_pair [CharP F 2] {u w : V} (h : polar Q u w ≠ 0) :
    hullDim Q (Submodule.span F {u, w}) = 2 := by
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, QuadraticMap.polar_zero_left] at h
    exact h rfl
  have hlin : LinearIndependent F ![u, w] := by
    rw [LinearIndependent.pair_iff' hu0]
    intro a ha
    have h1 : polar Q u (a • u) = polar Q u w := by rw [ha]
    rw [QuadraticMap.polar_smul_right, polar_self_eq_zero, smul_zero] at h1
    exact h h1.symm
  have hspan : finrank F (Submodule.span F {u, w}) = 2 := by
    rw [← Matrix.range_cons_cons_empty u w ![], finrank_span_eq_card hlin, Fintype.card_fin]
  have hrad : Submodule.span F {u, w} ⊓
      LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span F {u, w}) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxs, hxo⟩ := Submodule.mem_inf.mp hx
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hxs
    obtain ⟨h1, h2⟩ := (LinearMap.BilinForm.mem_orthogonal_span_pair_iff (polarBilin Q)).mp hxo
    have h1' : t * polar Q u w = 0 := by
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_add_right,
        QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right, polar_self_eq_zero,
        smul_eq_mul, mul_zero, zero_add] at h1
      simpa using h1
    have ht : t = 0 := (mul_eq_zero.mp h1').resolve_right h
    have h2' : s * polar Q u w = 0 := by
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_add_right,
        QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right, polar_self_eq_zero,
        smul_eq_mul, smul_zero, add_zero, polar_comm Q w u] at h2
      simpa using h2
    have hs : s = 0 := (mul_eq_zero.mp h2').resolve_right h
    rw [hs, ht, zero_smul, zero_smul, add_zero]
    simp
  rw [hullDim, hspan, hrad, finrank_bot, add_zero]

omit [Module.Finite F V] in
private lemma sup_span_pair_add_smul_eq (A : Submodule F V) {z p₁ p₂ : V}
    (hz : z ∈ A) (a b : F) :
    A ⊔ Submodule.span F {p₁, p₂} =
      A ⊔ Submodule.span F {p₁ + a • z, p₂ + b • z} := by
  let R : Submodule F V := A ⊔ Submodule.span F {p₁, p₂}
  let R' : Submodule F V := A ⊔ Submodule.span F {p₁ + a • z, p₂ + b • z}
  have hzR' : z ∈ R' := Submodule.mem_sup_left hz
  have hp₁ : p₁ ∈ R := Submodule.mem_sup_right (Submodule.subset_span (by simp))
  have hp₂ : p₂ ∈ R := Submodule.mem_sup_right (Submodule.subset_span (by simp))
  have hp₁' : p₁ + a • z ∈ R' :=
    Submodule.mem_sup_right (Submodule.subset_span (by simp))
  have hp₂' : p₂ + b • z ∈ R' :=
    Submodule.mem_sup_right (Submodule.subset_span (by simp))
  refine le_antisymm ?_ ?_
  · refine sup_le le_sup_left ?_
    rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      have h : p₁ + a • z - a • z ∈ R' :=
        Submodule.sub_mem R' hp₁' (Submodule.smul_mem R' a hzR')
      simpa only [add_sub_cancel_right, SetLike.mem_coe] using h
    · rw [hx]
      have h : p₂ + b • z - b • z ∈ R' :=
        Submodule.sub_mem R' hp₂' (Submodule.smul_mem R' b hzR')
      simpa only [add_sub_cancel_right, SetLike.mem_coe] using h
  · refine sup_le le_sup_left ?_
    rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact Submodule.add_mem R hp₁ (Submodule.smul_mem R a (Submodule.mem_sup_left hz))
    · rw [hx]
      exact Submodule.add_mem R hp₂ (Submodule.smul_mem R b (Submodule.mem_sup_left hz))

omit [Module.Finite F V] in
private lemma mem_span_pair_add_smul (a b : F) (z' l' : V) :
    a • z' + b • l' ∈ Submodule.span F {z', l'} :=
  Submodule.mem_span_pair.mpr ⟨a, b, rfl⟩

omit [Module.Finite F V] in
private lemma smul_sub_mem_span_pair {t : F} {m z' l' : V}
    (hm : m ∈ Submodule.span F {z', l'}) :
    t • z' - m ∈ Submodule.span F {z', l'} :=
  Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))) hm

omit [Module.Finite F V] in
private lemma span_pair_le_orthogonal_of_mem {U : Submodule F V} {z' l' : V}
    (hz' : z' ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U)
    (hl' : l' ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U) :
    Submodule.span F {z', l'} ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) U := by
  rw [Submodule.span_le]
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with hw | hw
  · rw [hw]
    exact hz'
  · rw [hw]
    exact hl'

omit [Module.Finite F V] in
private lemma polar_add_div_polar_smul_self_eq_zero [CharP F 2] {z₁ z₂ p : V}
    (h : polar Q z₁ p = 0) :
    polar Q z₁ (p + (polar Q p z₂ / polar Q z₁ z₂) • z₁) = 0 := by
  rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, polar_self_eq_zero, h,
    smul_zero, add_zero]

omit [Module.Finite F V] in
private lemma polar_add_div_polar_smul_eq_zero [CharP F 2] {z₁ z₂ p : V}
    (hz : polar Q z₁ z₂ ≠ 0) :
    polar Q z₂ (p + (polar Q p z₂ / polar Q z₁ z₂) • z₁) = 0 := by
  rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
    polar_comm Q z₂ p, polar_comm Q z₂ z₁, smul_eq_mul]
  rw [div_mul_cancel₀ _ hz, add_self_eq_zero_char_two]

omit [Module.Finite F V] in
private lemma polar_add_div_polar_smul_add_div_polar_smul_ne_zero [CharP F 2]
    {z₁ z₂ p₁ p₂ : V} (hp : polar Q p₁ p₂ ≠ 0) (h₁ : polar Q z₁ p₁ = 0)
    (h₂ : polar Q z₁ p₂ = 0) :
    polar Q (p₁ + (polar Q p₁ z₂ / polar Q z₁ z₂) • z₁)
      (p₂ + (polar Q p₂ z₂ / polar Q z₁ z₂) • z₁) ≠ 0 := by
  have hp₁z₁ : polar Q p₁ z₁ = 0 := by rw [polar_comm Q p₁ z₁, h₁]
  rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
    QuadraticMap.polar_add_right, QuadraticMap.polar_add_right,
    QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right]
  simp only [hp₁z₁, h₂, polar_self_eq_zero, smul_zero, add_zero, zero_add]
  exact hp

private lemma modified_pair_le_orthogonal [CharP F 2] {z₁ z₂ p₁ p₂ : V}
    (hz : polar Q z₁ z₂ ≠ 0) (h₁ : polar Q z₁ p₁ = 0) (h₂ : polar Q z₁ p₂ = 0) :
    Submodule.span F
      {p₁ + (polar Q p₁ z₂ / polar Q z₁ z₂) • z₁,
       p₂ + (polar Q p₂ z₂ / polar Q z₁ z₂) • z₁} ≤
      LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span F {z₁, z₂}) := by
  rw [Submodule.span_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · refine (LinearMap.BilinForm.mem_orthogonal_iff).mpr ?_
    intro y hy
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hy
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_add_left,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left,
      polar_add_div_polar_smul_self_eq_zero (Q := Q) h₁,
      polar_add_div_polar_smul_eq_zero (Q := Q) hz]
    simp
  · refine (LinearMap.BilinForm.mem_orthogonal_iff).mpr ?_
    intro y hy
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hy
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_add_left,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left,
      polar_add_div_polar_smul_self_eq_zero (Q := Q) h₂,
      polar_add_div_polar_smul_eq_zero (Q := Q) hz]
    simp

theorem hullDim_span_pair_sup_le_four [CharP F 2] {z₁ z₂ p₁ p₂ : V}
    (hz : polar Q z₁ z₂ ≠ 0) (hp : polar Q p₁ p₂ ≠ 0) (h₁ : polar Q z₁ p₁ = 0)
    (h₂ : polar Q z₁ p₂ = 0) :
    hullDim Q (Submodule.span F {z₁, z₂} ⊔ Submodule.span F {p₁, p₂}) ≤ 4 := by
  set q₁ : V := p₁ + (polar Q p₁ z₂ / polar Q z₁ z₂) • z₁ with hq₁
  set q₂ : V := p₂ + (polar Q p₂ z₂ / polar Q z₁ z₂) • z₁ with hq₂
  have hspan_eq : Submodule.span F {z₁, z₂} ⊔ Submodule.span F {p₁, p₂} =
      Submodule.span F {z₁, z₂} ⊔ Submodule.span F {q₁, q₂} := by
    rw [hq₁, hq₂]
    exact sup_span_pair_add_smul_eq (A := Submodule.span F {z₁, z₂}) (z := z₁) (p₁ := p₁)
      (p₂ := p₂) (a := polar Q p₁ z₂ / polar Q z₁ z₂)
      (b := polar Q p₂ z₂ / polar Q z₁ z₂) (Submodule.subset_span (by simp))
  have horth : Submodule.span F {q₁, q₂} ≤
      LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span F {z₁, z₂}) := by
    rw [hq₁, hq₂]
    exact modified_pair_le_orthogonal (Q := Q) hz h₁ h₂
  have hp' : polar Q q₁ q₂ ≠ 0 := by
    rw [hq₁, hq₂]
    exact polar_add_div_polar_smul_add_div_polar_smul_ne_zero (Q := Q) hp h₁ h₂
  rw [hspan_eq]
  calc
    hullDim Q (Submodule.span F {z₁, z₂} ⊔ Submodule.span F {q₁, q₂})
        ≤ hullDim Q (Submodule.span F {z₁, z₂}) + hullDim Q (Submodule.span F {q₁, q₂}) :=
          hullDim_sup_le_of_le_orthogonal horth
    _ = 2 + 2 := by rw [hullDim_span_pair hz, hullDim_span_pair hp']
    _ = 4 := by norm_num

omit [Module.Finite F V] in
private lemma smul_not_mem_of_not_mem {U : Submodule F V} {t : V} (htU : t ∉ U) {s : F}
    (hs : s ≠ 0) : s • t ∉ U := by
  intro h
  have h' : s⁻¹ • (s • t) ∈ U := Submodule.smul_mem U s⁻¹ h
  rw [smul_smul, inv_mul_cancel₀ hs, one_smul] at h'
  exact htU h'

omit [Module.Finite F V] in
private lemma exists_Q_eq_one_smul_of_not_mem [Finite F] [CharP F 2]
    {U : Submodule F V} {t : V}
    (ht : t ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U) (htU : t ∉ U)
    (hQt : Q t ≠ 0) :
    ∃ z ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U, Q z = 1 ∧ z ∉ U := by
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) (Q t)
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hs
    exact hQt hs
  refine ⟨s⁻¹ • t, Submodule.smul_mem _ _ ht, ?_, ?_⟩
  · rw [QuadraticMap.map_smul, hs, smul_eq_mul]
    field_simp [hs0]
  · intro hmem
    exact smul_not_mem_of_not_mem htU (inv_ne_zero hs0) hmem

private lemma exists_polar_eq_one_of_not_mem [CharP F 2]
    (hQ : Q.polarBilin.Nondegenerate) {U : Submodule F V} {z : V} (hzU : z ∉ U) :
    ∃ l ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U, polar Q z l = 1 := by
  have hrefl : (polarBilin Q).IsRefl := (QuadraticMap.isSymm_polarBilin (Q := Q)).isRefl
  have horth : LinearMap.BilinForm.orthogonal (polarBilin Q)
      (LinearMap.BilinForm.orthogonal (polarBilin Q) U) = U :=
    LinearMap.BilinForm.orthogonal_orthogonal hQ hrefl U
  have hzorth : z ∉ LinearMap.BilinForm.orthogonal (polarBilin Q)
      (LinearMap.BilinForm.orthogonal (polarBilin Q) U) := by rwa [horth]
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hzorth
  push Not at hzorth
  obtain ⟨l, hl, hBl⟩ := hzorth
  have hzl : polar Q z l ≠ 0 := by
    rw [polar_comm Q z l]
    rwa [QuadraticMap.polarBilin_apply_apply] at hBl
  refine ⟨(polar Q z l)⁻¹ • l, Submodule.smul_mem _ _ hl, ?_⟩
  rw [QuadraticMap.polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hzl]

omit [Module.Finite F V] in
private lemma exists_Q_ne_zero_of_polar_ne_zero [CharP F 2] {x y : V}
    (h : polar Q x y ≠ 0) : Q x ≠ 0 ∨ Q y ≠ 0 ∨ Q (x + y) ≠ 0 := by
  have htri : Q x + Q y + Q (x + y) = polar Q x y := by
    rw [QuadraticMap.map_add Q]
    rw [show Q x + Q y + (Q x + Q y + polar Q x y) =
        (Q x + Q x) + (Q y + Q y) + polar Q x y by abel]
    rw [add_self_eq_zero_char_two, add_self_eq_zero_char_two, zero_add, zero_add]
  by_contra hne
  push Not at hne
  exact h (by rw [← htri, hne.1, hne.2.1, hne.2.2, add_zero, add_zero])

private lemma exists_mem_orthogonal_not_mem (hQ : Q.polarBilin.Nondegenerate)
    {U : Submodule F V} (hU : hullDim Q U < finrank F V) :
    ∃ x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U, x ∉ U := by
  have hdimL : finrank F (LinearMap.BilinForm.orthogonal (polarBilin Q) U) =
      finrank F V - finrank F U :=
    LinearMap.BilinForm.finrank_orthogonal hQ U
  have hUle : finrank F U ≤ finrank F V := Submodule.finrank_le U
  have hnotle : ¬ LinearMap.BilinForm.orthogonal (polarBilin Q) U ≤ U := by
    intro hle
    have hEq : U ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) U =
        LinearMap.BilinForm.orthogonal (polarBilin Q) U := inf_eq_right.mpr hle
    have hlt := hU
    rw [hullDim, hEq, hdimL] at hlt
    omega
  exact SetLike.not_le_iff_exists.mp hnotle

omit [Module.Finite F V] in
private lemma not_mem_and_add_not_mem [CharP F 2] {U : Submodule F V} {x y : V}
    (hxL : x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U)
    (hpol : polar Q x y ≠ 0) : y ∉ U ∧ x + y ∉ U := by
  constructor
  · intro hyU
    have h0 : polar Q y x = 0 := by
      simpa only [QuadraticMap.polarBilin_apply_apply] using
        (LinearMap.BilinForm.mem_orthogonal_iff.mp hxL) y hyU
    exact hpol (by rw [polar_comm Q x y]; exact h0)
  · intro hxyU
    have h0 : polar Q (x + y) x = 0 := by
      simpa only [QuadraticMap.polarBilin_apply_apply] using
        (LinearMap.BilinForm.mem_orthogonal_iff.mp hxL) (x + y) hxyU
    rw [QuadraticMap.polar_add_left, polar_self_eq_zero, zero_add] at h0
    exact hpol (by rw [polar_comm Q x y]; exact h0)

private lemma exists_Q_eq_one_polar_eq_one_of_mem [Finite F] [CharP F 2]
    (hQ : Q.polarBilin.Nondegenerate) {U : Submodule F V} {w : V}
    (hw : w ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U) (hwU : w ∉ U)
    (hQw : Q w ≠ 0) :
    ∃ z ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U, Q z = 1 ∧
      ∃ l ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U, polar Q z l = 1 := by
  obtain ⟨z, hzL, hQz, hzU⟩ := exists_Q_eq_one_smul_of_not_mem (Q := Q) hw hwU hQw
  exact ⟨z, hzL, hQz, exists_polar_eq_one_of_not_mem (Q := Q) hQ hzU⟩

theorem exists_Q_eq_one_polar_eq_one [Finite F] [CharP F 2] (hQ : Q.polarBilin.Nondegenerate)
    {U : Submodule F V} (hU : hullDim Q U < finrank F V) :
    ∃ z ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U, Q z = 1 ∧
      ∃ l ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U, polar Q z l = 1 := by
  obtain ⟨x, hxL, hxU⟩ := exists_mem_orthogonal_not_mem (Q := Q) hQ hU
  have horth : LinearMap.BilinForm.orthogonal (polarBilin Q)
      (LinearMap.BilinForm.orthogonal (polarBilin Q) U) = U :=
    LinearMap.BilinForm.orthogonal_orthogonal hQ
      (QuadraticMap.isSymm_polarBilin (Q := Q)).isRefl U
  have hxorth : x ∉ LinearMap.BilinForm.orthogonal (polarBilin Q)
      (LinearMap.BilinForm.orthogonal (polarBilin Q) U) := by rwa [horth]
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hxorth
  push Not at hxorth
  obtain ⟨y, hyL, hByx⟩ := hxorth
  have hpol : polar Q x y ≠ 0 := by
    rw [polar_comm Q x y]
    rwa [QuadraticMap.polarBilin_apply_apply] at hByx
  obtain ⟨hyU, hxyU⟩ := not_mem_and_add_not_mem (Q := Q) hxL hpol
  rcases exists_Q_ne_zero_of_polar_ne_zero (Q := Q) hpol with hxQ | hyQ | hxyQ
  · exact exists_Q_eq_one_polar_eq_one_of_mem (Q := Q) hQ hxL hxU hxQ
  · exact exists_Q_eq_one_polar_eq_one_of_mem (Q := Q) hQ hyL hyU hyQ
  · have hxyL : x + y ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U :=
      Submodule.add_mem _ hxL hyL
    exact exists_Q_eq_one_polar_eq_one_of_mem (Q := Q) hQ hxyL hxyU hxyQ

omit [Module.Finite F V] in
private lemma polar_self_add_smul_add_smul [CharP F 2] (l z' l' : V)
    (h : polar Q z' l' = 1) :
    polar Q z' (polar Q l l' • z' + polar Q l z' • l') = polar Q l z' := by
  rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
    QuadraticMap.polar_smul_right, polar_self_eq_zero, h]
  simp only [smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]

omit [Module.Finite F V] in
private lemma polar_add_smul_add_smul_self_eq_zero [CharP F 2] (l z' l' : V) :
    polar Q l (polar Q l l' • z' + polar Q l z' • l') = 0 := by
  rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
    QuadraticMap.polar_smul_right, smul_eq_mul, smul_eq_mul,
    mul_comm (polar Q l l') (polar Q l z'), add_self_eq_zero_char_two]

private lemma exists_Q_eq_one_orthogonal_pair [Finite F] [CharP F 2]
    (hQ : Q.polarBilin.Nondegenerate) {U : Submodule F V} {z : V}
    (hU : hullDim Q U + 3 ≤ finrank F V) :
    ∃ z' ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U, Q z' = 1 ∧
      polar Q z z' = 0 ∧
        ∃ l' ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U,
          polar Q z' l' = 1 ∧ polar Q z l' = 0 := by
  have hUz : hullDim Q (U ⊔ Submodule.span F {z}) < finrank F V := by
    have h1 := hullDim_sup_le (Q := Q) U (Submodule.span F {z})
    have h2 : finrank F (Submodule.span F {z}) ≤ 1 := by
      by_cases hz : z = 0
      · rw [hz, Submodule.span_zero_singleton, finrank_bot]
        exact zero_le_one
      · rw [finrank_span_singleton hz]
    omega
  obtain ⟨z', hz'P, hQz', l', hl'P, hz'l'⟩ :=
    exists_Q_eq_one_polar_eq_one (Q := Q) hQ (U := U ⊔ Submodule.span F {z}) hUz
  have hz_mem : z ∈ U ⊔ Submodule.span F {z} :=
    Submodule.mem_sup_right (Submodule.subset_span (by simp))
  have hz'z : polar Q z z' = 0 := by
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hz'P) z hz_mem
    simpa only [QuadraticMap.polarBilin_apply_apply] using h
  have hl'z : polar Q z l' = 0 := by
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hl'P) z hz_mem
    simpa only [QuadraticMap.polarBilin_apply_apply] using h
  have hz'U : z' ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U :=
    (LinearMap.BilinForm.orthogonal_le (le_sup_left : U ≤ U ⊔ Submodule.span F {z})) hz'P
  have hl'U : l' ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U :=
    (LinearMap.BilinForm.orthogonal_le (le_sup_left : U ≤ U ⊔ Submodule.span F {z})) hl'P
  exact ⟨z', hz'U, hQz', hz'z, l', hl'U, hz'l', hl'z⟩

private lemma exists_polar_eq_one_Q_eq_add [Finite F] [CharP F 2]
    {U : Submodule F V} {z l z' l' : V}
    (hl : l ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U) (hzl : polar Q z l = 1)
    (hz'U : z' ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U) (hQz' : Q z' = 1)
    (hz'z : polar Q z z' = 0)
    (hl'U : l' ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U) (hz'l' : polar Q z' l' = 1)
    (hl'z : polar Q z l' = 0) (c : F) :
    ∃ y ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U, polar Q z y = 1 ∧ Q y = c := by
  let m : V := polar Q l l' • z' + polar Q l z' • l'
  have hm_span : m ∈ Submodule.span F {z', l'} := mem_span_pair_add_smul _ _ _ _
  have hz'm : polar Q z' m = polar Q l z' := polar_self_add_smul_add_smul l z' l' hz'l'
  have hlm : polar Q l m = 0 := polar_add_smul_add_smul_self_eq_zero l z' l'
  obtain ⟨t, ht⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) (c - Q l + Q m)
  let k : V := t • z' - m
  have hk_span : k ∈ Submodule.span F {z', l'} := smul_sub_mem_span_pair hm_span
  have hkl : polar Q l k = t * polar Q l z' := by
    simp only [k, QuadraticMap.polar_sub_right, QuadraticMap.polar_smul_right, hlm,
      smul_eq_mul, sub_zero]
  have hQk : Q k = t * t - t * polar Q l z' + Q m := by
    dsimp only [k]
    rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_smul Q,
      QuadraticMap.map_neg Q, QuadraticMap.polar_smul_left, QuadraticMap.polar_neg_right,
      smul_neg, hQz', hz'm, smul_eq_mul, smul_eq_mul]
    ring
  have hQsum : Q k + polar Q l k = c - Q l := by
    rw [hQk, hkl, ← ht]
    linear_combination add_self_eq_zero_char_two (Q m)
  have hzk : polar Q z k = 0 := by
    dsimp only [k, m]
    simp [hz'z, hl'z]
  refine ⟨l + k, Submodule.add_mem _ hl
    (span_pair_le_orthogonal_of_mem (Q := Q) hz'U hl'U hk_span), ?_, ?_⟩
  · rw [QuadraticMap.polar_add_right, hzl, hzk, add_zero]
  · rw [QuadraticMap.map_add Q, add_assoc, hQsum]
    ring

theorem exists_polar_eq_one_Q_eq [Finite F] [CharP F 2] (hQ : Q.polarBilin.Nondegenerate)
    {U : Submodule F V} (hU : hullDim Q U + 3 ≤ finrank F V) {z l : V}
    (hl : l ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U) (hzl : polar Q z l = 1) (c : F) :
    ∃ y ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U, polar Q z y = 1 ∧ Q y = c := by
  obtain ⟨z', hz'U, hQz', hz'z, l', hl'U, hz'l', hl'z⟩ :=
    exists_Q_eq_one_orthogonal_pair (Q := Q) hQ hU
  exact exists_polar_eq_one_Q_eq_add (Q := Q) hl hzl hz'U hQz' hz'z hl'U hz'l' hl'z c

theorem exists_framedPair_orthogonal [Finite F] [CharP F 2] (hQ : Q.polarBilin.Nondegenerate)
    {U : Submodule F V} (hU : hullDim Q U + 3 ≤ finrank F V) (c : F) :
    ∃ u ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U,
      ∃ w ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U,
        Q u = 1 ∧ Q w = c ∧ polar Q u w = 1 := by
  have hU' : hullDim Q U < finrank F V := by omega
  obtain ⟨u, hu, hQu, l, hl, hul⟩ :=
    exists_Q_eq_one_polar_eq_one (Q := Q) hQ (U := U) hU'
  obtain ⟨w, hw, huw, hQw⟩ :=
    exists_polar_eq_one_Q_eq (Q := Q) hQ hU hl hul c
  exact ⟨u, hu, w, hw, hQu, hQw, huw⟩

end CFSG.ClassicalGroups.Orthogonal.FramedPlanes
