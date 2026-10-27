module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Iwasawa
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Odd

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

variable {K : Type} [Field K] [IsF2 K] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

section Rotation

variable {a b : V} (ha : Q a = 1) (hb : Q b = 1) (hab : polar Q a b = 1)

include ha hb hab

theorem reflect_mul_reflect_apply (v : V) :
    (reflect Q a * reflect Q b) v =
      v + polar Q v b • b + (polar Q v a + polar Q v b) • a := by
  have hba : polar Q b a = 1 := by rw [polar_comm, hab]
  rw [LinearEquiv.mul_apply, reflect_apply_of_map_eq_one' hb, reflect_apply_of_map_eq_one' ha,
    polar_add_left, polar_smul_left_eq, hba, mul_one]

theorem reflect_mul_reflect_cube : (reflect Q a * reflect Q b) ^ 3 = 1 := by
  have hba : polar Q b a = 1 := by rw [polar_comm, hab]
  have haa : polar Q a a = 0 := polar_self_f2 a
  have hbb : polar Q b b = 0 := polar_self_f2 b
  have hT := reflect_mul_reflect_apply ha hb hab
  have hA : ∀ v, polar Q ((reflect Q a * reflect Q b) v) a = polar Q v a + polar Q v b := by
    intro v
    rw [hT, polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq, hba, haa]
    ring
  have hB : ∀ v, polar Q ((reflect Q a * reflect Q b) v) b = polar Q v a := by
    intro v
    rw [hT, polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq, hab, hbb]
    linear_combination (polar Q v b) * (IsF2.two_eq_zero (K := K))
  have h2a : (2 : K) • a = 0 := by rw [IsF2.two_eq_zero, zero_smul]
  have h2b : (2 : K) • b = 0 := by rw [IsF2.two_eq_zero, zero_smul]
  generalize reflect Q a * reflect Q b = T at hT hA hB ⊢
  refine LinearEquiv.ext fun v => ?_
  rw [pow_three]
  change T (T (T v)) = v
  rw [hT (T (T v)), hA (T v), hB (T v), hT (T v), hA v, hB v, hT v]
  rcases IsF2.eq_zero_or_one (polar Q v a) with h1 | h1 <;>
    rcases IsF2.eq_zero_or_one (polar Q v b) with h2 | h2 <;>
    simp [h1, h2, IsF2.one_add_one] <;>
    linear_combination (norm := module) (1 : K) • h2a + (1 : K) • h2b

theorem reflect_mul_reflect_apply_left : (reflect Q a * reflect Q b) a = b := by
  have h2a : (2 : K) • a = 0 := by rw [IsF2.two_eq_zero, zero_smul]
  rw [reflect_mul_reflect_apply ha hb hab, polar_self_f2, hab]
  linear_combination (norm := module) (1 : K) • h2a

theorem reflect_mul_reflect_apply_right : (reflect Q a * reflect Q b) b = a + b := by
  have hba : polar Q b a = 1 := by rw [polar_comm, hab]
  rw [reflect_mul_reflect_apply ha hb hab, polar_self_f2, hba]
  module

theorem reflect_mul_reflect_apply_of_orth {u : V} (hua : polar Q u a = 0) (hub : polar Q u b = 0) :
    (reflect Q a * reflect Q b) u = u := by
  rw [reflect_mul_reflect_apply ha hb hab, hua, hub]
  simp

end Rotation

variable [FiniteDimensional K V]

theorem commutator_eq_top_of_single_center (hQ : (polarBilin Q).Nondegenerate)
    (hd : 4 ≤ finrank K V) {u₀ : V} (hu₀0 : u₀ ≠ 0) (hu₀ : Q u₀ = 0)
    (h : ∀ w, polar Q u₀ w = 0 → eichler Q u₀ w ∈ ⁅elementaryGroup Q, elementaryGroup Q⁆) :
    commutator (elementaryGroup Q) = ⊤ := by
  set N := commutator (elementaryGroup Q) with hNdef
  have hN : N.Normal := inferInstance
  have hmemN : ∀ x : elementaryGroup Q, (x : V ≃ₗ[K] V) ∈ ⁅elementaryGroup Q, elementaryGroup Q⁆ →
      x ∈ N := by
    intro x hx
    rw [← Subgroup.map_subtype_commutator (elementaryGroup Q)] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  have hgen : ∀ u w, Q u = 0 → polar Q u w = 0 →
      (⟨eichler Q u w, eichler_mem_elementaryGroup Q u w⟩ : elementaryGroup Q) ∈ N := by
    intro u w hu hw
    by_cases hu0 : u = 0
    · subst hu0
      have : (⟨eichler Q 0 w, eichler_mem_elementaryGroup Q 0 w⟩ : elementaryGroup Q) = 1 :=
        Subtype.ext (eichler_zero_left Q w)
      rw [this]
      exact N.one_mem
    obtain ⟨g, hg, hgu⟩ := exists_mem_elementaryGroup_apply_eq_f2 hQ hd hu₀0 hu0 hu₀ hu
    have hgO := elementaryGroup_le_orthogonalGroup Q hg
    have hv : polar Q u₀ (g⁻¹ w) = 0 := by
      rw [← polar_map_of_mem hgO, hgu, LinearEquiv.apply_inv_apply', hw]
    have hmem := hN.conj_mem _ (hmemN ⟨eichler Q u₀ (g⁻¹ w), eichler_mem_elementaryGroup Q _ _⟩
      (h _ hv)) ⟨g, hg⟩
    convert hmem using 1
    apply Subtype.ext
    change eichler Q u w = g * eichler Q u₀ (g⁻¹ w) * g⁻¹
    rw [eichler_conj hgO, hgu, LinearEquiv.apply_inv_apply']
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨u, w, hu, hw, rfl⟩ := hx
    exact hgen u w hu hw
  | one => exact N.one_mem
  | mul x y hx hy ihx ihy => exact N.mul_mem ihx ihy
  | inv x hx ihx => exact N.inv_mem ihx

theorem finrank_perp (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q) :
    finrank K P.perp = finrank K V - 2 := by
  have hspan : finrank K (Submodule.span K {P.e, P.f}) = 2 := by
    have hli := linearIndependent_pair_of_ne (K := K) P.e_ne_zero P.f_ne_zero (fun h => by
      have := P.polar_ef
      rw [← h, P.polar_ee] at this
      exact zero_ne_one this)
    rw [← Matrix.range_cons_cons_empty P.e P.f ![], finrank_span_eq_card hli, Fintype.card_fin]
  have hperp : P.perp = LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {P.e, P.f}) := by
    ext v
    rw [HypPair.mem_perp, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · rintro ⟨h1, h2⟩ y hy
      obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hy
      simp only [polarBilin_apply_apply, polar_add_left, polar_smul_left_eq, h1, h2, mul_zero,
        add_zero]
    · intro h
      have h1 := h P.e (Submodule.subset_span (by simp))
      have h2 := h P.f (Submodule.subset_span (by simp))
      exact ⟨by simpa [polarBilin_apply_apply] using h1, by simpa [polarBilin_apply_apply] using h2⟩
  rw [hperp, LinearMap.BilinForm.finrank_orthogonal hQ, hspan]

theorem commutator_elementaryGroup_eq_top_of_four (hQ : (polarBilin Q).Nondegenerate)
    (hd : finrank K V = 4)
    (hplane : ¬ ∃ W : Submodule K V, finrank K W = 2 ∧ ∀ w ∈ W, Q w = 0) :
    commutator (elementaryGroup Q) = ⊤ := by
  obtain ⟨u₀, hu₀0, hu₀⟩ := exists_ne_zero_map_eq_zero' (Q := Q) (by omega)
  obtain ⟨P, hPe⟩ := exists_hypPair hQ hu₀ hu₀0
  obtain ⟨a₁, ha₁, hea₁, hfa₁⟩ := exists_map_eq_one_polar_eq_zero hQ (by omega) P.polar_ef
  have ha₁0 : a₁ ≠ 0 := fun h0 => by rw [h0, QuadraticMap.map_zero] at ha₁; exact zero_ne_one ha₁
  have ha₁W : a₁ ∈ P.perp := HypPair.mem_perp.mpr ⟨hea₁, hfa₁⟩
  obtain ⟨a₂, ha₂W, ha₂ne⟩ := (P.polarNondegOn_perp hQ).exists_polar_ne_zero ha₁W ha₁0
  have ha₁a₂ : polar Q a₁ a₂ = 1 := IsF2.eq_one_of_ne_zero ha₂ne
  obtain ⟨hea₂, hfa₂⟩ := HypPair.mem_perp.mp ha₂W
  have ha₂0 : a₂ ≠ 0 := fun h0 => by rw [h0, polar_zero_right] at ha₁a₂; exact zero_ne_one ha₁a₂
  have ha₂Q : Q a₂ = 1 := by
    by_contra hne
    have hz : Q a₂ = 0 := by
      rcases IsF2.eq_zero_or_one (Q a₂) with h | h
      · exact h
      · exact absurd h hne
    refine hplane (exists_plane_of_orth_singular P.e_ne_zero ha₂0 (fun h => ?_) P.Q_e hz hea₂)
    rw [h, P.polar_fe] at hfa₂
    exact one_ne_zero hfa₂
  set g := reflect Q a₁ * reflect Q a₂ with hgdef
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    mul_mem (reflect_mem_orthogonalGroup Q a₁) (reflect_mem_orthogonalGroup Q a₂)
  have hg3 : g ^ 3 = 1 := reflect_mul_reflect_cube ha₁ ha₂Q ha₁a₂
  have hgE : g ∈ elementaryGroup Q :=
    mem_elementaryGroup_of_pow_eq_one_of_odd hQ (by omega) (Or.inr hplane) hgO
      (N := 3) ⟨1, rfl⟩ hg3
  have hgu : g P.e = P.e := reflect_mul_reflect_apply_of_orth ha₁ ha₂Q ha₁a₂ hea₁ hea₂
  have hga₁ : g a₁ = a₂ := reflect_mul_reflect_apply_left ha₁ ha₂Q ha₁a₂
  have hga₂ : g a₂ = a₁ + a₂ := reflect_mul_reflect_apply_right ha₁ ha₂Q ha₁a₂
  have hE₁ : eichler Q P.e a₁ ∈ ⁅elementaryGroup Q, elementaryGroup Q⁆ := by
    have := Subgroup.commutator_mem_commutator hgE (eichler_mem_elementaryGroup Q P.e a₂)
    rwa [commutatorElement_eichler hgO hgu hea₂, hga₂, add_sub_cancel_right] at this
  have hE₁₂ : eichler Q P.e (a₁ + a₂) ∈ ⁅elementaryGroup Q, elementaryGroup Q⁆ := by
    have := Subgroup.commutator_mem_commutator hgE (eichler_mem_elementaryGroup Q P.e a₁)
    rw [commutatorElement_eichler hgO hgu hea₁, hga₁, sub_eq_add_neg,
      neg_eq_self_of_two_eq_zero (K := K) IsF2.two_eq_zero a₁, add_comm] at this
    exact this
  have hE₂ : eichler Q P.e a₂ ∈ ⁅elementaryGroup Q, elementaryGroup Q⁆ := by
    have : eichler Q P.e a₂ = (eichler Q P.e a₁)⁻¹ * eichler Q P.e (a₁ + a₂) := by
      rw [← eichler_mul hea₁ hea₂, inv_mul_cancel_left]
    rw [this]
    exact mul_mem (inv_mem hE₁) hE₁₂
  have hspan : Submodule.span K {a₁, a₂} = P.perp := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]
      rintro z (rfl | rfl)
      · exact ha₁W
      · exact ha₂W
    · have hli := linearIndependent_pair_of_ne (K := K) ha₁0 ha₂0 (fun h => by
        rw [← h, polar_self_f2] at ha₁a₂
        exact zero_ne_one ha₁a₂)
      rw [← Matrix.range_cons_cons_empty a₁ a₂ ![], finrank_span_eq_card hli, Fintype.card_fin,
        finrank_perp hQ P, hd]
  refine commutator_eq_top_of_single_center hQ (by omega) hu₀0 hu₀ fun w hw => ?_
  rw [← hPe] at hw ⊢
  have hwe : polar Q w P.e = 0 := by rw [polar_comm]; exact hw
  have hdec : P.proj w + polar Q w P.f • P.e = w := by
    have := P.eq_add_proj w
    rw [hwe, zero_smul, add_zero] at this
    rw [add_comm]
    exact this.symm
  have hproj : P.proj w ∈ Submodule.span K {a₁, a₂} := by
    rw [hspan]
    exact P.proj_mem_perp w
  obtain ⟨c₁, c₂, hc⟩ := Submodule.mem_span_pair.mp hproj
  rw [← hdec, eichler_add_smul_self P.Q_e, ← hc]
  rcases IsF2.eq_zero_or_one c₁ with rfl | rfl <;> rcases IsF2.eq_zero_or_one c₂ with rfl | rfl
  · simp only [zero_smul, add_zero]
    rw [eichler_zero_right]
    exact one_mem _
  · simpa using hE₂
  · simpa using hE₁
  · simpa only [one_smul] using hE₁₂

theorem isSimpleGroup_elementaryGroup_of_four (hQ : (polarBilin Q).Nondegenerate)
    (hd : finrank K V = 4)
    (hplane : ¬ ∃ W : Submodule K V, finrank K W = 2 ∧ ∀ w ∈ W, Q w = 0) :
    IsSimpleGroup (elementaryGroup Q) :=
  isSimpleGroup_elementaryGroup_of_perfect hQ (by omega) (Or.inr hplane)
    (commutator_elementaryGroup_eq_top_of_four hQ hd hplane)

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
