module

public import CFSG.FeitThompson.Representations.DisjointConjugateFamiliesOrthogonalImages
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.RealBridgeRemainderProjectionBound
import CFSG.FeitThompson.Representations.ArrayProjectionEnergySaturation
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
public import CFSG.FeitThompson.Representations.EqualDegreeFamilyCoherence
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace SibleyCentralAlignment

section Prescribe

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G] {S : Set (L → ℂ)}

noncomputable def spanLinear (hS : S ⊆ Irr L) (w : S → virtualChars G) :
    Submodule.span ℤ S →ₗ[ℤ] virtualChars G :=
  (spanBasis hS).constr ℤ w

noncomputable def spanHom (hS : S ⊆ Irr L) (w : S → virtualChars G) :
    Submodule.span ℤ S →+ virtualChars G := (spanLinear hS w).toAddMonoidHom

omit [Fintype G] in
theorem spanLinear_apply_mem (hS : S ⊆ Irr L) (w : S → virtualChars G) {v : L → ℂ}
    (hv : v ∈ Submodule.span ℤ S) (hvS : v ∈ S) :
    spanLinear hS w ⟨v, hv⟩ = w ⟨v, hvS⟩ := by
  have h : (spanBasis hS) ⟨v, hvS⟩ = (⟨v, hv⟩ : Submodule.span ℤ S) := Subtype.ext (by simp)
  rw [spanLinear, ← h, Module.Basis.constr_basis]

omit [Fintype G] in
theorem spanHom_apply_mem (hS : S ⊆ Irr L) (w : S → virtualChars G) {v : L → ℂ}
    (hv : v ∈ Submodule.span ℤ S) (hvS : v ∈ S) :
    spanHom hS w ⟨v, hv⟩ = w ⟨v, hvS⟩ := spanLinear_apply_mem hS w hv hvS

omit [Fintype G] in
theorem coherentVal_spanHom (hS : S ⊆ Irr L) (w : S → virtualChars G) (χ : S) :
    coherentVal (spanHom hS w) χ = (w χ : G → ℂ) := by
  rw [coherentVal_apply, spanHom_apply_mem hS w _ χ.2]

open scoped Classical in
theorem isCoherentWith_spanHom (hSfin : S.Finite) (hS : S ⊆ Irr L) {χ₀ : L → ℂ} (hχ₀ : χ₀ ∈ S)
    {d : ℂ} (hdeg : ∀ χ ∈ S, χ 1 = d) (τ : charSpanZero S →+ virtualChars G)
    (w : S → virtualChars G)
    (hw : ∀ χ ψ : S, cfInner (w χ : G → ℂ) (w ψ : G → ℂ) = if χ = ψ then 1 else 0)
    (hτw : ∀ (χ : S) (h : (χ : L → ℂ) - χ₀ ∈ charSpanZero S), (χ : L → ℂ) ≠ χ₀ →
      (τ ⟨(χ : L → ℂ) - χ₀, h⟩ : G → ℂ) = (w χ : G → ℂ) - (w ⟨χ₀, hχ₀⟩ : G → ℂ)) :
    IsCoherentWith S τ (spanHom hS w) := by
  classical
  refine ⟨?_, ?_⟩
  · intro f g
    refine cfInner_apply_apply_eq (spanBasis hS) (fun χ : S => (χ : L → ℂ))
      (fun χ : S => (w χ : G → ℂ))
      (Submodule.subtype _) (fun χ => by simp)
      ((virtualChars G).subtype.comp (spanLinear hS w)) (fun χ => ?_) ?_ ?_ ?_ ?_ f g
    · change ((spanLinear hS w) ((spanBasis hS) χ) : G → ℂ) = (w χ : G → ℂ)
      rw [spanLinear_apply_mem hS w ((spanBasis hS) χ).2 (by simpa using χ.2)]
      congr 1
      exact Subtype.ext (by simp)
    · intro χ; exact cfInner_self_of_mem_Irr (hS χ.2)
    · intro χ ψ h
      exact cfInner_eq_zero_of_mem_Irr (hS χ.2) (hS ψ.2) (fun he => h (Subtype.ext he))
    · intro χ; simpa using hw χ χ
    · intro χ ψ h; simpa [h] using hw χ ψ
  · have key : ((spanHom hS w).comp
        (Submodule.inclusion (charSpanZero_le S)).toAddMonoidHom).toIntLinearMap
        = τ.toIntLinearMap := by
      refine Module.Basis.ext (charSpanZeroBasis hSfin hS hχ₀ hdeg) fun χ => ?_
      have hχS : (χ : L → ℂ) ∈ S := χ.2.1
      have hχne : (χ : L → ℂ) ≠ χ₀ := χ.2.2
      have hcoe : ((charSpanZeroBasis hSfin hS hχ₀ hdeg χ : charSpanZero S) : L → ℂ)
          = (χ : L → ℂ) - χ₀ := charSpanZeroBasis_apply hSfin hS hχ₀ hdeg χ
      have hmem : (χ : L → ℂ) - χ₀ ∈ charSpanZero S :=
        hcoe ▸ (charSpanZeroBasis hSfin hS hχ₀ hdeg χ).2
      have hτeq : τ (charSpanZeroBasis hSfin hS hχ₀ hdeg χ) = τ ⟨(χ : L → ℂ) - χ₀, hmem⟩ :=
        congrArg τ (Subtype.ext hcoe)
      have hsplit : (Submodule.inclusion (charSpanZero_le S))
          (charSpanZeroBasis hSfin hS hχ₀ hdeg χ)
          = (⟨(χ : L → ℂ), Submodule.subset_span hχS⟩ : Submodule.span ℤ S)
            - ⟨χ₀, Submodule.subset_span hχ₀⟩ :=
        Subtype.ext (by simp [hcoe])
      change spanHom hS w ((Submodule.inclusion (charSpanZero_le S))
        (charSpanZeroBasis hSfin hS hχ₀ hdeg χ)) = τ (charSpanZeroBasis hSfin hS hχ₀ hdeg χ)
      rw [hsplit, map_sub, hτeq]
      refine Subtype.ext ?_
      rw [Submodule.coe_sub, spanHom_apply_mem hS w _ hχS, spanHom_apply_mem hS w _ hχ₀,
        hτw ⟨(χ : L → ℂ), hχS⟩ hmem hχne]
    intro f
    exact congrArg (fun (m : charSpanZero S →ₗ[ℤ] virtualChars G) => m f) key

end Prescribe

section Values

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G] {S : Set (L → ℂ)}
  {τ : charSpanZero S →+ virtualChars G} {ν : Submodule.span ℤ S →+ virtualChars G}

theorem coe_baseline_sub_zsmul (hν : IsCoherentWith S τ ν) {χ ψ : L → ℂ} (hχ : χ ∈ S) (hψ : ψ ∈ S)
    (n : ℤ) (h : χ - n • ψ ∈ charSpanZero S) :
    (τ ⟨χ - n • ψ, h⟩ : G → ℂ)
      = coherentVal ν ⟨χ, hχ⟩ - (n : ℂ) • coherentVal ν ⟨ψ, hψ⟩ := by
  have he := hν.eq_on_zero ⟨χ - n • ψ, h⟩
  have hincl : Submodule.inclusion (charSpanZero_le S) ⟨χ - n • ψ, h⟩
      = (⟨χ, Submodule.subset_span hχ⟩ : Submodule.span ℤ S)
        - n • ⟨ψ, Submodule.subset_span hψ⟩ := Subtype.ext (by simp)
  rw [hincl, map_sub, map_zsmul] at he
  have he' := congrArg (fun z : virtualChars G => (z : G → ℂ)) he
  simp only [Submodule.coe_sub, SetLike.val_smul] at he'
  rw [← he', coherentVal_apply, coherentVal_apply, ← Int.cast_smul_eq_zsmul ℂ]

theorem coe_baseline_sub (hν : IsCoherentWith S τ ν) {χ ψ : L → ℂ} (hχ : χ ∈ S) (hψ : ψ ∈ S)
    (h : χ - ψ ∈ charSpanZero S) :
    (τ ⟨χ - ψ, h⟩ : G → ℂ) = coherentVal ν ⟨χ, hχ⟩ - coherentVal ν ⟨ψ, hψ⟩ := by
  have h1 : χ - (1 : ℤ) • ψ = χ - ψ := by simp
  have h' : χ - (1 : ℤ) • ψ ∈ charSpanZero S := by rwa [h1]
  have hval := coe_baseline_sub_zsmul hν hχ hψ 1 h'
  rw [show (⟨χ - (1 : ℤ) • ψ, h'⟩ : charSpanZero S) = ⟨χ - ψ, h⟩ from Subtype.ext h1] at hval
  simpa using hval

end Values

section Coefficient

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G] {X Y : Set (L → ℂ)}

theorem cfInner_bridge_coherentVal (hXIrr : X ⊆ Irr L) (hYIrr : Y ⊆ Irr L) (hXY : Disjoint X Y)
    {τ : charSpanZero (X ∪ Y) →+ virtualChars G}
    (hτiso : ∀ f g : charSpanZero (X ∪ Y),
      cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ))
    {νX : Submodule.span ℤ X →+ virtualChars G} {νY : Submodule.span ℤ Y →+ virtualChars G}
    (hνX : IsCoherentWith X (restrictBaseline Set.subset_union_left τ) νX)
    {ξ₀ η₀ : L → ℂ} (hξ₀ : ξ₀ ∈ X) (hη₀ : η₀ ∈ Y)
    (hXYortho : ∀ (χ : X) (η : Y), cfInner (coherentVal νX χ) (coherentVal νY η) = 0)
    {c : ℤ} (hc : ξ₀ 1 = (c : ℂ) * η₀ 1) {Γ : G → ℂ}
    (hbridge : ∀ f : charSpanZero (X ∪ Y), (f : L → ℂ) = ξ₀ - (c : ℤ) • η₀ →
      (τ f : G → ℂ) = Γ - (c : ℂ) • coherentVal νY ⟨η₀, hη₀⟩)
    (χ : X) (hχne : (χ : L → ℂ) ≠ ξ₀) {b : ℤ} (hbdeg : (χ : L → ℂ) 1 = (b : ℂ) * ξ₀ 1) :
    cfInner Γ (coherentVal νX χ)
      = (b : ℂ) * (cfInner Γ (coherentVal νX ⟨ξ₀, hξ₀⟩) - 1) := by
  classical
  have hgX : (χ : L → ℂ) - b • ξ₀ ∈ charSpanZero X := by
    refine mem_charSpanZero.2 ⟨Submodule.sub_mem _ (Submodule.subset_span χ.2)
      (Submodule.smul_mem _ _ (Submodule.subset_span hξ₀)), ?_⟩
    rw [Pi.sub_apply, Pi.smul_apply, zsmul_eq_mul, hbdeg]
    ring
  have hgU : (χ : L → ℂ) - b • ξ₀ ∈ charSpanZero (X ∪ Y) :=
    FeitExtension.charSpanZero_mono Set.subset_union_left hgX
  have hfU : ξ₀ - (c : ℤ) • η₀ ∈ charSpanZero (X ∪ Y) := by
    refine mem_charSpanZero.2 ⟨Submodule.sub_mem _
      (Submodule.subset_span (Or.inl hξ₀))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr hη₀))), ?_⟩
    rw [Pi.sub_apply, Pi.smul_apply, zsmul_eq_mul, hc]
    ring
  have hτg : (τ ⟨(χ : L → ℂ) - b • ξ₀, hgU⟩ : G → ℂ)
      = coherentVal νX χ - (b : ℂ) • coherentVal νX ⟨ξ₀, hξ₀⟩ := by
    have h := hνX.eq_on_zero ⟨(χ : L → ℂ) - b • ξ₀, hgX⟩
    have hincl : Submodule.inclusion (charSpanZero_le X) ⟨(χ : L → ℂ) - b • ξ₀, hgX⟩
        = (⟨(χ : L → ℂ), Submodule.subset_span χ.2⟩ : Submodule.span ℤ X)
          - b • ⟨ξ₀, Submodule.subset_span hξ₀⟩ := Subtype.ext (by simp)
    rw [hincl, map_sub, map_zsmul] at h
    have h' := congrArg (fun z : virtualChars G => (z : G → ℂ)) h
    simp only [Submodule.coe_sub, SetLike.val_smul] at h'
    rw [restrictBaseline_coe_mk _ _ hgX hgU] at h'
    rw [← h', coherentVal_apply, coherentVal_apply, ← Int.cast_smul_eq_zsmul ℂ]
  have hiso := hτiso ⟨ξ₀ - (c : ℤ) • η₀, hfU⟩ ⟨(χ : L → ℂ) - b • ξ₀, hgU⟩
  rw [hbridge _ rfl, hτg] at hiso
  have hRHS : cfInner (ξ₀ - (c : ℤ) • η₀) ((χ : L → ℂ) - b • ξ₀) = -(b : ℂ) := by
    have h1 : cfInner ξ₀ (χ : L → ℂ) = 0 :=
      cfInner_eq_zero_of_mem_Irr (hXIrr hξ₀) (hXIrr χ.2) (Ne.symm hχne)
    have h2 : cfInner ξ₀ ξ₀ = 1 := cfInner_self_of_mem_Irr (hXIrr hξ₀)
    have h3 : cfInner η₀ (χ : L → ℂ) = 0 :=
      cfInner_eq_zero_of_mem_Irr (hYIrr hη₀) (hXIrr χ.2)
        (fun he => (Set.disjoint_left.1 hXY χ.2) (he ▸ hη₀))
    have h4 : cfInner η₀ ξ₀ = 0 :=
      cfInner_eq_zero_of_mem_Irr (hYIrr hη₀) (hXIrr hξ₀)
        (fun he => (Set.disjoint_left.1 hXY hξ₀) (he ▸ hη₀))
    rw [← Int.cast_smul_eq_zsmul ℂ, ← Int.cast_smul_eq_zsmul ℂ, cfInner_sub_left,
      cfInner_sub_right, cfInner_sub_right, cfInner_smul_left, cfInner_smul_left,
      cfInner_smul_right, cfInner_smul_right, h1, h2, h3, h4]
    simp
  rw [hRHS] at hiso
  have hortho : cfInner (coherentVal νY ⟨η₀, hη₀⟩) (coherentVal νX χ) = 0 := by
    rw [← conj_cfInner, hXYortho χ ⟨η₀, hη₀⟩, map_zero]
  have hortho0 : cfInner (coherentVal νY ⟨η₀, hη₀⟩) (coherentVal νX ⟨ξ₀, hξ₀⟩) = 0 := by
    rw [← conj_cfInner, hXYortho ⟨ξ₀, hξ₀⟩ ⟨η₀, hη₀⟩, map_zero]
  rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, cfInner_smul_left,
    cfInner_smul_left, cfInner_smul_right, cfInner_smul_right, hortho, hortho0,
    map_intCast] at hiso
  simp only [mul_zero, sub_zero] at hiso
  linear_combination hiso

end Coefficient

section Pivot

variable {G : Type*} [Group G] [Fintype G]

open ComplexConjugate

private theorem sum_mul_conj_intCast {ι : Type*} [Fintype ι] (a : ι → ℤ) :
    ∑ i, ((a i : ℂ)) * conj ((a i : ℂ)) = ((∑ i, a i ^ 2 : ℤ) : ℂ) := by
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_intCast]
  ring

private theorem eq_sum_smul_of_cfInner_eq_ite {ι : Type*} [Fintype ι] [DecidableEq ι]
    {e : ι → G → ℂ} (he : ∀ i j, cfInner (e i) (e j) = if i = j then 1 else 0)
    {x : G → ℂ} {c : ι → ℂ} (hc : ∀ i, cfInner x (e i) = c i)
    (hnorm : cfInner x x = ∑ i, c i * conj (c i)) : x = ∑ i, c i • e i := by
  have hη : ∀ k l, CauchySchwarzProjection.classFunInner (e k) (e l) = if k = l then 1 else 0 :=
    fun k l => by rw [← cfInner_eq_classFunInner]; exact he k l
  have hc' : ∀ k, CauchySchwarzProjection.classFunInner x (e k) = c k := fun k => by
    rw [← cfInner_eq_classFunInner]; exact hc k
  have h := CauchySchwarzProjection.classFunInner_self_eq_add_of_inner_eq hη x c hc'
  rw [← cfInner_eq_classFunInner, ← cfInner_eq_classFunInner, hnorm] at h
  have hz : cfInner (x - ∑ k, c k • e k) (x - ∑ k, c k • e k) = 0 := by linear_combination -h
  have : Nonempty G := ⟨1⟩
  exact sub_eq_zero.1 (cfInner_self_eq_zero.1 hz)

theorem eq_pivot_or_exists_eq_neg {ι : Type*} [Finite ι] [DecidableEq ι]
    {e : ι → G → ℂ} {i₀ : ι} (hcard : 2 ≤ Nat.card ι)
    (hmem : ∀ i, e i ∈ Submodule.span ℤ (Irr G))
    (he : ∀ i j, cfInner (e i) (e j) = if i = j then 1 else 0)
    {x : G → ℂ} (hx : x ∈ Submodule.span ℤ (Irr G)) (hxx : cfInner x x = 1)
    {b : ι → ℤ} (hbpos : ∀ i, 0 < b i)
    (hrel : ∀ i, i ≠ i₀ → cfInner x (e i) = (b i : ℂ) * (cfInner x (e i₀) - 1)) :
    x = e i₀ ∨ ∃ i₁, i₁ ≠ i₀ ∧ (∀ i, i ≠ i₀ → i = i₁) ∧ b i₁ = 1 ∧ x = -e i₁ := by
  classical
  have hfin : Fintype ι := Fintype.ofFinite ι
  choose a ha using fun i => exists_int_cfInner_of_mem_span_Irr hx (hmem i)
  have hbound : (∑ i, a i ^ 2 : ℤ) ≤ 1 := by
    have hb := sum_norm_sq_cfInner_le_re_of_cfInner_eq_ite he x
    rw [hxx] at hb
    simp only [Complex.one_re] at hb
    have hrw : ∀ i ∈ (Finset.univ : Finset ι), ‖cfInner x (e i)‖ ^ 2 = ((a i ^ 2 : ℤ) : ℝ) := by
      intro i _
      rw [ha i, Complex.norm_intCast]
      push_cast
      rw [sq_abs]
    rw [Finset.sum_congr rfl hrw] at hb
    exact_mod_cast hb
  have hpair : ∀ i j, i ≠ j → a i ^ 2 + a j ^ 2 ≤ 1 := by
    intro i j hij
    have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({i, j} : Finset ι))
      (fun k _ _ => sq_nonneg (a k))
    rw [Finset.sum_pair hij] at h
    exact le_trans h hbound
  have hrelZ : ∀ i, i ≠ i₀ → a i = b i * (a i₀ - 1) := by
    intro i hi
    have hab := hrel i hi
    rw [ha i, ha i₀] at hab
    exact_mod_cast hab
  obtain ⟨i₁, hi₁⟩ : ∃ i₁ : ι, i₁ ≠ i₀ := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have : Nat.card ι ≤ 1 := by
      rw [Nat.card_eq_fintype_card]
      refine Finset.card_le_one.2 fun x _ y _ => ?_
      rw [hcon x, hcon y]
    omega
  have hi0 : a i₀ = 1 ∨ a i₀ = 0 := by
    have hp := hpair i₀ i₁ (Ne.symm hi₁)
    have hab := hrelZ i₁ hi₁
    have hb1 := hbpos i₁
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨h1, h0⟩ := hcon
    have hsq : 1 ≤ a i₀ ^ 2 := by
      rcases lt_or_gt_of_ne h0 with h | h <;> nlinarith
    have hsq1 : 1 ≤ (a i₀ - 1) ^ 2 := by
      rcases lt_or_gt_of_ne h1 with h | h <;> nlinarith
    have hbsq : 1 ≤ b i₁ ^ 2 := by nlinarith
    have : 1 ≤ a i₁ ^ 2 := by
      rw [hab]
      calc (1 : ℤ) = 1 * 1 := by ring
        _ ≤ b i₁ ^ 2 * (a i₀ - 1) ^ 2 :=
            mul_le_mul hbsq hsq1 (by norm_num) (by positivity)
        _ = (b i₁ * (a i₀ - 1)) ^ 2 := by ring
    omega
  rcases hi0 with h1 | h0
  ·
    left
    have hzero : ∀ i, i ≠ i₀ → a i = 0 := fun i hi => by rw [hrelZ i hi, h1]; ring
    have hsum : (∑ i, a i ^ 2 : ℤ) = 1 := by
      rw [Finset.sum_eq_single i₀ (fun i _ hi => by rw [hzero i hi]; ring) (by simp), h1]
      ring
    have hxeq := eq_sum_smul_of_cfInner_eq_ite he (c := fun i => ((a i : ℤ) : ℂ)) (fun i => ha i)
      (by simp only [hxx, sum_mul_conj_intCast a, hsum]; norm_num)
    rw [hxeq, Finset.sum_eq_single i₀ (fun i _ hi => by rw [hzero i hi]; simp) (by simp), h1]
    simp
  ·
    right
    have hneg : ∀ i, i ≠ i₀ → a i = -b i := fun i hi => by rw [hrelZ i hi, h0]; ring
    have hone : ∀ i, i ≠ i₀ → b i = 1 := by
      intro i hi
      have hp := hpair i i₀ hi
      have hb := hbpos i
      rw [hneg i hi, h0] at hp
      nlinarith
    have huniq : ∀ i, i ≠ i₀ → i = i₁ := by
      intro i hi
      by_contra hne
      have hp := hpair i i₁ hne
      rw [hneg i hi, hneg i₁ hi₁, hone i hi, hone i₁ hi₁] at hp
      norm_num at hp
    refine ⟨i₁, hi₁, huniq, hone i₁ hi₁, ?_⟩
    have huniv : (Finset.univ : Finset ι) = {i₀, i₁} := by
      refine Finset.ext fun i => ⟨fun _ => ?_, fun _ => Finset.mem_univ i⟩
      by_cases hi : i = i₀
      · simp [hi]
      · simp [huniq i hi]
    have ha₁ : a i₁ = -1 := by rw [hneg i₁ hi₁, hone i₁ hi₁]
    have hsum : (∑ i, a i ^ 2 : ℤ) = 1 := by
      rw [huniv, Finset.sum_pair (Ne.symm hi₁), h0, ha₁]
      ring
    have hxeq := eq_sum_smul_of_cfInner_eq_ite he (c := fun i => ((a i : ℤ) : ℂ)) (fun i => ha i)
      (by simp only [hxx, sum_mul_conj_intCast a, hsum]; norm_num)
    rw [hxeq, huniv, Finset.sum_pair (Ne.symm hi₁), h0, ha₁]
    push_cast
    module

end Pivot

section Swap

theorem span_le_of_forall_eq_neg {ι α : Type*} (u v : ι → α → ℂ) (h : ∀ i, ∃ j, u i = -v j) :
    Submodule.span ℂ (Set.range u) ≤ Submodule.span ℂ (Set.range v) := by
  rw [Submodule.span_le]
  rintro y ⟨i, rfl⟩
  obtain ⟨j, hj⟩ := h i
  rw [hj]
  exact neg_mem (Submodule.subset_span ⟨j, rfl⟩)

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]

open scoped Classical in
theorem exists_isCoherentWith_swap {X : Set (L → ℂ)} (hXIrr : X ⊆ Irr L) (hXfin : X.Finite)
    {τ : charSpanZero X →+ virtualChars G} {νX : Submodule.span ℤ X →+ virtualChars G}
    (hνX : IsCoherentWith X τ νX)
    {ξ₀ : L → ℂ} (hξ₀ : ξ₀ ∈ X) (χ₁ : X) (hχ₁ne : χ₁ ≠ ⟨ξ₀, hξ₀⟩)
    (huniq : ∀ χ : X, χ ≠ ⟨ξ₀, hξ₀⟩ → χ = χ₁)
    (hdeg : ∀ χ ∈ X, χ 1 = ξ₀ 1) {Γ : G → ℂ} (hΓ₁ : Γ = -coherentVal νX χ₁) :
    ∃ μX : Submodule.span ℤ X →+ virtualChars G, IsCoherentWith X τ μX ∧
      Submodule.span ℂ (Set.range fun χ : X => coherentVal μX χ)
        = Submodule.span ℂ (Set.range fun χ : X => coherentVal νX χ) ∧
      coherentVal μX ⟨ξ₀, hξ₀⟩ = Γ := by
  classical
  set ξ₁ : L → ℂ := (χ₁ : L → ℂ) with hξ₁def
  have hξ₁ : ξ₁ ∈ X := χ₁.2
  have hne : ξ₁ ≠ ξ₀ := fun he => hχ₁ne (Subtype.ext he)
  set w : X → virtualChars G := fun χ =>
    if (χ : L → ℂ) = ξ₀ then -(νX ⟨ξ₁, Submodule.subset_span hξ₁⟩)
    else -(νX ⟨ξ₀, Submodule.subset_span hξ₀⟩) with hwdef
  have hw0 : (w ⟨ξ₀, hξ₀⟩ : G → ℂ) = -coherentVal νX ⟨ξ₁, hξ₁⟩ := by
    rw [hwdef]
    simp only [coherentVal_apply]
    simp
  have hw1 : ∀ χ : X, (χ : L → ℂ) ≠ ξ₀ → (w χ : G → ℂ) = -coherentVal νX ⟨ξ₀, hξ₀⟩ := by
    intro χ hχ
    rw [hwdef]
    simp only [hχ, if_false, coherentVal_apply]
    simp
  have hON : ∀ χ ψ : X, cfInner (coherentVal νX χ) (coherentVal νX ψ) = if χ = ψ then 1 else 0 :=
    cfInner_coherentVal_coherentVal hXIrr hνX
  have hwON : ∀ χ ψ : X, cfInner (w χ : G → ℂ) (w ψ : G → ℂ) = if χ = ψ then 1 else 0 := by
    intro χ ψ
    by_cases hχ : (χ : L → ℂ) = ξ₀ <;> by_cases hψ : (ψ : L → ℂ) = ξ₀
    · have hχe : χ = ⟨ξ₀, hξ₀⟩ := Subtype.ext hχ
      have hψe : ψ = ⟨ξ₀, hξ₀⟩ := Subtype.ext hψ
      rw [hχe, hψe, hw0, cfInner_neg_left, cfInner_neg_right, hON, if_pos rfl]
      norm_num
    · have hχe : χ = ⟨ξ₀, hξ₀⟩ := Subtype.ext hχ
      rw [hχe, hw0, hw1 ψ hψ, cfInner_neg_left, cfInner_neg_right, hON,
        if_neg (fun he : (⟨ξ₁, hξ₁⟩ : X) = ⟨ξ₀, hξ₀⟩ => hne (congrArg Subtype.val he)),
        if_neg (fun he : (⟨ξ₀, hξ₀⟩ : X) = ψ => hψ (congrArg Subtype.val he.symm))]
      norm_num
    · have hψe : ψ = ⟨ξ₀, hξ₀⟩ := Subtype.ext hψ
      rw [hψe, hw0, hw1 χ hχ, cfInner_neg_left, cfInner_neg_right, hON,
        if_neg (fun he : (⟨ξ₀, hξ₀⟩ : X) = ⟨ξ₁, hξ₁⟩ => hne (congrArg Subtype.val he.symm)),
        if_neg (fun he : χ = ⟨ξ₀, hξ₀⟩ => hχ (congrArg Subtype.val he))]
      norm_num
    · have hχe : χ = χ₁ := huniq χ (fun he => hχ (congrArg Subtype.val he))
      have hψe : ψ = χ₁ := huniq ψ (fun he => hψ (congrArg Subtype.val he))
      rw [hw1 χ hχ, hw1 ψ hψ, cfInner_neg_left, cfInner_neg_right, hON, if_pos rfl,
        if_pos (hχe.trans hψe.symm)]
      norm_num
  refine ⟨spanHom hXIrr w, ?_, ?_, ?_⟩
  · refine isCoherentWith_spanHom hXfin hXIrr hξ₀ hdeg τ w hwON ?_
    intro χ h hχ
    have hχe : χ = χ₁ := huniq χ (fun he => hχ (congrArg Subtype.val he))
    rw [coe_baseline_sub hνX χ.2 hξ₀ h, hw1 χ hχ, hw0]
    have hcv : coherentVal νX (⟨ξ₁, hξ₁⟩ : X) = coherentVal νX χ := by rw [hχe]
    rw [hcv]
    have hcv2 : coherentVal νX (⟨(χ : L → ℂ), χ.2⟩ : X) = coherentVal νX χ := rfl
    rw [hcv2]
    module
  · refine le_antisymm (span_le_of_forall_eq_neg _ _ fun χ => ?_)
      (span_le_of_forall_eq_neg _ _ fun χ => ?_)
    · by_cases hχ : (χ : L → ℂ) = ξ₀
      · refine ⟨⟨ξ₁, hξ₁⟩, ?_⟩
        rw [coherentVal_spanHom, show χ = (⟨ξ₀, hξ₀⟩ : X) from Subtype.ext hχ, hw0]
      · exact ⟨⟨ξ₀, hξ₀⟩, by rw [coherentVal_spanHom, hw1 χ hχ]⟩
    · by_cases hχ : (χ : L → ℂ) = ξ₀
      · refine ⟨χ₁, ?_⟩
        rw [coherentVal_spanHom, hw1 χ₁ hne, neg_neg,
          show χ = (⟨ξ₀, hξ₀⟩ : X) from Subtype.ext hχ]
      · refine ⟨⟨ξ₀, hξ₀⟩, ?_⟩
        have hχe : χ = χ₁ := huniq χ (fun he => hχ (congrArg Subtype.val he))
        rw [coherentVal_spanHom, hw0, neg_neg, hχe]
  · rw [coherentVal_spanHom, hw0, hΓ₁]

end Swap

section Main

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G] {X Y : Set (L → ℂ)}

open scoped Classical in
theorem exists_isCoherentWith_apply_eq_of_bridge
    (hXIrr : X ⊆ Irr L) (hYIrr : Y ⊆ Irr L) (hXY : Disjoint X Y)
    (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXstar : ∀ χ ∈ X, star χ ∈ X) (hYstar : ∀ χ ∈ Y, star χ ∈ Y)
    (hXnr : ∀ χ ∈ X, star χ ≠ χ) (hYnr : ∀ χ ∈ Y, star χ ≠ χ)
    {τ : charSpanZero (X ∪ Y) →+ virtualChars G}
    (hτ1 : ∀ f : charSpanZero (X ∪ Y), (τ f : G → ℂ) 1 = 0)
    (hτiso : ∀ f g : charSpanZero (X ∪ Y),
      cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ))
    (hτstar : ∀ f g : charSpanZero (X ∪ Y), (g : L → ℂ) = star (f : L → ℂ) →
      (τ g : G → ℂ) = star ((τ f : G → ℂ)))
    {νX : Submodule.span ℤ X →+ virtualChars G} {νY : Submodule.span ℤ Y →+ virtualChars G}
    (hνX : IsCoherentWith X (restrictBaseline Set.subset_union_left τ) νX)
    (hνY : IsCoherentWith Y (restrictBaseline Set.subset_union_right τ) νY)
    {ξ₀ η₀ : L → ℂ} (hξ₀ : ξ₀ ∈ X) (hη₀ : η₀ ∈ Y)
    (hdegratio : ∀ χ : X, ∃ b : ℤ, 0 < b ∧ (χ : L → ℂ) 1 = (b : ℂ) * ξ₀ 1)
    {c : ℤ} (hc : ξ₀ 1 = (c : ℂ) * η₀ 1)
    {Γ : G → ℂ} (hΓmem : Γ ∈ virtualChars G) (hΓnorm : cfInner Γ Γ = 1)
    (_hΓY : ∀ η : Y, cfInner Γ (coherentVal νY η) = 0)
    (hbridge : ∀ f : charSpanZero (X ∪ Y), (f : L → ℂ) = ξ₀ - (c : ℤ) • η₀ →
      (τ f : G → ℂ) = Γ - (c : ℂ) • coherentVal νY ⟨η₀, hη₀⟩) :
    ∃ μX : Submodule.span ℤ X →+ virtualChars G,
      IsCoherentWith X (restrictBaseline Set.subset_union_left τ) μX ∧
      Submodule.span ℂ (Set.range fun χ : X => coherentVal μX χ)
        = Submodule.span ℂ (Set.range fun χ : X => coherentVal νX χ) ∧
      coherentVal μX ⟨ξ₀, hξ₀⟩ = Γ := by
  classical
  have hXfin : X.Finite := finite_Irr.subset hXIrr
  have hXsub : Finite X := hXfin
  have hXYortho : ∀ (χ : X) (η : Y), cfInner (coherentVal νX χ) (coherentVal νY η) = 0 :=
    fun χ η => cfInner_coherentVal_coherentVal_eq_zero_of_disjoint hXIrr hYIrr hXY hXne hYne
      hXstar hYstar hXnr hYnr hτ1 hτiso (fun f => hτstar f _ (by simp)) hνX hνY χ η
  have hON : ∀ χ ψ : X, cfInner (coherentVal νX χ) (coherentVal νX ψ) = if χ = ψ then 1 else 0 :=
    cfInner_coherentVal_coherentVal hXIrr hνX
  have hmemν : ∀ χ : X, coherentVal νX χ ∈ Submodule.span ℤ (Irr G) := fun χ =>
    mem_span_Irr_of_mem_virtualChars (coherentVal_mem_virtualChars νX χ)
  have hcard : 2 ≤ Nat.card X := by
    rw [Nat.card_coe_set_eq]
    exact two_le_ncard_of_star_ne hXfin hXne hXstar hXnr
  choose b hbpos hbdeg using hdegratio
  have hpivot : ∀ χ : X, χ ≠ ⟨ξ₀, hξ₀⟩ →
      cfInner Γ (coherentVal νX χ)
        = (b χ : ℂ) * (cfInner Γ (coherentVal νX ⟨ξ₀, hξ₀⟩) - 1) := fun χ hχ =>
    cfInner_bridge_coherentVal hXIrr hYIrr hXY hτiso hνX hξ₀ hη₀ hXYortho hc hbridge χ
      (fun he => hχ (Subtype.ext he)) (hbdeg χ)
  rcases eq_pivot_or_exists_eq_neg (i₀ := ⟨ξ₀, hξ₀⟩) hcard hmemν hON
      (mem_span_Irr_of_mem_virtualChars hΓmem) hΓnorm hbpos hpivot with hΓ0 | hexc
  ·
    exact ⟨νX, hνX, rfl, hΓ0.symm⟩
  ·
    obtain ⟨χ₁, hχ₁ne, huniq, hb₁, hΓ₁⟩ := hexc
    have hdeg : ∀ χ ∈ X, χ 1 = ξ₀ 1 := by
      intro χ hχ
      by_cases hχ0 : χ = ξ₀
      · rw [hχ0]
      · have hsub : (⟨χ, hχ⟩ : X) = χ₁ :=
          huniq ⟨χ, hχ⟩ (fun he => hχ0 (congrArg Subtype.val he))
        have hb : b ⟨χ, hχ⟩ = 1 := by rw [hsub, hb₁]
        have hd := hbdeg ⟨χ, hχ⟩
        rw [hb] at hd
        simpa using hd
    exact exists_isCoherentWith_swap hXIrr hXfin hνX hξ₀ χ₁ hχ₁ne huniq hdeg hΓ₁

end Main

end SibleyCentralAlignment

end CFSG.FeitThompson
