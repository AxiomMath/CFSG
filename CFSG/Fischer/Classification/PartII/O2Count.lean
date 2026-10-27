module

public import CFSG.Fischer.Classification.PartII.O2Coord
public import CFSG.Fischer.Classification.PartII.Herm.Count
public import CFSG.Fischer.Classification.Unitary.Mu

public noncomputable section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer LocalU O2Twin CFSG.Fischer.Classification.Unitary
open CFSG.ClassicalGroups.Unitary
open scoped LinearAlgebra.Projectivization

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace O2Mod

theorem two_le_of_isotropic {N : ℕ} {z : Fin N → K} (hz0 : z ≠ 0) (hz : herm frob z z = 0) :
    2 ≤ N := by
  by_contra hN
  push Not at hN
  interval_cases N
  · exact hz0 (Subsingleton.elim _ _)
  · have h0 : z 0 = 0 := by
      rw [herm_def, Fin.sum_univ_one] at hz
      by_contra h0
      exact one_ne_zero ((frob_mul_self h0).symm.trans hz)
    apply hz0
    funext i
    rw [Subsingleton.elim i 0, h0]
    rfl

theorem mem_muSet_DU_iff {n : ℕ} (hn : 1 ≤ n) {q : U2 (n + 2)} :
    q ∈ muSet (DU (n + 2)) (tqU (v₀ n)) (tqU (u₀ n)) ↔
      ∃ z : Fin n → K, z ≠ 0 ∧ herm frob z z = 0 ∧ tqU (ι n z) = q := by
  constructor
  · rintro ⟨hq1, hq2⟩
    obtain ⟨w, hw0, hw, rfl⟩ := mem_DU_iff.1 hq1.1
    obtain ⟨hvw, -⟩ := (tqU_mem_localClass_iff (by omega) v₀_ne_zero herm_v₀_v₀ hw0 hw).1 hq1
    obtain ⟨huw, -⟩ := (tqU_mem_localClass_iff (by omega) u₀_ne_zero herm_u₀_u₀ hw0 hw).1 hq2
    have hwι : w = ι n (π n w) := by
      conv_lhs => rw [decomp_of_perp hvw]
      rw [huw, zero_smul, zero_add]
    refine ⟨π n w, fun h => hw0 (by rw [hwι, h, map_zero]), ?_, by rw [← hwι]⟩
    rw [← herm_ι_ι, ← hwι, hw]
  · rintro ⟨z, hz0, hz, rfl⟩
    have hι0 := ι_ne_zero hz0
    have hι : herm frob (ι n z) (ι n z) = 0 := by rw [herm_ι_ι, hz]
    exact ⟨(tqU_mem_localClass_iff (by omega) v₀_ne_zero herm_v₀_v₀ hι0 hι).2
        ⟨herm_v₀_ι z, ι_ne_smul_v₀ hz0⟩,
      (tqU_mem_localClass_iff (by omega) u₀_ne_zero herm_u₀_u₀ hι0 hι).2
        ⟨herm_u₀_ι z, ι_ne_smul_u₀ hz0⟩⟩

variable {H : Type} [Group H] {E μ : Set H}

namespace IsTwinSection

namespace Coords

variable {hμ : IsTwinSection E μ} {hP : Pair H E} {h4 : ∀ a ∈ E, (twinClass E a).ncard = 4}
  {N : ℕ} (C : hμ.Coords hP h4 N)

include C in
theorem two_le (hZ : Subgroup.center H = ⊥) : 2 ≤ N := by
  obtain ⟨e, he⟩ := Pair.nonempty hP
  exact two_le_of_isotropic (C.cv_ne_zero hZ he) (C.herm_cv_self he)

theorem herm_ξ_eq_zero {z : Fin N → K} (h : ∀ f : XT E μ, herm frob z (C.xv f) = 0)
    (u : SecModule E μ) : herm frob z (C.ξ u) = 0 := by
  have hu : u ∈ Submodule.span (ZMod 2) (Set.range (vec (E := E) (μ := μ))) := by
    rw [span_range_vec]
    trivial
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, rfl⟩ := hx
    exact h f
  | zero => rw [map_zero, herm_zero_right]
  | add x y _ _ hx hy => rw [map_add, herm_add_right, hx, hy, add_zero]
  | smul r x _ hx =>
    rcases Symplectic.zmod_two_cases r with rfl | rfl
    · rw [zero_smul, map_zero, herm_zero_right]
    · rw [one_smul, hx]

theorem eq_zero_of_herm_xv {z : Fin N → K} (h : ∀ f : XT E μ, herm frob z (C.xv f) = 0) :
    z = 0 :=
  eq_zero_of_herm frob fun y => by
    rw [← C.ξ.apply_symm_apply y]
    exact C.herm_ξ_eq_zero h _

theorem exists_conj_translate (hZ : Subgroup.center H = ⊥) (v : Fin N → K) :
    ∃ h : H, ∀ e ∈ E, C.toModel (h * e * h⁻¹) =
      tqU (lineVec (C.cv e) (ht μ e + herm frob v (C.cv e))) := by
  have hN : 1 ≤ N := by have := C.two_le hZ; omega
  have h0 : ∃ h : H, ∀ e ∈ E, C.toModel (h * e * h⁻¹) =
      tqU (lineVec (C.cv e) (ht μ e + herm frob (C.ξ 0) (C.cv e))) :=
    ⟨1, fun e _ => by rw [map_zero, herm_zero_left, add_zero, one_mul, inv_one, mul_one]; rfl⟩
  obtain ⟨u, rfl⟩ := C.ξ.surjective v
  have hu : u ∈ Submodule.span (ZMod 2) (Set.range (vec (E := E) (μ := μ))) := by
    rw [span_range_vec]
    trivial
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, rfl⟩ := hx
    have hfE := f.2.1
    have hfμ := f.2.2
    obtain ⟨t, ht, hft⟩ : ∃ t, t ∈ μ ∧ IsTwin E f t :=
      ⟨sec E μ f, hμ.sec_mem hfE, hμ.isTwin_sec hfE⟩
    have htE := hμ.subset ht
    obtain ⟨c, hc0, hc⟩ := (C.isTwin_iff_cv htE hfE).1 (isTwin_symm hft)
    have hxv : C.ξ (vec f) = C.cv f := (C.cv_of_notMem hfE hfμ).symm
    refine ⟨t * f, fun e he => ?_⟩
    have hconj : t * f * e * (t * f)⁻¹ = t * (f * e * f) * t := by
      rw [mul_inv_rev, Pair.inv_eq hP hfE, Pair.inv_eq hP htE]
      group
    have hfefE := Pair.mul_mul_mem hP hfE he
    rw [hconj, C.toModel_mul_mul hZ htE hfefE, C.toModel_mul_mul hZ hfE he, C.toModel_of_mem ht,
      C.toModel_of_notMem hfμ, toModel, mvec, ← lineVec_zero,
      tqU_mul_mul_lineVec (C.herm_cv_self hfE) (C.herm_cv_self he), hxv]
    have hiso : herm frob (C.cv e + herm frob (C.cv f) (C.cv e) • C.cv f)
        (C.cv e + herm frob (C.cv f) (C.cv e) • C.cv f) = 0 := by
      rw [herm_add_left, herm_add_right, herm_add_right, herm_smul_left, herm_smul_left,
        herm_smul_right, herm_smul_right, C.herm_cv_self he, C.herm_cv_self hfE,
        herm_conj frob frob_frob (C.cv f) (C.cv e)]
      linear_combination (herm frob (C.cv f) (C.cv e) * frob (herm frob (C.cv f) (C.cv e))) *
        two_eq_zero
    rw [tqU_mul_mul_lineVec (C.herm_cv_self htE) hiso]
    have hft' : herm frob (C.cv t) (C.cv f) = 0 := (C.herm_cv_eq_zero_iff htE hfE).2 hft.2.2.1.symm
    have hfe : herm frob (C.cv f) (C.cv e) = frob c * herm frob (C.cv t) (C.cv e) := by
      rw [hc, herm_smul_left]
    rw [herm_add_right, herm_smul_right, hft', mul_zero, add_zero, mul_zero, add_zero, mul_one]
    congr 2
    rw [hfe, hc, smul_smul, add_assoc, ← add_smul,
      show frob c * herm frob (C.cv t) (C.cv e) * c + herm frob (C.cv t) (C.cv e) =
        (frob c * c) * herm frob (C.cv t) (C.cv e) + herm frob (C.cv t) (C.cv e) by ring,
      frob_mul_self hc0, one_mul, add_self_K, zero_smul, add_zero]
  | zero => exact h0
  | add x y _ _ hx hy =>
    obtain ⟨h₁, hh₁⟩ := hx
    obtain ⟨h₂, hh₂⟩ := hy
    refine ⟨h₁ * h₂, fun e he => ?_⟩
    have he' : h₂ * e * h₂⁻¹ ∈ E := Pair.conj_mem hP he h₂
    have e1 : h₁ * h₂ * e * (h₁ * h₂)⁻¹ = h₁ * (h₂ * e * h₂⁻¹) * h₁⁻¹ := by group
    rw [e1, hh₁ _ he']
    have h2 := hh₂ e he
    rw [toModel, mvec] at h2
    obtain ⟨c, hc1, hc2⟩ := (tqU_lineVec_eq_iff hN (C.cv_ne_zero hZ he') (C.herm_cv_self he')
      (C.cv_ne_zero hZ he) (C.herm_cv_self he) _ _).1 h2
    refine (tqU_lineVec_eq_iff hN (C.cv_ne_zero hZ he') (C.herm_cv_self he')
      (C.cv_ne_zero hZ he) (C.herm_cv_self he) _ _).2 ⟨c, hc1, ?_⟩
    rw [map_add, herm_add_left, ← add_assoc, add_right_comm, hc2, hc1, herm_smul_right]
    ring
  | smul r x _ hx =>
    rcases Symplectic.zmod_two_cases r with rfl | rfl
    · rw [zero_smul]
      exact h0
    · rw [one_smul]
      exact hx

@[expose] def transSet (v : Fin N → K) : Set H :=
  {e | e ∈ E ∧ ht μ e + herm frob v (C.cv e) = 0}

theorem exists_transSet_eq_conj (hZ : Subgroup.center H = ⊥) (v : Fin N → K) :
    ∃ h : H, C.transSet v = (fun e => h * e * h⁻¹) '' μ := by
  have hN : 1 ≤ N := by have := C.two_le hZ; omega
  obtain ⟨h, hh⟩ := C.exists_conj_translate hZ v
  refine ⟨h⁻¹, Set.ext fun e => ⟨fun ⟨he, hv⟩ => ?_, ?_⟩⟩
  · have hE' := Pair.conj_mem hP he h
    refine ⟨h * e * h⁻¹, ?_, by group⟩
    have h1 := hh e he
    rw [toModel, mvec] at h1
    obtain ⟨c, hc1, hc2⟩ := (tqU_lineVec_eq_iff hN (C.cv_ne_zero hZ hE') (C.herm_cv_self hE')
      (C.cv_ne_zero hZ he) (C.herm_cv_self he) _ _).1 h1
    have hc : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc1
      exact C.cv_ne_zero hZ he hc1
    rw [hv] at hc2
    by_contra hnot
    rw [ht_of_notMem hnot, mul_one] at hc2
    exact hc hc2.symm
  · rintro ⟨s, hs, rfl⟩
    have heE : h⁻¹ * s * h⁻¹⁻¹ ∈ E := Pair.conj_mem hP (hμ.subset hs) h⁻¹
    refine ⟨heE, ?_⟩
    have h1 := hh _ heE
    have e2 : h * (h⁻¹ * s * h⁻¹⁻¹) * h⁻¹ = s := by group
    rw [e2, toModel, mvec, ht_of_mem hs] at h1
    obtain ⟨c, -, hc2⟩ := (tqU_lineVec_eq_iff hN (C.cv_ne_zero hZ (hμ.subset hs))
      (C.herm_cv_self (hμ.subset hs)) (C.cv_ne_zero hZ heE) (C.herm_cv_self heE) _ _).1 h1
    rw [hc2, mul_zero]

theorem transSet_injective : Function.Injective C.transSet := by
  intro v w hvw
  have key : ∀ s ∈ μ, herm frob v (C.cv s) = herm frob w (C.cv s) := by
    intro s hs
    have hsE := hμ.subset hs
    have hmem : ∀ u, s ∈ C.transSet u ↔ herm frob u (C.cv s) = 0 := fun u => by
      simp only [transSet, Set.mem_ofPred_eq, ht_of_mem hs, zero_add, hsE, true_and]
    by_cases h0 : herm frob v (C.cv s) = 0
    · rw [h0, eq_comm, ← hmem, ← hvw, hmem, h0]
    · obtain ⟨g, -, hgv⟩ := C.exists_xv_eq_smul' (hμ.xrT hP h4 hsE) (inv_ne_zero h0)
      have hcg : C.cv g = (herm frob v (C.cv s))⁻¹ • C.cv s := by
        rw [← C.cv_eq_xv hsE] at hgv
        rw [C.cv_of_notMem g.2.1 g.2.2]
        exact hgv
      have hgmem : ∀ u, (g : H) ∈ C.transSet u ↔
          1 + (herm frob v (C.cv s))⁻¹ * herm frob u (C.cv s) = 0 := fun u => by
        simp only [transSet, Set.mem_ofPred_eq, ht_of_notMem g.2.2, g.2.1, true_and, hcg,
          herm_smul_right]
      have h1 : (g : H) ∈ C.transSet v := by rw [hgmem, inv_mul_cancel₀ h0, add_self_K]
      rw [hvw, hgmem, one_add_eq_zero_iff, inv_mul_eq_one₀ h0] at h1
      exact h1
  have key' : ∀ f : XT E μ, herm frob (v - w) (C.xv f) = 0 := by
    intro f
    obtain ⟨c, -, hc⟩ := (C.isTwin_iff_cv (hμ.subset (hμ.sec_mem f.2.1)) f.2.1).1
      (isTwin_symm (hμ.isTwin_sec f.2.1))
    rw [← C.cv_of_notMem f.2.1 f.2.2, hc, herm_sub_left, herm_smul_right, herm_smul_right,
      key _ (hμ.sec_mem f.2.1), sub_self]
  exact sub_eq_zero.1 (C.eq_zero_of_herm_xv key')

@[expose] def secPt (hZ : Subgroup.center H = ⊥) {e : H} (he : e ∈ E) : isoPts frob N :=
  pt (C.cv e) (C.cv_ne_zero hZ he) (C.herm_cv_self he)

theorem herm_secPt_ne_zero (hZ : Subgroup.center H = ⊥) {e₀ s : H} (he₀ : e₀ ∈ E) (hs : s ∈ E)
    (hne : s * e₀ ≠ e₀ * s) :
    herm frob (C.cv e₀) ((C.secPt hZ hs : isoPts frob N) : ℙ K (Fin N → K)).rep ≠ 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K (C.cv s) (C.cv_ne_zero hZ hs)
  change herm frob (C.cv e₀) (Projectivization.mk K (C.cv s) (C.cv_ne_zero hZ hs)).rep ≠ 0
  rw [← ha, Units.smul_def, herm_smul_right]
  exact mul_ne_zero a.ne_zero fun h => hne ((C.herm_cv_eq_zero_iff he₀ hs).1 h).symm

@[expose] def secPtMap (hZ : Subgroup.center H = ⊥) {e₀ : H} (he₀ : e₀ ∈ E) :
    {s | s ∈ μ ∧ s * e₀ ≠ e₀ * s} →
      {p : isoPts frob N // herm frob (C.cv e₀) (p : ℙ K (Fin N → K)).rep ≠ 0} :=
  fun s => ⟨C.secPt hZ (hμ.subset s.2.1), C.herm_secPt_ne_zero hZ he₀ (hμ.subset s.2.1) s.2.2⟩

theorem secPtMap_injective (hZ : Subgroup.center H = ⊥) {e₀ : H} (he₀ : e₀ ∈ E) :
    Function.Injective (C.secPtMap hZ he₀) := by
  intro s s' h
  have h1 : C.secPt hZ (hμ.subset s.2.1) = C.secPt hZ (hμ.subset s'.2.1) :=
    congrArg Subtype.val h
  obtain ⟨c, hc⟩ := (pt_eq_pt_iff _ _ _ _).1 h1
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact C.cv_ne_zero hZ (hμ.subset s.2.1) hc.symm
  have htw : IsTwin E (s' : H) s :=
    (C.isTwin_iff_cv (hμ.subset s'.2.1) (hμ.subset s.2.1)).2 ⟨c, hc0, hc.symm⟩
  exact Subtype.ext (hμ.eq_of_isTwin _ s'.2.1 _ s.2.1 htw).symm

include C in
theorem ncard_sec_not_commute_le (hZ : Subgroup.center H = ⊥) {e₀ : H} (he₀ : e₀ ∈ E) :
    {s | s ∈ μ ∧ s * e₀ ≠ e₀ * s}.ncard ≤ 4 ^ N / 8 := by
  have := Pair.finite hP
  rw [← natCard_isoPts_herm_ne_zero (C.cv_ne_zero hZ he₀) (C.herm_cv_self he₀),
    ← Nat.card_coe_set_eq]
  exact Nat.card_le_card_of_injective _ (C.secPtMap_injective hZ he₀)

theorem exists_eq_smul_cv (hZ : Subgroup.center H = ⊥)
    (hall : ∀ e₀ ∈ E, {s | s ∈ μ ∧ s * e₀ ≠ e₀ * s}.ncard = 4 ^ N / 8) {z : Fin N → K}
    (hz0 : z ≠ 0) (hz : herm frob z z = 0) : ∃ s ∈ μ, ∃ c : K, z = c • C.cv s := by
  have := Pair.finite hP
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : XT E μ, herm frob z (C.xv f₀) ≠ 0 := by
    by_contra! h
    exact hz0 (C.eq_zero_of_herm_xv h)
  set e₀ : H := (f₀ : H)
  have he₀ : e₀ ∈ E := f₀.2.1
  have hne : herm frob (C.cv e₀) z ≠ 0 := by
    rw [C.cv_of_notMem f₀.2.1 f₀.2.2]
    exact fun h => hf₀ (herm_eq_zero_comm frob frob_frob h)
  have hbij := (C.secPtMap_injective hZ he₀).bijective_of_nat_card_le (by
    rw [natCard_isoPts_herm_ne_zero (C.cv_ne_zero hZ he₀) (C.herm_cv_self he₀),
      Nat.card_coe_set_eq, hall e₀ he₀])
  have hp : herm frob (C.cv e₀) ((pt z hz0 hz : isoPts frob N) : ℙ K (Fin N → K)).rep ≠ 0 := by
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K z hz0
    change herm frob (C.cv e₀) (Projectivization.mk K z hz0).rep ≠ 0
    rw [← ha, Units.smul_def, herm_smul_right]
    exact mul_ne_zero a.ne_zero hne
  obtain ⟨s, hs⟩ := hbij.2 ⟨pt z hz0 hz, hp⟩
  have h1 : C.secPt hZ (hμ.subset s.2.1) = pt z hz0 hz := congrArg Subtype.val hs
  obtain ⟨c, hc⟩ := (pt_eq_pt_iff _ _ _ _).1 h1
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact C.cv_ne_zero hZ (hμ.subset s.2.1) hc.symm
  refine ⟨s, s.2.1, c⁻¹, ?_⟩
  rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]

variable (hZ : Subgroup.center H = ⊥)
  (hiso : ∀ z : Fin N → K, z ≠ 0 → herm frob z z = 0 → ∃ s ∈ μ, ∃ c : K, z = c • C.cv s)
include hZ hiso

theorem exists_toModel_eq {q : U2 (N + 2)} (hq : q ∈ LocalClass (DU (N + 2)) (tqU (v₀ N))) :
    ∃ e ∈ E, C.toModel e = q := by
  have hN : 1 ≤ N := by have := C.two_le hZ; omega
  obtain ⟨w, hw0, hw, rfl⟩ := mem_DU_iff.1 hq.1
  obtain ⟨hvw, hwv⟩ := (tqU_mem_localClass_iff (by omega) v₀_ne_zero herm_v₀_v₀ hw0 hw).1 hq
  obtain ⟨z, a, rfl⟩ : ∃ z a, w = lineVec z a :=
    ⟨π N w, herm frob (u₀ N) w, decomp_of_perp hvw⟩
  have hz0 : z ≠ 0 := fun h => hwv a (by rw [h, lineVec, map_zero, add_zero])
  have hz : herm frob z z = 0 := by
    rw [← herm_lineVec_eq z z a a]
    exact hw
  obtain ⟨s, hs, c, rfl⟩ := hiso z hz0 hz
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hz0
    exact hz0 rfl
  have hsE := hμ.subset hs
  by_cases ha : a = 0
  · refine ⟨s, hsE, ?_⟩
    rw [C.toModel_of_mem hs, ← lineVec_zero, ha,
      show lineVec (c • C.cv s) 0 = c • lineVec (C.cv s) 0 by rw [smul_lineVec, mul_zero],
      tqU_smul (isotropic_lineVec (C.herm_cv_self hsE) 0) hc0]
  · obtain ⟨g, -, hgv⟩ := C.exists_xv_eq_smul' (hμ.xrT hP h4 hsE)
      (mul_ne_zero (inv_ne_zero ha) hc0)
    refine ⟨g, g.2.1, ?_⟩
    have hcg : C.cv g = (a⁻¹ * c) • C.cv s := by
      rw [← C.cv_eq_xv hsE] at hgv
      rw [C.cv_of_notMem g.2.1 g.2.2]
      exact hgv
    have e1 : lineVec (c • C.cv s) a = a • lineVec ((a⁻¹ * c) • C.cv s) 1 := by
      rw [smul_lineVec, smul_smul, ← mul_assoc, mul_inv_cancel₀ ha, one_mul, mul_one]
    rw [C.toModel_of_notMem g.2.2, hcg, e1, tqU_smul (isotropic_lineVec (by
      rw [herm_smul_left, herm_smul_right, C.herm_cv_self hsE, mul_zero, mul_zero]) _) ha]

theorem image_toModel_sec :
    C.toModel '' μ = muSet (DU (N + 2)) (tqU (v₀ N)) (tqU (u₀ N)) := by
  have hN : 1 ≤ N := by have := C.two_le hZ; omega
  ext q
  rw [mem_muSet_DU_iff hN]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨C.cv s, C.cv_ne_zero hZ (hμ.subset hs), C.herm_cv_self (hμ.subset hs),
      (C.toModel_of_mem hs).symm⟩
  · rintro ⟨z, hz0, hz, rfl⟩
    obtain ⟨s, hs, c, rfl⟩ := hiso z hz0 hz
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hz0
      exact hz0 rfl
    refine ⟨s, hs, ?_⟩
    rw [C.toModel_of_mem hs, map_smul,
      tqU_smul (by rw [herm_ι_ι]; exact C.herm_cv_self (hμ.subset hs)) hc0]

end Coords

end IsTwinSection

end O2Mod

end CFSG.Fischer.Classification
