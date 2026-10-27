module

public import CFSG.ClassicalGroups.Orthogonal.Derived
import CFSG.ClassicalGroups.Orthogonal.CharTwoTransvection
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticNormalForms
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankInv
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowTwist
import CFSG.Timmesfeld.Orders.ClassicalTransitive
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

private theorem exists_smul_map_eq_one_of_map_ne_zero [Finite K] [CharP K 2] {w : V}
    (hw : Q w ≠ 0) : ∃ c : K, c ≠ 0 ∧ Q (c • w) = 1 := by
  obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) ((Q w)⁻¹)
  refine ⟨c, ?_, ?_⟩
  · intro hc0
    rw [hc0, mul_zero] at hc
    exact inv_ne_zero hw hc
  · rw [map_smul_eq_sq, pow_two, ← hc, inv_mul_cancel₀ hw]

private theorem exists_smul_map_eq_of_map_ne_zero [Finite K] [CharP K 2] {x y : V}
    (hy : Q y ≠ 0) : ∃ c : K, Q (c • y) = Q x := by
  obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (Q x / Q y)
  refine ⟨c, ?_⟩
  rw [map_smul_eq_sq, pow_two, ← hc]
  exact div_mul_cancel₀ (Q x) hy

private theorem exists_mem_orthogonal_span_singleton_of_map_ne_zero [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {w : V} (hw0 : w ≠ 0) (h3 : 3 ≤ finrank K V) :
    ∃ a, a ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {w}) ∧
      Q a ≠ 0 := by
  have hV : 2 < finrank K V := lt_of_lt_of_le (by norm_num) h3
  set W := LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {w})
  have hWfin : finrank K W = finrank K V - 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hQ, finrank_span_singleton hw0]
  by_contra! hno
  have hle : W ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) W := by
    intro a ha
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro b hb
    have hQa : Q a = 0 := hno a ha
    have hQb : Q b = 0 := hno b hb
    have hQab : Q (b + a) = 0 := hno (b + a) (W.add_mem hb ha)
    rw [polarBilin_apply_apply, polar, hQab, hQb, hQa]
    ring
  have hle' := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hQ W] at hle'
  omega

private theorem span_setOf_map_eq_one_eq_top_of_three_le_finrank [Finite K] [CharP K 2]
    [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate) (h3 : 3 ≤ finrank K V) :
    Submodule.span K {v : V | Q v = 1} = ⊤ := by
  rw [eq_top_iff]
  intro w _
  by_cases hQw : Q w = 0
  · by_cases hw0 : w = 0
    · rw [hw0]
      exact Submodule.zero_mem _
    · obtain ⟨a, haW, hQa⟩ := exists_mem_orthogonal_span_singleton_of_map_ne_zero hQ hw0 h3
      obtain ⟨c, -, hQc⟩ := exists_smul_map_eq_one_of_map_ne_zero hQa
      have hwa : polar Q w a = 0 := by
        have := (LinearMap.BilinForm.mem_orthogonal_iff.mp haW) w
          (Submodule.subset_span (Set.mem_singleton w))
        rwa [polarBilin_apply_apply] at this
      have hwca : polar Q w (c • a) = 0 := by
        rw [polar_smul_right_eq, hwa, mul_zero]
      have h1 : Q (w + c • a) = 1 := by
        rw [QuadraticMap.map_add Q, hQw, hQc, hwca, zero_add, add_zero]
      have h2 : w = (w + c • a) - c • a := by abel
      rw [h2]
      exact Submodule.sub_mem _ (Submodule.subset_span h1) (Submodule.subset_span hQc)
  · obtain ⟨c, hc0, hQc⟩ := exists_smul_map_eq_one_of_map_ne_zero hQw
    have h1 : w = c⁻¹ • (c • w) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hQc)

private theorem exists_eq_smul_of_polar_eq_zero_of_anisotropic [Finite K] [CharP K 2]
    {P : ℕ → HypPair Q} {r : ℕ}
    (hA : ∀ x ∈ tailSpace P r, Q x = 0 → x = 0) {x : V} (hx : x ∈ tailSpace P r)
    (hx0 : x ≠ 0) {y : V} (hy : y ∈ tailSpace P r) (hxy : polar Q x y = 0) :
    ∃ c : K, y = c • x := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  by_cases hy0 : y = 0
  · exact ⟨0, by rw [hy0, zero_smul]⟩
  have hQx : Q x ≠ 0 := fun h => hx0 (hA x hx h)
  have hQy : Q y ≠ 0 := fun h => hy0 (hA y hy h)
  obtain ⟨c, hc⟩ := exists_smul_map_eq_of_map_ne_zero (x := x) (y := y) hQy
  have hsum : x + c • y = 0 := by
    apply hA (x + c • y) (Submodule.add_mem _ hx (Submodule.smul_mem _ _ hy))
    rw [QuadraticMap.map_add Q, hc, polar_smul_right_eq, hxy, mul_zero, add_zero,
      ← two_mul, h2, zero_mul]
  have hc0 : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_smul, map_zero] at hc
    exact hQx hc.symm
  have hxx : x + x = 0 := by rw [← two_smul K x, h2, zero_smul]
  have hcy : c • y = x := add_left_cancel (a := x) (by rw [hsum, hxx])
  refine ⟨c⁻¹, ?_⟩
  calc y = c⁻¹ • (c • y) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    _ = c⁻¹ • x := by rw [hcy]

private theorem elementaryGroup_le_closure_reflect_of_finite [Finite K] [CharP K 2]
    [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate) (h5 : 5 ≤ finrank K V) :
    elementaryGroup Q ≤ Subgroup.closure (Set.range (reflect Q)) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  refine elementaryGroup_le_of_eichler_mem fun u w hu huw => ?_
  by_cases hw : Q w = 0
  · obtain ⟨a, hua, hwa, ha⟩ := exists_polar_eq_zero_map_ne_zero hQ h5 u w
    obtain ⟨c, -, hQc⟩ := exists_smul_map_eq_one_of_map_ne_zero ha
    have hua' : polar Q u (c • a) = 0 := by rw [polar_smul_right_eq, hua, mul_zero]
    have hwa' : polar Q w (c • a) = 0 := by rw [polar_smul_right_eq, hwa, mul_zero]
    exact eichler_mem_closure_reflect_of_polar_eq_zero h2 hu huw hw hua' hwa' hQc
  · obtain ⟨c, hc0, hQc⟩ := exists_smul_map_eq_one_of_map_ne_zero hw
    have hu' : Q (c⁻¹ • u) = 0 := by rw [map_smul_eq_sq, hu, mul_zero]
    have huw' : polar Q (c⁻¹ • u) (c • w) = 0 := by
      rw [polar_smul_left_eq, polar_smul_right_eq, huw, mul_zero, mul_zero]
    have h1 : eichler Q u w = eichler Q (c⁻¹ • u) (c • w) := by
      simpa [smul_smul, mul_inv_cancel₀ hc0] using
        eichler_smul_left (Q := Q) c (c⁻¹ • u) w
    rw [h1]
    exact eichler_mem_closure_reflect_of_map_eq_one h2 hu' huw' hQc

private theorem closure_image_setOf_map_eq_one_eq_closure_range [Finite K] [CharP K 2] :
    Subgroup.closure ((reflect Q) '' {v : V | Q v = 1}) =
      Subgroup.closure (Set.range (reflect Q)) := by
  refine le_antisymm (Subgroup.closure_mono (Set.image_subset_range _ _)) ?_
  rw [Subgroup.closure_le]
  rintro _ ⟨v, rfl⟩
  by_cases hv : Q v = 0
  · rw [reflect_of_map_eq_zero hv]
    exact Subgroup.one_mem _
  · obtain ⟨c, hc0, hQc⟩ := exists_smul_map_eq_one_of_map_ne_zero hv
    rw [← CFSG.Timmesfeld.ClassicalOrders.reflect_smul hc0 v]
    exact Subgroup.subset_closure ⟨c • v, hQc, rfl⟩

theorem orthogonalGroup_eq_closure_reflect_of_finite {K V : Type*} [Field K] [Finite K]
    [CharP K 2] [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (h6 : 6 ≤ Module.finrank K V) :
    TauCeti.QuadraticMap.orthogonalGroup Q =
      Subgroup.closure ((reflect Q) '' {v | Q v = 1}) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h3 : 3 ≤ finrank K V := le_trans (by norm_num) h6
  have h5 : 5 ≤ finrank K V := le_trans (by norm_num) h6
  obtain ⟨x₀, -, hx₀, hQx₀⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.exists_singular_of_three_le
      (Q := Q) (polarNondegOn_top hQ) (by rw [finrank_top]; exact h3)
  obtain ⟨P₀, -⟩ := exists_hypPair hQ hQx₀ hx₀
  obtain ⟨r, P, hP, hA⟩ := exists_family_anisotropic hQ P₀
  have hr : 1 ≤ r := by
    by_contra! hr0
    rw [Nat.lt_one_iff.mp hr0] at hA
    exact hx₀ (hA x₀ Submodule.mem_top hQx₀)
  have hA' : ∀ x ∈ tailSpace P r, x ≠ 0 → ∀ y ∈ tailSpace P r,
      polar Q x y = 0 → ∃ c : K, y = c • x :=
    fun x hx hx0 y hy hxy => exists_eq_smul_of_polar_eq_zero_of_anisotropic hA hx hx0 hy hxy
  have hgen := orthogonalGroup_le_closure_of_two_eq_zero hP hQ h2 hA hA' hr
  have hEle := elementaryGroup_le_closure_reflect_of_finite (Q := Q) hQ h5
  have hRS := closure_image_setOf_map_eq_one_eq_closure_range (Q := Q)
  refine le_antisymm ?_ ?_
  · rw [hRS]
    refine hgen.trans ((Subgroup.closure_le _).mpr ?_)
    intro x hx
    rcases hx with hx | hx
    · exact Subgroup.subset_closure hx
    · exact hEle hx
  · rw [hRS]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨v, rfl⟩
    exact reflect_mem_orthogonalGroup Q v

theorem commute_reflect_iff {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {v w : V} (hv : Q v = 1) (hw : Q w = 1) :
    Commute (reflect Q v) (reflect Q w) ↔ QuadraticMap.polar Q v w = 0 := by
  have hv0 : v ≠ 0 := fun h0 => by rw [h0, map_zero] at hv; exact zero_ne_one hv
  constructor
  · intro h
    by_contra hb
    have hrvv : reflect Q v v = v := by
      rw [CFSG.SeitzReduction.SymplecticPilot.reflect_apply_of_map_eq_one_two hv,
        CFSG.ComponentClassification.UnbalancedCatalog.polar_self_charTwo Q v, zero_smul,
        add_zero]
    have hrvw : reflect Q v w = w + polar Q v w • v := by
      rw [CFSG.SeitzReduction.SymplecticPilot.reflect_apply_of_map_eq_one_two hv]
    have hrwv : reflect Q w v = v + polar Q v w • w := by
      rw [CFSG.SeitzReduction.SymplecticPilot.reflect_apply_of_map_eq_one_two hw, polar_comm]
    have hL : (reflect Q v * reflect Q w) v = v + polar Q v w • w +
        (polar Q v w * polar Q v w) • v := by
      rw [LinearEquiv.mul_apply, hrwv, map_add, map_smul, hrvv, hrvw, smul_add, smul_smul]
      abel
    have hR : (reflect Q w * reflect Q v) v = v + polar Q v w • w := by
      rw [LinearEquiv.mul_apply, hrvv, hrwv]
    have key := DFunLike.congr_fun h.eq v
    rw [hL, hR] at key
    have h' : (v + polar Q v w • w) + (polar Q v w * polar Q v w) • v =
        (v + polar Q v w • w) + 0 := by
      rw [add_zero]
      exact key
    have hzero : (polar Q v w * polar Q v w) • v = 0 := add_left_cancel h'
    rcases smul_eq_zero.mp hzero with h | h
    · exact hb (mul_self_eq_zero.mp h)
    · exact hv0 h
  · intro h
    exact CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.commute_reflect_of_polar_eq_zero h

private theorem eq_of_reflect_eq_of_map_eq [CharP K 2] {w v : V}
    (hQ : (polarBilin Q).Nondegenerate) (h : reflect Q w = reflect Q v) (hQwv : Q w = Q v)
    (hv : Q v ≠ 0) : w = v := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hv0 : v ≠ 0 := fun h0 => hv (by rw [h0, map_zero])
  obtain ⟨x, hx⟩ := exists_polar_ne_zero hQ hv0
  have key := DFunLike.congr_fun h x
  rw [reflect_apply (by rw [hQwv]; exact hv), reflect_apply hv] at key
  have hcoef : (polar Q w x / Q w) • w = (polar Q v x / Q v) • v := by
    have h1 : x + -((polar Q w x / Q w) • w) =
        x + -((polar Q v x / Q v) • v) := by
      simpa [sub_eq_add_neg] using key
    exact neg_inj.mp (add_left_cancel h1)
  have hb : polar Q v x / Q v ≠ 0 := div_ne_zero hx hv
  set c : K := (polar Q v x / Q v)⁻¹ * (polar Q w x / Q w) with hc
  have hvc : v = c • w := by
    calc v = (polar Q v x / Q v)⁻¹ • ((polar Q v x / Q v) • v) := by
          rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
      _ = (polar Q v x / Q v)⁻¹ • ((polar Q w x / Q w) • w) := by rw [← hcoef]
      _ = c • w := by rw [hc, smul_smul]
  have hcsq : c ^ 2 = 1 := by
    have h1 : Q v = c ^ 2 * Q v := by
      calc Q v = Q (c • w) := by rw [hvc]
        _ = c ^ 2 * Q w := by rw [map_smul_eq_sq]
        _ = c ^ 2 * Q v := by rw [hQwv]
    exact mul_right_cancel₀ hv (by rw [← h1, one_mul])
  have hc1 : c = 1 := by
    rcases sq_eq_one_iff.mp hcsq with h1 | h1
    · exact h1
    · rwa [neg_eq_self_of_two_eq_zero h2] at h1
  rw [hvc, hc1, one_smul]

theorem reflect_eq_reflect_iff {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {v w : V} (hv : Q v = 1) (hw : Q w = 1) :
    reflect Q v = reflect Q w ↔ v = w := by
  constructor
  · intro h
    exact eq_of_reflect_eq_of_map_eq hQ h (by rw [hv, hw]) (by rw [hw]; exact one_ne_zero)
  · rintro rfl
    rfl

theorem commute_reflect_iff_apply_eq {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (g : TauCeti.QuadraticMap.orthogonalGroup Q) {v : V} (hv : Q v ≠ 0) :
    Commute g ⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ ↔ (g : V ≃ₗ[K] V) v = v := by
  have hcomm_iff : Commute g ⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ ↔
      reflect Q ((g : V ≃ₗ[K] V) v) = reflect Q v := by
    have hcoe : Commute g ⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ ↔
        (g : V ≃ₗ[K] V) * reflect Q v = reflect Q v * (g : V ≃ₗ[K] V) := by
      constructor
      · intro h
        have := congrArg (fun s : TauCeti.QuadraticMap.orthogonalGroup Q => (s : V ≃ₗ[K] V))
          h.eq
        simpa [Subgroup.coe_mul] using this
      · intro h
        rw [Commute]
        exact Subtype.ext (by simpa [Subgroup.coe_mul] using h)
    rw [hcoe]
    constructor
    · intro h
      rw [← reflect_conj g.2 v, mul_inv_eq_iff_eq_mul]
      exact h
    · intro h
      rw [← mul_inv_eq_iff_eq_mul, reflect_conj g.2 v]
      exact h
  rw [hcomm_iff]
  constructor
  · intro h
    exact eq_of_reflect_eq_of_map_eq hQ h (map_of_mem g.2 v) hv
  · intro hgv
    rw [hgv]

theorem center_orthogonalGroup_eq_bot {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (h4 : 4 ≤ Module.finrank K V) :
    Subgroup.center (TauCeti.QuadraticMap.orthogonalGroup Q) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hfix : ∀ v : V, Q v = 1 → (g : V ≃ₗ[K] V) v = v := by
    intro v hv
    exact (commute_reflect_iff_apply_eq hQ g (by rw [hv]; exact one_ne_zero)).mp
      (Subgroup.mem_center_iff.mp hg ⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩).symm
  have h3 : 3 ≤ finrank K V := le_trans (by norm_num) h4
  have hspan : Submodule.span K {v : V | Q v = 1} = ⊤ :=
    span_setOf_map_eq_one_eq_top_of_three_le_finrank hQ h3
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext_on hspan
  intro v hv
  exact hfix v hv

end CFSG.ClassicalGroups.Orthogonal

end
