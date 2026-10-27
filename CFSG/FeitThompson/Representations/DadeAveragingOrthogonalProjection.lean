module

public import CFSG.FeitThompson.Representations.DadeMapPreservesInnerProduct
public import CFSG.FeitThompson.Representations.DadeReciprocityAveraging
public import CFSG.FeitThompson.Representations.DadeAveragingLeftInverse
public import CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open ComplexConjugate ComplexOrder

variable {G : Type*} [Group G] {L : Subgroup G} {A : Set G} {H : G → Subgroup G}

theorem cfInner_self_nonneg {α : Type*} [Fintype α] (f : α → ℂ) : 0 ≤ cfInner f f := by
  rw [cfInner_self_eq_sum_normSq]
  have h : ((Nat.card α : ℂ))⁻¹ * ((∑ x, Complex.normSq (f x) : ℝ) : ℂ)
      = (((Nat.card α : ℝ)⁻¹ * ∑ x, Complex.normSq (f x) : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.zero_le_real]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ => Complex.normSq_nonneg _)

theorem cfInner_self_eq_add_of_cfInner_sub_eq_zero {α : Type*} [Fintype α] {u v : α → ℂ}
    (h : cfInner u (v - u) = 0) : cfInner v v = cfInner u u + cfInner (v - u) (v - u) := by
  have h1 : cfInner u v = cfInner u u := by
    rw [cfInner_sub_right] at h; linear_combination h
  have h2 : cfInner v u = cfInner u u := by
    rw [← conj_cfInner, h1, conj_cfInner]
  rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, h1, h2]
  ring

section

variable [Fintype G]

theorem dadeAverage_restrict_mem_dadeDomain (hD : IsDadeData L A H) {χ : G → ℂ}
    (hχ : χ ∈ classFun G) :
    (fun y : ↥L => dadeAverage A H χ (y : G)) ∈ dadeDomain L A :=
  mem_dadeDomain.2 ⟨dadeAverage_restrict_mem_classFun hD hχ,
    fun _ hx => dadeAverage_eq_zero_of_notMem hx⟩

noncomputable def dadeAverageToDomain (hD : IsDadeData L A H) :
    classFun G →ₗ[ℂ] dadeDomain L A where
  toFun χ := ⟨fun y : ↥L => dadeAverage A H (χ : G → ℂ) (y : G),
    dadeAverage_restrict_mem_dadeDomain hD χ.2⟩
  map_add' χ ψ := by
    refine Subtype.ext (funext fun y => ?_)
    simp [dadeAverage_add]
  map_smul' c χ := by
    refine Subtype.ext (funext fun y => ?_)
    simp [dadeAverage_smul]

@[simp]
theorem dadeAverageToDomain_coe (hD : IsDadeData L A H) (χ : classFun G) :
    ((dadeAverageToDomain hD χ : dadeDomain L A) : ↥L → ℂ)
      = fun y : ↥L => dadeAverage A H (χ : G → ℂ) (y : G) := (rfl)

noncomputable def dadeProjection (hD : IsDadeData L A H) : classFun G →ₗ[ℂ] classFun G :=
  (dadeMap hD).comp (dadeAverageToDomain hD)

theorem dadeProjection_apply (hD : IsDadeData L A H) (χ : classFun G) :
    dadeProjection hD χ = dadeMap hD (dadeAverageToDomain hD χ) := (rfl)

theorem dadeProjection_mem_range (hD : IsDadeData L A H) (χ : classFun G) :
    dadeProjection hD χ ∈ LinearMap.range (dadeMap hD) := ⟨_, rfl⟩

theorem dadeAverageToDomain_dadeProjection (hD : IsDadeData L A H) (χ : classFun G) :
    dadeAverageToDomain hD (dadeProjection hD χ) = dadeAverageToDomain hD χ := by
  refine Subtype.ext (funext fun y => ?_)
  simpa [dadeProjection_apply] using dadeAverage_dadeMap_apply hD (dadeAverageToDomain hD χ) y

theorem dadeProjection_idem (hD : IsDadeData L A H) (χ : classFun G) :
    dadeProjection hD (dadeProjection hD χ) = dadeProjection hD χ := by
  rw [dadeProjection_apply, dadeAverageToDomain_dadeProjection, dadeProjection_apply]

theorem cfInner_dadeMap_sub_dadeProjection (hD : IsDadeData L A H) (χ : classFun G)
    (f : dadeDomain L A) :
    cfInner ((dadeMap hD f : classFun G) : G → ℂ)
      ((χ : G → ℂ) - ((dadeProjection hD χ : classFun G) : G → ℂ)) = 0 := by
  have : Fintype ↥L := Fintype.ofFinite ↥L
  rw [cfInner_sub_right, cfInner_dadeMap_eq_cfInner_dadeAverage hD f χ.2, dadeProjection_apply,
    cfInner_dadeMap hD f (dadeAverageToDomain hD χ), dadeAverageToDomain_coe, sub_self]

theorem cfInner_eq_zero_of_mem_range_dadeMap (hD : IsDadeData L A H) (χ : classFun G)
    {ψ : classFun G} (hψ : ψ ∈ LinearMap.range (dadeMap hD)) :
    cfInner ((ψ : classFun G) : G → ℂ)
      ((χ : G → ℂ) - ((dadeProjection hD χ : classFun G) : G → ℂ)) = 0 := by
  obtain ⟨f, rfl⟩ := hψ
  exact cfInner_dadeMap_sub_dadeProjection hD χ f

section

variable [Fintype ↥L]

theorem cfInner_self_dadeProjection (hD : IsDadeData L A H) (χ : classFun G) :
    cfInner ((dadeProjection hD χ : classFun G) : G → ℂ)
        ((dadeProjection hD χ : classFun G) : G → ℂ)
      = cfInner (fun y : ↥L => dadeAverage A H (χ : G → ℂ) (y : G))
        (fun y : ↥L => dadeAverage A H (χ : G → ℂ) (y : G)) := by
  rw [dadeProjection_apply, cfInner_self_dadeMap hD (dadeAverageToDomain hD χ),
    dadeAverageToDomain_coe]

theorem cfInner_self_eq_add_cfInner_self_sub_dadeProjection (hD : IsDadeData L A H)
    (χ : classFun G) :
    cfInner (χ : G → ℂ) (χ : G → ℂ)
      = cfInner (fun y : ↥L => dadeAverage A H (χ : G → ℂ) (y : G))
          (fun y : ↥L => dadeAverage A H (χ : G → ℂ) (y : G))
        + cfInner ((χ : G → ℂ) - ((dadeProjection hD χ : classFun G) : G → ℂ))
          ((χ : G → ℂ) - ((dadeProjection hD χ : classFun G) : G → ℂ)) := by
  rw [← cfInner_self_dadeProjection hD χ]
  exact cfInner_self_eq_add_of_cfInner_sub_eq_zero
    (cfInner_dadeMap_sub_dadeProjection hD χ (dadeAverageToDomain hD χ))

theorem cfInner_self_dadeAverage_le (hD : IsDadeData L A H) (χ : classFun G) :
    cfInner (fun y : ↥L => dadeAverage A H (χ : G → ℂ) (y : G))
        (fun y : ↥L => dadeAverage A H (χ : G → ℂ) (y : G))
      ≤ cfInner (χ : G → ℂ) (χ : G → ℂ) := by
  rw [cfInner_self_eq_add_cfInner_self_sub_dadeProjection hD χ]
  exact le_add_of_nonneg_right (cfInner_self_nonneg _)

theorem cfInner_self_dadeAverage_eq_iff (hD : IsDadeData L A H) (χ : classFun G) :
    cfInner (fun y : ↥L => dadeAverage A H (χ : G → ℂ) (y : G))
        (fun y : ↥L => dadeAverage A H (χ : G → ℂ) (y : G))
      = cfInner (χ : G → ℂ) (χ : G → ℂ) ↔ χ = dadeProjection hD χ := by
  rw [cfInner_self_eq_add_cfInner_self_sub_dadeProjection hD χ, eq_comm, add_eq_left,
    cfInner_self_eq_zero, sub_eq_zero, Subtype.ext_iff]

end

end

end CFSG.FeitThompson
