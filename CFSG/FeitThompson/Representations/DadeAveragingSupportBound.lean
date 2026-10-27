module

public import CFSG.FeitThompson.Representations.DadeAveragingOrthogonalProjection

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open ComplexOrder

variable {G : Type*} [Group G] {L : Subgroup G} {A : Set G} {H : G → Subgroup G}

theorem mem_totalDadeSupport_of_isConj {x y : G} (h : IsConj x y)
    (hx : x ∈ totalDadeSupport A H) : y ∈ totalDadeSupport A H := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  simpa using conj_mem_totalDadeSupport hx c⁻¹

theorem indicator_totalDadeSupport_mem_classFun {χ : G → ℂ} (hχ : χ ∈ classFun G) :
    (totalDadeSupport A H).indicator χ ∈ classFun G := by
  refine mem_classFun.2 fun x y h => ?_
  by_cases hx : x ∈ totalDadeSupport A H
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (mem_totalDadeSupport_of_isConj h hx),
      classFun.apply_eq_of_isConj hχ h]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem
      fun hy => hx (mem_totalDadeSupport_of_isConj h.symm hy)]

noncomputable def truncTotalDadeSupport (A : Set G) (H : G → Subgroup G) (χ : classFun G) :
    classFun G :=
  ⟨(totalDadeSupport A H).indicator (χ : G → ℂ), indicator_totalDadeSupport_mem_classFun χ.2⟩

@[simp]
theorem truncTotalDadeSupport_coe (A : Set G) (H : G → Subgroup G) (χ : classFun G) :
    ((truncTotalDadeSupport A H χ : classFun G) : G → ℂ)
      = (totalDadeSupport A H).indicator (χ : G → ℂ) := (rfl)

theorem truncTotalDadeSupport_apply_of_mem {χ : classFun G} {x : G}
    (hx : x ∈ totalDadeSupport A H) :
    ((truncTotalDadeSupport A H χ : classFun G) : G → ℂ) x = (χ : G → ℂ) x := by
  rw [truncTotalDadeSupport_coe, Set.indicator_of_mem hx]

theorem truncTotalDadeSupport_apply_of_notMem {χ : classFun G} {x : G}
    (hx : x ∉ totalDadeSupport A H) :
    ((truncTotalDadeSupport A H χ : classFun G) : G → ℂ) x = 0 := by
  rw [truncTotalDadeSupport_coe, Set.indicator_of_notMem hx]

section

variable [Fintype G]

theorem dadeAverage_indicator_totalDadeSupport (A : Set G) (H : G → Subgroup G) (χ : G → ℂ) :
    dadeAverage A H ((totalDadeSupport A H).indicator χ) = dadeAverage A H χ := by
  classical
  funext x
  by_cases hx : x ∈ A
  · rw [dadeAverage_apply_of_mem hx, dadeAverage_apply_of_mem hx]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    exact Set.indicator_of_mem (dadeSupport_subset_totalDadeSupport hx
      (dadeCoset_subset_dadeSupport H x (mul_mem_dadeCoset u.2))) _
  · rw [dadeAverage_eq_zero_of_notMem hx, dadeAverage_eq_zero_of_notMem hx]

theorem cfInner_self_indicator_totalDadeSupport (A : Set G) (H : G → Subgroup G) (χ : G → ℂ) :
    cfInner ((totalDadeSupport A H).indicator χ) ((totalDadeSupport A H).indicator χ)
      = (Nat.card G : ℂ)⁻¹ *
        ∑ g ∈ (totalDadeSupport_finite A H).toFinset, (‖χ g‖ : ℂ) ^ 2 := by
  rw [cfInner_self_eq_sum_norm_sq]
  congr 1
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm.trans (Finset.sum_congr rfl ?_)
  · intro g _ hg
    rw [Set.indicator_of_notMem (by simpa using hg)]
    norm_num
  · intro g hg
    rw [Set.indicator_of_mem (by simpa using hg)]

theorem dadeProjection_truncTotalDadeSupport_apply (hD : IsDadeData L A H) (χ : classFun G)
    {a : G} (ha : a ∈ A) {x : G} (hx : x ∈ dadeSupport H a) :
    ((dadeProjection hD (truncTotalDadeSupport A H χ) : classFun G) : G → ℂ) x
      = dadeAverage A H (χ : G → ℂ) a := by
  rw [dadeProjection_apply, dadeMap_apply_of_mem_dadeSupport hD _ ha hx]
  simp only [dadeAverageToDomain_coe, truncTotalDadeSupport_coe,
    dadeAverage_indicator_totalDadeSupport]

theorem truncTotalDadeSupport_eq_dadeProjection_iff (hD : IsDadeData L A H) (χ : classFun G) :
    truncTotalDadeSupport A H χ = dadeProjection hD (truncTotalDadeSupport A H χ) ↔
      ∀ a ∈ A, ∀ u ∈ H a, (χ : G → ℂ) (u * a) = (χ : G → ℂ) a := by
  constructor
  · intro hEq a ha u hu
    have hfun : ((truncTotalDadeSupport A H χ : classFun G) : G → ℂ)
        = ((dadeProjection hD (truncTotalDadeSupport A H χ) : classFun G) : G → ℂ) :=
      congrArg (fun c : classFun G => (c : G → ℂ)) hEq
    have hua : u * a ∈ dadeSupport H a :=
      dadeCoset_subset_dadeSupport H a (mul_mem_dadeCoset hu)
    have h1 : (χ : G → ℂ) (u * a) = dadeAverage A H (χ : G → ℂ) a := by
      rw [← truncTotalDadeSupport_apply_of_mem
        (dadeSupport_subset_totalDadeSupport ha hua), hfun,
        dadeProjection_truncTotalDadeSupport_apply hD χ ha hua]
    have h2 : (χ : G → ℂ) a = dadeAverage A H (χ : G → ℂ) a := by
      rw [← truncTotalDadeSupport_apply_of_mem
        (dadeSupport_subset_totalDadeSupport ha (self_mem_dadeSupport H a)), hfun,
        dadeProjection_truncTotalDadeSupport_apply hD χ ha (self_mem_dadeSupport H a)]
    rw [h1, h2]
  · intro hcond
    have havg : ∀ a ∈ A, dadeAverage A H (χ : G → ℂ) a = (χ : G → ℂ) a :=
      fun a ha => dadeAverage_apply_of_eq_on ha fun u hu => hcond a ha u hu
    refine Subtype.ext (funext fun x => ?_)
    by_cases hx : x ∈ totalDadeSupport A H
    · obtain ⟨a, ha, hxa⟩ := mem_totalDadeSupport_iff.1 hx
      rw [truncTotalDadeSupport_apply_of_mem hx,
        dadeProjection_truncTotalDadeSupport_apply hD χ ha hxa, havg a ha]
      obtain ⟨y, hy, hc⟩ := mem_dadeSupport_iff.1 hxa
      have hu : y * a⁻¹ ∈ H a := mem_dadeCoset_iff.1 hy
      have h2 : (χ : G → ℂ) (y * a⁻¹ * a) = (χ : G → ℂ) a := hcond a ha _ hu
      rw [show y * a⁻¹ * a = y by group] at h2
      rw [← classFun.apply_eq_of_isConj χ.2 hc]
      exact h2
    · rw [truncTotalDadeSupport_apply_of_notMem hx, dadeProjection_apply,
        dadeMap_eq_zero_of_notMem hD _ hx]

section

variable [Fintype ↥L]

theorem cfInner_self_dadeAverage_le_sum_totalDadeSupport (hD : IsDadeData L A H)
    (χ : classFun G) :
    cfInner (fun y : ↥L => dadeAverage A H (χ : G → ℂ) (y : G))
        (fun y : ↥L => dadeAverage A H (χ : G → ℂ) (y : G))
      ≤ (Nat.card G : ℂ)⁻¹ *
        ∑ g ∈ (totalDadeSupport_finite A H).toFinset, (‖(χ : G → ℂ) g‖ : ℂ) ^ 2 := by
  have h := cfInner_self_dadeAverage_le hD (truncTotalDadeSupport A H χ)
  rwa [truncTotalDadeSupport_coe, dadeAverage_indicator_totalDadeSupport,
    cfInner_self_indicator_totalDadeSupport] at h

theorem cfInner_self_dadeAverage_eq_sum_totalDadeSupport_iff (hD : IsDadeData L A H)
    (χ : classFun G) :
    cfInner (fun y : ↥L => dadeAverage A H (χ : G → ℂ) (y : G))
          (fun y : ↥L => dadeAverage A H (χ : G → ℂ) (y : G))
        = (Nat.card G : ℂ)⁻¹ *
          ∑ g ∈ (totalDadeSupport_finite A H).toFinset, (‖(χ : G → ℂ) g‖ : ℂ) ^ 2 ↔
      ∀ a ∈ A, ∀ u ∈ H a, (χ : G → ℂ) (u * a) = (χ : G → ℂ) a := by
  have key := cfInner_self_dadeAverage_eq_iff hD (truncTotalDadeSupport A H χ)
  rw [truncTotalDadeSupport_coe, dadeAverage_indicator_totalDadeSupport,
    cfInner_self_indicator_totalDadeSupport] at key
  rw [key, truncTotalDadeSupport_eq_dadeProjection_iff hD χ]

end

end

end CFSG.FeitThompson

end
