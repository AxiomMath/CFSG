module

public import CFSG.FeitThompson.Representations.CoherentFamilyCommonSignDegreeRatio
public import CFSG.FeitThompson.Representations.DegreeZeroIsometryDisjointConjPairs
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality
import CFSG.FeitThompson.Representations.CommonClassLinearCharacterCongruence

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {L G : Type*} [Group L] [Group G] {S : Set (L → ℂ)}

omit [Group L] in
theorem star_mem_span_of_star_mem (hSstar : ∀ χ ∈ S, star χ ∈ S) {f : L → ℂ}
    (hf : f ∈ Submodule.span ℤ S) : star f ∈ Submodule.span ℤ S := by
  induction hf using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (hSstar x hx)
  | zero => simp
  | add x y _ _ hx hy => rw [star_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [star_zsmul]; exact Submodule.smul_mem _ _ hx

theorem star_mem_charSpanZero (hSstar : ∀ χ ∈ S, star χ ∈ S) {f : L → ℂ}
    (hf : f ∈ charSpanZero S) : star f ∈ charSpanZero S :=
  mem_charSpanZero.2 ⟨star_mem_span_of_star_mem hSstar (mem_charSpanZero.1 hf).1, by
    simp [(mem_charSpanZero.1 hf).2]⟩

def starElem (hSstar : ∀ χ ∈ S, star χ ∈ S) (χ : S) : S := ⟨star (χ : L → ℂ), hSstar _ χ.2⟩

omit [Group L] in
@[simp] theorem coe_starElem (hSstar : ∀ χ ∈ S, star χ ∈ S) (χ : S) :
    ((starElem hSstar χ : S) : L → ℂ) = star (χ : L → ℂ) := (rfl)

omit [Group L] in
@[simp] theorem starElem_starElem (hSstar : ∀ χ ∈ S, star χ ∈ S) (χ : S) :
    starElem hSstar (starElem hSstar χ) = χ := Subtype.ext (by simp)

def starCharSpanZero (hSstar : ∀ χ ∈ S, star χ ∈ S) (f : charSpanZero S) : charSpanZero S :=
  ⟨star (f : L → ℂ), star_mem_charSpanZero hSstar f.2⟩

@[simp] theorem coe_starCharSpanZero (hSstar : ∀ χ ∈ S, star χ ∈ S) (f : charSpanZero S) :
    ((starCharSpanZero hSstar f : charSpanZero S) : L → ℂ) = star (f : L → ℂ) := (rfl)

open scoped Classical in
theorem eq_star_of_add_star_eq_add_star [Finite G] {η θ : G → ℂ} (hη : η ∈ Irr G)
    (hθ : θ ∈ Irr G) (hne : θ ≠ η) (h : η + star η = θ + star θ) :
    star η ≠ η ∧ θ = star η := by
  have : Fintype G := Fintype.ofFinite G
  have hpair : cfInner (η + star η) η = cfInner (θ + star θ) η := by rw [h]
  rw [cfInner_add_left, cfInner_add_left, cfInner_eq_ite_of_mem_Irr hη hη,
    cfInner_eq_ite_of_mem_Irr (star_mem_Irr hη) hη, cfInner_eq_ite_of_mem_Irr hθ hη,
    cfInner_eq_ite_of_mem_Irr (star_mem_Irr hθ) hη, if_pos rfl, if_neg hne] at hpair
  have hnr : star η ≠ η := by
    intro hc
    rw [if_pos hc] at hpair
    by_cases h2 : star θ = η
    · rw [if_pos h2] at hpair; norm_num at hpair
    · rw [if_neg h2] at hpair; norm_num at hpair
  refine ⟨hnr, ?_⟩
  rw [if_neg hnr] at hpair
  by_cases h2 : star θ = η
  · rw [← h2, star_star]
  · rw [if_neg h2] at hpair; norm_num at hpair

section Main

variable [Fintype L] [Fintype G] {τ : charSpanZero S →+ virtualChars G}
  {ν : Submodule.span ℤ S →+ virtualChars G}

theorem coherentVal_sub_coherentVal_starElem (hS : S ⊆ Irr L) (hSstar : ∀ χ ∈ S, star χ ∈ S)
    (hν : IsCoherentWith S τ ν) (χ : S) :
    coherentVal ν χ - coherentVal ν (starElem hSstar χ)
      = (τ ⟨(χ : L → ℂ) - star (χ : L → ℂ),
          sub_star_mem_charSpanZero hS hSstar χ.2⟩ : G → ℂ) := by
  set f : charSpanZero S := ⟨(χ : L → ℂ) - star (χ : L → ℂ),
    sub_star_mem_charSpanZero hS hSstar χ.2⟩ with hf
  have hincl : Submodule.inclusion (charSpanZero_le S) f
      = (⟨(χ : L → ℂ), Submodule.subset_span χ.2⟩ : Submodule.span ℤ S)
        - ⟨star (χ : L → ℂ), Submodule.subset_span (hSstar _ χ.2)⟩ :=
    Subtype.ext (by simp [hf])
  have h := hν.eq_on_zero f
  rw [hincl, map_sub] at h
  rw [coherentVal_apply, coherentVal_apply]
  simpa using congrArg (fun z : virtualChars G => (z : G → ℂ)) h

theorem exists_sign_nonreal_root_of_isCoherentWith (hS : S ⊆ Irr L) (hS2 : 2 ≤ S.ncard)
    (hSstar : ∀ χ ∈ S, star χ ∈ S) (hSne : ∀ χ ∈ S, star χ ≠ χ)
    (hτ1 : ∀ f : charSpanZero S, (τ f : G → ℂ) 1 = 0)
    (hτstar : ∀ f : charSpanZero S,
      (τ (starCharSpanZero hSstar f) : G → ℂ) = star ((τ f : G → ℂ)))
    (hν : IsCoherentWith S τ ν) :
    ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ ∃ η : S → (G → ℂ), Function.Injective η ∧
      (∀ χ : S, η χ ∈ Irr G) ∧ (∀ χ : S, coherentVal ν χ = ε • η χ) ∧
      (∀ χ : S, star (η χ) ≠ η χ) ∧ (∀ χ : S, η (starElem hSstar χ) = star (η χ)) := by
  obtain ⟨ε, hε, c, -, η, hηinj, hηIrr, hηeq, -⟩ :=
    exists_sign_and_degree_ratio_of_isCoherentWith hS hS2 hτ1 hν
  have hstarε : star ε = ε := by rcases hε with rfl | rfl <;> simp
  have hεne : ε ≠ 0 := by rcases hε with rfl | rfl <;> simp
  have main : ∀ χ : S, star (η χ) ≠ η χ ∧ η (starElem hSstar χ) = star (η χ) := by
    intro χ
    set χ' : S := starElem hSstar χ with hχ'
    have hne' : χ' ≠ χ := fun hc => hSne _ χ.2 (congrArg (fun z : S => (z : L → ℂ)) hc)
    set f : charSpanZero S := ⟨(χ : L → ℂ) - star (χ : L → ℂ),
      sub_star_mem_charSpanZero hS hSstar χ.2⟩ with hf
    have hstarf : starCharSpanZero hSstar f = -f := Subtype.ext (by simp [hf])
    have hanti : star ((τ f : G → ℂ)) = -(τ f : G → ℂ) := by
      rw [← hτstar f, hstarf, map_neg]; rfl
    have hsub := coherentVal_sub_coherentVal_starElem hS hSstar hν χ
    rw [hηeq χ, hηeq χ'] at hsub
    have key : η χ + star (η χ) = η χ' + star (η χ') := by
      have h1 : star (ε • η χ - ε • η χ') = -(ε • η χ - ε • η χ') := by
        rw [hsub]; exact hanti
      rw [star_sub, star_smul, star_smul, hstarε] at h1
      exact smul_right_injective _ hεne (by linear_combination (norm := module) h1)
    exact eq_star_of_add_star_eq_add_star (hηIrr χ) (hηIrr χ')
      (fun hc => hne' (hηinj hc)) key
  exact ⟨ε, hε, η, hηinj, hηIrr, hηeq, fun χ => (main χ).1, fun χ => (main χ).2⟩

theorem coherentVal_starElem (hS : S ⊆ Irr L) (hS2 : 2 ≤ S.ncard)
    (hSstar : ∀ χ ∈ S, star χ ∈ S) (hSne : ∀ χ ∈ S, star χ ≠ χ)
    (hτ1 : ∀ f : charSpanZero S, (τ f : G → ℂ) 1 = 0)
    (hτstar : ∀ f : charSpanZero S,
      (τ (starCharSpanZero hSstar f) : G → ℂ) = star ((τ f : G → ℂ)))
    (hν : IsCoherentWith S τ ν) (χ : S) :
    coherentVal ν (starElem hSstar χ) = star (coherentVal ν χ) := by
  obtain ⟨ε, hε, η, -, -, hηeq, -, hηstar⟩ :=
    exists_sign_nonreal_root_of_isCoherentWith hS hS2 hSstar hSne hτ1 hτstar hν
  have hstarε : star ε = ε := by rcases hε with rfl | rfl <;> simp
  rw [hηeq (starElem hSstar χ), hηeq χ, hηstar χ, star_smul, hstarε]

theorem cfInner_coherentVal_one (hS : S ⊆ Irr L) (hS2 : 2 ≤ S.ncard)
    (hSstar : ∀ χ ∈ S, star χ ∈ S) (hSne : ∀ χ ∈ S, star χ ≠ χ)
    (hτ1 : ∀ f : charSpanZero S, (τ f : G → ℂ) 1 = 0)
    (hτstar : ∀ f : charSpanZero S,
      (τ (starCharSpanZero hSstar f) : G → ℂ) = star ((τ f : G → ℂ)))
    (hν : IsCoherentWith S τ ν) (χ : S) :
    cfInner (coherentVal ν χ) (1 : G → ℂ) = 0 := by
  classical
  obtain ⟨ε, -, η, -, hηIrr, hηeq, hηnr, -⟩ :=
    exists_sign_nonreal_root_of_isCoherentWith hS hS2 hSstar hSne hτ1 hτstar hν
  have hone : η χ ≠ (1 : G → ℂ) := by
    rintro h
    exact hηnr χ (by rw [h]; simp)
  rw [hηeq χ, cfInner_smul_left, cfInner_eq_ite_of_mem_Irr (hηIrr χ) one_mem_Irr, if_neg hone,
    mul_zero]

end Main

end CFSG.FeitThompson
