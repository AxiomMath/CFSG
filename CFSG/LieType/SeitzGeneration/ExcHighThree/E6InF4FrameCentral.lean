module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6InF4Frame

public section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree


open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.E6
  CFSG.HardMathSupport.Lang.AnisoE6 CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

abbrev e6Node0 : Fin TwClass.e6Six.tag.rank := ⟨0, by decide⟩

abbrev e6Node2 : Fin TwClass.e6Six.tag.rank := ⟨2, by decide⟩

abbrev e6Node3 : Fin TwClass.e6Six.tag.rank := ⟨3, by decide⟩

theorem e6_col0 : ∀ i : Fin 6, Tag.E6.symmetrizedCartan i 0 = ![2, 0, -1, 0, 0, 0] i := by
  decide

theorem e6_sum_col0 (β : Fin 6 → ℤ) :
    ∑ i : Fin 6, β i * Tag.E6.symmetrizedCartan i 0 = 2 * β 0 - β 2 := by
  simp only [e6_col0]
  simp [Fin.sum_univ_six]
  ring

theorem e6_col2 : ∀ i : Fin 6, Tag.E6.symmetrizedCartan i 2 = ![-1, 0, 2, -1, 0, 0] i := by
  decide

theorem e6_sum_col2 (β : Fin 6 → ℤ) :
    ∑ i : Fin 6, β i * Tag.E6.symmetrizedCartan i 2 = -β 0 + 2 * β 2 - β 3 := by
  simp only [e6_col2]
  simp [Fin.sum_univ_six]
  ring

theorem e6_coeff_three (β : Fin 6 → ℤ)
    (h0 : ∑ i : Fin 6, β i * Tag.E6.symmetrizedCartan i 0 = 0)
    (h2 : ∑ i : Fin 6, β i * Tag.E6.symmetrizedCartan i 2 = 0) : β 3 = 3 * β 0 := by
  rw [e6_sum_col0] at h0
  rw [e6_sum_col2] at h2
  omega

theorem e6_iform_single_eq_sum (x : Fin TwClass.e6Six.tag.rank → ℤ) (j : Fin TwClass.e6Six.tag.rank) :
    CFSG.LieType.Steinberg.Adjoint.iform x (Pi.single j 1) =
      ∑ i, x i * TwClass.e6Six.tag.symmetrizedCartan i j := by
  simp [CFSG.LieType.Steinberg.Adjoint.iform, Pi.single_apply]

theorem e6FrameCentral_holds : E6FrameCentral := by
  intro K _ _ h3 D₆ ω₆ hω₆ z₆ hzbc
  set a : Fin TwClass.e6Six.tag.rank → D₆.Lˣ := Pi.mulSingle e6Node3 ω₆ with ha
  have hchar : ∀ α : Fin TwClass.e6Six.tag.rank → ℤ, rootChar a α = ω₆ ^ (α e6Node3) := by
    intro α
    unfold rootChar
    rw [Finset.prod_eq_single e6Node3]
    · simp [ha]
    · intro j _ hj
      simp [ha, Pi.mulSingle_eq_of_ne hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hS₂ : ∀ α ∈ TwClass.e6Six.S₂, IsRoot TwClass.e6Six.tag α ∧ rootChar a α = 1 := by
    rintro α ⟨hr, hsupp⟩
    refine ⟨hr, ?_⟩
    rw [hchar, hsupp e6Node3 (by decide), zpow_zero]
  have hmemS₂ : ∀ j : Fin TwClass.e6Six.tag.rank, (j = e6Node0 ∨ j = e6Node2) →
      (Pi.single j 1 : Fin TwClass.e6Six.tag.rank → ℤ) ∈ TwClass.e6Six.S₂ := by
    rintro j (rfl | rfl)
    · exact ⟨isRoot_single _ _, by decide⟩
    · exact ⟨isRoot_single _ _, by decide⟩
  have hS₁ : ∀ β ∈ TwClass.e6Six.S₁, IsRoot TwClass.e6Six.tag β ∧ rootChar a β = 1 := by
    rintro β ⟨hr, horth⟩
    refine ⟨hr, ?_⟩
    have h0 := horth _ (hmemS₂ e6Node0 (Or.inl rfl))
    have h2 := horth _ (hmemS₂ e6Node2 (Or.inr rfl))
    rw [e6_iform_single_eq_sum] at h0 h2
    have key : β e6Node3 = 3 * β e6Node0 :=
      e6_coeff_three β h0 h2
    have hdvd : ((3 : ℕ) : ℤ) ∣ β e6Node3 := ⟨β e6Node0, by rw [key]; push_cast; ring⟩
    rw [hchar, ← orderOf_dvd_iff_zpow_eq_one, hω₆]
    exact_mod_cast hdvd
  have hcomm : ∀ S : Set (Fin TwClass.e6Six.tag.rank → ℤ),
      (∀ α ∈ S, IsRoot TwClass.e6Six.tag α ∧ rootChar a α = 1) →
      D₆.frame S ≤ Subgroup.centralizer ({z₆} : Set (ModGL TwClass.e6Six.tag K)) := by
    intro S hS' x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxc := rootSpan_le_centralizer_rootDiagUnit (K := D₆.L) a hS' hx.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hxc
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxc
    apply baseChangeGL_injective (algebraMap K D₆.L)
    rw [map_mul, map_mul, hzbc]
    calc baseChangeGL (algebraMap K D₆.L) x * (D₆.g * rootDiagUnit TwClass.e6Six.tag a * D₆.g⁻¹)
        = D₆.g * ((D₆.g⁻¹ * baseChangeGL (algebraMap K D₆.L) x * D₆.g⁻¹⁻¹) *
            rootDiagUnit TwClass.e6Six.tag a) * D₆.g⁻¹ := by group
      _ = D₆.g * (rootDiagUnit TwClass.e6Six.tag a * (D₆.g⁻¹ * baseChangeGL (algebraMap K D₆.L) x *
            D₆.g⁻¹⁻¹)) * D₆.g⁻¹ := by rw [hxc]
      _ = (D₆.g * rootDiagUnit TwClass.e6Six.tag a * D₆.g⁻¹) * baseChangeGL (algebraMap K D₆.L) x := by
          group
  exact sup_le (hcomm _ hS₁) (hcomm _ hS₂)

theorem twistedFrameTwo_of_central (hNR : LangPlaneKillsRoot Tag.F4) (hT : E6TwistedTransport)
    (hTwo : E6FrameAtTwo) : TwistedFrameTwo :=
  twistedFrameTwo_of hNR hT e6FrameCentral_holds hTwo

end CFSG.LieType.SeitzGeneration.ExcHighThree

end
