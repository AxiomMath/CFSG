module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcIdx
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicRootCenter

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem eq_zero_of_sum_smul_toReal_unionSimpleRoots
    {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {J : Set (KernelComponent χ)}
    {Δ : Finset (Fin τ.rank → ℤ)}
    (hΔ : (Δ : Set (Fin τ.rank → ℤ)) = unionSimpleRoots χ J)
    {c : Δ → ℝ} (hc : ∑ β : Δ, c β • toReal (β : Fin τ.rank → ℤ) = 0) :
    ∀ β : Δ, c β = 0 := by
  classical
  have hmem : ∀ {β : Fin τ.rank → ℤ}, β ∈ Δ → β ∈ unionSimpleRoots χ J := by
    intro β hβ
    rw [← hΔ]
    exact hβ
  have hht : ∀ β ∈ Δ, 0 < height β := by
    intro β hβ
    obtain ⟨i, -, hβi⟩ := hmem hβ
    exact simpleRoots_height_pos hβi
  have hle : ∀ β ∈ Δ, ∀ γ ∈ Δ, β ≠ γ → iform β γ ≤ 0 := by
    intro β hβ γ hγ hne
    obtain ⟨i, -, hβi⟩ := hmem hβ
    obtain ⟨j, -, hγj⟩ := hmem hγ
    by_cases hij : i = j
    · subst hij
      exact iform_simpleRoots_nonpos (isRootComponent_componentRoots i) hβi hγj hne
    · exact le_of_eq (iform_eq_zero_of_mem_componentRoots hij (simpleRoots_subset hβi)
        (simpleRoots_subset hγj))
  have hc' : ∑ β ∈ Δ, (fun β => if h : β ∈ Δ then c ⟨β, h⟩ else 0) β • toReal β = 0 := by
    rw [← Finset.sum_attach]
    simpa using hc
  intro β
  have h := eq_zero_of_sum_smul_toReal_eq_zero hht hle hc' β β.2
  simpa using h

theorem closure_corootVec_unionRoots_eq
    {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {J : Set (KernelComponent χ)} :
    AddSubgroup.closure (corootVec '' unionRoots χ J) =
      AddSubgroup.closure (corootVec '' unionSimpleRoots χ J) := by
  classical
  apply le_antisymm
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, rfl⟩
    rw [← Submodule.span_int_eq_addSubgroupClosure]
    change corootVec α ∈ Submodule.span ℤ (corootVec '' unionSimpleRoots χ J)
    obtain ⟨i, hi, hαi⟩ := mem_unionRoots_iff.1 hα
    obtain ⟨c, hc⟩ := CFSG.StandardType.LayerCycRoot.exists_corootPair_eq_sum
      (isRootComponent_componentRoots i) hαi
    have hvec : corootVec α =
        ∑ β : simpleRoots (componentRoots χ i), c β • corootVec (β : Fin τ.rank → ℤ) := by
      funext k
      have h := hc (Pi.single k 1)
      simpa [corootVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
    have hsum : (∑ β : simpleRoots (componentRoots χ i),
          c β • corootVec (β : Fin τ.rank → ℤ)) =
        ∑ β ∈ simpleRoots (componentRoots χ i),
          (fun β => if h : β ∈ simpleRoots (componentRoots χ i) then c ⟨β, h⟩ else 0) β
            • corootVec β := by
      conv_rhs => rw [← Finset.sum_attach]
      simp
    rw [hvec, hsum]
    refine Submodule.sum_mem _ fun β hβ => ?_
    refine Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_image_of_mem corootVec ?_))
    exact ⟨i, hi, hβ⟩
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨β, hβ, rfl⟩
    exact AddSubgroup.subset_closure
      (Set.mem_image_of_mem corootVec (mem_unionRoots_of_mem_unionSimpleRoots hβ))

theorem linearIndependent_corootVec_unionSimpleRoots
    {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {J : Set (KernelComponent χ)}
    (Δ : Finset (Fin τ.rank → ℤ)) (hΔ : (Δ : Set (Fin τ.rank → ℤ)) = unionSimpleRoots χ J) :
    LinearIndependent ℤ fun β : Δ => corootVec (β : Fin τ.rank → ℤ) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc β
  set F : Δ → ℝ := fun β => (iform (β : Fin τ.rank → ℤ) (β : Fin τ.rank → ℤ) : ℝ) with hFdef
  have hFpos : ∀ β : Δ, 0 < F β := by
    intro β
    have hβ : IsRoot τ (β : Fin τ.rank → ℤ) :=
      isRoot_of_mem_unionSimpleRoots (by rw [← hΔ]; exact β.2)
    change (0 : ℝ) < ((iform (β : Fin τ.rank → ℤ) (β : Fin τ.rank → ℤ) : ℤ) : ℝ)
    exact_mod_cast iform_self_pos_of_isRoot hβ
  have hFne : ∀ β : Δ, F β ≠ 0 := fun β => (hFpos β).ne'
  set d : Δ → ℝ := fun β => 2 * (c β : ℝ) / F β with hddef
  set v : Fin τ.rank → ℝ := ∑ β : Δ, d β • toReal (β : Fin τ.rank → ℤ) with hvdef
  have hc_coord : ∀ j : Fin τ.rank,
      ∑ β : Δ, (c β : ℝ) * (corootVec (β : Fin τ.rank → ℤ) j : ℝ) = 0 := by
    intro j
    have h := congrFun hc j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    exact_mod_cast h
  have hcor : ∀ (β : Δ) (j : Fin τ.rank),
      (corootVec (β : Fin τ.rank → ℤ) j : ℝ) * F β =
        2 * (iform (β : Fin τ.rank → ℤ) (Pi.single j 1) : ℝ) := by
    intro β j
    have hβ : IsRoot τ (β : Fin τ.rank → ℤ) :=
      isRoot_of_mem_unionSimpleRoots (by rw [← hΔ]; exact β.2)
    have h := corootPair_mul hβ (Pi.single j 1)
    change (corootPair (β : Fin τ.rank → ℤ) (Pi.single j 1) : ℝ) *
      ((iform (β : Fin τ.rank → ℤ) (β : Fin τ.rank → ℤ) : ℤ) : ℝ) =
        2 * (iform (β : Fin τ.rank → ℤ) (Pi.single j 1) : ℝ)
    exact_mod_cast h
  have hsingle : ∀ j : Fin τ.rank, rform v (toReal (Pi.single j 1)) = 0 := by
    intro j
    have hv : v = ∑ β : Δ, d β • toReal (β : Fin τ.rank → ℤ) := hvdef
    rw [hv, rform_sum_left]
    rw [show (∑ β : Δ, rform (d β • toReal (β : Fin τ.rank → ℤ))
          (toReal (Pi.single j 1)))
        = ∑ β : Δ, (c β : ℝ) * (corootVec (β : Fin τ.rank → ℤ) j : ℝ) from ?_]
    · exact hc_coord j
    · refine Finset.sum_congr rfl fun β _ => ?_
      rw [rform_smul_left, rform_toReal]
      show d β * (iform (β : Fin τ.rank → ℤ) (Pi.single j 1) : ℝ) =
        (c β : ℝ) * (corootVec (β : Fin τ.rank → ℤ) j : ℝ)
      rw [hddef]
      simp only
      have hF := hFne β
      have hrel := hcor β j
      rw [div_mul_eq_mul_div, div_eq_iff hF]
      rw [show (c β : ℝ) * (corootVec (β : Fin τ.rank → ℤ) j : ℝ) * F β =
          (c β : ℝ) * ((corootVec (β : Fin τ.rank → ℤ) j : ℝ) * F β) by ring, hrel]
      ring
  have hv0 : v = 0 := by
    have hvv : rform v v = 0 := by
      have hdecomp : v = ∑ i : Fin τ.rank, v i • toReal (Pi.single i 1 : Fin τ.rank → ℤ) := by
        funext j
        simp [Finset.sum_apply, toReal, Pi.single_apply]
      have h1 : rform v v = rform v (∑ i : Fin τ.rank,
          v i • toReal (Pi.single i 1 : Fin τ.rank → ℤ)) :=
        congrArg (fun w => rform v w) hdecomp
      rw [h1, rform_sum_right]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [rform_smul_right, hsingle i, mul_zero]
    by_contra h
    exact (ne_of_gt (rform_self_pos h)) hvv
  have hsub : ∑ β : Δ, d β • toReal (β : Fin τ.rank → ℤ) = 0 := by
    rw [← hvdef]
    exact hv0
  have hd : d β = 0 := eq_zero_of_sum_smul_toReal_unionSimpleRoots hΔ hsub β
  have hcβ : (c β : ℝ) = 0 := by
    have hF := hFne β
    rw [hddef] at hd
    simp only at hd
    field_simp [hF] at hd
    linarith
  exact_mod_cast hcβ

end CFSG.HardMathSupport.C14Idx
