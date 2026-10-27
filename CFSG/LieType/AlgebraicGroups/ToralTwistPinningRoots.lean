module

public import CFSG.LieType.Chevalley.SignKernelStabilizer
public import CFSG.LieType.Chevalley.OrthogonalUnionBruhat
public import CFSG.LieType.Chevalley.LangRootRankOneTorus

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

section Roots

variable {τ : Tag} {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem unionSimpleRoots_univ_eq :
    unionSimpleRoots χ Set.univ = (simpleRoots (kernelRoots χ) : Set (Fin τ.rank → ℤ)) := by
  ext β
  constructor
  · rintro ⟨i, -, hβi⟩
    obtain ⟨hβS, rfl⟩ := simpleRoots_subset hβi
    exact (mem_simpleRoots_kernelRoots_iff hβS).2 hβi
  · intro hβ
    have hβS : β ∈ kernelRoots χ := simpleRoots_subset hβ
    exact ⟨_, Set.mem_univ _, (mem_simpleRoots_kernelRoots_iff hβS).1 hβ⟩

theorem smul_mem_posRoots_kernelRoots
    {ω : WeylGroup τ} (hω : ω ∈ kernelPosStabilizer χ)
    {α : Fin τ.rank → ℤ} (hα : α ∈ posRoots (kernelRoots χ)) :
    ω • α ∈ posRoots (kernelRoots χ) := by
  rw [← hω.2]
  exact ⟨α, hα, rfl⟩

theorem smul_mem_simpleRoots_kernelRoots
    {ω : WeylGroup τ} (hω : ω ∈ kernelPosStabilizer χ)
    {β : Fin τ.rank → ℤ} (hβ : β ∈ simpleRoots (kernelRoots χ)) :
    ω • β ∈ simpleRoots (kernelRoots χ) := by
  obtain ⟨hβr, hβpos, hns⟩ := mem_simpleRoots.1 hβ
  have hω' : ω⁻¹ ∈ kernelPosStabilizer χ := inv_mem hω
  refine mem_simpleRoots.2 ⟨IsRoot.smul hβr ω, smul_mem_posRoots_kernelRoots hω hβpos,
    fun γ hγ δ hδ e => ?_⟩
  refine hns (ω⁻¹ • γ) (smul_mem_posRoots_kernelRoots hω' hγ) (ω⁻¹ • δ)
    (smul_mem_posRoots_kernelRoots hω' hδ) ?_
  rw [← smul_add, ← e, inv_smul_smul]

theorem iform_nonpos_of_mem_simpleRoots_kernelRoots
    {β γ : Fin τ.rank → ℤ}
    (hβ : β ∈ simpleRoots (kernelRoots χ)) (hγ : γ ∈ simpleRoots (kernelRoots χ)) (hne : β ≠ γ) :
    iform β γ ≤ 0 := by
  have hβS : β ∈ kernelRoots χ := simpleRoots_subset hβ
  have hγS : γ ∈ kernelRoots χ := simpleRoots_subset hγ
  by_cases hij : (⟦⟨β, hβS⟩⟧ : KernelComponent χ) = ⟦⟨γ, hγS⟩⟧
  · have hβ' := (mem_simpleRoots_kernelRoots_iff hβS).1 hβ
    have hγ' := (mem_simpleRoots_kernelRoots_iff hγS).1 hγ
    rw [hij] at hβ'
    exact iform_simpleRoots_nonpos (isRootComponent_componentRoots _) hβ' hγ' hne
  · exact (iform_eq_zero_of_mk_ne hij).le

theorem linearIndependent_simpleRoots_kernelRoots
    {s : ℕ} {ν : Fin s → Fin τ.rank → ℤ}
    (hν : Function.Injective ν) (hνΔ : ∀ i, ν i ∈ simpleRoots (kernelRoots χ)) :
    LinearIndependent ℚ fun i j => (ν i j : ℚ) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  set Δ := Finset.univ.image ν with hΔ
  set c : (Fin τ.rank → ℤ) → ℝ := Function.extend ν (fun i => (g i : ℝ)) 0 with hc
  have hcν : ∀ i, c (ν i) = g i := fun i => hν.extend_apply _ _ i
  have hΔS : ∀ β ∈ Δ, β ∈ simpleRoots (kernelRoots χ) := by
    intro β hβ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hβ
    exact hνΔ i
  have hsum : ∑ β ∈ Δ, c β • toReal β = 0 := by
    rw [Finset.sum_image fun i _ j _ h => hν h]
    ext j
    have h := congrFun hg j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hcν, toReal]
    exact_mod_cast h
  have h0 := eq_zero_of_sum_smul_toReal_eq_zero
    (fun β hβ => simpleRoots_height_pos (hΔS β hβ))
    (fun β hβ γ hγ hne => iform_nonpos_of_mem_simpleRoots_kernelRoots (hΔS β hβ) (hΔS γ hγ) hne)
    hsum (ν i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [hcν] at h0
  exact_mod_cast h0

end Roots

section Span

variable {τ : Tag} {K : Type} [Field K] {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem exists_mem_iSup_rootRankOneGroup_mapsRootLines
    (i : KernelComponent χ) {w : WeylGroup τ}
    (hw : w ∈ componentWeylGroup (componentRoots χ i)) :
    ∃ n ∈ ⨆ β ∈ (simpleRoots (kernelRoots χ) : Set (Fin τ.rank → ℤ)), rootRankOneGroup τ K β,
      n ∈ monomialSubgroup τ K ∧ MapsRootLines n w := by
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨β, hβ, rfl⟩ := hw
    have hβi : β ∈ simpleRoots (componentRoots χ i) := hβ
    obtain ⟨hβk, hi⟩ := simpleRoots_subset hβi
    have hβS : β ∈ simpleRoots (kernelRoots χ) := by
      rw [mem_simpleRoots_kernelRoots_iff hβk, hi]
      exact hβi
    obtain ⟨-, -, hn, -⟩ := exceptional_Lang_root_rank_one_torus_transport τ K hβk.1
    obtain ⟨hnN, hπ⟩ := hn 1
    refine ⟨rootWeylSL2 τ K β 1, ?_, hnN, ?_⟩
    · exact le_iSup₂_of_le (f := fun β (_ : β ∈ (simpleRoots (kernelRoots χ) :
        Set (Fin τ.rank → ℤ))) => rootRankOneGroup τ K β) β hβS le_rfl ⟨nSL 1, rfl⟩
    · have h := mapsRootLines_weylQuotientHom (R := K) ⟨_, hnN⟩
      rwa [hπ] at h
  | one => exact ⟨1, one_mem _, one_mem _, mapsRootLines_one⟩
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn, hnN, hnx⟩ := hx
    obtain ⟨n', hn', hn'N, hn'y⟩ := hy
    exact ⟨n * n', mul_mem hn hn', mul_mem hnN hn'N, hnx.mul hn'y⟩
  | inv x _ hx =>
    obtain ⟨n, hn, hnN, hnx⟩ := hx
    exact ⟨n⁻¹, inv_mem hn, inv_mem hnN, hnx.inv⟩

theorem rootSubgroup_le_iSup_rootRankOneGroup
    {α : Fin τ.rank → ℤ} (hα : α ∈ kernelRoots χ) :
    rootSubgroup τ K α ≤
      ⨆ β ∈ (simpleRoots (kernelRoots χ) : Set (Fin τ.rank → ℤ)), rootRankOneGroup τ K β := by
  set i : KernelComponent χ := ⟦⟨α, hα⟩⟧
  have hαi : α ∈ componentRoots χ i := ⟨hα, rfl⟩
  obtain ⟨w, hw, β₀, hβ₀, rfl⟩ := exists_smul_simpleRoot (isRootComponent_componentRoots i) hαi
  obtain ⟨n, hn, hnN, hnw⟩ := exists_mem_iSup_rootRankOneGroup_mapsRootLines (K := K) i hw
  have hβ₀r : IsRoot τ β₀ := simpleRoots_isRoot hβ₀
  obtain ⟨hβ₀k, hi⟩ := simpleRoots_subset hβ₀
  have hβ₀S : β₀ ∈ simpleRoots (kernelRoots χ) := by
    rw [mem_simpleRoots_kernelRoots_iff hβ₀k, hi]
    exact hβ₀
  have hL : rootSubgroup τ K β₀ ≤
      ⨆ β ∈ (simpleRoots (kernelRoots χ) : Set (Fin τ.rank → ℤ)), rootRankOneGroup τ K β := by
    refine le_trans ?_ (le_iSup₂_of_le (f := fun β (_ : β ∈ (simpleRoots (kernelRoots χ) :
      Set (Fin τ.rank → ℤ))) => rootRankOneGroup τ K β) β₀ hβ₀S le_rfl)
    rw [(exceptional_Lang_root_rank_one_torus_transport τ K hβ₀r).1]
    exact le_sup_left
  intro y hy
  have h1 := conj_mem_rootSpan_of_mapsRootLines (inv_mem hnN) hnw.inv (S := {w • β₀})
    (by rintro _ rfl; exact IsRoot.smul hβ₀r w) (by rwa [rootSpan_singleton])
  rw [Set.image_singleton, inv_smul_smul, inv_inv, rootSpan_singleton] at h1
  have h2 := mul_mem (mul_mem hn (hL h1)) (inv_mem hn)
  simpa [mul_assoc] using h2

theorem rootSpan_kernelRoots_eq_iSup_rootRankOneGroup :
    rootSpan τ K (kernelRoots χ) =
      ⨆ β ∈ (simpleRoots (kernelRoots χ) : Set (Fin τ.rank → ℤ)), rootRankOneGroup τ K β := by
  refine le_antisymm (iSup₂_le fun α hα => rootSubgroup_le_iSup_rootRankOneGroup hα)
    (iSup₂_le fun β hβ => ?_)
  have hβS : β ∈ kernelRoots χ := simpleRoots_subset hβ
  rw [(exceptional_Lang_root_rank_one_torus_transport τ K hβS.1).1]
  exact sup_le (le_iSup₂_of_le β hβS le_rfl)
    (le_iSup₂_of_le (-β) ⟨IsRoot.neg hβS.1, chi_neg hβS.2⟩ le_rfl)

end Span

end CFSG.LieType.AlgebraicGroups
