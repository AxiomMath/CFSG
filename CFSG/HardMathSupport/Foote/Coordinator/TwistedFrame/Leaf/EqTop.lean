module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Defs
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.CoordSpec

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false

namespace EqTopAux

theorem exists_deg_one_corootPair_neg_one (τ : Tag) :
    ∀ γ ∈ rootFinset τ, γ (iθ τ) = 0 →
      ∃ β ∈ rootFinset τ, β (iθ τ) = 1 ∧ 2 * iform β γ = -iform β β := by
  cases τ <;> decide +kernel

end EqTopAux


namespace EqTopAux

theorem weylElt_one_mem_sup (τ : Tag) (K : Type) [Field K] (j : Fin τ.rank) :
    weylElt τ K j 1 ∈ rootSubgroup τ K (Pi.single j 1) ⊔ rootSubgroup τ K (-Pi.single j 1) := by
  have hx : xUnit τ K j 1 ∈ rootSubgroup τ K (Pi.single j 1) ⊔ rootSubgroup τ K (-Pi.single j 1) := by
    rw [← pinnedX_single]
    exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, rfl⟩)
  rw [weylElt_eq_xUnit_mul]
  refine mul_mem (mul_mem hx ?_) hx
  rw [← pinnedX_neg_single]
  exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨_, rfl⟩)

theorem exists_mem_sup_conjSub (τ : Tag) (K : Type) [Field K] {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) :
    ∃ g ∈ rootSubgroup τ K β ⊔ rootSubgroup τ K (-β), ∀ δ, IsRoot τ δ →
      conjSub g (rootSubgroup τ K δ) = rootSubgroup τ K (rootReflection β • δ) := by
  obtain ⟨w, j, hwj⟩ := isRoot_iff_exists_smul_single.1 hβ
  have hT := (canonical_weyl_root_transport τ K).2.1
  refine ⟨canonicalRep (coxeterSystem τ) K w * weylElt τ K j 1 *
    (canonicalRep (coxeterSystem τ) K w)⁻¹, ?_, fun δ hδ => ?_⟩
  · have h1 : conjSub (canonicalRep (coxeterSystem τ) K w) (rootSubgroup τ K (Pi.single j 1)) =
        rootSubgroup τ K β := by
      rw [← hwj]
      exact hT w _ (isRoot_single τ j)
    have h2 : conjSub (canonicalRep (coxeterSystem τ) K w) (rootSubgroup τ K (-Pi.single j 1)) =
        rootSubgroup τ K (-β) := by
      rw [← hwj, ← smul_neg]
      exact hT w _ (isRoot_neg_single τ j)
    have hmem : canonicalRep (coxeterSystem τ) K w * weylElt τ K j 1 *
        (canonicalRep (coxeterSystem τ) K w)⁻¹ ∈
        conjSub (canonicalRep (coxeterSystem τ) K w)
          (rootSubgroup τ K (Pi.single j 1) ⊔ rootSubgroup τ K (-Pi.single j 1)) :=
      Subgroup.mem_map_of_mem _ (weylElt_one_mem_sup τ K j)
    unfold conjSub at hmem h1 h2
    rwa [Subgroup.map_sup, h1, h2] at hmem
  · have hw : IsRoot τ (w⁻¹ • δ) := IsRoot.smul hδ w⁻¹
    have e1 : conjSub (canonicalRep (coxeterSystem τ) K w)⁻¹ (rootSubgroup τ K δ) =
        rootSubgroup τ K (w⁻¹ • δ) := by
      have h := hT w (w⁻¹ • δ) hw
      rw [smul_inv_smul] at h
      calc conjSub (canonicalRep (coxeterSystem τ) K w)⁻¹ (rootSubgroup τ K δ)
          = conjSub (canonicalRep (coxeterSystem τ) K w)⁻¹
              (conjSub (canonicalRep (coxeterSystem τ) K w) (rootSubgroup τ K (w⁻¹ • δ))) := by
            rw [show conjSub (canonicalRep (coxeterSystem τ) K w) (rootSubgroup τ K (w⁻¹ • δ)) =
              rootSubgroup τ K δ from h]
        _ = rootSubgroup τ K (w⁻¹ • δ) := by
            rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
    have e2 : conjSub (weylElt τ K j 1) (rootSubgroup τ K (w⁻¹ • δ)) =
        rootSubgroup τ K (reflect τ j (w⁻¹ • δ)) :=
      map_conj_weylElt_rootSubgroup K j hw
    have e3 : conjSub (canonicalRep (coxeterSystem τ) K w)
        (rootSubgroup τ K (reflect τ j (w⁻¹ • δ))) =
        rootSubgroup τ K (w • reflect τ j (w⁻¹ • δ)) :=
      hT w _ (IsRoot.reflect j hw)
    rw [conjSub_mul, conjSub_mul, e1, e2, e3, rootReflection_eq_conj hwj, mul_smul, mul_smul,
      simple_smul]

theorem degθ_rootReflection_highRoot (τ : Tag) (α : Fin τ.rank → ℤ) :
    (rootReflection (highRoot τ) • α) (iθ τ) = -(α (iθ τ)) := by
  have hθ := isRoot_highRoot τ
  have h := corootPair_mul hθ α
  rw [iform_highRoot_apply, iform_highRoot_apply, CoordAux.highRoot_degree] at h
  have hc : corootPair (highRoot τ) α = α (iθ τ) := by
    have h2 : (corootPair (highRoot τ) α - α (iθ τ)) * (2 * cθ τ) = 0 := by
      linear_combination h
    rcases mul_eq_zero.1 h2 with h3 | h3
    · linarith
    · exact absurd h3 (mul_ne_zero two_ne_zero (cθ_ne_zero τ))
  rw [rootReflection_smul hθ, hc]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, CoordAux.highRoot_degree]
  ring

theorem rootSubgroup_le_Qθ_of_one_le (τ : Tag) (K : Type) [Field K] {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (h : 1 ≤ γ (iθ τ)) : rootSubgroup τ K γ ≤ Qθ τ K := by
  have hpos : 0 < height γ := by
    rcases IsRoot.height_pos_or_neg hγ with hp | hn
    · exact hp
    · have := (IsRoot.height_neg_iff hγ).1 hn (iθ τ)
      omega
  have hmem : γ ∈ parabolicRadicalRoots τ (Jθ τ) :=
    mem_parabolicRadicalRoots_of_degree hγ hpos (by rw [CoordAux.parabolicDegree_Jθ]; omega)
  exact le_iSup₂_of_le γ hmem le_rfl

theorem conjSub_le_of_mem_of_le' {G : Type*} [Group G] {A H : Subgroup G} {g : G} (hg : g ∈ H)
    (hA : A ≤ H) : conjSub g A ≤ H := by
  rintro _ ⟨a, ha, rfl⟩
  exact mul_mem (mul_mem hg (hA ha)) (inv_mem hg)

end EqTopAux

theorem eq_top_of_Qθ_Uneg_le_of_any (τ : Tag) (K : Type) [Field K]
    {H : Subgroup (ModGL τ K)} (hH : H ≤ adjointGroup τ K) (hQ : Qθ τ K ≤ H)
    (hU : Heis.Uneg τ K ≤ H) : H = adjointGroup τ K := by
  have hpos : ∀ γ, IsRoot τ γ → 1 ≤ γ (iθ τ) → rootSubgroup τ K γ ≤ H := fun γ hγ h =>
    (EqTopAux.rootSubgroup_le_Qθ_of_one_le τ K hγ h).trans hQ
  have hθ := isRoot_highRoot τ
  obtain ⟨gθ, hgθ, hconjθ⟩ := EqTopAux.exists_mem_sup_conjSub τ K hθ
  have hgθH : gθ ∈ H := sup_le (hpos _ hθ (by rw [CoordAux.highRoot_degree]; omega)) hU hgθ
  have hneg : ∀ α, IsRoot τ α → α (iθ τ) ≤ -1 → rootSubgroup τ K α ≤ H := by
    intro α hα hd
    have hγ : IsRoot τ (rootReflection (highRoot τ) • α) := IsRoot.smul hα _
    have hγd := EqTopAux.degθ_rootReflection_highRoot τ α
    have hinv : rootReflection (highRoot τ) • rootReflection (highRoot τ) • α = α := by
      rw [← mul_smul, rootReflection_mul_self hθ, one_smul]
    have h := hconjθ _ hγ
    rw [hinv] at h
    rw [← h]
    exact EqTopAux.conjSub_le_of_mem_of_le' hgθH (hpos _ hγ (by omega))
  refine le_antisymm hH ?_
  rw [adjointGroup_eq_rootSpan]
  refine iSup₂_le fun α hα => ?_
  have hα : IsRoot τ α := hα
  rcases lt_trichotomy (α (iθ τ)) 0 with hd | hd | hd
  · exact hneg α hα (by omega)
  ·
    obtain ⟨β, hβmem, hβd, hβc⟩ := EqTopAux.exists_deg_one_corootPair_neg_one τ α
      (mem_rootFinset.2 hα) hd
    have hβ : IsRoot τ β := mem_rootFinset.1 hβmem
    have hcp : corootPair β α = -1 := by
      have h := corootPair_mul hβ α
      have hpos' := iform_self_pos_of_isRoot hβ
      have h2 : (corootPair β α + 1) * iform β β = 0 := by linear_combination h + hβc
      rcases mul_eq_zero.1 h2 with h3 | h3
      · linarith
      · exact absurd h3 hpos'.ne'
    obtain ⟨g, hg, hconj⟩ := EqTopAux.exists_mem_sup_conjSub τ K hβ
    have hgH : g ∈ H := sup_le (hpos β hβ (by omega))
      (hneg (-β) (IsRoot.neg hβ) (by rw [Pi.neg_apply]; omega)) hg
    have hδ : IsRoot τ (rootReflection β • α) := IsRoot.smul hα _
    have hδd : (rootReflection β • α) (iθ τ) = 1 := by
      rw [rootReflection_smul hβ, hcp]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hd, hβd]
      ring
    have hinv : rootReflection β • rootReflection β • α = α := by
      rw [← mul_smul, rootReflection_mul_self hβ, one_smul]
    have h := hconj _ hδ
    rw [hinv] at h
    rw [← h]
    exact EqTopAux.conjSub_le_of_mem_of_le' hgH (hpos _ hδ (by omega))
  · exact hpos α hα (by omega)

theorem eq_top_of_Qθ_Uneg_le (τ : Tag) (K : Type) [Field K] (h3 : 3 ≤ Nat.card K)
    {H : Subgroup (ModGL τ K)} (hH : H ≤ adjointGroup τ K) (hQ : Qθ τ K ≤ H)
    (hU : Heis.Uneg τ K ≤ H) : H = adjointGroup τ K := by
  have _ := h3
  exact eq_top_of_Qθ_Uneg_le_of_any τ K hH hQ hU

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
