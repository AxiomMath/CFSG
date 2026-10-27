module

public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6CartanRankFour
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Exc

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6CartanRankFourAux (exists_elemAbelian_three_pow)
open CFSG.HardMathSupport.Timmesfeld.FieldBonus.Orth (c3)

theorem map_c3 {K : Type} [Field K] (σ : K →+* K) :
    Matrix.SpecialLinearGroup.map σ (c3 : Matrix.SpecialLinearGroup (Fin 2) K) = c3 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [c3]


theorem exists_four_roots (τ : Tag) (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ∃ α : Fin 4 → Fin τ.rank → ℤ, (∀ i, RootOps.isRootB τ (α i) = true) ∧
      ∀ i j, i ≠ j → iform (α i) (α j) = 0 ∧ RootOps.isRootB τ (α i + α j) = false ∧
        RootOps.isRootB τ (α i - α j) = false := by
  rcases hτ with rfl | rfl | rfl | rfl
  · exact ⟨![![0, 1, 0, 0], ![0, 1, 2, 0], ![0, 1, 2, 2], ![2, 3, 4, 2]], by decide +kernel⟩
  · exact ⟨![![0, 0, 0, 1, 0, 0], ![0, 0, 1, 1, 1, 0], ![1, 0, 1, 1, 1, 1], ![1, 2, 2, 3, 2, 1]],
      by decide +kernel⟩
  · exact ⟨![![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0, 0],
      ![0, 1, 0, 0, 0, 0, 0]], by decide +kernel⟩
  · exact ⟨![![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0],
      ![0, 1, 1, 1, 0, 0, 0, 0]], by decide +kernel⟩

theorem exists_fixed_rank_four {K : Type} [Field K] [CharP K 2] (τ : Tag)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (σ : K ≃+* K) :
    ∃ E : Subgroup (adjointGroup τ K), E ≤ fixSubgroup (entrywiseAdjointAut τ σ) ∧
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
  obtain ⟨α, hroot, horth⟩ := exists_four_roots τ hτ
  have hroot' : ∀ i, IsRoot τ (α i) := fun i => RootOps.isRootB_iff.1 (hroot i)
  have hnot : ∀ {v : Fin τ.rank → ℤ}, RootOps.isRootB τ v = false → ¬ IsRoot τ v :=
    fun hv hr => by
      rw [← RootOps.isRootB_iff, hv] at hr
      exact Bool.false_ne_true hr
  let ι : Fin 4 → (SL2 K →* adjointGroup τ K) := fun i =>
    (rootSL2 τ K (α i)).codRestrict (adjointGroup τ K)
      (exceptional_Lang_root_rank_one_data τ K (α i)).2.2.2.2.1
  have hι : ∀ i, Function.Injective (ι i) := fun i A B hAB =>
    (even_Chevalley_pinned_root_SL2_maps τ K (hroot' i)).1 (congrArg Subtype.val hAB)
  have hc : ∀ i j, i ≠ j → ∀ A B, Commute (ι i A) (ι j B) := fun i j hij A B => by
    obtain ⟨h0, hp, hm⟩ := horth i j hij
    exact Subtype.ext (exceptional_Lang_strongly_orthogonal_root_rank_one_commutation τ K
      (hroot' i) (hroot' j) h0 (hnot hp) (hnot hm) _ ⟨A, rfl⟩ _ ⟨B, rfl⟩)
  obtain ⟨E, hEel, hEcard, hEN⟩ := exists_elemAbelian_three_pow ι hι hc
  refine ⟨E, hEN _ fun i => ?_, hEel, hEcard⟩
  rw [mem_fixSubgroup]
  apply Subtype.ext
  rw [coe_entrywiseAdjointAut]
  show Units.map (entrywiseHom σ.toRingHom) (rootSL2 τ K (α i) c3) = rootSL2 τ K (α i) c3
  rw [entrywise_rootSL2_of_field σ.toRingHom (α i) c3, map_c3]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Exc

end
