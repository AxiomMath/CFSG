module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.CTP.SeitzOrthCount

public section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.CTP

structure IsOrthogonalCover {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) {G : Type} [Group G] (π : elementaryGroup Q →* G) : Prop where
  nondegenerate : (polarBilin Q).Nondegenerate
  surjective : Function.Surjective π
  ker_scalar : ∀ g ∈ π.ker, (g : V ≃ₗ[K] V) ∈ scalars K V

theorem exists_orthCover {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hnd : (polarBilin Q).Nondegenerate) {G : Type} [Group G]
    (e : G ≃* StatedProj (StatedOmega Q₀)) :
    ∃ π : elementaryGroup Q →* G, IsOrthogonalCover Q π := by
  let ψ : StatedOmega Q₀ ≃* elementaryGroup Q := statedOmegaEquiv hQ hE
  let π₀ : elementaryGroup Q →* StatedProj (StatedOmega Q₀) :=
    (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf (StatedOmega Q₀))).comp
      ψ.symm.toMonoidHom
  refine ⟨e.symm.toMonoidHom.comp π₀, hnd, ?_, ?_⟩
  · exact e.symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp ψ.symm.surjective)
  · intro g hg
    have h1 : π₀ g = 1 := by
      have h : e.symm (π₀ g) = 1 := hg
      exact e.symm.injective (h.trans (map_one e.symm).symm)
    have h2 : QuotientGroup.mk (ψ.symm g) = 1 := h1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, mem_statedScalars_iff] at h2
    have h3 := coe_statedOmegaEquiv hQ hE (ψ.symm g)
    have h5 : statedOmegaEquiv hQ hE (ψ.symm g) = g := ψ.apply_symm_apply g
    rw [h5] at h3
    rw [h3]
    exact h2

theorem orthCover_odd {K : Type} [Field K] [Finite K] {r : ℕ} (hr3 : 3 ≤ r) (h2 : (2 : K) ≠ 0)
    {G : Type} [Group G] (e : G ≃* StatedProj (StatedOmega (StatedQuadOdd r K))) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
      (Q : QuadraticForm K V) (π : elementaryGroup Q →* G), IsOrthogonalCover Q π := by
  have hreg := regular_quadOdd (K := K) h2 hr3
  obtain ⟨π, hπ⟩ := exists_orthCover (coe_quadOdd r K) (commutator_orthogonalGroup_quadOdd h2 hr3)
    hreg.1 e
  exact ⟨_, inferInstance, inferInstance, inferInstance, quadOdd r K, π, hπ⟩

theorem orthCover_plus {K : Type} [Field K] [Finite K] {r : ℕ} (hr3 : 3 ≤ r) {G : Type} [Group G]
    (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus r K))) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
      (Q : QuadraticForm K V) (π : elementaryGroup Q →* G), IsOrthogonalCover Q π := by
  have hreg := regular_quadPlus (K := K) (n := r) hr3
  obtain ⟨π, hπ⟩ := exists_orthCover (coe_quadPlus r K) (commutator_orthogonalGroup_quadPlus hr3)
    hreg.1 e
  exact ⟨_, inferInstance, inferInstance, inferInstance, quadPlus r K, π, hπ⟩

theorem orthCover_minus {K : Type} [Field K] [Finite K] {r : ℕ} {b c : K} (hr : 4 ≤ r)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {G : Type} [Group G]
    (e : G ≃* StatedProj (StatedOmega (StatedQuadMinus r K b c))) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
      (Q : QuadraticForm K V) (π : elementaryGroup Q →* G), IsOrthogonalCover Q π := by
  have hreg := regular_quadMinus (K := K) (n := r) hr hirr
  obtain ⟨π, hπ⟩ := exists_orthCover (coe_quadMinus r K b c)
    (commutator_orthogonalGroup_quadMinus hr hirr) hreg.1 e
  exact ⟨_, inferInstance, inferInstance, inferInstance, quadMinus r K b c, π, hπ⟩

end CFSG.LieType.SeitzGeneration
