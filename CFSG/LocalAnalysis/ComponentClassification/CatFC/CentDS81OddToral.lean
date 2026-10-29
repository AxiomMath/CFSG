module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81LieAPI

public noncomputable section

namespace CFSG.ComponentClassification.CatFC.DS81

open Subgroup CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

theorem isSolvable_pi_of_finite {ι : Type*} [Finite ι] {H : ι → Type*} [∀ i, Group (H i)]
    [∀ i, Group.IsSolvable (H i)] : Group.IsSolvable (∀ i, H i) := by
  classical
  haveI := Fintype.ofFinite ι
  choose n hn using fun i => (inferInstance : Group.IsSolvable (H i)).solvable
  refine ⟨⟨Finset.univ.sup n, ?_⟩⟩
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  funext i
  have h1 : (Pi.evalMonoidHom H i) g ∈ derivedSeries (H i) (Finset.univ.sup n) := by
    have := map_derivedSeries_le_derivedSeries (Pi.evalMonoidHom H i) (Finset.univ.sup n)
    exact this ⟨g, hg, rfl⟩
  have h2 : derivedSeries (H i) (Finset.univ.sup n) ≤ derivedSeries (H i) (n i) :=
    derivedSeries_antitone (H i) (Finset.le_sup (Finset.mem_univ i))
  have h3 := h2 h1
  rw [hn i, Subgroup.mem_bot] at h3
  exact h3


theorem hasCompOrSolv_toralCentralizer (τ : Tag) {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) (b : Fin τ.rank → Kˣ) (hb : ∀ i, b i = 1 ∨ b i = -1) :
    HasCompOrSolv (toralCentralizer τ K b) := by
  classical
  set χ := maskChar (signTupleBits b) with hχ
  have hker : rootCharKernel b = kernelRoots χ := rootCharKernel_eq_kernelRoots hK hb
  obtain ⟨hSle, hSnorm, hquot, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction τ K hK b hb
  obtain ⟨hfin, hfinc, -, hnormS, ⟨μ, -, hμs, -⟩, -⟩ :=
    root_character_kernel_orthogonal_central_product τ K χ
  haveI := hfinc
  haveI := Fintype.ofFinite (KernelComponent χ)
  by_cases hall : ∀ i : KernelComponent χ, Group.IsSolvable (componentRootSpan K χ i)
  ·
    left
    haveI : ∀ i, Group.IsSolvable (componentRootSpan K χ i) := hall
    haveI : Group.IsSolvable (∀ i : KernelComponent χ, componentRootSpan K χ i) :=
      isSolvable_pi_of_finite
    haveI hS' : Group.IsSolvable (rootSpan τ K (kernelRoots χ)) := solvable_of_surjective hμs
    have hS : Group.IsSolvable (rootSpan τ K (rootCharKernel b)) := by
      rw [hker]; exact hS'
    haveI : Group.IsSolvable ((rootSpan τ K (rootCharKernel b)).subgroupOf (toralCentralizer τ K b)) :=
      solvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hSle).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hSle).symm.surjective
    haveI := hquot
    exact solvable_of_ker_le_range
      (((rootSpan τ K (rootCharKernel b)).subgroupOf (toralCentralizer τ K b)).subtype)
      (QuotientGroup.mk' ((rootSpan τ K (rootCharKernel b)).subgroupOf (toralCentralizer τ K b)))
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    right
    have hq : IsQuasisimple (componentRootSpan K χ i) :=
      (OddToralOrdinary.componentRootSpan_quasisimple_or_solvable hK χ rfl i).resolve_right hi
    have hle1 : componentRootSpan K χ i ≤ rootSpan τ K (rootCharKernel b) := by
      rw [hker]; exact (hnormS i).1
    have hle : componentRootSpan K χ i ≤ toralCentralizer τ K b := hle1.trans hSle
    refine ⟨(componentRootSpan K χ i).subgroupOf (toralCentralizer τ K b),
      LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm hq, ?_⟩
    have hnz : rootSpan τ K (rootCharKernel b) ≤
        Subgroup.normalizer (componentRootSpan K χ i : Set (ModGL τ K)) := by
      rw [hker]; exact rootSpan_le_normalizer (K := K) (χ := χ) i
    have hN2le : (componentRootSpan K χ i).subgroupOf (toralCentralizer τ K b) ≤
        (rootSpan τ K (rootCharKernel b)).subgroupOf (toralCentralizer τ K b) :=
      Subgroup.comap_mono hle1
    have hN2norm : (((componentRootSpan K χ i).subgroupOf (toralCentralizer τ K b)).subgroupOf
        ((rootSpan τ K (rootCharKernel b)).subgroupOf (toralCentralizer τ K b))).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hN2le]
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have hgS : ((g : toralCentralizer τ K b) : ModGL τ K) ∈
          rootSpan τ K (rootCharKernel b) := hg
      have := Subgroup.mem_normalizer_iff.1 (hnz hgS) ((h : toralCentralizer τ K b) : ModGL τ K)
      simpa [Subgroup.mem_subgroupOf] using this
    exact Subgroup.IsSubnormal.trans hN2le hN2norm.isSubnormal hSnorm.isSubnormal

end CFSG.ComponentClassification.CatFC.DS81
