module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamCore
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQuadDescentMain
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQuadDescent
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7Twist
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7Inner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddLieFamilies
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4CubeReturn
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Export
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.Pairs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentCore
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentDisplayed
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentTags
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic

public noncomputable section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG
  CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification
open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups
open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley CFSG.ComponentClassification.CatLeaf

theorem cl24_family_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {p : ℕ} {R : ℕ → Prop}
    (h : ∀ α : MulAut B, orderOf α = 2 →
      ∀ L : Subgroup (fixedSubgroup α), IsComponent L → Cl24Q p R L)
    (α : MulAut A) (hα : orderOf α = 2) (L : Subgroup (fixedSubgroup α)) (hL : IsComponent L) :
    Cl24Q p R L := by
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  exact cl24_of_component_equiv (fixedSubgroupCongrEquiv e α) (h _ hβ) hL

section


variable {τ : Tag} {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

variable {R : ℕ → Prop}

theorem cl24_orbitGroup_of_quadGroup
    (D : OrthogonalSemilinearFixedRootDatum τ p k)
    (hθ2 : ∀ β ∈ D.simpleRootsJ, D.θ (D.θ (toReal β)) = toReal β)
    (hcard : ∀ O ∈ D.orbits, orbitCard O = 1 ∨ orbitCard O = 2)
    (hnc : ∃ y ∈ quadGens D, ∃ x ∈ quadGens D, ¬ Commute (D.F y * y⁻¹) x)
    (hq : IsQuasisimple D.orbitGroup)
    (hfam : ∀ α : MulAut (↥(quadGroup D) ⧸ Subgroup.center ↥(quadGroup D)), orderOf α = 2 →
      ∀ L : Subgroup (fixedSubgroup α), IsComponent L → Cl24Q p R L) :
    Cl24Q p R D.orbitGroup := by
  have := finite_quadGroup D
  let Y := quadGroup D
  let σ := quadAut D hθ2
  have hσσ : ∀ y, σ (σ y) = y := fun y => Subtype.ext (F_mem_quadGroup D hθ2 y.2).2
  let π := QuotientGroup.mk' (Subgroup.center Y)
  let σ' : MulAut (Y ⧸ Subgroup.center Y) :=
    QuotientGroup.congr (Subgroup.center Y) (Subgroup.center Y) σ (Subgroup.map_center_eq σ)
  have hcomm : ∀ y, π (σ y) = σ' (π y) := fun y => rfl
  have hσ'2 : σ' ^ 2 = 1 := by
    ext z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Y) z
    rw [sq, MulAut.mul_apply, ← hcomm, ← hcomm, hσσ]
    rfl
  have hσ'1 : σ' ≠ 1 := by
    obtain ⟨y, hy, x, hx, hyx⟩ := hnc
    intro h
    have hyY : y ∈ Y := Subgroup.subset_closure hy
    have hxY : x ∈ Y := Subgroup.subset_closure hx
    have h1 : π (σ ⟨y, hyY⟩) = π ⟨y, hyY⟩ := by rw [hcomm, h]; rfl
    have hz : (σ ⟨y, hyY⟩)⁻¹ * ⟨y, hyY⟩ ∈ Subgroup.center Y := QuotientGroup.eq.1 h1
    have hzc := Subgroup.mem_center_iff.1 (inv_mem hz)
    have he : σ ⟨y, hyY⟩ * (⟨y, hyY⟩ : Y)⁻¹ = ((σ ⟨y, hyY⟩)⁻¹ * ⟨y, hyY⟩)⁻¹ := by
      have h2 := hzc (σ ⟨y, hyY⟩)
      rw [mul_inv_rev, inv_inv] at h2 ⊢
      calc σ ⟨y, hyY⟩ * (⟨y, hyY⟩ : Y)⁻¹ =
          σ ⟨y, hyY⟩ * ((⟨y, hyY⟩ : Y)⁻¹ * σ ⟨y, hyY⟩) * (σ ⟨y, hyY⟩)⁻¹ := by group
        _ = (⟨y, hyY⟩ : Y)⁻¹ * σ ⟨y, hyY⟩ := by rw [h2]; group
    apply hyx
    have hc : Commute (σ ⟨y, hyY⟩ * (⟨y, hyY⟩ : Y)⁻¹) ⟨x, hxY⟩ := by
      rw [he]
      exact (hzc ⟨x, hxY⟩).symm
    exact hc.map Y.subtype
  have hord : orderOf σ' = 2 := orderOf_eq_prime hσ'2 hσ'1
  have hCY : D.orbitGroupC ≤ Y := fun x hx => by
    obtain ⟨y, hy, hyx⟩ := orbitGroup_le_map_quadGroup D hcard (Subgroup.mem_subgroupOf.1 hx)
    rwa [← Subtype.ext hyx]
  let C₁ : Subgroup Y := D.orbitGroupC.subgroupOf Y
  let eC : C₁ ≃* D.orbitGroup := (Subgroup.subgroupOfEquivOfLe hCY).trans
    (Subgroup.subgroupOfEquivOfLe D.orbitGroup_le_adjointGroup)
  have hq₁ : IsQuasisimple C₁ := LocalCores.isQuasisimple_of_mulEquiv eC.symm hq
  have hC₁fix : C₁ ≤ fixedSubgroup σ := fun c hc =>
    Subtype.ext (D.mem_fixedGroup.1 (D.orbitGroupC_le_fixedGroup hc)).2
  have hYfix : ∀ g : Y, σ g = g → (g : adjointGroup τ k) ∈ D.fixedGroup := fun g hg =>
    D.mem_fixedGroup.2 ⟨Subgroup.mem_subgroupOf.1 (quadGroup_le_rootSpanJ D g.2),
      congrArg Subtype.val hg⟩
  have hN : (C₁.subgroupOf (fixedSubgroup σ)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hnor := D.orbitGroupC_normal
    have hn' : (⟨(n : Y), hYfix _ n.2⟩ : D.fixedGroup) ∈ D.orbitGroupC.subgroupOf D.fixedGroup :=
      Subgroup.mem_subgroupOf.2 hn
    have := hnor.conj_mem _ hn' ⟨((g : Y) : adjointGroup τ k), hYfix _ g.2⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hC₁comp : Assembly.IsComponentOf C₁ (fixedSubgroup σ) :=
    ⟨hC₁fix, Assembly.IsSubnormal.step hC₁fix hN (Assembly.IsSubnormal.refl _),
      (AssemblyBPredicates.isQuasisimple_iff_native C₁).2 hq₁⟩
  have hmap := LocalAnalysis.ComponentInitial.isComponentOf_map_fixed (π := π)
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) hσσ hcomm hC₁comp
  have hK := (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    hmap.1).1 hmap
  obtain ⟨τ', n', f', hR, hadm, hlie⟩ := cl24_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hmap.1).symm (hfam σ' hord _ hK)
  have hker : (π.subgroupMap C₁).ker ≤ Subgroup.center C₁ := by
    intro x hx
    have hx1 : π (x : Y) = 1 := congrArg Subtype.val hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
    exact Subgroup.mem_center_iff.2 fun w =>
      Subtype.ext (Subgroup.mem_center_iff.1 hx1 (w : Y))
  obtain ⟨e₂⟩ := LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hq₁
    (π.subgroupMap C₁) (π.subgroupMap_surjective C₁) hker
  exact cl24_of_mulEquiv eC.symm
    ⟨τ', n', f', hR, hadm, LieType.CurtisTits.lieModel_of_mulEquiv e₂.symm hlie⟩

end

end CFSG.OddStandard.SmallF3.HypA2Leaves
