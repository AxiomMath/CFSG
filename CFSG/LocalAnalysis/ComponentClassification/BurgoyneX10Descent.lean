module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10Pred
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQuadDescentMain

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.X10

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open scoped MatrixGroups

@[expose] def InnerP (P : CompPred) (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → Nat.card K = p ^ f →
    ∀ (α : MulAut (adjointGroup τ K)) (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ),
      (∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
        (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹) → orderOf α = 2 →
      ∀ L : Subgroup (fixedSubgroup α), IsComponent L → P.P p L

@[expose] def FamilyP (P : CompPred) (t : StatedLieTag) : Prop :=
  ∀ (J : Type) [Group J] (n p f : ℕ), p.Prime → p ≠ 2 →
    StatedLieAdmissible t n p f → LieModel J t n p f →
    ∀ α : MulAut J, orderOf α = 2 → ∀ K : Subgroup (fixedSubgroup α), IsComponent K → P.P p K

theorem FamilyP.of_model (P : CompPred) {t : StatedLieTag} (h : ExcFamilyModel t)
    (hexc : ∀ (L : Type) [Group L], LieModel L .PSL 2 2 3 → P.P 3 L) : FamilyP P t := by
  intro J _ n p f hp hp2 hadm hm α hα Kc hKc
  rcases h J n p f hp hp2 hadm hm α hα Kc hKc with h | ⟨rfl, -, -, h8⟩
  · exact P.of_model hp2 h
  · exact hexc _ h8

theorem noPSp4Odd_of_lieModel_psl_two_two_three (hO : LieOrderFormulasInput) {L : Type}
    [Group L] (h : LieModel L .PSL 2 2 3) : (CompPred.noPSp4Odd hO).P 3 L :=
  (noPSp4_of_lieModel_psl_two_two_three hO h).toOdd

variable {τ : Tag} {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem CompPred.family_of_mulEquiv (P : CompPred) {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {p : ℕ} (h : ∀ α : MulAut B, orderOf α = 2 →
      ∀ L : Subgroup (fixedSubgroup α), IsComponent L → P.P p L)
    (α : MulAut A) (hα : orderOf α = 2) (L : Subgroup (fixedSubgroup α)) (hL : IsComponent L) :
    P.P p L := by
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  exact P.of_component_equiv (fixedSubgroupCongrEquiv e α) (h _ hβ) hL

theorem CompPred.orbitGroup_of_quadGroup
    (P : CompPred) (D : OrthogonalSemilinearFixedRootDatum τ p k)
    (hθ2 : ∀ β ∈ D.simpleRootsJ, D.θ (D.θ (toReal β)) = toReal β)
    (hcard : ∀ O ∈ D.orbits, orbitCard O = 1 ∨ orbitCard O = 2)
    (hnc : ∃ y ∈ quadGens D, ∃ x ∈ quadGens D, ¬ Commute (D.F y * y⁻¹) x)
    (hq : IsQuasisimple D.orbitGroup)
    (hfam : ∀ α : MulAut (↥(quadGroup D) ⧸ Subgroup.center ↥(quadGroup D)), orderOf α = 2 →
      ∀ L : Subgroup (fixedSubgroup α), IsComponent L → P.P p L) :
    P.P p D.orbitGroup := by
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
  have hPK : P.P p ↥(C₁.map π) :=
    P.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hmap.1).symm (hfam σ' hord _ hK)
  have hker : (π.subgroupMap C₁).ker ≤ Subgroup.center C₁ := by
    intro x hx
    have hx1 : π (x : Y) = 1 := congrArg Subtype.val hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
    exact Subgroup.mem_center_iff.2 fun w =>
      Subtype.ext (Subgroup.mem_center_iff.1 hx1 (w : Y))
  exact P.of_mulEquiv eC.symm (P.of_central hq₁ (π.subgroupMap C₁) (π.subgroupMap_surjective C₁)
    hker hPK)

end CFSG.ComponentClassification.Burgoyne.X10
