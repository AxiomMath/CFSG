module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamCore
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofKleinSixB
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofKleinSix
public import CFSG.LieType.Universal.Spin.Generation.Eichler
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOrthLow
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentTags
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentCore
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentDisplayed
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic

public noncomputable section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG
  CFSG.ComponentClassification.CatLeafProof.KleinSix
  CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification
open Matrix QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K]

open CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.CatalogueBOrthogonal CFSG.Assembly.LowTwoRank in
theorem cl24_quadPlus_three_component [Finite K] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = p ^ e)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K))}
    (hM : CFSG.IsComponent M)
    {Rel : ℕ → Prop} (hRel : ∀ f', f' = e → Rel f' := by cl24_rel) :
    Cl24Q p Rel M := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hq := derived_quasisimple (quadPlus 3 K) h2 quadPlus_nondegenerate finrank_singularT.ge
    singularT_singular
  have hMeq := eq_commutator_of_isComponent hq hM
  have hmap := derived_map_eq_elementary (quadPlus 3 K) h2 quadPlus_nondegenerate
    finrank_singularT.ge singularT_singular
  have hrange := range_eq_elementaryGroup (K := K) h2
  let eD : commutator (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K)) ≃*
      (rhoGL (K := K)).range :=
    ((commutator (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K))).equivMapOfInjective
      (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K)).subtype
      (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K)).subtype_injective).trans
      (MulEquiv.subgroupCongr (hmap.trans hrange.symm))
  let eM : M ≃* (rhoGL (K := K)).range := (MulEquiv.subgroupCongr hMeq).trans eD
  have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 4 K (by norm_num)
    (Or.inl (by norm_num)) (Or.inl (by norm_num))
  have hrq : CFSG.IsQuasisimple (rhoGL (K := K)).range :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eD hq
  obtain ⟨eS⟩ := nonempty_centerQuotient_equiv_range hSL rhoGL (ne_bot_of_isQuasisimple hrq)
  let eTot : M ⧸ Subgroup.center M ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) K :=
    (QuotientGroup.congr _ _ eM (Subgroup.map_center_eq eM)).trans eS.symm
  have hadm : StatedLieAdmissible .PSL 4 p e :=
    ⟨hp, he, by norm_num, fun h => by have := (Prod.mk.inj h).1; omega,
      fun h => by have := (Prod.mk.inj h).1; omega⟩
  exact ⟨.PSL, 4, e, hRel e rfl, hadm,
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eTot.symm
    (Or.inl ⟨by decide, ⟨hadm, K, inferInstance, inferInstance, hK,
      ⟨projectiveSpecialLinearGroupEquivStatedProj 4 K⟩⟩⟩)⟩

open CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.RankThree.PartOne.KCOrthogonalDescent CFSG.Assembly.LowTwoRank in
theorem cl24_split_six_component {k W : Type} [Field k] [Finite k] [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hk : Nat.card k = p ^ e) (Q₀ : QuadraticForm k W) (hQ₀ : Q₀.polarBilin.Nondegenerate)
    (hdim : Module.finrank k W = 6)
    (hT : ∃ T : Submodule k W, Module.finrank k T = 3 ∧ ∀ x ∈ T, Q₀ x = 0)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q₀)} (hM : CFSG.IsComponent M)
    {Rel : ℕ → Prop} (hRel : ∀ f', f' = e → Rel f' := by cl24_rel) :
    Cl24Q p Rel M := by
  obtain ⟨m, δ, hδ, ⟨H⟩⟩ := exists_regular_split Q₀ hQ₀
  have hfin := H.finrank_eq
  have hwitt := H.sourceWittIndex_eq hQ₀
  obtain ⟨T, hTdim, hTQ⟩ := hT
  have h3 := CFSG.Blueprint.EvenSource.le_sourceWittIndex (K := k) (V := W) (⇑Q₀) (W := T) hTQ
  have hm : m = 3 := by omega
  have hδ0 : δ = 0 := by omega
  have H' : HypSplit Q₀ 3 0 := by rw [← hm, ← hδ0]; exact H
  let bk := H'.b.reindex (HypSplit.plusEquiv 3)
  have hS : ∀ w, quadPlus 3 k (bk.equivFun w) = ((1 : kˣ) : k) * Q₀ w := fun w => by
    rw [Units.val_one, one_mul, show quadPlus 3 k (bk.equivFun w) =
      StatedQuadPlus 3 k (bk.equivFun w) from congrFun (coe_quadPlus 3 k) _]
    exact H'.displayPlus w
  let eO : TauCeti.QuadraticMap.orthogonalGroup Q₀ ≃*
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 k) :=
    ((TauCeti.QuadraticMap.orthogonalGroup Q₀).equivMapOfInjective
      (linConj bk.equivFun).toMonoidHom (linConj bk.equivFun).injective).trans
      (MulEquiv.subgroupCongr (map_orthogonalGroup bk.equivFun 1 hS))
  have hM' := CFSG.LocalCores.isComponent_map_mulEquiv eO hM
  exact cl24_of_mulEquiv (M.equivMapOfInjective eO.toMonoidHom eO.injective)
    (cl24_quadPlus_three_component hp hp2 he hk hM')

end CFSG.OddStandard.SmallF3.HypA2Leaves
