module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OuterPlane
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLInnerInvolution
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoSemilinear
import CFSG.Dihedral.GorensteinWalter.PGL2SquareRange
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (relIndex_inner_linearAutGroup_dvd)
open CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL (mem_semilinearAutGroup_of_odd)
open CFSG.GorensteinWalter Matrix
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

theorem exists_inner_plane_projectiveSL {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpg : ¬ p ∣ Nat.gcd n (Nat.card K - 1))
    (D : Subgroup (MulAut (projectiveSL n K))) (hD : IsElemAbelian p D)
    (hcard : Nat.card D = p ^ 3) :
    ∃ E : Subgroup (MulAut (projectiveSL n K)), E ≤ D ∧ E ≤ innerAut (projectiveSL n K) ∧
      IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  classical
  have hDfin : Finite D :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 hp.ne_zero)
  set Dl := linearAutGroup n K with hDl
  set Es := semilinearAutGroup n K with hEs
  have hgen := (automorphism_generation (K := K) hn).1
  obtain ⟨hID, -, hDnorm, -, -, ⟨g, hgE, hg⟩, -⟩ := standard_outer_quotients (n := n) (K := K)
  rw [hgen] at hDnorm
  have hDlN : Dl.Normal := ⟨fun d hd x =>
    hDnorm.conj_mem ⟨d, Subgroup.mem_top d⟩ hd ⟨x, Subgroup.mem_top x⟩⟩
  have hcyc : IsCyclic (Es ⧸ Dl.subgroupOf Es) := by
    refine ⟨⟨QuotientGroup.mk ⟨g, hgE⟩, fun y => ?_⟩⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := hg x x.2
    refine ⟨-k, ?_⟩
    change (QuotientGroup.mk (⟨g, hgE⟩ : Es) : Es ⧸ Dl.subgroupOf Es) ^ (-k) = QuotientGroup.mk x
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf, _root_.zpow_neg,
      inv_inv, Subgroup.coe_mul, Subgroup.coe_zpow]
    exact hk
  have hDE : D ≤ Es := fun x hx => by
    have hdvd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one (hD.2 x hx)
    refine mem_semilinearAutGroup_of_odd hn ?_
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · rw [h]; exact odd_one
    · rw [h]; exact hp.odd_of_ne_two hp2
  let α : D →* Es ⧸ Dl.subgroupOf Es :=
    (QuotientGroup.mk' (Dl.subgroupOf Es)).comp (Subgroup.inclusion hDE)
  refine exists_plane_of_hom_cyclic hp (innerAut (projectiveSL n K)) hD hcard α fun x hx => ?_
  have hxDl : (x : MulAut (projectiveSL n K)) ∈ Dl := by
    change QuotientGroup.mk (Subgroup.inclusion hDE x) = (1 : Es ⧸ Dl.subgroupOf Es) at hx
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
    exact hx
  have hm := relIndex_inner_linearAutGroup_dvd (k := K) (n := n) (by omega)
  have hcop : Nat.Coprime p ((Inn (projectiveSL n K)).relIndex Dl) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    exact fun h => hpg (h.trans hm)
  have hNorm : ((Inn (projectiveSL n K)).subgroupOf Dl).Normal := inferInstance
  set y : Dl ⧸ (Inn (projectiveSL n K)).subgroupOf Dl :=
    QuotientGroup.mk ⟨(x : MulAut (projectiveSL n K)), hxDl⟩ with hy
  have hy1 : y ^ p = 1 := by
    rw [hy, ← QuotientGroup.mk_pow]
    have : (⟨(x : MulAut (projectiveSL n K)), hxDl⟩ : Dl) ^ p = 1 :=
      Subtype.ext (hD.2 x x.2)
    rw [this]; rfl
  have hy2 : y ^ ((Inn (projectiveSL n K)).relIndex Dl) = 1 := by
    have h1 := pow_card_eq_one' (G := Dl ⧸ (Inn (projectiveSL n K)).subgroupOf Dl) (x := y)
    rw [← Subgroup.index_eq_card] at h1
    exact h1
  have hord : orderOf y ∣ Nat.gcd p ((Inn (projectiveSL n K)).relIndex Dl) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hy1) (orderOf_dvd_of_pow_eq_one hy2)
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hord
  have := (QuotientGroup.eq_one_iff _).1 hord
  exact (Subgroup.mem_subgroupOf.1 this)

theorem sq_mem_range_toPGL' {K : Type*} [Field K] (g : PGL2 K) :
    g ^ 2 ∈ (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range :=
  CFSG.GorensteinWalter.pgl2_sq_mem_psl2Range g

theorem mem_range_toPGL_of_pow_eq_one' {K : Type*} [Field K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (g : PGL2 K) (hg : g ^ p = 1) :
    g ∈ (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range :=
  CFSG.GorensteinWalter.pgl2_mem_psl2Range_of_pow_odd (hp.odd_of_ne_two hp2) hg


theorem exists_inner_plane_psl2 {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (D : Subgroup (MulAut (PSL2 K))) (hD : IsElemAbelian p D)
    (hcard : Nat.card D = p ^ 3) :
    ∃ E : Subgroup (MulAut (PSL2 K)), E ≤ D ∧ E ≤ innerAut (PSL2 K) ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ 2 := by
  classical
  let Ψ : PGammaL2 K ≃* MulAut (PSL2 K) := semilinearEquivAut K
  have : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  let α : D →* (K ≃+* K) :=
    ((SemidirectProduct.rightHom : PGammaL2 K →* (K ≃+* K)).comp Ψ.symm.toMonoidHom).comp
      D.subtype
  refine exists_plane_of_hom_cyclic hp (innerAut (PSL2 K)) hD hcard α fun x hx => ?_
  have hdk' : SemidirectProduct.rightHom (Ψ.symm (x : MulAut (PSL2 K))) = 1 := hx
  have hmem : Ψ.symm (x : MulAut (PSL2 K)) ∈
      (SemidirectProduct.inl : PGL2 K →* PGammaL2 K).range := by
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    exact hdk'
  obtain ⟨g, hg⟩ := hmem
  have hdg : (x : MulAut (PSL2 K)) = pglAction K g := by
    have : (x : MulAut (PSL2 K)) = Ψ (SemidirectProduct.inl g) := by
      rw [hg]; simp
    rw [this]
    exact semilinearAction_inl K g
  have hgp : g ^ p = 1 := by
    have h1 : Ψ.symm ((x : MulAut (PSL2 K)) ^ p) = 1 := by
      rw [hD.2 x x.2, map_one]
    rw [map_pow, ← hg, ← map_pow] at h1
    exact SemidirectProduct.inl_injective (by rw [map_one]; exact h1)
  obtain ⟨y, hy⟩ := mem_range_toPGL_of_pow_eq_one' hp hp2 g hgp
  exact ⟨y, by rw [hdg, ← hy, pglAction_toPGL]⟩

end CFSG.HardMathSupport.Timmesfeld.CrossChar
