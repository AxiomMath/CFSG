module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentComp
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OrthBlocks
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Orth
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInOmGen

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Polynomial
open CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
open CFSG.RankThree.Classical2 CFSG.SeitzReduction.OmegaPilot CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin (quadPlus quadMinus)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open scoped Classical

abbrev OrthPairedBlock {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) : Prop :=
  ∀ {p : ℕ} (_hp : p.Prime) (_hp2 : p ≠ 2) (x y : ↥(orthDerived Q))
    (_hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V))
    (_hyc : (y : V ≃ₗ[K] V) ∈ isometryCentralizer Q (x : V ≃ₗ[K] V))
    (hyp : y ^ p = 1) {h : K[X]}
    (hh : h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap) (hne1 : h ≠ X - 1)
    (hne : h ≠ reciprocalPolynomial h)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h))
    (J : Subgroup (ProjOrthDerived Q))
    (hJeq : J = componentImage Q (x : V ≃ₗ[K] V) h)
    (hN : piOrth Q y ∈ Subgroup.normalizer (J : Set (ProjOrthDerived Q))),
    (catalogIs (PSimple p J) (onLie isLinearCharTwoIdx) ∧
        MI.indAut p J (piOrth Q y) hN ∈ innAutDerived (PSimple p J)) ∨
      MI.indAut p J (piOrth Q y) hN ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple p J)

abbrev OrthSelfDualBlock {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V) : Prop :=
  ∀ {p : ℕ} (_hp : p.Prime) (_hp2 : p ≠ 2) (x y : ↥(orthDerived Q))
    (_hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V))
    (_hyc : (y : V ≃ₗ[K] V) ∈ isometryCentralizer Q (x : V ≃ₗ[K] V))
    (hyp : y ^ p = 1) {h : K[X]}
    (hh : h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h))
    (J : Subgroup (ProjOrthDerived Q))
    (hJeq : J = componentImage Q (x : V ≃ₗ[K] V) h)
    (hN : piOrth Q y ∈ Subgroup.normalizer (J : Set (ProjOrthDerived Q))),
    (catalogIs (PSimple p J) (onLie isUnitaryCharTwoIdx) ∧
        MI.indAut p J (piOrth Q y) hN ∈ innAutDerived (PSimple p J)) ∨
      MI.indAut p J (piOrth Q y) hN ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple p J)

abbrev OrthFixedBlock {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) : Prop :=
  ∀ {p : ℕ} (_hp : p.Prime) (_hp2 : p ≠ 2) (x y : ↥(orthDerived Q))
    (_hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V))
    (_hyc : (y : V ≃ₗ[K] V) ∈ isometryCentralizer Q (x : V ≃ₗ[K] V))
    (hyp : y ^ p = 1) (F : Subgroup (V ≃ₗ[K] V))
    (hFq : CFSG.IsQuasisimple ↥F) (hFle : F ≤ supportedFixedDerived Q (x : V ≃ₗ[K] V))
    (hFn : (F.subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[K] V))).Normal)
    (J : Subgroup (ProjOrthDerived Q))
    (hJeq : J = (F.subgroupOf (orthDerived Q)).map (piOrth Q))
    (hN : piOrth Q y ∈ Subgroup.normalizer (J : Set (ProjOrthDerived Q))),
    MI.indAut p J (piOrth Q y) hN ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple p J)

abbrev OrthComponentBlockAnalysis {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V) : Prop :=
  ∀ {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (x y : ↥(orthDerived Q))
    (hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V))
    (hyc : (y : V ≃ₗ[K] V) ∈ isometryCentralizer Q (x : V ≃ₗ[K] V))
    (hyp : y ^ p = 1) (hx1 : x ≠ 1)
    (J : Subgroup (ProjOrthDerived Q))
    (hcomp : CFSG.Assembly.IsComponentOf J (CFSG.RankThree.PartOne.KCOrthogonal.centralizerImage Q
      (x : V ≃ₗ[K] V)))
    (hN : piOrth Q y ∈ Subgroup.normalizer (J : Set (ProjOrthDerived Q))),
    (catalogIs (PSimple p J) (onLie isLinearCharTwoIdx) ∧
        MI.indAut p J (piOrth Q y) hN ∈ innAutDerived (PSimple p J)) ∨
      (catalogIs (PSimple p J) (onLie isUnitaryCharTwoIdx) ∧
        MI.indAut p J (piOrth Q y) hN ∈ innAutDerived (PSimple p J)) ∨
        MI.indAut p J (piOrth Q y) hN ∈
          CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple p J)

theorem piOrth_orthProjEquiv {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (hQ : ∃ v, Q v ≠ 0) (z : ProjOrthDerived Q) :
    piOrth Q (CFSG.LocalAnalysis.GLTheoremA.K155XOr.orthProjEquiv hQ z) = z := by
  obtain ⟨w, rfl⟩ := CFSG.RankThree.PartOne.piOrth_surjective (Q := Q) z
  exact congrArg (piOrth Q) (CFSG.LocalAnalysis.GLTheoremA.K155XOr.orthProjEquiv_mk hQ w)

theorem map_centralizerImage_orthProjEquiv {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} (hQ : ∃ v, Q v ≠ 0)
    (x : ↥(orthDerived Q)) :
    (CFSG.RankThree.PartOne.KCOrthogonal.centralizerImage Q (x : V ≃ₗ[K] V)).map
        (CFSG.LocalAnalysis.GLTheoremA.K155XOr.orthProjEquiv hQ).toMonoidHom =
      Subgroup.centralizer ({x} : Set ↥(orthDerived Q)) := by
  rw [← CFSG.RankThree.PartOne.map_centralizer_eq_centralizerImage (Q := Q) (x := x)]
  rw [Subgroup.map_map]
  rw [show ((CFSG.LocalAnalysis.GLTheoremA.K155XOr.orthProjEquiv hQ).toMonoidHom.comp
      (piOrth Q)) = MonoidHom.id ↥(orthDerived Q) from by
    refine MonoidHom.ext fun v => ?_
    exact CFSG.LocalAnalysis.GLTheoremA.K155XOr.orthProjEquiv_mk hQ v]
  exact Subgroup.map_id _

theorem orthComponentBlockAnalysis_of_cases {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hQne : ∃ v, Q v ≠ 0)
    (hpair : OrthPairedBlock Q) (hself : OrthSelfDualBlock Q) (hfix : OrthFixedBlock Q) :
    OrthComponentBlockAnalysis Q := by
  intro p hp hp2 x y hx hyc hyp hx1 J hcomp hN
  set sigma := CFSG.LocalAnalysis.GLTheoremA.K155XOr.orthProjEquiv hQne with hsigma
  have hcompSigma : CFSG.Assembly.IsComponentOf (J.map sigma.toMonoidHom)
      (Subgroup.centralizer ({x} : Set ↥(orthDerived Q))) := by
    have h := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map sigma
      ((CFSG.Assembly.isComponentOf_iff_open).1 hcomp)
    rw [show Subgroup.map (↑sigma)
        (CFSG.RankThree.PartOne.KCOrthogonal.centralizerImage Q (x : V ≃ₗ[K] V)) =
        Subgroup.centralizer ({x} : Set ↥(orthDerived Q)) from by
      rw [hsigma]
      exact map_centralizerImage_orthProjEquiv hQne x] at h
    exact (CFSG.Assembly.isComponentOf_iff_open).2 h
  haveI : Fact p.Prime := ⟨hp⟩
  have hxord : orderOf x = p := by
    refine orderOf_eq_prime ?_ hx1
    apply Subtype.ext
    simpa using hx.pow_eq_one
  have hmapPi : (J.map sigma.toMonoidHom).map (piOrth Q) = J := by
    rw [Subgroup.map_map]
    rw [show (piOrth Q).comp sigma.toMonoidHom = MonoidHom.id (ProjOrthDerived Q) from by
      refine MonoidHom.ext fun z => ?_
      exact piOrth_orthProjEquiv hQne z]
    exact Subgroup.map_id J
  rcases CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.comp_cases_orthDerived_of_prime hQ hp hp2
      hxord ((CFSG.Assembly.isComponentOf_iff_open).1 hcompSigma) with
    ⟨h, hh, hne1, hq, hJmap⟩ | ⟨F, hFq, hFle, hFn, _hdim, hJmap⟩
  ·
    have hJeq : J = componentImage Q (x : V ≃ₗ[K] V) h := by
      have h1 : (J.map sigma.toMonoidHom).map (piOrth Q) =
          ((specialBlock Q (x : V ≃ₗ[K] V) h).subgroupOf (orthDerived Q)).map (piOrth Q) := by
        rw [hJmap]
      rw [hmapPi] at h1
      simpa [componentImage] using h1
    by_cases hselfcase : h = reciprocalPolynomial h
    · rcases hself hp hp2 x y hx hyc hyp hh hne1 hselfcase hq J hJeq hN with h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
    · rcases hpair hp hp2 x y hx hyc hyp hh hne1 hselfcase hq J hJeq hN with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')
  ·
    have hJeq : J = (F.subgroupOf (orthDerived Q)).map (piOrth Q) := by
      have h1 : (J.map sigma.toMonoidHom).map (piOrth Q) =
          (F.subgroupOf (orthDerived Q)).map (piOrth Q) := by
        rw [hJmap]
      rwa [hmapPi] at h1
    exact Or.inr (Or.inr (hfix hp hp2 x y hx hyc hyp F hFq hFle hFn J hJeq hN))

theorem chevAut_eq_conj_chevQuotHom {G : Type} [Group G] {p : ℕ} {L : Subgroup G} {g h : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (hh : h ∈ L)
    (hconj : ∀ z : ↥L, g * (z : G) * g⁻¹ = h * (z : G) * h⁻¹) :
    chevAut p L ⟨g, hg⟩ = MulAut.conj (chevQuotHom p L ⟨h, hh⟩) := by
  refine MulEquiv.ext fun r => ?_
  obtain ⟨k, rfl⟩ := chevQuotHom_surjective p L r
  rw [chevAut_chevQuotHom, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  have hgz : ((L.normalizerMonoidHom ⟨g, hg⟩ k : ↥L) : G) = g * (k : G) * g⁻¹ := by
    change g * (k : G) * g⁻¹ = _
    rfl
  have hhz : (((⟨h, hh⟩ : ↥L) * k * (⟨h, hh⟩ : ↥L)⁻¹ : ↥L) : G) = h * (k : G) * h⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hgz, hhz]
  exact hconj k

theorem indAut_mem_inner_of_conj_eq {G : Type} [Group G] {p : ℕ} {L : Subgroup G} {g h : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (hh : h ∈ L)
    (hconj : ∀ z : ↥L, g * (z : G) * g⁻¹ = h * (z : G) * h⁻¹) :
    MI.indAut p L g hg ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple p L) := by
  have h1 : chevAut p L ⟨g, hg⟩ = MulAut.conj (chevQuotHom p L ⟨h, hh⟩) :=
    chevAut_eq_conj_chevQuotHom hg hh hconj
  have hmem : chevAut p L ⟨g, hg⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple p L) := ⟨_, h1.symm⟩
  have hinv : (chevAut p L ⟨g, hg⟩)⁻¹ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple p L) :=
    Subgroup.inv_mem _ hmem
  have heq : MI.indAut p L g hg = (chevAut p L ⟨g, hg⟩)⁻¹ := by
    rw [MI.indAut, ← map_inv]
    exact congrArg (chevAut p L) (Subtype.ext rfl)
  rwa [heq]

theorem fixSubgroup_conj_eq_centralizerImage {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} (hQ : ∃ v, Q v ≠ 0)
    (x : ProjOrthDerived Q) :
    CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x) =
      CFSG.RankThree.PartOne.KCOrthogonal.centralizerImage Q
        ((CFSG.LocalAnalysis.GLTheoremA.K155XOr.orthProjEquiv hQ x : ↥(orthDerived Q)) :
          V ≃ₗ[K] V) := by
  set sigma := CFSG.LocalAnalysis.GLTheoremA.K155XOr.orthProjEquiv hQ with hsigma
  have h1 : (CFSG.RankThree.PartOne.KCOrthogonal.centralizerImage Q
        ((sigma x : ↥(orthDerived Q)) : V ≃ₗ[K] V)).map sigma.toMonoidHom =
      Subgroup.centralizer ({sigma x} : Set ↥(orthDerived Q)) :=
    map_centralizerImage_orthProjEquiv hQ (sigma x)
  have h2 : (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x)).map
        sigma.toMonoidHom =
      Subgroup.centralizer ({sigma.toMonoidHom x} : Set ↥(orthDerived Q)) := by
    rw [CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.fixSubgroup_conj_eq_centralizer' x]
    rw [show Subgroup.centralizer ({x} : Set (ProjOrthDerived Q)) =
        Subgroup.centralizer ((Subgroup.zpowers x : Subgroup (ProjOrthDerived Q)) :
          Set (ProjOrthDerived Q)) from by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]]
    rw [CFSG.Glauberman.map_centralizer_eq_of_equiv sigma (Subgroup.zpowers x)]
    rw [MonoidHom.map_zpowers]
    rw [show Subgroup.centralizer ((Subgroup.zpowers (sigma.toMonoidHom x) :
          Subgroup ↥(orthDerived Q)) : Set ↥(orthDerived Q)) =
        Subgroup.centralizer ({sigma.toMonoidHom x} : Set ↥(orthDerived Q)) from by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]]
  have h1' : (CFSG.RankThree.PartOne.KCOrthogonal.centralizerImage Q
        ((sigma x : ↥(orthDerived Q)) : V ≃ₗ[K] V)).map sigma.toMonoidHom =
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x)).map
        sigma.toMonoidHom := by
    rw [h1, h2]
    rfl
  exact (Subgroup.map_injective (f := sigma.toMonoidHom) sigma.injective h1').symm

theorem indAut_eq_of_proof {G : Type} [Group G] {p : ℕ} {L : Subgroup G} {g : G}
    (h1 h2 : g ∈ Subgroup.normalizer (L : Set G)) :
    MI.indAut p L g h1 = MI.indAut p L g h2 := by
  change chevAut p L ⟨g⁻¹, Subgroup.inv_mem _ h1⟩ =
    chevAut p L ⟨g⁻¹, Subgroup.inv_mem _ h2⟩
  congr 1

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
