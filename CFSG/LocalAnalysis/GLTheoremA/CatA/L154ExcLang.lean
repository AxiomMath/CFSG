module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobRoot
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.GGInnLocalDefs
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.Yardstones.Md0ec50421ce4.Definitions
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8Five
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.AlgebraicGroups.ConnectedToralLang
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Assembly (LargeEvenInduces LargeEvenMarking)
open CFSG.StandardType (GGOutdiagPrime)
open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie)
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open CFSG.ComponentClassification.PerfectAutomorphisms (hom_eq_id_of_central_displacement)

section Abstract

variable {G : Type*} [Group G]

theorem l154_induces_pow {X : Subgroup G} (σ : G →* G) (hσ : ∀ x ∈ X, σ x ∈ X) {R : Type}
    [Group R] (θ : ↥X ⧸ Subgroup.center ↥X ≃* R) {φ : MulAut R}
    (hind : LargeEvenInduces θ (fun x x' : ↥X => σ (x : G) = (x' : G)) φ) (n : ℕ) :
    LargeEvenInduces θ (fun x x' : ↥X => σ^[n] (x : G) = (x' : G)) (φ ^ n) := by
  induction n with
  | zero =>
    intro x x' h
    rw [Function.iterate_zero_apply] at h
    rw [pow_zero, MulAut.one_apply, Subtype.ext h]
  | succ n ih =>
    intro x x' h
    rw [pow_succ, MulAut.mul_apply, hind x ⟨σ x, hσ x x.2⟩ rfl]
    exact ih ⟨σ x, hσ x x.2⟩ x' (by
      show (⇑σ)^[n] (σ x) = x'
      rw [← h, Function.iterate_succ_apply])

theorem l154_exists_conj_of_induces_inner {X : Subgroup G} (hX : commutator ↥X = ⊤)
    (σ : G →* G) (hσ : ∀ x ∈ X, σ x ∈ X) {R : Type} [Group R]
    (θ : ↥X ⧸ Subgroup.center ↥X ≃* R) (ρ : R)
    (hind : LargeEvenInduces θ (fun x x' : ↥X => σ (x : G) = (x' : G)) (MulAut.conj ρ)) :
    ∃ z ∈ X, ∀ x ∈ X, σ x = z * x * z⁻¹ := by
  haveI : Group.IsPerfect ↥X := ⟨hX⟩
  obtain ⟨z, hz⟩ := QuotientGroup.mk_surjective (θ.symm ρ)
  let σX : ↥X →* ↥X := (σ.comp X.subtype).codRestrict X fun x => hσ x x.2
  let f : ↥X →* ↥X := (MulAut.conj z⁻¹).toMonoidHom.comp σX
  have hf : f = MonoidHom.id _ := by
    refine hom_eq_id_of_central_displacement f fun x => ?_
    have h1 : (MulAut.conj ρ) (θ (QuotientGroup.mk x)) = θ (QuotientGroup.mk (σX x)) :=
      hind x (σX x) rfl
    have h2 : (QuotientGroup.mk (σX x) : ↥X ⧸ Subgroup.center ↥X) =
        QuotientGroup.mk (z * x * z⁻¹) := by
      apply θ.injective
      rw [← h1, MulAut.conj_apply, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, map_mul, map_mul, map_inv, hz, θ.apply_symm_apply]
    have hc : (σX x)⁻¹ * (z * x * z⁻¹) ∈ Subgroup.center ↥X := QuotientGroup.eq.1 h2
    have hcomm := Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hc) z
    have e1 : x⁻¹ * f x = z⁻¹ * ((σX x)⁻¹ * (z * x * z⁻¹))⁻¹ * z := by
      show x⁻¹ * (z⁻¹ * σX x * z⁻¹⁻¹) = _
      group
    rw [e1, mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
    exact Subgroup.inv_mem _ hc
  refine ⟨z, z.2, fun x hx => ?_⟩
  have h0 := congrArg Subtype.val (DFunLike.congr_fun hf ⟨x, hx⟩)
  have h' : (z : G)⁻¹ * σ x * ((z : G)⁻¹)⁻¹ = x := h0
  rw [inv_inv] at h'
  calc σ x = z * ((z : G)⁻¹ * σ x * z) * (z : G)⁻¹ := by group
    _ = z * x * (z : G)⁻¹ := by rw [h']

end Abstract

section Lang

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem l154_rationalComponent_le_Γ (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) :
    rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ S.Γ :=
  (Subgroup.commutator_le_self _).trans inf_le_right

theorem l154_step_eq_of_mem_Γ (S : LangSetup τ L p₀) {x : ModGL τ L} (hx : x ∈ S.Γ) :
    S.D.step x = x :=
  (S.D.mem_model.1 (Subgroup.commutator_le_self S.D.model hx)).2

theorem l154_lang_exists_conj (S : LangSetup τ L p₀) {p : ℕ} (R : FrobRoot S.D p)
    {a : Fin τ.rank → Lˣ} {i : KernelComponent (rootCharHom a)}
    (hstab : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      R.step0 x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i)
    (hM : LargeEvenMarking ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) fun _ R' _ I _ θ =>
      GGOutdiagPrime p R' I ∧
        ∃ φ ∈ I, LargeEvenInduces θ (fun x x' => R.step0 (x : ModGL τ L) = (x' : ModGL τ L)) φ) :
    ∃ z ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, R.step0 x = z * x * z⁻¹ := by
  obtain ⟨hperf, lab, -, hraw⟩ := hM
  obtain ⟨R', _, I, F, -, -, θ, hout, φ, hφ, hind⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  have hfix : ∀ x : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i),
      R.step0^[p] (x : ModGL τ L) = x := fun x => by
    rw [R.step0_iterate]
    exact l154_step_eq_of_mem_Γ S (l154_rationalComponent_le_Γ S i x.2)
  have hpow : φ ^ p = 1 := by
    have h1 := l154_induces_pow R.step0 hstab θ hind p
    ext u
    obtain ⟨w, rfl⟩ := θ.surjective u
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
    rw [h1 x x (hfix x), MulAut.one_apply]
  obtain ⟨ρ, rfl⟩ := hout φ hφ hpow
  exact l154_exists_conj_of_induces_inner hperf R.step0 hstab θ ρ hind

end Lang

section Residual

@[expose] def L154LangInnRes : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀)
    (p : ℕ) (R : FrobRoot S.D p) (a : Fin τ.rank → Lˣ) (i : KernelComponent (rootCharHom a)),
    p.Prime → p ≠ 2 → rootDiagUnit τ a ∈ S.D.torus → (∀ k, a k ^ p = 1) →
    rootDiagUnit τ a ≠ 1 → R.step0 (rootDiagUnit τ a) = rootDiagUnit τ a →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    (∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      R.step0 x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    LargeEvenMarking ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) (fun _ R' _ I _ θ =>
      ¬ GGOutdiagPrime p R' I ∧
        ∃ φ ∈ I, LargeEvenInduces θ (fun x x' => R.step0 (x : ModGL τ L) = (x' : ModGL τ L)) φ) →
    ∃ z : ModGL τ L, ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, R.step0 x = z * x * z⁻¹

@[expose] def FrobRootNotConjG2 : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup .G2 L p₀) (p : ℕ)
    (R : FrobRoot S.D p) (e : ℕ) (a : Fin Tag.G2.rank → Lˣ)
    (i : KernelComponent (rootCharHom a)) (z : ModGL .G2 L),
    p.Prime → p ≠ 2 → 1 ≤ e → R.q0 = 2 ^ e → rootDiagUnit .G2 a ∈ S.D.torus →
    (∀ k, a k ^ p = 1) → rootDiagUnit .G2 a ≠ 1 →
    R.step0 (rootDiagUnit .G2 a) = rootDiagUnit .G2 a →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    (∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      R.step0 x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    (∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, R.step0 x = z * x * z⁻¹) → False

end Residual

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
