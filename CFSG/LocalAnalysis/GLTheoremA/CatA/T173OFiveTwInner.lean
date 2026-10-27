module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TwE6LeviRank
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
public import CFSG.GroupTheory.CentralizerMap
public import CFSG.GroupTheory.ConjKerCenter
public import CFSG.LocalAnalysis.ComponentClassification.PerfectCentralQuotient
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LieType.SeitzGeneration.OuterQuotient
public import CFSG.Quasithin.SteinbergUnitaryOuterPrimeControl
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Reduction
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
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

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OuterAutomorphisms

local notation "Γ₂" F => ModGL TwistTag.E6.tag F

theorem card_outer_dvd_two_and_center_eq_bot_of_su_two {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ 2) {n : ℕ} (hn : 3 ≤ n) (hn3 : Nat.Coprime n 3) {L : Type}
    [Group L] [Finite L] [Group.IsPerfect L]
    (ρ : ↥(CFSG.Assembly.LargeEvenSUGroup (Fin n) F 2) →* L) (hρ : Function.Surjective ρ)
    (hρk : ρ.ker ≤ Subgroup.center _) :
    Nat.card (Outer L) ∣ 2 ∧ Subgroup.center L = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : UnitaryFieldData 2 1 F := ⟨Nat.prime_two, le_rfl, by simpa using hF⟩
  haveI : CharP F 2 := hU.charP
  have hF' : Nat.card F = (2 ^ 1) ^ 2 := by simpa using hF
  have hn1 : 1 ≤ n := by omega
  have hn3' : n ≠ 3 := by
    rintro rfl
    norm_num at hn3
  have hnq : (n, 2 ^ 1) ≠ (3, 2) := fun h => hn3' (congrArg Prod.fst h)
  have hcenSU : Subgroup.center ↥(StatedSU n (2 ^ 1) F) = unitaryScalars hU n := by
    rw [(CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
      (p := 2) (f := 1) (n := n) hF' hn hnq).2,
      CFSG.ClassicalGroups.UnitaryFlag.unitaryScalars_eq hU hn1]
  have hcard : Nat.card ↥(unitaryScalars hU n) = 1 := by
    rw [CFSG.ClassicalGroups.UnitaryFlag.card_unitaryScalars hU hn1]
    simpa using hn3
  have hcenSU' : Subgroup.center ↥(CFSG.Assembly.LargeEvenSUGroup (Fin n) F 2) =
      unitaryScalars hU n := hcenSU
  have hcenSUbot : Subgroup.center ↥(CFSG.Assembly.LargeEvenSUGroup (Fin n) F 2) = ⊥ := by
    rw [hcenSU']
    exact Subgroup.card_eq_one.mp hcard
  have hperfSU : Group.IsPerfect ↥(StatedSU n (2 ^ 1) F) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hF' (n := n) hn hnq
  haveI : Group.IsPerfect ↥(CFSG.Assembly.LargeEvenSUGroup (Fin n) F 2) := hperfSU
  have e2 : ↥(StatedSU n (2 ^ 1) F) ⧸ Subgroup.center ↥(StatedSU n (2 ^ 1) F) ≃*
      unitaryPSU hU n := QuotientGroup.quotientMulEquivOfEq hcenSU
  let e : L ⧸ Subgroup.center L ≃* unitaryPSU hU n :=
    (CFSG.ComponentClassification.PerfectCentralQuotient.equivalence ρ hρ hρk).symm.trans e2
  have hcontrol :=
    CFSG.Quasithin.OuterPrimeControl.perfect_unitary_central_quotient_outer_prime_control
      hU (n := n) hn (fun h => hn3' h.1) L e
  have hgcd : Nat.gcd n (2 ^ 1 + 1) = 1 := by simpa using hn3
  have hout' : Nat.card (Outer L) ∣ 2 * 1 * Nat.gcd n (2 ^ 1 + 1) := hcontrol.1
  rw [hgcd] at hout'
  have hker : ρ.ker = ⊥ := le_bot_iff.mp (hρk.trans (le_of_eq hcenSUbot))
  have hρinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).mp hker
  let eSU : ↥(CFSG.Assembly.LargeEvenSUGroup (Fin n) F 2) ≃* L :=
    MulEquiv.ofBijective ρ ⟨hρinj, hρ⟩
  have hcenter : Subgroup.center L = ⊥ := by
    rw [← Subgroup.map_center_eq eSU, hcenSUbot, Subgroup.map_bot]
  exact ⟨by simpa using hout', hcenter⟩

private lemma conj_eq_of_inner_lift {Γ : Type} [Group Γ] {L : Subgroup Γ} {g : Γ}
    (hg : g ∈ Subgroup.normalizer (L : Set Γ)) {y : ↥L}
    (hy : MulAut.conj y = L.normalizerMonoidHom ⟨g, hg⟩) {l : Γ} (hl : l ∈ L) :
    g * l * g⁻¹ = (y : Γ) * l * (y : Γ)⁻¹ := by
  have h := congrArg (fun φ : MulAut ↥L => ((φ ⟨l, hl⟩ : ↥L) : Γ)) hy
  simpa [MulAut.conj_apply, Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_mul,
    Subgroup.coe_inv] using h.symm

private lemma exists_inner_lift {Γ : Type} [Group Γ] [Finite Γ] {L : Subgroup Γ}
    (hcenter : Subgroup.center ↥L = ⊥) (hout : Nat.card (Outer ↥L) ∣ 2) {g : Γ}
    (hg : g ∈ Subgroup.normalizer (L : Set Γ)) (hg3 : g ^ 3 = 1) :
    ∃ y : ↥L, MulAut.conj y = L.normalizerMonoidHom ⟨g, hg⟩ ∧ y ^ 3 = 1 := by
  let α : MulAut ↥L := L.normalizerMonoidHom ⟨g, hg⟩
  have hα3 : α ^ 3 = 1 := by
    change (L.normalizerMonoidHom ⟨g, hg⟩) ^ 3 = 1
    rw [← map_pow]
    have h : (⟨g, hg⟩ : Subgroup.normalizer (L : Set Γ)) ^ 3 = 1 := by
      apply Subtype.ext
      exact hg3
    rw [h, map_one]
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers α)) (Nat.card (Outer ↥L)) := by
    rw [Nat.card_zpowers]
    exact (Nat.Coprime.of_dvd_left (orderOf_dvd_of_pow_eq_one hα3) (by decide)).of_dvd_right hout
  have hinner : α ∈ inner ↥L :=
    CFSG.LieType.SeitzGeneration.le_inner_of_coprime_card_outer hcop
      (Subgroup.mem_zpowers α)
  obtain ⟨y, hy⟩ := hinner
  refine ⟨y, hy, ?_⟩
  have hconj : MulAut.conj (y ^ 3) = 1 := by
    rw [map_pow, hy, hα3]
  have hz : y ^ 3 ∈ (MulAut.conj : ↥L →* MulAut ↥L).ker := by
    rw [MonoidHom.mem_ker]
    exact hconj
  rw [CFSG.GroupTheory.ker_conj_eq_center, hcenter] at hz
  simpa using hz

private lemma mem_centralizer_A_of_inner_lift {Γ : Type} [Group Γ] [Finite Γ]
    {L : Subgroup Γ} {A : Subgroup Γ} (hAel : IsElemAbelian 3 A)
    (hAN : A ≤ Subgroup.normalizer (L : Set Γ))
    (hcenter : Subgroup.center ↥L = ⊥) (hout : Nat.card (Outer ↥L) ∣ 2)
    {a : Γ} (ha : a ∈ A) (haN : a ∈ Subgroup.normalizer (L : Set Γ))
    {y : ↥L} (hyconj : MulAut.conj y = L.normalizerMonoidHom ⟨a, haN⟩) :
    (y : Γ) ∈ Subgroup.centralizer (A : Set Γ) := by
  haveI : IsMulCommutative ↥A := hAel.1
  rw [Subgroup.mem_centralizer_iff]
  intro a' ha'
  have ha'N : a' ∈ Subgroup.normalizer (L : Set Γ) := hAN ha'
  have ha'3 : a' ^ 3 = 1 := hAel.2 a' ha'
  obtain ⟨y', hy'conj, -⟩ := exists_inner_lift hcenter hout ha'N ha'3
  have hgg : (⟨a', ha'N⟩ : Subgroup.normalizer (L : Set Γ)) * ⟨a, haN⟩ *
      ⟨a', ha'N⟩⁻¹ = ⟨a, haN⟩ := by
    apply Subtype.ext
    change a' * a * a'⁻¹ = a
    have hc : a' * a = a * a' := congrArg Subtype.val (mul_comm' (⟨a', ha'⟩ : ↥A) ⟨a, ha⟩)
    rw [hc]
    group
  have hαeq : L.normalizerMonoidHom ⟨a', ha'N⟩ * L.normalizerMonoidHom ⟨a, haN⟩ *
      (L.normalizerMonoidHom ⟨a', ha'N⟩)⁻¹ = L.normalizerMonoidHom ⟨a, haN⟩ := by
    rw [← map_inv, ← map_mul, ← map_mul, hgg]
  have hz : MulAut.conj (y' * y * y'⁻¹ * y⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hy'conj, hyconj, hαeq, mul_inv_cancel]
  have hz1 : y' * y * y'⁻¹ * y⁻¹ = 1 := by
    have hmem : y' * y * y'⁻¹ * y⁻¹ ∈ (MulAut.conj : ↥L →* MulAut ↥L).ker := by
      rw [MonoidHom.mem_ker]
      exact hz
    rw [CFSG.GroupTheory.ker_conj_eq_center, hcenter] at hmem
    simpa using hmem
  have hy'y : y' * y * y'⁻¹ = y := by
    have h := congrArg (fun z : ↥L => z * y) hz1
    simpa [mul_assoc] using h
  have hconj' : a' * (y : Γ) * a'⁻¹ = (y' : Γ) * (y : Γ) * (y' : Γ)⁻¹ :=
    conj_eq_of_inner_lift ha'N hy'conj y.2
  have hy'yΓ : (y' : Γ) * (y : Γ) * (y' : Γ)⁻¹ = (y : Γ) := by
    simpa using congrArg Subtype.val hy'y
  rw [hy'yΓ] at hconj'
  exact mul_inv_eq_iff_eq_mul.mp hconj'

private lemma mul_inv_mem_centralizer_L_of_inner_lift {Γ : Type} [Group Γ]
    {L : Subgroup Γ} {a : Γ} (haN : a ∈ Subgroup.normalizer (L : Set Γ))
    {y : ↥L} (hyconj : MulAut.conj y = L.normalizerMonoidHom ⟨a, haN⟩) :
    a * (y : Γ)⁻¹ ∈ Subgroup.centralizer (L : Set Γ) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hu : (y : Γ)⁻¹ * l * (y : Γ) ∈ L :=
    L.mul_mem (L.mul_mem (L.inv_mem y.2) hl) y.2
  have hkey : a * (y : Γ)⁻¹ * l * (y : Γ) * a⁻¹ = l := by
    have h := conj_eq_of_inner_lift haN hyconj hu
    simpa [mul_assoc] using h
  have hcomm : (a * (y : Γ)⁻¹) * l = l * (a * (y : Γ)⁻¹) := by
    have h := congrArg (fun z => z * (a * (y : Γ)⁻¹)) hkey
    simpa [mul_assoc] using h
  exact hcomm.symm

private lemma conj_mem_normalizer_stdLayerD {F : Type} [Field F] {σ : F ≃+* F}
    {A : Subgroup (Γ₂ F)} (hAel : IsElemAbelian 3 A)
    (hAL : A ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA5 ⊔
      twistedE6DiagGL F σ)
    {d : Γ₂ F} (hdA : d ∈ A) {a : Γ₂ F} (ha : a ∈ A) :
    (stdLayerD (twistedE6RootGroup F σ) d).map (MulAut.conj a).toMonoidHom =
      stdLayerD (twistedE6RootGroup F σ) d := by
  haveI : IsMulCommutative ↥A := hAel.1
  have hN : A ≤ Subgroup.normalizer (twistedE6RootGroup F σ : Set (Γ₂ F)) :=
    hAL.trans (sup_le
      ((graphFixedParabolicLevi_le (t := TwistTag.E6) (K := F) (σ := σ.toRingHom)
        (J := twE6MaxA5)).trans Subgroup.le_normalizer)
      (le_sup_right.trans (twistedE6InndiagGL_le_normalizer F σ)))
  have hC0 : (twistedE6RootGroup F σ).map (MulAut.conj a).toMonoidHom =
      twistedE6RootGroup F σ :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hN ha)
  have hdc : (MulAut.conj a) d = d := by
    rw [MulAut.conj_apply]
    have hc : a * d = d * a := congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥A) ⟨d, hdA⟩)
    rw [hc]
    group
  have hCd : (Subgroup.centralizer ({d} : Set (Γ₂ F))).map (MulAut.conj a).toMonoidHom =
      Subgroup.centralizer ({d} : Set (Γ₂ F)) := by
    rw [CFSG.centralizer_singleton_map (MulAut.conj a) d, hdc]
  have hX : (twistedE6RootGroup F σ ⊓ Subgroup.centralizer ({d} : Set (Γ₂ F))).map
      (MulAut.conj a).toMonoidHom =
      twistedE6RootGroup F σ ⊓ Subgroup.centralizer ({d} : Set (Γ₂ F)) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj a).injective, hC0, hCd]
  have hXinv : (twistedE6RootGroup F σ ⊓ Subgroup.centralizer ({d} : Set (Γ₂ F))).map
      ((MulAut.conj a)⁻¹).toMonoidHom =
      twistedE6RootGroup F σ ⊓ Subgroup.centralizer ({d} : Set (Γ₂ F)) := by
    have h := congrArg (Subgroup.map ((MulAut.conj a)⁻¹).toMonoidHom) hX
    rw [Subgroup.map_map] at h
    have hcomp : ((MulAut.conj a)⁻¹).toMonoidHom.comp (MulAut.conj a).toMonoidHom =
        MonoidHom.id (Γ₂ F) := by
      apply MonoidHom.ext
      intro x
      exact MulAut.inv_apply_self (M := Γ₂ F) (MulAut.conj a) x
    rw [hcomp, Subgroup.map_id] at h
    exact h.symm
  have hle : (stdLayerD (twistedE6RootGroup F σ) d).map (MulAut.conj a).toMonoidHom ≤
      stdLayerD (twistedE6RootGroup F σ) d :=
    CFSG.LocalAnalysis.GLTheoremA.I142N.map_GLALayer_le_of_eq (MulAut.conj a) hX
  have hleinv : (stdLayerD (twistedE6RootGroup F σ) d).map
      ((MulAut.conj a)⁻¹).toMonoidHom ≤ stdLayerD (twistedE6RootGroup F σ) d :=
    CFSG.LocalAnalysis.GLTheoremA.I142N.map_GLALayer_le_of_eq (MulAut.conj a)⁻¹ hXinv
  refine le_antisymm hle ?_
  intro x hx
  exact Subgroup.mem_map.mpr
    ⟨((MulAut.conj a)⁻¹) x, hleinv (Subgroup.mem_map_of_mem _ hx),
      MulAut.apply_inv_self (M := Γ₂ F) (MulAut.conj a) x⟩

private lemma le_normalizer_stdLayerD {F : Type} [Field F] {σ : F ≃+* F}
    {A : Subgroup (Γ₂ F)} (hAel : IsElemAbelian 3 A)
    (hAL : A ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA5 ⊔
      twistedE6DiagGL F σ)
    {d : Γ₂ F} (hdA : d ∈ A) :
    A ≤ Subgroup.normalizer (stdLayerD (twistedE6RootGroup F σ) d : Set (Γ₂ F)) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact conj_mem_normalizer_stdLayerD hAel hAL hdA ha

theorem inner_of_card_outer_dvd_two {F : Type} [Field F] [Finite F] {σ : F ≃+* F}
    {A : Subgroup (Γ₂ F)} (hAel : IsElemAbelian 3 A)
    (hAL : A ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA5 ⊔
      twistedE6DiagGL F σ)
    {d : Γ₂ F} (hdA : d ∈ A)
    (hout : Nat.card (Outer ↥(stdLayerD (twistedE6RootGroup F σ) d)) ∣ 2)
    (hcenter : Subgroup.center ↥(stdLayerD (twistedE6RootGroup F σ) d) = ⊥) :
    ∀ a ∈ A, ∃ y ∈ stdLayerD (twistedE6RootGroup F σ) d, y ^ 3 = 1 ∧
      y ∈ Subgroup.centralizer (A : Set (Γ₂ F)) ∧
      a * y⁻¹ ∈ Subgroup.centralizer
        (stdLayerD (twistedE6RootGroup F σ) d : Set (Γ₂ F)) := by
  haveI : Finite (Γ₂ F) := finite_modGL
  have hAN := le_normalizer_stdLayerD hAel hAL hdA
  intro a ha
  have haN : a ∈ Subgroup.normalizer
      (stdLayerD (twistedE6RootGroup F σ) d : Set (Γ₂ F)) := hAN ha
  obtain ⟨y, hyconj, hy3⟩ := exists_inner_lift hcenter hout haN (hAel.2 a ha)
  exact ⟨(y : Γ₂ F), y.2, by simpa using congrArg Subtype.val hy3,
    mem_centralizer_A_of_inner_lift hAel hAN hcenter hout ha haN hyconj,
    mul_inv_mem_centralizer_L_of_inner_lift haN hyconj⟩

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
