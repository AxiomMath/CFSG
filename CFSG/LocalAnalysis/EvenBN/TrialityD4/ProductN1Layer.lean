module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductN1Hat
public import CFSG.LocalAnalysis.EvenBN.GMSK.LayerListK
public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialClosuresLift
public import CFSG.LocalAnalysis.EvenBN.GMSK.ConsumerSections
public import CFSG.LocalAnalysis.EvenBN.TwoF4.BenderOutcomesExclusions
public import CFSG.LocalAnalysis.SteinbergBKOddNormalQuotientStandard
public import CFSG.LocalAnalysis.EvenBN.GMSK.SL2Facts
public import CFSG.LocalAnalysis.EvenBN.GMS.NormalForms
public import CFSG.LocalAnalysis.EvenBN.GMSK.LayerRankOne
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCCOddNormalCore
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusNine
public import CFSG.LocalAnalysis.EvenBN.Common.CoprimeQuotient
public import CFSG.Walter.J1.BenderLemma
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModels
public import CFSG.LocalAnalysis.ComponentClassification.OddSelector
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIL3
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCaseB
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdFamilies
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLAllInvolutions
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponent
public import CFSG.LocalAnalysis.OddStandard.Seitz77U
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterExc
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusion
public import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
public import CFSG.Monster.B.TwoA.Base.FourNorm
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.BRANCH.RankG2
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.Bridge.BOrder
public import CFSG.Sporadic.Bridge.BSurjInputs
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.HeldB.OuterFixed
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.ON.SimpleBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.Sporadic.Th.CertificateBase1
public import CFSG.Sporadic.ThSchreier.KernelAutBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase1
public import CFSG.Sporadic.ThSchreier.ThSchreierCase
public import CFSG.StronglyEmbedded.BenderUnitaryBorel
public import CFSG.YGroups.Y443.Native.Parabolic2CheckB
public import CFSG.YGroups.Y443.Native.Parabolic2CheckW
public import Certificates.Certificate10095
public import Certificates.Certificate10095Base
public import Certificates.Certificate10100
public import Certificates.Certificate10101
public import Certificates.Certificate10102
public import Certificates.Certificate10104
public import Certificates.Certificate2323
public import Certificates.Certificate3085Base
public import Certificates.Certificate9201

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.EvenBN.Common
open CFSG.ABGLocalTools (IsSylowOf)
open scoped MatrixGroups

section Defs

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {q : ℕ}

@[expose] noncomputable def xBar (d : TrialityD4Data L q) (t : G) : Subgroup (H1bar d t) :=
  normalClosure ((kBar d t : Subgroup (H1bar d t)) : Set (H1bar d t))

@[expose] noncomputable def nOneBar (d : TrialityD4Data L q) (t : G) : Subgroup (H1bar d t) :=
  (CFSG.perfectResidual ↥(xBar d t)).map (xBar d t).subtype

@[expose] noncomputable def nOne (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  NormalizerQuotient.lift (nOneBar d t)

structure IsN1Factor (d : TrialityD4Data L q) (t : G) (K₁ : Subgroup G) : Prop where
  D₅_le : yamadaD₅ d t ≤ K₁
  sup_eq : nOne d t = K₁ ⊔ K₁ᵍ[t]
  inf_eq : K₁ ⊓ K₁ᵍ[t] = yamadaD₅ d t
  comm_le : ⁅K₁, K₁ᵍ[t]⁆ ≤ yamadaD₅ d t
  iso : IsQuotientIso K₁ (yamadaD₅ d t) (SL(2, d.Γ))

end Defs

section Aux

open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialLayer

namespace ProductN1LayerAux

theorem not_isSimpleGroup_prod_self {N B : Type*} [Group N] [Group B] [Nontrivial B]
    [IsSimpleGroup N] (e : N ≃* B × B) : False := by
  have hn : ((⊤ : Subgroup B).prod (⊥ : Subgroup B)).Normal := inferInstance
  have hn' : (((⊤ : Subgroup B).prod (⊥ : Subgroup B)).comap e.toMonoidHom).Normal :=
    hn.comap e.toMonoidHom
  obtain ⟨b, hb⟩ := exists_ne (1 : B)
  haveI := hn'
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (((⊤ : Subgroup B).prod (⊥ : Subgroup B)).comap e.toMonoidHom) with h | h
  · have hmem : e.symm (b, 1) ∈ ((⊤ : Subgroup B).prod (⊥ : Subgroup B)).comap e.toMonoidHom := by
      simp [Subgroup.mem_prod]
    rw [h, Subgroup.mem_bot] at hmem
    apply hb
    have := congrArg e hmem
    simpa using this
  · have hmem : e.symm (1, b) ∈ ((⊤ : Subgroup B).prod (⊥ : Subgroup B)).comap e.toMonoidHom := by
      rw [h]; trivial
    simp [Subgroup.mem_prod] at hmem
    exact hb hmem

theorem closureSelection_of_layerList
    (hGMS : GMSK.GMSLinearStandardLayerListKRankOneStatement)
    {M : Type} [Group M] [Finite M] (hM : CFSG.SectionRank.IsKGroupCat M)
    {A : Subgroup M} {n : ℕ} (hn : 4 ≤ n) {k : Type} [Field k] [Fintype k]
    (hk : Fintype.card k = 2 ^ n) (α : A ≃* SL(2, k)) {τ : M} (hτ : orderOf τ = 2)
    (hAτ : A ≤ centralizer ({τ} : Set M))
    (hAn : (A.subgroupOf (centralizer ({τ} : Set M))).Normal)
    (hsyl : ∃ S : Sylow 2 ↥(centralizer (A : Set M) ⊓ centralizer ({τ} : Set M)),
      (S : Subgroup _).map (centralizer (A : Set M) ⊓ centralizer ({τ} : Set M)).subtype =
        zpowers τ)
    {V : Subgroup M} (hV2 : ∀ v ∈ V, v * v = 1) (hVcard : Nat.card V = (2 ^ n) ^ 2)
    (hVA : V ≤ normalClosure (A : Set M)) (hτV : τ ∈ normalizer (V : Set M)) :
    ClosureSelection A α τ V n := by
  unfold ClosureSelection
  intro R π
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn2 : 2 ≤ n := by omega
  have hR : Odd (Nat.card R) := GMSK.odd_card_standardComponentOddCore M
  have h2 : (2 : k) = 0 := GMSK.two_eq_zero_of_card (by omega) hk
  have hk4 : 4 ≤ Fintype.card k :=
    hk ▸ (Nat.pow_le_pow_right (by norm_num) hn2 : 2 ^ 2 ≤ 2 ^ n)
  have : IsSimpleGroup SL(2, k) := GMSK.sl2_isSimpleGroup h2 hk4
  have : IsSimpleGroup A := α.isSimpleGroup
  have hnab : ∃ x y : A, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := GMSK.sl2_exists_mul_ne (K := k)
    exact ⟨α.symm x, α.symm y, fun e => hxy (by simpa using congrArg α e)⟩
  have hE : ∃ E : Subgroup M, E ≤ A ∧ CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 4 := by
    obtain ⟨E, hE, hE4⟩ := GMSK.exists_elementaryAbelian_four h2
      (hk ▸ pow_dvd_pow 2 hn2 : 2 ^ 2 ∣ Fintype.card k)
    set f : Multiplicative k →* M := A.subtype.comp (α.symm.toMonoidHom.comp (GMSK.sl2Upper k))
    have hf : Function.Injective f :=
      A.subtype_injective.comp (α.symm.injective.comp GMSK.sl2Upper_injective)
    have hEf : CFSG.IsElementaryAbelian 2 (E.map f) := CFSG.IsElementaryAbelian.map f
    refine ⟨E.map f, ?_, ⟨hEf.toIsMulCommutative, fun x hx =>
      CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩, by rw [card_map_of_injective hf, hE4]⟩
    rintro _ ⟨x, -, rfl⟩
    exact (α.symm (GMSK.sl2Upper k x)).2
  obtain ⟨hinjA, hinj2, hθτ, -, -, hAθ, -, -, -, -, -, -⟩ :=
    CFSG.LocalAnalysis.SteinbergBK.simple_involution_centralizer_odd_normal_quotient_standardness
      hnab hE hτ hAτ hAn hsyl R hR
  have hVinj := hinj2 V (isPGroup_of_mul_self hV2)
  have hVcard' : Nat.card (V.map π) = (2 ^ n) ^ 2 := by rw [card_map_of_injOn π hVinj, hVcard]
  let ιA : A ≃* A.map π := MulEquiv.ofBijective (π.subgroupMap A)
    ⟨fun x y hxy => Subtype.ext (hinjA x.2 y.2 (congrArg Subtype.val hxy)),
      π.subgroupMap_surjective A⟩
  have hιA : ∀ a : A, (ιA a : M ⧸ R) = π a := fun _ => rfl
  let αA : A.map π ≃* SL(2, k) := ιA.symm.trans α
  have hαA : ∀ a : A, αA (ιA a) = α a := fun a => by simp [αA]
  have hNC : (normalClosure (A : Set M)).map π =
      normalClosure ((A.map π : Subgroup (M ⧸ R)) : Set (M ⧸ R)) := by
    rw [map_normalClosure _ _ (QuotientGroup.mk'_surjective R), ← coe_map]
  have hVN : V.map π ≤ normalClosure ((A.map π : Subgroup (M ⧸ R)) : Set (M ⧸ R)) :=
    hNC ▸ map_mono hVA
  have hnn : ¬ (A.map π).Normal := by
    intro hN
    have hle : V.map π ≤ A.map π := hVN.trans (normalClosure_le_normal le_rfl)
    have hd := card_dvd_of_le hle
    rw [hVcard', card_map_of_injOn π hinjA, Nat.card_congr α.toEquiv,
      CFSG.CGT.Timmesfeld75.card_sl2, Nat.card_eq_fintype_card, hk] at hd
    have hq0 : 0 < 2 ^ n := by positivity
    have h1 : 2 ^ n ∣ (2 ^ n) ^ 2 - 1 :=
      Nat.dvd_of_mul_dvd_mul_left hq0 (by rw [← pow_two]; exact hd)
    have h3 : 2 ∣ (2 ^ n) ^ 2 - 1 := (dvd_pow_self 2 (by omega)).trans h1
    have h4 : 2 ∣ (2 ^ n) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
    have h5 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ hq0
    omega
  obtain ⟨hstd, hsylq⟩ := GMSK.stdLinearData_odd_quotient hn2 hk α hτ hAτ hAn hsyl R hR hnn
  have hπτ : π τ ∈ centralizer ((A.map π : Subgroup (M ⧸ R)) : Set (M ⧸ R)) :=
    mem_centralizer_iff.mpr fun x hx => mem_centralizer_singleton_iff.mp (hAθ hx)
  have hodd := not_two_dvd_relIndex_of_sylow hsylq hπτ hθτ
  obtain ⟨-, -, hAL, hDE, hCE, halt, -⟩ := GMSK.oneOrTwoLayer_of_stdLinearData
    (GMSK.standardComponentOddCore_quotient_eq_bot M) hstd hθτ hπτ hodd
  have hττ : π τ * π τ = 1 := by rw [← sq, ← hθτ, pow_orderOf_eq_one]
  have hτ1 : π τ ≠ 1 := fun h => by rw [h, orderOf_one] at hθτ; omega
  refine ⟨by rw [← hDE]; exact hCE, hDE.symm.trans hNC.symm, hDE ▸ hVN, hinj2, ?_⟩
  have hLO := hGMS (M ⧸ R) (hM.quotient R) (GMSK.standardComponentOddCore_quotient_eq_bot M) n
    (A.map π) hstd hsylq
  unfold GMSK.LayerOutcome at hLO
  rw [← hDE] at hLO
  rw [← hDE]
  set N := normalClosure ((A.map π : Subgroup (M ⧸ R)) : Set (M ⧸ R)) with hNdef
  have hexcl : ∀ (k₂ : Type) (_ : Field k₂) (_ : Fintype k₂), Fintype.card k₂ = (2 ^ n) ^ 2 →
      (N ≃* SL(2, k) × SL(2, k)) → (N ≃* SL(2, k₂)) → False := by
    intro k₂ _ _ hk₂ ψ₁ ψ₂
    have hk₂' : Nat.card k₂ = 2 ^ (2 * n) := by
      rw [Nat.card_eq_fintype_card, hk₂, ← pow_mul, mul_comm]
    exact (GMS.isEmpty_mulEquiv_sl2_prod (k := k) (by omega) hk₂').false (ψ₂.symm.trans ψ₁)
  rcases halt with ⟨⟨hDs, -, hAD, hnt⟩, -⟩ |
    ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ψ, hψ₁, hψ₂⟩, -⟩
  ·
    have := hDs
    set E' : Subgroup N := (V.map π).subgroupOf N with hE'
    have hE'2 : ∀ x ∈ E', x * x = 1 := by
      intro x hx
      obtain ⟨v, hv, hvx⟩ := mem_subgroupOf.mp hx
      apply Subtype.ext
      rw [coe_mul, ← hvx, ← map_mul, hV2 v hv, map_one]
      rfl
    have hE'card : Nat.card E' = (2 ^ n) ^ 2 := by
      rw [hE', Nat.card_congr (subgroupOfEquivOfLe hVN).toEquiv, hVcard']
    have hq : 2 ^ n < (2 ^ n) ^ 2 := by
      have : 4 ≤ 2 ^ n := (Nat.pow_le_pow_right (by norm_num) hn2 : 2 ^ 2 ≤ 2 ^ n)
      nlinarith
    have hk' : Nat.card k = 2 ^ n := by rw [Nat.card_eq_fintype_card, hk]
    have hτV' : π τ ∈ normalizer ((V.map π : Subgroup (M ⧸ R)) : Set (M ⧸ R)) :=
      le_normalizer_map π ⟨τ, hτV, rfl⟩
    rcases hLO with hAA | ⟨hL2 | hU3 | hL3⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    ·
      exfalso
      obtain ⟨e⟩ := hAA
      haveI : Nontrivial (A.map π) := αA.toEquiv.nontrivial
      exact not_isSimpleGroup_prod_self e
    ·
      obtain ⟨F, _, _, _, -, ⟨ψ₀⟩⟩ := exists_sl2_of_lieModel (by omega) hL2
      have hnabA : ∃ x y : A.map π, x * y ≠ y * x := by
        obtain ⟨x, y, hxy⟩ := hnab
        exact ⟨ιA x, ιA y, fun e => hxy (ιA.injective (by rw [map_mul, map_mul, e]))⟩
      have hout := conjNormal_not_mem_range hCE hτ1 hττ hAD.le hAθ hnabA ψ₀
      have h2 := alternative_two_of_lieModel hn2 hττ hAD.le hAθ hk αA hL2 hout
      refine Or.inr ⟨h2, ?_⟩
      rintro ⟨ψ₁, -⟩
      obtain ⟨k₂, _, _, hk₂, ψ₂, -⟩ := h2
      exact hexcl k₂ inferInstance inferInstance hk₂ ψ₁ ψ₂
    ·
      have h1 := TwoF4.card_le_of_lieModel_PSU3 hU3 hE'2
      rw [hE'card] at h1
      exact absurd h1 (not_le.mpr hq)
    · exact (false_of_lieModel_PSL3 hττ (by omega) hL3 hnt hAD.le hAθ hk' αA hVN
        (fun x hx => by
          obtain ⟨v, hv, rfl⟩ := hx
          rw [← map_mul, hV2 v hv, map_one])
        (by rw [hVcard', ← pow_mul, mul_comm]) hτV').elim
    · omega
    · omega
  ·
    let ψ' : N ≃* SL(2, k) × SL(2, k) := ψ.trans (MulEquiv.prodCongr αA αA)
    have hψ' : ∀ x : N, ψ' x = ((αA (ψ x).1), (αA (ψ x).2)) := fun _ => rfl
    have h1 : ∃ ψ : N ≃* SL(2, k) × SL(2, k),
        (∀ (a : A) (x : N), (x : M ⧸ R) = π a → ψ x = (α a, α a)) ∧
        ∀ x y : N, (y : M ⧸ R) = (π τ)⁻¹ * x * π τ → ψ y = (ψ x).swap := by
      refine ⟨ψ', fun a x hxa => ?_, fun x y hyx => ?_⟩
      · have hx : x = ⟨π a, hxa ▸ x.2⟩ := Subtype.ext hxa
        rw [hψ', hx, hψ₁ (π a) ⟨a, a.2, rfl⟩ (hxa ▸ x.2)]
        exact Prod.ext (hαA a) (hαA a)
      · have hy : y = ⟨(π τ)⁻¹ * x * π τ, hyx ▸ y.2⟩ := Subtype.ext hyx
        rw [hψ', hψ', hy, hψ₂ x x.2 (hyx ▸ y.2)]
        rfl
    refine Or.inl ⟨h1, ?_⟩
    rintro ⟨k₂, _, _, hk₂, ψ₂, -⟩
    exact hexcl k₂ inferInstance inferInstance hk₂ ψ' ψ₂

theorem exactClosure_of_layerList
    (hGMS : GMSK.GMSLinearStandardLayerListKRankOneStatement)
    {M : Type} [Group M] [Finite M] (hM : CFSG.SectionRank.IsKGroupCat M)
    {A : Subgroup M} {n : ℕ} (hn : 4 ≤ n) {k : Type} [Field k] [Fintype k]
    (hk : Fintype.card k = 2 ^ n) (α : A ≃* SL(2, k)) {τ : M} (hτ : orderOf τ = 2)
    (hAτ : A ≤ centralizer ({τ} : Set M))
    (hAn : (A.subgroupOf (centralizer ({τ} : Set M))).Normal)
    (hsyl : ∃ S : Sylow 2 ↥(centralizer (A : Set M) ⊓ centralizer ({τ} : Set M)),
      (S : Subgroup _).map (centralizer (A : Set M) ⊓ centralizer ({τ} : Set M)).subtype =
        zpowers τ)
    {V : Subgroup M} (hV2 : ∀ v ∈ V, v * v = 1) (hVcard : Nat.card V = (2 ^ n) ^ 2)
    (hVA : V ≤ normalClosure (A : Set M)) (hτV : τ ∈ normalizer (V : Set M))
    (hcomm_ne : closure {x | ∃ v ∈ V, x = v⁻¹ * (τ⁻¹ * v * τ)} ≠ ⊥)
    (hcomm_le : closure {x | ∃ v ∈ V, x = v⁻¹ * (τ⁻¹ * v * τ)} ≤ A) :
    Group.IsPerfect (normalClosure (A : Set M)) ∧
      ⁅CFSG.Open.standardComponentOddCore M, normalClosure (A : Set M)⁆ = ⊥ ∧
      ClosureSelection A α τ V n ∧ ExactClosure A α τ V n := by
  classical
  have hn2 : 2 ≤ n := by omega
  have hsel := closureSelection_of_layerList hGMS hM hn hk α hτ hAτ hAn hsyl hV2 hVcard hVA hτV
  have h2 : (2 : k) = 0 := GMSK.two_eq_zero_of_card (by omega) hk
  have hk4 : 4 ≤ Fintype.card k :=
    hk ▸ (Nat.pow_le_pow_right (by norm_num) hn2 : 2 ^ 2 ≤ 2 ^ n)
  have : IsSimpleGroup SL(2, k) := GMSK.sl2_isSimpleGroup h2 hk4
  have : IsSimpleGroup A := α.isSimpleGroup
  have hnab : ∃ x y : A, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := GMSK.sl2_exists_mul_ne (K := k)
    exact ⟨α.symm x, α.symm y, fun e => hxy (by simpa using congrArg α e)⟩
  have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
    intro x hx y hy
    have hxy := hV2 _ (mul_mem hx hy)
    have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hV2 x hx)
    have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hV2 y hy)
    calc x * y = y⁻¹ * x⁻¹ := by rw [← mul_inv_rev, inv_eq_of_mul_eq_one_right hxy]
      _ = y * x := by rw [hx', hy']
  have : CFSG.IsElementaryAbelian 2 V :=
    CFSG.IsElementaryAbelian.two_of_forall_mul_self hVcomm hV2
  obtain ⟨hperf, hcent, -⟩ :=
    ComponentInitial.elementary_involution_commutator_centralizes_odd_normal_core
      (L := normalClosure (A : Set M)) hτ hnab hAτ hAn hτV hcomm_ne hcomm_le rfl
  have hcent' : ⁅CFSG.Open.standardComponentOddCore M, normalClosure (A : Set M)⁆ = ⊥ :=
    hcent _ inferInstance (GMSK.odd_card_standardComponentOddCore M)
  exact ⟨hperf, hcent', hsel, exactClosure_of_selection hn2 hk α hsel hperf hcent' hVcard hVA⟩

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem t_mem_normalizer_D₅ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    t ∈ normalizer (yamadaD₅ d t : Set G) :=
  h.t_mem_normalizer_yamadaD₅_C9 d

theorem tBar_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    tBar d t = NormalizerQuotient.proj (yamadaD₅ d t) ⟨t, t_mem_normalizer_D₅ h d⟩ := by
  unfold tBar
  rw [dif_pos (t_mem_normalizer_D₅ h d)]

theorem cLV_le_centralizer_t (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    cLV d ≤ centralizer ({t} : Set G) := by
  rintro _ ⟨l, -, rfl⟩
  exact h.L_le_centralizer l.2

theorem S_le_cLV (d : TrialityD4Data L (2 ^ f)) : d.S.map L.subtype ≤ cLV d :=
  map_mono d.S_le_centralizer_V

theorem J₆_le_cLV (d : TrialityD4Data L (2 ^ f)) : d.J₆.map L.subtype ≤ cLV d :=
  map_mono (d.J₆_le_leviShort.trans d.leviShort_le_centralizer_V)

theorem normalizer_D₅_ne_top (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) : normalizer (yamadaD₅ d t : Set G) ≠ ⊤ := by
  intro htop
  have hf := hp.two_le
  have hN : (yamadaD₅ d t).Normal := normalizer_eq_top_iff.1 htop
  obtain ⟨-, -, -, -, -, -, -, hD, -, hP, -⟩ := T4_series_free h d hp
  have hq : 1 < (2 ^ f) ^ 18 :=
    Nat.one_lt_pow (by norm_num) (Nat.one_lt_pow (by omega) (by norm_num))
  have := h.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (yamadaD₅ d t) with hb | ht
  · rw [hb, Subgroup.card_bot] at hD
    omega
  · have hle : Nat.card (yamadaP d t) ≤ Nat.card G :=
      Nat.card_le_card_of_injective _ Subtype.val_injective
    rw [ht, Subgroup.card_top] at hD
    rw [hD] at hle
    have : (2 ^ f) ^ 18 < (2 ^ f) ^ 24 :=
      Nat.pow_lt_pow_right (Nat.one_lt_pow (by omega) (by norm_num)) (by norm_num)
    omega

theorem isKGroupCat_H1bar (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) : CFSG.SectionRank.IsKGroupCat (H1bar d t) :=
  CFSG.LocalAnalysis.EvenBN.GMSK.isKGroupCat_of_section_of_kProper h.kproper
    (normalizer_D₅_ne_top h d hp) _

theorem kBar_le_centralizer_tBar (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) : kBar d t ≤ centralizer ({tBar d t} : Set (H1bar d t)) := by
  rintro _ ⟨⟨x, hxN⟩, hx, rfl⟩
  have hxc : x ∈ cLV d := hx
  have hxt : x * t = t * x := mem_centralizer_singleton_iff.1 (cLV_le_centralizer_t h d hxc)
  rw [tBar_eq h d, mem_centralizer_singleton_iff]
  change NormalizerQuotient.proj _ _ * NormalizerQuotient.proj _ _ =
    NormalizerQuotient.proj _ _ * NormalizerQuotient.proj _ _
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hxt

theorem mem_cLV_iff (d : TrialityD4Data L (2 ^ f)) {x : G} :
    x ∈ cLV d ↔ ∃ hx : x ∈ L, (⟨x, hx⟩ : L) ∈ centralizer (d.V : Set L) := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l.2, hl⟩
  · rintro ⟨hx, hc⟩
    exact ⟨⟨x, hx⟩, hc, rfl⟩

theorem conj_mem_cLV (d : TrialityD4Data L (2 ^ f)) {γ x : G}
    (hγL : γ ∈ normalizer (L : Set G))
    (hγV : γ ∈ normalizer ((d.V.map L.subtype : Subgroup G) : Set G))
    (hx : x ∈ cLV d) : γ * x * γ⁻¹ ∈ cLV d := by
  obtain ⟨hxL, hxc⟩ := (mem_cLV_iff d).1 hx
  have hL' : γ * x * γ⁻¹ ∈ L := (mem_normalizer_iff.1 hγL x).1 hxL
  refine (mem_cLV_iff d).2 ⟨hL', mem_centralizer_iff.2 fun v hv => ?_⟩
  have hvG : (v : G) ∈ (d.V.map L.subtype : Subgroup G) := ⟨v, hv, rfl⟩
  have hw : γ⁻¹ * (v : G) * γ ∈ (d.V.map L.subtype : Subgroup G) := by
    have := (mem_normalizer_iff.1 (inv_mem hγV) (v : G)).1 hvG
    simpa using this
  obtain ⟨w, hwV, hwe⟩ := hw
  have hcw := mem_centralizer_iff.1 hxc w hwV
  have hcw' : (w : G) * x = x * (w : G) := congrArg Subtype.val hcw
  apply Subtype.ext
  change (v : G) * (γ * x * γ⁻¹) = γ * x * γ⁻¹ * (v : G)
  have hwe' : (w : G) = γ⁻¹ * (v : G) * γ := hwe
  have hv' : (v : G) = γ * (w : G) * γ⁻¹ := by rw [hwe']; group
  rw [hv']
  calc γ * (w : G) * γ⁻¹ * (γ * x * γ⁻¹) = γ * ((w : G) * x) * γ⁻¹ := by group
    _ = γ * (x * (w : G)) * γ⁻¹ := by rw [hcw']
    _ = _ := by group

theorem kBar_normal_in_centralizer_tBar (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hC : centralizer ({tBar d t} : Set (H1bar d t)) =
      NormalizerQuotient.bar (yamadaD₅ d t)
        (centralizer ({t} : Set G) ⊓ normalizer ((d.V.map L.subtype : Subgroup G) : Set G))) :
    ((kBar d t).subgroupOf (centralizer ({tBar d t} : Set (H1bar d t)))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_subgroupOf] at hn ⊢
  have hg : (g : H1bar d t) ∈ NormalizerQuotient.bar (yamadaD₅ d t)
      (centralizer ({t} : Set G) ⊓ normalizer ((d.V.map L.subtype : Subgroup G) : Set G)) := by
    rw [← hC]; exact g.2
  obtain ⟨⟨γ, hγN⟩, hγ, hγe⟩ := hg
  obtain ⟨⟨x, hxN⟩, hx, hxe⟩ := hn
  have hγ' : γ ∈ centralizer ({t} : Set G) ⊓
      normalizer ((d.V.map L.subtype : Subgroup G) : Set G) :=
    mem_subgroupOf.1 hγ
  have hx' : x ∈ cLV d := mem_subgroupOf.1 hx
  have hxγ : γ * x * γ⁻¹ ∈ cLV d :=
    conj_mem_cLV d (h.centralizer_le_normalizer hγ'.1) hγ'.2 hx'
  have hgn : ((g * n * g⁻¹ : ↥(centralizer ({tBar d t} : Set (H1bar d t)))) : H1bar d t) =
      NormalizerQuotient.proj (yamadaD₅ d t) (⟨γ, hγN⟩ * ⟨x, hxN⟩ * ⟨γ, hγN⟩⁻¹) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    rw [hγe, hxe]
  show ((g * n * g⁻¹ : ↥(centralizer ({tBar d t} : Set (H1bar d t)))) : H1bar d t) ∈ kBar d t
  rw [hgn]
  exact NormalizerQuotient.proj_mem_bar hxγ

theorem tBar_mem_normalizer_pBar (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) :
    tBar d t ∈ normalizer ((pBar d t : Subgroup (H1bar d t)) : Set (H1bar d t)) := by
  have htP : t ∈ normalizer ((yamadaP d t : Subgroup G) : Set G) :=
    h.t_mem_normalizer_yamadaD₅_sup_QD d hp.layer
  refine mem_normalizer_fintype fun y hy => ?_
  obtain ⟨⟨x, hxN⟩, hx, rfl⟩ := hy
  have hxP : x ∈ yamadaP d t := mem_subgroupOf.1 hx
  rw [tBar_eq h d]
  have : NormalizerQuotient.proj (yamadaD₅ d t) ⟨t, t_mem_normalizer_D₅ h d⟩ *
      NormalizerQuotient.proj (yamadaD₅ d t) ⟨x, hxN⟩ *
      (NormalizerQuotient.proj (yamadaD₅ d t) ⟨t, t_mem_normalizer_D₅ h d⟩)⁻¹ =
      NormalizerQuotient.proj (yamadaD₅ d t)
        (⟨t, t_mem_normalizer_D₅ h d⟩ * ⟨x, hxN⟩ * ⟨t, t_mem_normalizer_D₅ h d⟩⁻¹) := by
    simp only [map_mul, map_inv]
  rw [this]
  exact NormalizerQuotient.proj_mem_bar ((mem_normalizer_iff.1 htP x).1 hxP)

theorem jSixBar_le_kBar (d : TrialityD4Data L (2 ^ f)) : jSixBar d t ≤ kBar d t :=
  NormalizerQuotient.bar_mono (J₆_le_cLV d)

theorem sBar_le_kBar (d : TrialityD4Data L (2 ^ f)) :
    NormalizerQuotient.bar (yamadaD₅ d t) (d.S.map L.subtype) ≤ kBar d t :=
  NormalizerQuotient.bar_mono (S_le_cLV d)

theorem comm_of_sq_eq_one {M : Type*} [Group M] {V : Subgroup M} (hV2 : ∀ v ∈ V, v * v = 1) :
    ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
  intro x hx y hy
  have hxy := hV2 _ (mul_mem hx hy)
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hV2 x hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hV2 y hy)
  calc x * y = y⁻¹ * x⁻¹ := by rw [← mul_inv_rev, inv_eq_of_mul_eq_one_right hxy]
    _ = y * x := by rw [hx', hy']

theorem commutatorWith_gen_mem {M : Type*} [Group M] {V : Subgroup M} {τ : M}
    (hV2 : ∀ v ∈ V, v * v = 1) (hτ2 : τ * τ = 1) (hτV : τ ∈ normalizer (V : Set M)) {v : M}
    (hv : v ∈ V) : v⁻¹ * (τ⁻¹ * v * τ) ∈ V ⊓ centralizer ({τ} : Set M) := by
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ2
  have hu : τ⁻¹ * v * τ ∈ V := by
    have := (mem_normalizer_iff.1 (inv_mem hτV) v).1 hv
    simpa using this
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hV2 v hv)
  have hcomm := comm_of_sq_eq_one hV2
  refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hv) hu, mem_centralizer_singleton_iff.2 ?_⟩
  rw [hτi, hvi]
  have h1 : v * (τ * v * τ) = (τ * v * τ) * v := hcomm v hv _ (by rwa [hτi] at hu)
  calc v * (τ * v * τ) * τ = v * τ * v * (τ * τ) := by group
    _ = v * τ * v := by rw [hτ2, mul_one]
    _ = (τ * τ) * v * τ * v := by rw [hτ2, one_mul]
    _ = τ * ((τ * v * τ) * v) := by group
    _ = τ * (v * (τ * v * τ)) := by rw [h1]

theorem closure_data
    (hGMS : GMSK.GMSLinearStandardLayerListKRankOneStatement)
    (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    ∃ α : ↥(kBar d t) ≃* SL(2, d.Γ),
      Group.IsPerfect ↥(xBar d t) ∧
      ClosureSelection (kBar d t) α (tBar d t) (pBar d t) (3 * f) ∧
      ExactClosure (kBar d t) α (tBar d t) (pBar d t) (3 * f) := by
  classical
  obtain ⟨-, ⟨hC1, hC2, hord⟩, ⟨⟨α⟩, hsyl⟩, ⟨hPel, hPcard, hPfree, hPfix, hSbar, hPcomm⟩⟩ :=
    D1_centralizer_tbar h d hp
  haveI : Fintype d.Γ := Fintype.ofFinite d.Γ
  have hf := hp.two_le
  have hn : 4 ≤ 3 * f := by omega
  have hk : Fintype.card d.Γ = 2 ^ (3 * f) := by
    rw [← Nat.card_eq_fintype_card, d.card_Γ, ← pow_mul, mul_comm]
  have hτ2 : tBar d t * tBar d t = 1 := by
    have := pow_orderOf_eq_one (tBar d t)
    rwa [hord, pow_two] at this
  have hV2 : ∀ v ∈ pBar d t, v * v = 1 := fun v hv => by
    have := hPel.2 v hv
    rwa [pow_two] at this
  have hVcard : Nat.card (pBar d t) = (2 ^ (3 * f)) ^ 2 := by
    rw [hPcard, ← pow_mul, ← pow_mul]; ring_nf
  have hτV := tBar_mem_normalizer_pBar h d hp
  have hxBar : xBar d t = normalClosure ((kBar d t : Subgroup (H1bar d t)) : Set (H1bar d t)) := rfl
  have hVA : pBar d t ≤ normalClosure ((kBar d t : Subgroup (H1bar d t)) : Set (H1bar d t)) := by
    rw [hPcomm]
    refine (Subgroup.commutator_mono le_rfl ((jSixBar_le_kBar d).trans
      (Subgroup.subset_normalClosure : (kBar d t : Set (H1bar d t)) ⊆ _))).trans
      (Subgroup.commutator_le_right _ _)
  have hgen : ∀ v ∈ pBar d t, v⁻¹ * ((tBar d t)⁻¹ * v * tBar d t) ∈ pBar d t ⊓
      centralizer ({tBar d t} : Set (H1bar d t)) := fun v hv =>
    commutatorWith_gen_mem hV2 hτ2 hτV hv
  have hcomm_le : closure {x | ∃ v ∈ pBar d t, x = v⁻¹ * ((tBar d t)⁻¹ * v * tBar d t)} ≤
      kBar d t := by
    rw [closure_le]
    rintro _ ⟨v, hv, rfl⟩
    have := (hgen v hv)
    rw [hPfix] at this
    exact sBar_le_kBar d this
  have hcomm_ne : closure {x | ∃ v ∈ pBar d t, x = v⁻¹ * ((tBar d t)⁻¹ * v * tBar d t)} ≠ ⊥ := by
    intro hbot
    have hle : pBar d t ≤ centralizer ({tBar d t} : Set (H1bar d t)) := by
      intro v hv
      have h1 : v⁻¹ * ((tBar d t)⁻¹ * v * tBar d t) ∈
          closure {x | ∃ v ∈ pBar d t, x = v⁻¹ * ((tBar d t)⁻¹ * v * tBar d t)} :=
        subset_closure ⟨v, hv, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h1
      rw [mem_centralizer_singleton_iff]
      have h2 : (tBar d t)⁻¹ * v * tBar d t = v := by
        have := congrArg (v * ·) h1
        simpa using this
      calc v * tBar d t = tBar d t * ((tBar d t)⁻¹ * v * tBar d t) := by group
        _ = tBar d t * v := by rw [h2]
    have h3 : pBar d t ⊓ centralizer ({tBar d t} : Set (H1bar d t)) = pBar d t :=
      inf_eq_left.2 hle
    rw [h3] at hPfree
    rw [hPcard] at hPfree
    have ha : 1 < (2 ^ f) ^ 6 :=
      Nat.one_lt_pow (by norm_num) (Nat.one_lt_pow (by omega) (by norm_num))
    have h4 : (2 ^ f) ^ 6 * ((2 ^ f) ^ 6) = (2 ^ f) ^ 6 * 1 := by
      calc (2 ^ f) ^ 6 * ((2 ^ f) ^ 6) = ((2 ^ f) ^ 6) ^ 2 := (pow_two _).symm
        _ = (2 ^ f) ^ 6 := hPfree.symm
        _ = (2 ^ f) ^ 6 * 1 := (mul_one _).symm
    have h5 := Nat.eq_of_mul_eq_mul_left (by omega) h4
    omega
  have hAτ := kBar_le_centralizer_tBar h d hp
  have hAn := kBar_normal_in_centralizer_tBar h d (hC1.trans hC2)
  rw [inf_comm] at hsyl
  obtain ⟨hperf, -, hsel, hex⟩ := exactClosure_of_layerList hGMS (isKGroupCat_H1bar h d hp) hn hk
    α hord hAτ hAn hsyl hV2 hVcard hVA hτV hcomm_ne hcomm_le
  exact ⟨α, hperf, hsel, hex⟩

section Corr

variable {G' : Type*} [Group G'] {A : Subgroup G'}

theorem lift_bot : NormalizerQuotient.lift (⊥ : Subgroup (NormalizerQuotient.Bar A)) = A := by
  ext g
  rw [NormalizerQuotient.mem_lift_iff]
  constructor
  · rintro ⟨hg, h1⟩
    exact NormalizerQuotient.proj_eq_one_iff.1 (Subgroup.mem_bot.1 h1)
  · intro hg
    exact ⟨le_normalizer hg, Subgroup.mem_bot.2 (NormalizerQuotient.proj_eq_one_iff.2 hg)⟩

theorem lift_inf (Y Y' : Subgroup (NormalizerQuotient.Bar A)) :
    NormalizerQuotient.lift (Y ⊓ Y') = NormalizerQuotient.lift Y ⊓ NormalizerQuotient.lift Y' := by
  ext g
  simp only [NormalizerQuotient.mem_lift_iff, Subgroup.mem_inf]
  constructor
  · rintro ⟨hg, h1, h2⟩
    exact ⟨⟨hg, h1⟩, ⟨hg, h2⟩⟩
  · rintro ⟨⟨hg, h1⟩, ⟨_, h2⟩⟩
    exact ⟨hg, h1, h2⟩

theorem lift_sup (Y Y' : Subgroup (NormalizerQuotient.Bar A)) :
    NormalizerQuotient.lift (Y ⊔ Y') = NormalizerQuotient.lift Y ⊔ NormalizerQuotient.lift Y' := by
  unfold NormalizerQuotient.lift
  rw [← Subgroup.map_sup, Subgroup.comap_sup_eq_of_le_range _
    (by rw [(MonoidHom.range_eq_top).2 NormalizerQuotient.proj_surjective]; exact le_top)
    (by rw [(MonoidHom.range_eq_top).2 NormalizerQuotient.proj_surjective]; exact le_top)]

theorem lift_map_conj {t : G'} (ht : t ∈ normalizer (A : Set G'))
    (Y : Subgroup (NormalizerQuotient.Bar A)) :
    NormalizerQuotient.lift (Y.map (MulAut.conj
      (NormalizerQuotient.proj A ⟨t, ht⟩)⁻¹).toMonoidHom) =
      (NormalizerQuotient.lift Y).map (MulAut.conj t⁻¹).toMonoidHom := by
  ext g
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv, NormalizerQuotient.mem_lift_iff,
    NormalizerQuotient.mem_lift_iff]
  constructor
  · rintro ⟨hg, hY⟩
    have hY' := (Subgroup.mem_map_equiv).1 hY
    rw [MulAut.conj_symm_apply, inv_inv] at hY'
    have hg' : t * g * t⁻¹ ∈ normalizer (A : Set G') :=
      mul_mem (mul_mem ht hg) (inv_mem ht)
    refine ⟨hg', ?_⟩
    have e : NormalizerQuotient.proj A ⟨t * g * t⁻¹, hg'⟩ =
        NormalizerQuotient.proj A ⟨t, ht⟩ * NormalizerQuotient.proj A ⟨g, hg⟩ *
          (NormalizerQuotient.proj A ⟨t, ht⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    simpa using hY'
  · rintro ⟨hg', hY⟩
    have hg : g ∈ normalizer (A : Set G') := by
      have h1 := mul_mem (mul_mem (inv_mem ht) hg') ht
      simpa [mul_assoc] using h1
    refine ⟨hg, ?_⟩
    have e : NormalizerQuotient.proj A ⟨t * g * t⁻¹, hg'⟩ =
        NormalizerQuotient.proj A ⟨t, ht⟩ * NormalizerQuotient.proj A ⟨g, hg⟩ *
          (NormalizerQuotient.proj A ⟨t, ht⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e] at hY
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
    simpa using hY

theorem isQuotientIso_lift (Nb : Subgroup (NormalizerQuotient.Bar A)) {T : Type*} [Group T]
    (ψ : ↥Nb ≃* T) : IsQuotientIso (NormalizerQuotient.lift Nb) A T := by
  let g : ↥(NormalizerQuotient.lift Nb) →* NormalizerQuotient.Bar A :=
    (NormalizerQuotient.proj A).comp
      (Subgroup.inclusion (NormalizerQuotient.lift_le_normalizer Nb))
  have hg : ∀ x, g x ∈ Nb := fun x => NormalizerQuotient.proj_mem_of_mem_lift x.2
  let f : ↥(NormalizerQuotient.lift Nb) →* T :=
    ψ.toMonoidHom.comp (g.codRestrict Nb hg)
  refine ⟨f, ?_, ?_⟩
  · intro s
    obtain ⟨x, hx⟩ := NormalizerQuotient.proj_surjective (A := A) (ψ.symm s : Nb).1
    have hxN : (x : G') ∈ NormalizerQuotient.lift Nb :=
      NormalizerQuotient.mem_lift_of_proj_mem (by rw [hx]; exact (ψ.symm s).2)
    refine ⟨⟨x, hxN⟩, ?_⟩
    change ψ ⟨g ⟨x, hxN⟩, hg _⟩ = s
    have : (⟨g ⟨x, hxN⟩, hg _⟩ : Nb) = ψ.symm s := Subtype.ext hx
    rw [this]
    simp
  · ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change ψ ⟨g x, hg x⟩ = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    constructor
    · intro h1
      have : g x = 1 := congrArg Subtype.val h1
      exact NormalizerQuotient.proj_eq_one_iff.1 this
    · intro h1
      exact Subtype.ext (NormalizerQuotient.proj_eq_one_iff.2 h1)

theorem exists_factor_of_prod {t : G'} (ht : t ∈ normalizer (A : Set G'))
    (Nb : Subgroup (NormalizerQuotient.Bar A)) {T : Type*} [Group T] (ψ : ↥Nb ≃* T × T)
    (hτN : NormalizerQuotient.proj A ⟨t, ht⟩ ∈ normalizer (Nb : Set (NormalizerQuotient.Bar A)))
    (hτ : ∀ x y : ↥Nb, (y : NormalizerQuotient.Bar A) =
      (NormalizerQuotient.proj A ⟨t, ht⟩)⁻¹ * x * NormalizerQuotient.proj A ⟨t, ht⟩ →
        ψ y = (ψ x).swap) :
    ∃ K₁ : Subgroup G', A ≤ K₁ ∧
      NormalizerQuotient.lift Nb = K₁ ⊔ K₁.map (MulAut.conj t⁻¹).toMonoidHom ∧
      K₁ ⊓ K₁.map (MulAut.conj t⁻¹).toMonoidHom = A ∧
      ⁅K₁, K₁.map (MulAut.conj t⁻¹).toMonoidHom⁆ ≤ A ∧ IsQuotientIso K₁ A T := by
  classical
  set τ := NormalizerQuotient.proj A ⟨t, ht⟩ with hτdef
  set K₁b : Subgroup (NormalizerQuotient.Bar A) :=
    (((⊤ : Subgroup T).prod (⊥ : Subgroup T)).comap ψ.toMonoidHom).map Nb.subtype with hK₁b
  set K₂b : Subgroup (NormalizerQuotient.Bar A) :=
    (((⊥ : Subgroup T).prod (⊤ : Subgroup T)).comap ψ.toMonoidHom).map Nb.subtype with hK₂b
  have hmem1 : ∀ z, z ∈ K₁b ↔ ∃ hz : z ∈ Nb, (ψ ⟨z, hz⟩).2 = 1 := by
    intro z
    simp only [hK₁b, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.mem_prod, Subgroup.mem_top,
      Subgroup.mem_bot, true_and, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨hz, h2⟩
      exact ⟨⟨z, hz⟩, h2, rfl⟩
  have hmem2 : ∀ z, z ∈ K₂b ↔ ∃ hz : z ∈ Nb, (ψ ⟨z, hz⟩).1 = 1 := by
    intro z
    simp only [hK₂b, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.mem_prod, Subgroup.mem_top,
      Subgroup.mem_bot, and_true, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨hz, h2⟩
      exact ⟨⟨z, hz⟩, h2, rfl⟩
  have hK₁le : K₁b ≤ Nb := fun z hz => ((hmem1 z).1 hz).1
  have hK₂le : K₂b ≤ Nb := fun z hz => ((hmem2 z).1 hz).1
  have hτinv : τ⁻¹ ∈ normalizer (Nb : Set (NormalizerQuotient.Bar A)) := inv_mem hτN
  have hconj : K₁b.map (MulAut.conj τ⁻¹).toMonoidHom = K₂b := by
    ext z
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
    constructor
    · intro hz
      obtain ⟨hzN, h2⟩ := (hmem1 _).1 hz
      have hzN' : z ∈ Nb := by
        have := (mem_normalizer_iff.1 hτinv (τ * z * τ⁻¹)).1 hzN
        simpa [mul_assoc] using this
      refine (hmem2 z).2 ⟨hzN', ?_⟩
      have := hτ ⟨τ * z * τ⁻¹, hzN⟩ ⟨z, hzN'⟩ (by simp [mul_assoc])
      have h3 := congrArg Prod.fst this
      simp only [Prod.fst_swap] at h3
      rw [h3]
      exact h2
    · intro hz
      obtain ⟨hzN, h1⟩ := (hmem2 _).1 hz
      have hwN : τ * z * τ⁻¹ ∈ Nb := by
        have := (mem_normalizer_iff.1 hτN z).1 hzN
        exact this
      refine (hmem1 _).2 ⟨hwN, ?_⟩
      have := hτ ⟨τ * z * τ⁻¹, hwN⟩ ⟨z, hzN⟩ (by simp [mul_assoc])
      have h3 := congrArg Prod.fst this
      simp only [Prod.fst_swap] at h3
      rw [← h3]
      exact h1
  have hsup : K₁b ⊔ K₂b = Nb := by
    refine le_antisymm (sup_le hK₁le hK₂le) fun z hz => ?_
    set w := ψ ⟨z, hz⟩ with hw
    have hz1 : ((ψ.symm (w.1, 1) : ↥Nb) : NormalizerQuotient.Bar A) ∈ K₁b := by
      rw [hmem1]
      exact ⟨(ψ.symm (w.1, 1)).2, by simp⟩
    have hz2 : ((ψ.symm (1, w.2) : ↥Nb) : NormalizerQuotient.Bar A) ∈ K₂b := by
      rw [hmem2]
      exact ⟨(ψ.symm (1, w.2)).2, by simp⟩
    have : z = ((ψ.symm (w.1, 1) : ↥Nb) : NormalizerQuotient.Bar A) *
        ((ψ.symm (1, w.2) : ↥Nb) : NormalizerQuotient.Bar A) := by
      have h1 : ψ.symm (w.1, 1) * ψ.symm (1, w.2) = ⟨z, hz⟩ := by
        rw [← map_mul]
        have : (w.1, (1 : T)) * ((1 : T), w.2) = w := by simp
        rw [this, hw, MulEquiv.symm_apply_apply]
      exact (congrArg Subtype.val h1).symm
    rw [this]
    exact mul_mem (mem_sup_left hz1) (mem_sup_right hz2)
  have hinf : K₁b ⊓ K₂b = ⊥ := by
    rw [eq_bot_iff]
    intro z ⟨h1, h2⟩
    obtain ⟨hzN, e2⟩ := (hmem1 _).1 h1
    obtain ⟨_, e1⟩ := (hmem2 _).1 h2
    rw [Subgroup.mem_bot]
    have : (⟨z, hzN⟩ : Nb) = 1 := ψ.injective (by ext <;> simp [e1, e2])
    exact congrArg (fun z : ↥Nb => z.1) this
  have hcomm : ∀ x ∈ K₁b, ∀ y ∈ K₂b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨hxN, e2⟩ := (hmem1 _).1 hx
    obtain ⟨hyN, e1⟩ := (hmem2 _).1 hy
    have : (⟨x, hxN⟩ * ⟨y, hyN⟩ : Nb) = ⟨y, hyN⟩ * ⟨x, hxN⟩ := by
      apply ψ.injective
      rw [map_mul, map_mul]
      ext <;> simp [e1, e2]
    exact congrArg (fun z : ↥Nb => z.1) this
  set K₁ := NormalizerQuotient.lift K₁b with hK₁
  have hK₂ : K₁.map (MulAut.conj t⁻¹).toMonoidHom = NormalizerQuotient.lift K₂b := by
    rw [hK₁, ← lift_map_conj ht, hconj]
  refine ⟨K₁, NormalizerQuotient.le_lift _, ?_, ?_, ?_, ?_⟩
  · rw [hK₂, hK₁, ← lift_sup, hsup]
  · rw [hK₂, hK₁, ← lift_inf, hinf, lift_bot]
  · rw [hK₂, Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨hxN, hxb⟩ := NormalizerQuotient.mem_lift_iff.1 hx
    obtain ⟨hyN, hyb⟩ := NormalizerQuotient.mem_lift_iff.1 hy
    rw [commutatorElement_def]
    have h1 := hcomm _ hxb _ hyb
    have : NormalizerQuotient.proj A (⟨x, hxN⟩ * ⟨y, hyN⟩ * ⟨x, hxN⟩⁻¹ * ⟨y, hyN⟩⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [h1]
      group
    exact NormalizerQuotient.proj_eq_one_iff.1 this
  ·
    let f₁ : ↥K₁b →* T := (MonoidHom.fst T T).comp (ψ.toMonoidHom.comp (Subgroup.inclusion hK₁le))
    have hf₁ : Function.Bijective f₁ := by
      constructor
      · intro a b hab
        obtain ⟨hae, hae2⟩ := (hmem1 _).1 a.2
        obtain ⟨hbe, hbe2⟩ := (hmem1 _).1 b.2
        have : (⟨a.1, hae⟩ : Nb) = ⟨b.1, hbe⟩ := by
          apply ψ.injective
          ext
          · exact hab
          · simp [hae2, hbe2]
        exact Subtype.ext (Subtype.mk.inj this)
      · intro s
        have hmem : ((ψ.symm (s, 1) : ↥Nb) : NormalizerQuotient.Bar A) ∈ K₁b := by
          rw [hmem1]
          exact ⟨(ψ.symm (s, 1)).2, by simp⟩
        refine ⟨⟨(ψ.symm (s, 1) : Nb), hmem⟩, ?_⟩
        have hinc : Subgroup.inclusion hK₁le ⟨(ψ.symm (s, 1) : Nb), hmem⟩ = ψ.symm (s, 1) :=
          Subtype.ext rfl
        simp [f₁, hinc]
    exact isQuotientIso_lift K₁b (MulEquiv.ofBijective f₁ hf₁)

end Corr

theorem perfectResidual_eq_top_of_perfect {X : Type*} [Group X] (hX : Group.IsPerfect X) :
    CFSG.perfectResidual X = ⊤ := by
  haveI := hX
  unfold CFSG.perfectResidual
  simp [Group.IsPerfect.derivedSeries_eq_top]

theorem nOneBar_eq_xBar (d : TrialityD4Data L (2 ^ f)) (t : G)
    (hperf : Group.IsPerfect ↥(xBar d t)) : nOneBar d t = xBar d t := by
  unfold nOneBar
  rw [perfectResidual_eq_top_of_perfect hperf, Subgroup.map_top, Subgroup.range_subtype]

theorem D5_core
    (hGMS : GMSK.GMSLinearStandardLayerListKRankOneStatement)
    (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    (nOneBar d t).Normal ∧
      (nOneBar d t ⊓ CFSG.oddCore (H1bar d t) = ⊥ ∧
        (nOneBar d t).map (piHat d t) = CFSG.layer (H1hat d t)) ∧
      (IsSylowOf 2 (pBar d t) (nOneBar d t) ∧ kBar d t ≤ nOneBar d t) ∧
      ((∃ K₁ : Subgroup G, IsN1Factor d t K₁) ∨
        ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = (2 ^ f) ^ 6 ∧
          IsQuotientIso (nOne d t) (yamadaD₅ d t) (Matrix.SpecialLinearGroup (Fin 2) k)) := by
  classical
  obtain ⟨α, hperf, hsel, hex⟩ := closure_data hGMS h d hp
  have hX := nOneBar_eq_xBar d t hperf
  unfold ExactClosure at hex
  obtain ⟨hNR, hCN, hVN, hSyl, hxor⟩ := hex
  unfold ClosureSelection at hsel
  obtain ⟨-, hL, -, -, -⟩ := hsel
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [hX]
    exact Subgroup.normalClosure_normal
  · rw [hX]
    exact hNR
  · rw [hX]
    exact hL.symm
  · rw [hX]
    exact hSyl
  · rw [hX]
    exact Subgroup.subset_normalClosure
  · have htD := t_mem_normalizer_D₅ h d
    have hτ : tBar d t = NormalizerQuotient.proj (yamadaD₅ d t) ⟨t, htD⟩ := tBar_eq h d
    rcases hxor with ⟨⟨ψ, -, hψτ⟩, -⟩ | ⟨⟨k₂, _, _, hk₂, ψ, -, -⟩, -⟩
    · left
      have hτN : NormalizerQuotient.proj (yamadaD₅ d t) ⟨t, htD⟩ ∈
          normalizer ((normalClosure ((kBar d t : Subgroup (H1bar d t)) : Set (H1bar d t)) :
            Subgroup (H1bar d t)) : Set (H1bar d t)) := by
        have h0 : (normalClosure ((kBar d t : Subgroup (H1bar d t)) : Set (H1bar d t))).Normal :=
          Subgroup.normalClosure_normal
        exact (normalizer_eq_top_iff.2 h0).ge (Subgroup.mem_top _)
      obtain ⟨K₁, hK₁A, hsup, hinf, hcomm, hiso⟩ := exists_factor_of_prod htD
        (normalClosure ((kBar d t : Subgroup (H1bar d t)) : Set (H1bar d t))) ψ hτN
        (fun x y hxy => hψτ x y (by rw [hτ]; exact hxy))
      refine ⟨K₁, ⟨hK₁A, ?_, hinf, hcomm, hiso⟩⟩
      change NormalizerQuotient.lift (nOneBar d t) = _
      rw [hX]
      exact hsup
    · right
      refine ⟨k₂, inferInstance, inferInstance, ?_, ?_⟩
      · rw [Nat.card_eq_fintype_card, hk₂, ← pow_mul, ← pow_mul]
        congr 1
        ring
      · change IsQuotientIso (NormalizerQuotient.lift (nOneBar d t)) _ _
        rw [hX]
        exact isQuotientIso_lift _ ψ

end ProductN1LayerAux

end Aux

section D6Aux

open scoped commutatorElement

namespace ProductN1LayerD6Aux

namespace ClaimB

section Generic

variable {G' : Type*} [Group G']

theorem le_normalizer_of_commutator_le {A B W : Subgroup G'} [Finite G'] (hWA : W ≤ A)
    (hAB : ⁅A, B⁆ ≤ W) : B ≤ normalizer (A : Set G') := by
  intro b hb
  refine mem_normalizer_fintype fun a ha => ?_
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ W := hAB (Subgroup.commutator_mem_commutator ha hb)
  have h2 : b * a * b⁻¹ = (b * a * b⁻¹ * a⁻¹) * a := by group
  have h3 : b * a * b⁻¹ * a⁻¹ ∈ W := by
    have := inv_mem h1
    simpa [mul_assoc] using this
  rw [h2]
  exact mul_mem (hWA h3) ha

theorem normalizer_le_normalizer_pCoreOf (p : ℕ) (H : Subgroup G') :
    normalizer (H : Set G') ≤ normalizer (pCoreOf p H : Set G') := by
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq] at hx ⊢
  have hx' : H.map (MulEquiv.toMonoidHom (MulAut.conj x)) = H := hx
  have h1 := CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv p (MulAut.conj x) H
  rw [hx'] at h1
  exact h1.symm

theorem mem_map_conj_inv_iff (H : Subgroup G') (g y : G') :
    y ∈ H.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * y * g⁻¹ ∈ H := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]

theorem centerMod_map_conj {N A : Subgroup G'} {g : G'} (hg : g ∈ normalizer (N : Set G'))
    (hNA : N ≤ A) :
    centerMod N (A.map (MulAut.conj g⁻¹).toMonoidHom) =
      (centerMod N A).map (MulAut.conj g⁻¹).toMonoidHom := by
  have hNmap : N.map (MulAut.conj g⁻¹).toMonoidHom = N :=
    mem_normalizer_iff_map_conj_eq.1 (inv_mem hg)
  have hNA' : N ≤ A.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [← hNmap]
    exact map_mono hNA
  have hgx : ∀ y : G', y ∈ normalizer (N : Set G') ↔ g * y * g⁻¹ ∈ normalizer (N : Set G') :=
    fun y => ⟨fun hy => mul_mem (mul_mem hg hy) (inv_mem hg), fun hy => by
      have := mul_mem (mul_mem (inv_mem hg) hy) hg
      simpa [mul_assoc] using this⟩
  have hgN : ∀ y : G', y ∈ N ↔ g * y * g⁻¹ ∈ N := fun y => mem_normalizer_iff.1 hg y
  ext x
  rw [mem_centerMod_iff hNA', mem_map_conj_inv_iff (centerMod N A) g x, mem_centerMod_iff hNA,
    mem_map_conj_inv_iff A g x]
  constructor
  · rintro ⟨hxA, hxN, hc⟩
    refine ⟨hxA, (hgx x).1 hxN, fun a ha han => ?_⟩
    have e0 : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    have hA' : g⁻¹ * a * g ∈ A.map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [mem_map_conj_inv_iff, e0]
      exact ha
    have hN' : g⁻¹ * a * g ∈ normalizer (N : Set G') := by
      apply (hgx (g⁻¹ * a * g)).2
      rw [e0]
      exact han
    have h1 := hc (g⁻¹ * a * g) hA' hN'
    rw [hgN] at h1
    have e : g * (x * (g⁻¹ * a * g) * x⁻¹ * (g⁻¹ * a * g)⁻¹) * g⁻¹ =
        (g * x * g⁻¹) * a * (g * x * g⁻¹)⁻¹ * a⁻¹ := by group
    rwa [e] at h1
  · rintro ⟨hxA, hxN, hc⟩
    refine ⟨hxA, (hgx x).2 hxN, fun a ha han => ?_⟩
    have ha' : g * a * g⁻¹ ∈ A := (mem_map_conj_inv_iff A g a).1 ha
    have han' : g * a * g⁻¹ ∈ normalizer (N : Set G') := (hgx a).1 han
    have h1 := hc (g * a * g⁻¹) ha' han'
    rw [hgN]
    have e : g * (x * a * x⁻¹ * a⁻¹) * g⁻¹ =
        (g * x * g⁻¹) * (g * a * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * a * g⁻¹)⁻¹ := by group
    rw [e]
    exact h1

end Generic

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem t_mem_normalizer_W₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : t ∈ normalizer (yamadaW₃ d t : Set G) := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h5101 := h.yamada_5_10_1 d hlay
  have h5102 := h.yamada_5_10_2 d hlay
  exact h.t_mem_normalizer_yamadaW₃_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102

theorem W₃_le_kTwo (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d)
    (K : Subgroup G) : yamadaW₃ d t ≤ kTwo d t K :=
  ((h.yamadaW₃_le_yamadaF₄_R5 d hlay).trans (h.yamadaF₄_le_yamadaM₆_PA d hlay)).trans le_sup_right

theorem zKTwoT_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d)
    (K : Subgroup G) :
    zKTwoT d t K = (zKTwo d t K).map (MulAut.conj t⁻¹).toMonoidHom :=
  centerMod_map_conj (t_mem_normalizer_W₃ h d hlay) (W₃_le_kTwo h d hlay K)

theorem false_of_le_of_conj {G' : Type*} [Group G'] [Finite G'] {Z Z' F W : Subgroup G'} {t : G'}
    (htt : t * t = 1) (hZ : Z = Z'.map (MulAut.conj t⁻¹).toMonoidHom)
    (hF : F.map (MulAut.conj t⁻¹).toMonoidHom = F) (hZF : Z ≤ F)
    (hc : Nat.card F ≤ Nat.card Z) (hZZ : Z' ⊓ Z = W) (hW : Nat.card W < Nat.card F) : False := by
  have hZeq : Z = F := eq_of_le_of_card_ge hZF hc
  have h1 : Z.map (MulAut.conj t⁻¹).toMonoidHom = Z' := by
    rw [hZ]
    exact map_conj_inv_map_conj_inv htt Z'
  have hZ'eq : Z' = F := by rw [← h1, hZeq, hF]
  have hWF : W = F := by rw [← hZZ, hZ'eq, ← hZeq, inf_idem]
  rw [hWF] at hW
  exact lt_irrefl _ hW

theorem mem_of_commutators_mem {G' : Type*} [Group G'] {P W F : Subgroup G'}
    (hS3 : Subgroup.map P.subtype (Subgroup.upperCentralSeries ↥P 3) = W)
    (hS4 : Subgroup.map P.subtype (Subgroup.upperCentralSeries ↥P 4) = F)
    (hPW : P ≤ normalizer (W : Set G')) {x : G'} (hxP : x ∈ P)
    (hxc : ∀ r ∈ P, x⁻¹ * (r * x * r⁻¹) ∈ W) : x ∈ F := by
  rw [← hS4]
  refine ⟨⟨x, hxP⟩, ?_, rfl⟩
  show (⟨x, hxP⟩ : ↥P) ∈ Subgroup.upperCentralSeries ↥P (3 + 1)
  refine Subgroup.mem_upperCentralSeries_succ_iff.2 fun y => ?_
  have hw : x⁻¹ * ((y : G') * x * (y : G')⁻¹) ∈ W := hxc y y.2
  have hcomm : x * (y : G') * x⁻¹ * (y : G')⁻¹ ∈ W := by
    set w := x⁻¹ * ((y : G') * x * (y : G')⁻¹) with hwdef
    have hyx : (y : G') * x * (y : G')⁻¹ = x * w := by rw [hwdef]; group
    have h2 : (y : G') * x⁻¹ * (y : G')⁻¹ = (x * w)⁻¹ := by
      rw [← hyx]; group
    have e : x * (y : G') * x⁻¹ * (y : G')⁻¹ = x * w⁻¹ * x⁻¹ := by
      calc x * (y : G') * x⁻¹ * (y : G')⁻¹ = x * ((y : G') * x⁻¹ * (y : G')⁻¹) := by group
        _ = x * (x * w)⁻¹ := by rw [h2]
        _ = x * w⁻¹ * x⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 (hPW hxP) w⁻¹).1 (inv_mem hw)
  rw [← hS3] at hcomm
  obtain ⟨c, hc, hce⟩ := hcomm
  have : c = ⁅(⟨x, hxP⟩ : ↥P), y⁆ := Subtype.ext (by simpa [commutatorElement_def] using hce)
  rw [← this]
  exact hc

theorem exists_mem_inf_of_normal {G' : Type*} [Group G'] [Finite G'] {P Z W F : Subgroup G'}
    (hP2 : IsPGroup 2 ↥P) (hZP : Z ≤ P) (hWZ : W ≤ Z) (hne : ¬ Z ≤ W)
    (hPZ : P ≤ normalizer (Z : Set G')) (hPW : P ≤ normalizer (W : Set G'))
    (hS3 : Subgroup.map P.subtype (Subgroup.upperCentralSeries ↥P 3) = W)
    (hS4 : Subgroup.map P.subtype (Subgroup.upperCentralSeries ↥P 4) = F) :
    ∃ x ∈ Z ⊓ F, x ∉ W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxZ, hxW, hxc⟩ := exists_mem_forall_conj_mem_of_isPGroup (p := 2) hP2
    (hP2.to_le hZP) hWZ hne hPZ hPW (hZP.trans hPW)
  exact ⟨x, ⟨hxZ, mem_of_commutators_mem hS3 hS4 hPW (hZP hxZ) hxc⟩, hxW⟩

theorem W₃_le_zKTwoT (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) : yamadaW₃ d t ≤ zKTwoT d t K := by
  obtain ⟨⟨-, hZZ, -, -⟩, -⟩ := C2_decomposition h d hp hK
  rw [← hZZ]
  exact inf_le_right

theorem zKTwoT_le_M₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) : zKTwoT d t K ≤ yamadaM₆ d t := by
  obtain ⟨⟨hM6, -, -, -⟩, -⟩ := C2_decomposition h d hp hK
  rw [hM6]
  exact le_sup_right

theorem card_zKTwoT (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    Nat.card (zKTwoT d t K) = (2 ^ f) ^ 16 := by
  obtain ⟨⟨-, -, -, hZc⟩, -⟩ := C2_decomposition h d hp hK
  have h1 := Subgroup.relIndex_mul_card (yamadaW₃ d t) (zKTwoT d t K)
  rw [inf_eq_left.2 (W₃_le_zKTwoT h d hp hK), hZc, h.card_yamadaW₃ d hp.layer, ← pow_add] at h1
  exact h1.symm

theorem claimB_left (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    yamadaD₅ d t < pCoreOf 2 (kFour d t K) ⊔ yamadaD₅ d t := by
  have hlay := hp.layer
  obtain ⟨⟨-, hZZ, -, -⟩, -, ⟨-, -, -, hpc⟩⟩ := C2_decomposition h d hp hK
  rw [hpc]
  refine lt_of_le_of_ne le_sup_right fun hDe => ?_
  have hZD : zKTwoT d t K ≤ yamadaD₅ d t := le_sup_left.trans hDe.ge
  have hZF4 : zKTwoT d t K ≤ yamadaF₄ d t := by
    rw [← h.yamadaD₅_inf_yamadaM₆_eq d hlay]
    exact le_inf hZD (zKTwoT_le_M₆ h d hp hK)
  have hf := hp.two_le
  have hq : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
  refine false_of_le_of_conj h.t_mul_t (zKTwoT_eq h d hlay K) ?_ hZF4 ?_ hZZ ?_
  · exact mem_normalizer_iff_map_conj_eq.1 (inv_mem (h.t_mem_normalizer_yamadaF₄ d hlay))
  · rw [h.card_yamadaF₄ d hlay, card_zKTwoT h d hp hK]
  · rw [h.card_yamadaW₃ d hlay, h.card_yamadaF₄ d hlay]
    exact Nat.pow_lt_pow_right hq (by norm_num)

theorem P_le_normalizer_zKTwoT (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    yamadaP d t ≤ normalizer (zKTwoT d t K : Set G) := by
  obtain ⟨-, ⟨hN2, -, hkc, -, -, -, -, -⟩, ⟨hW3k4, -, -, hpc⟩⟩ := C2_decomposition h d hp hK
  obtain ⟨-, -, -, hA3P, -⟩ := (A3_structure h d hp hK).2.2
  have hkFour : nTwo d t ≤ normalizer (kFour d t K : Set G) := by
    rw [hN2]
    exact sup_le le_normalizer (le_normalizer_of_commutator_le hW3k4 hkc)
  intro x hx
  have := normalizer_le_normalizer_pCoreOf 2 (kFour d t K) (hkFour (hA3P.le hx))
  rwa [hpc] at this

theorem le_normalizer_of_series {G' : Type*} [Group G'] [Finite G'] {P W : Subgroup G'} {n : ℕ}
    (hS : Subgroup.map P.subtype (Subgroup.upperCentralSeries ↥P n) = W) :
    P ≤ normalizer (W : Set G') := by
  intro x hx
  refine mem_normalizer_fintype fun w hw => ?_
  rw [← hS] at hw ⊢
  obtain ⟨z, hz, rfl⟩ := hw
  exact ⟨⟨x, hx⟩ * z * ⟨x, hx⟩⁻¹,
    (inferInstance : (Subgroup.upperCentralSeries ↥P n).Normal).conj_mem z hz _, rfl⟩

theorem P_le_normalizer_W₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaP d t ≤ normalizer (yamadaW₃ d t : Set G) := by
  obtain ⟨-, -, hS3, -⟩ := S5_upperCentralSeries_P h d hlay
  exact le_normalizer_of_series hS3

theorem M₆_eq_sup_of_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K)
    (hRP : zKTwoT d t K ⊔ yamadaD₅ d t = yamadaP d t) :
    yamadaM₆ d t = yamadaF₄ d t ⊔ zKTwoT d t K := by
  have hlay := hp.layer
  have hZM6 := zKTwoT_le_M₆ h d hp hK
  have hM6P : yamadaM₆ d t ≤ yamadaP d t := yamadaM₆_le_yamadaP d t
  have hZD' : zKTwoT d t K ≤ normalizer (yamadaD₅ d t : Set G) :=
    (hZM6.trans hM6P).trans (h.yamadaP_le_normalizer_yamadaD₅ d hlay)
  refine le_antisymm (fun m hm => ?_)
    (sup_le (h.yamadaF₄_le_yamadaM₆_PA d hlay) hZM6)
  have hmP : m ∈ yamadaD₅ d t ⊔ zKTwoT d t K := by
    rw [sup_comm]
    exact hRP ▸ hM6P hm
  have hmP' : m ∈ ((yamadaD₅ d t ⊔ zKTwoT d t K : Subgroup G) : Set G) := hmP
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (yamadaD₅ d t) (zKTwoT d t K) hZD'] at hmP'
  obtain ⟨d', hd', z, hz, rfl⟩ := hmP'
  have hdM6 : d' ∈ yamadaM₆ d t := by
    have := mul_mem hm (inv_mem (hZM6 hz))
    simpa using this
  have hdF4 : d' ∈ yamadaF₄ d t := by
    rw [← h.yamadaD₅_inf_yamadaM₆_eq d hlay]
    exact ⟨hd', hdM6⟩
  exact mul_mem (mem_sup_left hdF4) (mem_sup_right hz)

theorem F₄_inf_zKTwoT_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K)
    (hM6 : yamadaM₆ d t = yamadaF₄ d t ⊔ zKTwoT d t K) :
    yamadaF₄ d t ⊓ zKTwoT d t K = yamadaW₃ d t := by
  have hlay := hp.layer
  obtain ⟨-, -, -, -, -, -, -, -, hM6card, -, -⟩ := T4_series_free h d hp
  have hZF4N : zKTwoT d t K ≤ normalizer (yamadaF₄ d t : Set G) :=
    ((zKTwoT_le_M₆ h d hp hK).trans (yamadaM₆_le_yamadaP d t)).trans
      (h.yamadaP_le_normalizer_yamadaF₄_PA d hlay)
  have hprod := card_sup_mul_card_inf_eq_D4 hZF4N
  rw [← hM6, hM6card, h.card_yamadaF₄ d hlay, card_zKTwoT h d hp hK] at hprod
  have hinf : Nat.card (yamadaF₄ d t ⊓ zKTwoT d t K : Subgroup G) = Nat.card (yamadaW₃ d t) := by
    rw [h.card_yamadaW₃ d hlay]
    have h2 : (2 ^ f) ^ 22 * Nat.card (yamadaF₄ d t ⊓ zKTwoT d t K : Subgroup G) =
        (2 ^ f) ^ 22 * (2 ^ f) ^ 10 := by
      rw [hprod, ← pow_add, ← pow_add]
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h2
  exact (eq_of_le_of_card_ge (le_inf (h.yamadaW₃_le_yamadaF₄_R5 d hlay)
    (W₃_le_zKTwoT h d hp hK)) (le_of_eq hinf)).symm

theorem claimB_right (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    pCoreOf 2 (kFour d t K) ⊔ yamadaD₅ d t < yamadaP d t := by
  have hlay := hp.layer
  have hf := hp.two_le
  obtain ⟨-, -, ⟨-, -, -, hpc⟩⟩ := C2_decomposition h d hp hK
  obtain ⟨-, -, -, hA3P, -⟩ := (A3_structure h d hp hK).2.2
  obtain ⟨-, -, hS3, hS4⟩ := S5_upperCentralSeries_P h d hlay
  rw [hpc]
  have hZP : zKTwoT d t K ≤ yamadaP d t :=
    (zKTwoT_le_M₆ h d hp hK).trans (yamadaM₆_le_yamadaP d t)
  refine lt_of_le_of_ne (sup_le hZP (yamadaD₅_le_yamadaP d t)) fun hRP => ?_
  have hM6 := M₆_eq_sup_of_eq h d hp hK hRP
  have hF4Z := F₄_inf_zKTwoT_eq h d hp hK hM6
  have hq : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
  have hnot : ¬ zKTwoT d t K ≤ yamadaW₃ d t := by
    intro hle
    have hZW : zKTwoT d t K = yamadaW₃ d t := le_antisymm hle (W₃_le_zKTwoT h d hp hK)
    have h1 := card_zKTwoT h d hp hK
    rw [hZW, h.card_yamadaW₃ d hlay] at h1
    have : (2 ^ f) ^ 10 < (2 ^ f) ^ 16 := Nat.pow_lt_pow_right hq (by norm_num)
    omega
  obtain ⟨x, ⟨hxZ, hxF⟩, hxW⟩ := exists_mem_inf_of_normal hA3P.isPGroup hZP
    (W₃_le_zKTwoT h d hp hK) hnot (P_le_normalizer_zKTwoT h d hp hK) (P_le_normalizer_W₃ h d hlay)
    hS3 hS4
  have hx : x ∈ yamadaF₄ d t ⊓ zKTwoT d t K := ⟨hxF, hxZ⟩
  rw [hF4Z] at hx
  exact hxW hx

theorem claimB (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    yamadaD₅ d t < pCoreOf 2 (kFour d t K) ⊔ yamadaD₅ d t ∧
      pCoreOf 2 (kFour d t K) ⊔ yamadaD₅ d t < yamadaP d t :=
  ⟨claimB_left h d hp hK, claimB_right h d hp hK⟩

end Main

end ClaimB

end ProductN1LayerD6Aux

namespace ProductN1LayerD6Aux

theorem not_dvd_two_pow_sub_one {m w : ℕ} (hw0 : 0 < w) (hw : w < 2 * m) :
    ¬ (2 ^ m + 1) ∣ (2 ^ w - 1) := by
  intro h
  have h2w : 2 ≤ 2 ^ w := by
    calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw0
  by_cases hwm : w ≤ m
  · have h1 := Nat.le_of_dvd (by omega) h
    have h2 : 2 ^ w ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hwm
    omega
  · push Not at hwm
    obtain ⟨s, rfl⟩ : ∃ s, w = m + s := ⟨w - m, by omega⟩
    have hs0 : 0 < s := by omega
    have hsm : s < m := by omega
    have h1 : 1 ≤ 2 ^ (m + s) := Nat.one_le_two_pow
    have e : (2 ^ (m + s) - 1) + (2 ^ s + 1) = (2 ^ m + 1) * 2 ^ s := by
      rw [add_mul, one_mul, ← pow_add]
      omega
    have hd : (2 ^ m + 1) ∣ (2 ^ (m + s) - 1) + (2 ^ s + 1) := by
      rw [e]
      exact dvd_mul_right _ _
    have hd2 : (2 ^ m + 1) ∣ (2 ^ s + 1) := (Nat.dvd_add_right h).1 hd
    have h3 := Nat.le_of_dvd (Nat.succ_pos _) hd2
    have h4 : 2 ^ s < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) hsm
    omega

theorem orderOf_dvd_card_sub_one {X : Type*} [Group X] [Finite X] {W : Subgroup X} {z : X}
    (hz : z ∈ normalizer (W : Set X))
    (hfree : ∀ w ∈ W, w ≠ 1 → ∀ i : ℤ, z ^ i * w = w * z ^ i → z ^ i = 1) :
    orderOf z ∣ Nat.card W - 1 := by
  have hZ : zpowers z ≤ normalizer (W : Set X) := zpowers_le.2 hz
  have hX : ∀ u ∈ (W : Set X) \ {1}, ∀ h ∈ zpowers z, h * u * h⁻¹ ∈ (W : Set X) \ {1} := by
    intro u hu h hh
    refine ⟨(mem_normalizer_iff.1 (hZ hh) u).1 hu.1, fun h1 => hu.2 ?_⟩
    simpa using h1
  have h := CFSG.Walter.J1.card_dvd_ncard_of_free (H := zpowers z) (X := (W : Set X) \ {1}) hX
    (fun u hu h hh hc => by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hh
      exact hfree u hu.1 hu.2 i hc)
  rw [Nat.card_zpowers, Set.ncard_diff_singleton_of_mem W.one_mem, ← Nat.card_coe_set_eq] at h
  exact h

theorem two_pow_sub_one_mul_add_one {m : ℕ} :
    (2 ^ m - 1) * (2 ^ m + 1) = 2 ^ (2 * m) - 1 := by
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ (2 * m) := Nat.one_le_two_pow
  zify [h1, h2]
  rw [pow_mul']
  ring

theorem isCyclic_centralizer_zpowers {k : Type*} [Field k] [CharP k 2] [Finite k]
    {d : SL(2, k)} (hd1 : d ≠ 1) (hd : d ^ (Nat.card k - 1) = 1) :
    IsCyclic (centralizer (zpowers d : Set SL(2, k))) := by
  obtain ⟨ψ', μ, hμ, hψd, hC⟩ :=
    exists_mulEquiv_map_centralizer_zpowers (MulEquiv.refl SL(2, k)) hd1 hd
  have e : centralizer (zpowers d : Set SL(2, k)) ≃* torusSL k :=
    (ψ'.subgroupMap _).trans (MulEquiv.subgroupCongr hC)
  have : IsCyclic (torusSL k) := isCyclic_of_surjective (diagSLHom (k := k)).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

theorem exists_torus_element {k : Type*} [Field k] [CharP k 2] [Finite k] {m : ℕ} (hm : 1 ≤ m)
    (hk : Nat.card k = 2 ^ (2 * m)) {d : SL(2, k)} (hd1 : d ≠ 1)
    (hd : d ^ (Nat.card k - 1) = 1) :
    ∃ z ∈ centralizer (zpowers d : Set SL(2, k)), orderOf z = 2 ^ m + 1 := by
  haveI := isCyclic_centralizer_zpowers hd1 hd
  have hT : Nat.card (centralizer (zpowers d : Set SL(2, k))) = 2 ^ (2 * m) - 1 := by
    rw [card_centralizer_zpowers (MulEquiv.refl SL(2, k)) hd1 hd, hk]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := centralizer (zpowers d : Set SL(2, k)))
  have hord : orderOf g = 2 ^ (2 * m) - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hT]
  have hne : 2 ^ m - 1 ≠ 0 := by
    have : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  have hdvd : (2 ^ m - 1) ∣ orderOf g := by
    rw [hord, ← two_pow_sub_one_mul_add_one]
    exact dvd_mul_right _ _
  refine ⟨((g ^ (2 ^ m - 1) : centralizer (zpowers d : Set SL(2, k))) : SL(2, k)),
    (g ^ (2 ^ m - 1)).2, ?_⟩
  rw [Subgroup.orderOf_coe, orderOf_pow_of_dvd hne hdvd, hord, ← two_pow_sub_one_mul_add_one]
  exact Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hne)

theorem exists_odd_lift {G X : Type*} [Group G] [Finite G] [Group X] {N D J : Subgroup G}
    (φ : N →* X) (hker : φ.ker = D.subgroupOf N) (hDN : D ≤ N) (hD2 : IsPGroup 2 D)
    (hJN : J ≤ N) (hJodd : Odd (Nat.card J))
    {z : X} (hz : z ∈ φ.range) (hzodd : Odd (orderOf z))
    (hJz : (Nat.card J).Coprime (orderOf z))
    (hcomm : ∀ j : N, (j : G) ∈ J → Commute (φ j) z) :
    ∃ (y : G) (hy : y ∈ N), y ∈ centralizer (J : Set G) ∧ Odd (orderOf y) ∧
      φ ⟨y, hy⟩ ∈ zpowers z ∧ orderOf (φ ⟨y, hy⟩) = orderOf z := by
  obtain ⟨x, hx⟩ := hz
  have hNnorm : N ≤ normalizer (D : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hDN).1 (hker ▸ φ.normal_ker)
  have hker_mem : ∀ n : N, φ n = 1 ↔ (n : G) ∈ D := fun n => by
    rw [← MonoidHom.mem_ker, hker, mem_subgroupOf]
  set M0 : Subgroup N := (zpowers z).comap φ with hM0
  set M : Subgroup G := M0.map N.subtype with hM
  have hMmem : ∀ g : G, g ∈ M ↔ ∃ hg : g ∈ N, φ ⟨g, hg⟩ ∈ zpowers z := by
    intro g
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n.2, hn⟩
    · rintro ⟨hg, hgz⟩
      exact ⟨⟨g, hg⟩, hgz, rfl⟩
  have hDM : D ≤ M := fun a ha =>
    (hMmem a).2 ⟨hDN ha, by rw [(hker_mem ⟨a, hDN ha⟩).2 ha]; exact one_mem _⟩
  have hMN : M ≤ N := map_subtype_le _
  have hJM : J ≤ normalizer (M : Set G) := by
    refine fun j hj => mem_normalizer_fintype fun m hm => ?_
    obtain ⟨hmN, hmz⟩ := (hMmem m).1 hm
    refine (hMmem _).2 ⟨N.mul_mem (N.mul_mem (hJN hj) hmN) (N.inv_mem (hJN hj)), ?_⟩
    have e : φ ⟨j * m * j⁻¹, N.mul_mem (N.mul_mem (hJN hj) hmN) (N.inv_mem (hJN hj))⟩ =
        φ ⟨m, hmN⟩ := by
      have h1 := (hcomm ⟨j, hJN hj⟩ hj)
      have h2 : Commute (φ ⟨j, hJN hj⟩) (φ ⟨m, hmN⟩) := by
        obtain ⟨i, hi⟩ := mem_zpowers_iff.1 hmz
        rw [← hi]
        exact h1.zpow_right i
      have : (⟨j * m * j⁻¹, N.mul_mem (N.mul_mem (hJN hj) hmN) (N.inv_mem (hJN hj))⟩ : N) =
          ⟨j, hJN hj⟩ * ⟨m, hmN⟩ * ⟨j, hJN hj⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, h2.eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [e]
    exact hmz
  have hJD : J ≤ normalizer (D : Set G) := hJN.trans hNnorm
  have hxM : (x : G) ∈ M := (hMmem x).2 ⟨x.2, by rw [hx]; exact mem_zpowers z⟩
  have hsolv : Group.IsSolvable M := by
    let ψ0 : M →* X := φ.comp (Subgroup.inclusion hMN)
    have hψ0z : ∀ m : M, ψ0 m ∈ zpowers z := fun m => ((hMmem m).1 m.2).choose_spec
    let ψ : M →* zpowers z := ψ0.codRestrict (zpowers z) hψ0z
    haveI : Group.IsNilpotent D := hD2.isNilpotent
    haveI : Group.IsSolvable (zpowers z) := inferInstance
    refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hDM) ψ (fun m hm => ?_)
    have h1 : ψ0 m = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hm)
    have h2 : (m : G) ∈ D := (hker_mem ⟨m, hMN m.2⟩).1 h1
    exact ⟨⟨m, h2⟩, rfl⟩
  have hcop : (Nat.card J).Coprime (Nat.card M) := by
    refine Nat.coprime_of_dvd fun p hp hpJ hpM => ?_
    haveI := Fact.mk hp
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpM
    have hgN : (g : G) ∈ N := hMN g.2
    obtain ⟨hgN', hgz⟩ := (hMmem g).1 g.2
    have hgp : (g : G) ^ p = 1 := by
      have := pow_orderOf_eq_one g
      rw [hg] at this
      exact_mod_cast congrArg Subtype.val this
    have hng : (⟨g, hgN⟩ : N) ^ p = 1 := Subtype.ext hgp
    by_cases h1 : φ ⟨g, hgN⟩ = 1
    · have hgD : (g : G) ∈ D := (hker_mem ⟨g, hgN⟩).1 h1
      obtain ⟨k, hk⟩ := hD2 ⟨g, hgD⟩
      have hord : orderOf (⟨g, hgD⟩ : D) = p := by
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hg]
      have hpk : p ∣ 2 ^ k := hord ▸ orderOf_dvd_of_pow_eq_one hk
      have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hpk)
      rw [hp2] at hpJ
      exact (Nat.not_even_iff_odd.2 hJodd) (even_iff_two_dvd.2 hpJ)
    · have h2 : (φ ⟨g, hgN⟩) ^ p = 1 := by rw [← map_pow, hng, map_one]
      have h3 : orderOf (φ ⟨g, hgN⟩) = p := by
        rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one h2) with h | h
        · exact absurd (orderOf_eq_one_iff.1 h) h1
        · exact h
      have h4 : p ∣ orderOf z := h3 ▸ orderOf_dvd_of_mem_zpowers hgz
      exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hJz hpJ h4)
  obtain ⟨c, hcMC, n, hnD, hxcn⟩ := exists_mem_inf_centralizer_mul_of_coprime hDM
    (hMN.trans hNnorm) hJM hJD hsolv hcop hxM (fun s hs => by
      have hsN : s ∈ N := hJN hs
      have h1 : φ (x⁻¹ * (⟨s, hsN⟩ * x * ⟨s, hsN⟩⁻¹)) = 1 := by
        have h2 := (hcomm ⟨s, hsN⟩ hs).eq
        rw [map_mul, map_inv, map_mul, map_mul, map_inv, hx, h2, mul_assoc, mul_inv_cancel,
          mul_one, inv_mul_cancel]
      exact (hker_mem _).1 h1)
  obtain ⟨hcN, hcz⟩ := (hMmem c).1 hcMC.1
  have hφc : φ ⟨c, hcN⟩ = z := by
    have e : x = ⟨c, hcN⟩ * ⟨n, hDN hnD⟩ := Subtype.ext hxcn
    have h1 : φ ⟨n, hDN hnD⟩ = 1 := (hker_mem _).2 hnD
    rw [← hx, e, map_mul, h1, mul_one]
  set a := (orderOf c).factorization 2 with ha
  have hc0 : orderOf c ≠ 0 := (orderOf_pos c).ne'
  have h2a : 2 ^ a ∣ orderOf c := Nat.ordProj_dvd _ _
  have hy : c ^ 2 ^ a ∈ N := N.pow_mem hcN _
  refine ⟨c ^ 2 ^ a, hy, Subgroup.pow_mem _ hcMC.2 _, ?_, ?_, ?_⟩
  · rw [orderOf_pow' c (by positivity), Nat.gcd_eq_right h2a]
    exact Nat.not_even_iff_odd.1 (fun h => Nat.not_dvd_ordCompl Nat.prime_two hc0
      (even_iff_two_dvd.1 h))
  · have e : (⟨c ^ 2 ^ a, hy⟩ : N) = ⟨c, hcN⟩ ^ 2 ^ a := rfl
    rw [e, map_pow, hφc]
    exact Subgroup.pow_mem _ (mem_zpowers z) _
  · have e : (⟨c ^ 2 ^ a, hy⟩ : N) = ⟨c, hcN⟩ ^ 2 ^ a := rfl
    rw [e, map_pow, hφc]
    exact Nat.Coprime.orderOf_pow (Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hzodd))

theorem coprime_two_pow_sub_one_add_one {m : ℕ} (hm : 1 ≤ m) :
    Nat.Coprime (2 ^ m - 1) (2 ^ m + 1) := by
  have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hodd : Odd (2 ^ m - 1) := Nat.odd_iff.2 (by omega)
  refine Nat.Coprime.symm ?_
  have hg1 : Nat.gcd (2 ^ m + 1) (2 ^ m - 1) ∣ 2 ^ m - 1 := Nat.gcd_dvd_right _ _
  have hg2 : Nat.gcd (2 ^ m + 1) (2 ^ m - 1) ∣ 2 ^ m + 1 := Nat.gcd_dvd_left _ _
  have hg3 : Nat.gcd (2 ^ m + 1) (2 ^ m - 1) ∣ 2 := by
    have := Nat.dvd_sub hg2 hg1
    have e : 2 ^ m + 1 - (2 ^ m - 1) = 2 := by omega
    rwa [e] at this
  have hgodd : Odd (Nat.gcd (2 ^ m + 1) (2 ^ m - 1)) := hodd.of_dvd_nat hg1
  rcases (Nat.dvd_prime Nat.prime_two).1 hg3 with h | h
  · exact h
  · rw [h] at hgodd
    exact absurd hgodd (by decide)

theorem eq_or_eq_of_odd_invariant {G : Type*} [Group G] [Finite G]
    {k : Type*} [Field k] [CharP k 2] [Finite k] {N D P J R : Subgroup G}
    (φ : N →* SL(2, k)) (hφ : Function.Surjective φ) (hker : φ.ker = D.subgroupOf N)
    (hDP : D ≤ P) (hPN : P ≤ N) (hD2 : IsPGroup 2 D)
    {m : ℕ} (hm : 1 ≤ m) (hk : Nat.card k = 2 ^ (2 * m)) (hPD : D.relIndex P = 2 ^ (2 * m))
    (hJN : J ≤ N) (hJP : J ≤ normalizer (P : Set G))
    (hJcomm : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a)
    (hJcard : Nat.card J ∣ 2 ^ m - 1) (hJ1 : Nat.card J ≠ 1)
    (hDR : D ≤ R) (hRP : R ≤ P)
    (hinv : ∀ y ∈ N, y ∈ centralizer (J : Set G) → y ∈ normalizer (P : Set G) →
      Odd (orderOf y) → y ∈ normalizer (R : Set G)) :
    R = D ∨ R = P := by
  have hDN : D ≤ N := hDP.trans hPN
  have hker_mem : ∀ n : N, φ n = 1 ↔ (n : G) ∈ D := fun n => by
    rw [← MonoidHom.mem_ker, hker, mem_subgroupOf]
  let ψ : P →* SL(2, k) := φ.comp (Subgroup.inclusion hPN)
  let S' : Subgroup SL(2, k) := ψ.range
  have hψ : ∀ p : P, ψ p = φ ⟨p, hPN p.2⟩ := fun p => rfl
  have hS'card : Nat.card S' = Nat.card k := by
    have h1 := Subgroup.card_mul_index ψ.ker
    rw [Subgroup.index_ker] at h1
    have h2 : Nat.card ψ.ker = Nat.card D := by
      exact Nat.card_congr
        { toFun := fun p => ⟨p.1.1, (hker_mem ⟨p.1.1, hPN p.1.2⟩).1 (MonoidHom.mem_ker.1 p.2)⟩
          invFun := fun d => ⟨⟨d.1, hDP d.2⟩,
            MonoidHom.mem_ker.2 ((hker_mem ⟨d.1, hDN d.2⟩).2 d.2)⟩
          left_inv := fun p => rfl
          right_inv := fun d => rfl }
    have h3 := Subgroup.relIndex_mul_card D P
    rw [inf_of_le_left hDP, hPD] at h3
    have h4 : Nat.card P = Nat.card ψ.ker * Nat.card S' := h1.symm
    rw [h2] at h4
    have hpos : 0 < Nat.card D := Nat.card_pos
    rw [hk]
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [← h4, ← h3, mul_comm]
  have hJodd : Odd (Nat.card J) := by
    have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    exact (Nat.odd_iff.2 (by omega : (2 ^ m - 1) % 2 = 1)).of_dvd_nat hJcard
  obtain ⟨j0, hj0, hj01⟩ : ∃ j ∈ J, j ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hJ1
    have : J = ⊥ := (Subgroup.eq_bot_iff_forall J).2 hcon
    rw [this, Subgroup.card_bot]
  have hj0N : j0 ∈ N := hJN hj0
  set d1 : SL(2, k) := φ ⟨j0, hj0N⟩ with hd1def
  have hj0exp : j0 ^ (2 ^ m - 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 ((Subgroup.orderOf_dvd_natCard J hj0).trans hJcard)
  have hd1 : d1 ≠ 1 := by
    intro h1
    have hj0D : j0 ∈ D := (hker_mem ⟨j0, hj0N⟩).1 h1
    obtain ⟨e, he⟩ := hD2 ⟨j0, hj0D⟩
    have h2 : orderOf j0 ∣ 2 ^ e := by
      have := orderOf_dvd_of_pow_eq_one he
      rwa [Subgroup.orderOf_mk] at this
    have h3 : Odd (orderOf j0) := hJodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard J hj0)
    have h4 : orderOf j0 = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right e (Nat.coprime_two_right.2 h3)) h2
    exact hj01 (orderOf_eq_one_iff.1 h4)
  have hd1exp : d1 ^ (Nat.card k - 1) = 1 := by
    have e : Nat.card k - 1 = (2 ^ m - 1) * (2 ^ m + 1) := by
      rw [hk, two_pow_sub_one_mul_add_one]
    have h1 : d1 ^ (2 ^ m - 1) = 1 := by
      rw [hd1def, ← map_pow]
      have : (⟨j0, hj0N⟩ : N) ^ (2 ^ m - 1) = 1 := Subtype.ext hj0exp
      rw [this, map_one]
    rw [e, pow_mul, h1, one_pow]
  have hS'N : d1 ∈ normalizer (S' : Set SL(2, k)) := by
    refine mem_normalizer_fintype fun x hx => ?_
    obtain ⟨p, rfl⟩ := hx
    have hjp : j0 * (p : G) * j0⁻¹ ∈ P := by
      have := (mem_normalizer_iff.1 (hJP hj0) (p : G)).1 p.2
      exact this
    refine ⟨⟨j0 * (p : G) * j0⁻¹, hjp⟩, ?_⟩
    rw [hψ, hψ, hd1def, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hTcomm := isMulCommutative_centralizer_zpowers (MulEquiv.refl SL(2, k)) hd1 hd1exp
  have hTS' : centralizer (zpowers d1 : Set SL(2, k)) ≤ normalizer (S' : Set SL(2, k)) :=
    centralizer_zpowers_le_normalizer (MulEquiv.refl SL(2, k)) hd1 hd1exp hS'card hS'N
  obtain ⟨z, hzT, hzord⟩ := exists_torus_element hm hk hd1 hd1exp
  have hzodd : Odd (orderOf z) := by
    rw [hzord]
    have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
    exact Nat.odd_iff.2 (by omega)
  have hJz : (Nat.card J).Coprime (orderOf z) := by
    rw [hzord]
    exact (coprime_two_pow_sub_one_add_one hm).coprime_dvd_left hJcard
  have hcommT : ∀ j : N, (j : G) ∈ J → Commute (φ j) z := by
    intro j hj
    have hjd : Commute (φ j) d1 := by
      have := hJcomm _ hj j0 hj0
      have h2 : j * ⟨j0, hj0N⟩ = ⟨j0, hj0N⟩ * j := Subtype.ext this
      exact Commute.map (show Commute j ⟨j0, hj0N⟩ from h2) φ
    have hjT : φ j ∈ centralizer (zpowers d1 : Set SL(2, k)) := by
      rw [mem_centralizer_iff]
      intro h hh
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hh
      exact (hjd.symm.zpow_left i).eq
    exact congrArg Subtype.val (mul_comm' (⟨φ j, hjT⟩ : centralizer (zpowers d1 : Set SL(2, k)))
      ⟨z, hzT⟩)
  obtain ⟨y, hyN, hyC, hyodd, hyz, hyord⟩ := exists_odd_lift φ hker hDN hD2 hJN hJodd
    (MonoidHom.mem_range.2 (hφ z)) hzodd hJz hcommT
  set z1 : SL(2, k) := φ ⟨y, hyN⟩ with hz1def
  have hz1T : z1 ∈ centralizer (zpowers d1 : Set SL(2, k)) := by
    obtain ⟨i, hi⟩ := mem_zpowers_iff.1 hyz
    rw [← hi]
    exact Subgroup.zpow_mem _ hzT i
  have hz1S' : z1 ∈ normalizer (S' : Set SL(2, k)) := hTS' hz1T
  have hconj : ∀ g : G, ∀ hg : g ∈ N,
      φ ⟨y * g * y⁻¹, N.mul_mem (N.mul_mem hyN hg) (N.inv_mem hyN)⟩ =
        z1 * φ ⟨g, hg⟩ * z1⁻¹ := by
    intro g hg
    have : (⟨y * g * y⁻¹, N.mul_mem (N.mul_mem hyN hg) (N.inv_mem hyN)⟩ : N) =
        ⟨y, hyN⟩ * ⟨g, hg⟩ * ⟨y, hyN⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
  have hyP : y ∈ normalizer (P : Set G) := by
    refine mem_normalizer_fintype fun p hp => ?_
    have h1 : z1 * ψ ⟨p, hp⟩ * z1⁻¹ ∈ S' := (mem_normalizer_iff.1 hz1S' _).1 ⟨⟨p, hp⟩, rfl⟩
    obtain ⟨p', hp'⟩ := h1
    have hypN : y * p * y⁻¹ ∈ N := N.mul_mem (N.mul_mem hyN (hPN hp)) (N.inv_mem hyN)
    have h2 : φ ⟨y * p * y⁻¹, hypN⟩ = φ ⟨p', hPN p'.2⟩ := by
      rw [hconj p (hPN hp), ← hψ, ← hψ ⟨p, hp⟩]
      exact hp'.symm
    have h3 : (⟨y * p * y⁻¹, hypN⟩ : N)⁻¹ * ⟨p', hPN p'.2⟩ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h2, inv_mul_cancel]
    have h4 : (y * p * y⁻¹)⁻¹ * (p' : G) ∈ D := by
      have := (hker_mem _).1 h3
      exact this
    have e : y * p * y⁻¹ = (p' : G) * ((y * p * y⁻¹)⁻¹ * (p' : G))⁻¹ := by group
    rw [e]
    exact P.mul_mem p'.2 (P.inv_mem (hDP h4))
  have hyR : y ∈ normalizer (R : Set G) := hinv y hyN hyC hyP hyodd
  let ψR : R →* SL(2, k) := φ.comp (Subgroup.inclusion (hRP.trans hPN))
  let W : Subgroup SL(2, k) := ψR.range
  have hWS' : W ≤ S' := by
    rintro _ ⟨r, rfl⟩
    exact ⟨⟨r, hRP r.2⟩, rfl⟩
  have hz1W : z1 ∈ normalizer (W : Set SL(2, k)) := by
    refine mem_normalizer_fintype fun w hw => ?_
    obtain ⟨r, rfl⟩ := hw
    have hyr : y * (r : G) * y⁻¹ ∈ R := (mem_normalizer_iff.1 hyR _).1 r.2
    refine ⟨⟨y * r * y⁻¹, hyr⟩, ?_⟩
    exact hconj (r : G) (hRP.trans hPN r.2)
  have hz1ord : orderOf z1 = 2 ^ m + 1 := hyord.trans hzord
  have hfree : ∀ w ∈ W, w ≠ 1 → ∀ i : ℤ, z1 ^ i * w = w * z1 ^ i → z1 ^ i = 1 := by
    intro w hw hw1 i hi
    have hwS' : w ∈ S' := hWS' hw
    have hc : centralizer ({w} : Set SL(2, k)) = S' :=
      centralizer_eq_of_mem_of_card hS'card hwS' hw1
    have hz1i : z1 ^ i ∈ S' := by
      rw [← hc, mem_centralizer_singleton_iff]
      exact hi
    have h1 : orderOf (z1 ^ i) ∣ 2 ^ (2 * m) := by
      have := Subgroup.orderOf_dvd_natCard S' hz1i
      rwa [hS'card, hk] at this
    have h2 : orderOf (z1 ^ i) ∣ 2 ^ m + 1 :=
      hz1ord ▸ orderOf_dvd_of_mem_zpowers (mem_zpowers_iff.2 ⟨i, rfl⟩)
    have hodd : Odd (2 ^ m + 1) := by
      have h2' : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
      exact Nat.odd_iff.2 (by omega)
    have hcop : Nat.Coprime (2 ^ (2 * m)) (2 ^ m + 1) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hodd)
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hdvd : (2 ^ m + 1) ∣ Nat.card W - 1 := by
    have := orderOf_dvd_card_sub_one hz1W hfree
    rwa [hz1ord] at this
  have hWcard : Nat.card W ∣ 2 ^ (2 * m) := by
    have := Subgroup.card_dvd_of_le hWS'
    rwa [hS'card, hk] at this
  obtain ⟨w, hw, hWw⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hWcard
  rcases Nat.eq_zero_or_pos w with rfl | hw0
  · left
    apply le_antisymm _ hDR
    intro r hr
    have h1 : φ ⟨r, hPN (hRP hr)⟩ ∈ W := ⟨⟨r, hr⟩, rfl⟩
    have hW1 : W = ⊥ := Subgroup.eq_bot_of_card_eq W (by rw [hWw]; rfl)
    rw [hW1, mem_bot] at h1
    exact (hker_mem _).1 h1
  · rcases lt_or_eq_of_le hw with hlt | heq
    · exfalso
      rw [hWw] at hdvd
      exact not_dvd_two_pow_sub_one hw0 hlt hdvd
    · right
      have hWeq : W = S' :=
        Subgroup.eq_of_le_of_card_ge hWS' (by rw [hWw, hS'card, hk, heq])
      apply le_antisymm hRP
      intro p hp
      have h1 : ψ ⟨p, hp⟩ ∈ W := hWeq ▸ ⟨⟨p, hp⟩, rfl⟩
      obtain ⟨r, hr⟩ := h1
      have h3 : (⟨(r : G), hRP.trans hPN r.2⟩ : N)⁻¹ * ⟨p, hPN hp⟩ ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        have : φ ⟨(r : G), hRP.trans hPN r.2⟩ = φ ⟨p, hPN hp⟩ := hr
        rw [this, inv_mul_cancel]
      have h4 : (r : G)⁻¹ * p ∈ D := (hker_mem _).1 h3
      have e : p = (r : G) * ((r : G)⁻¹ * p) := by group
      rw [e]
      exact R.mul_mem r.2 (hDR h4)

section Normalizer

variable {G : Type*} [Group G]

theorem map_conj_eq_iff_mem_normalizer {A : Subgroup G} {g : G} :
    A.map (MulAut.conj g).toMonoidHom = A ↔ g ∈ normalizer (A : Set G) := by
  rw [mem_normalizer_iff]
  constructor
  · intro h x
    have h1 : g * x * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom ↔ x ∈ A := by
      rw [mem_map_equiv, MulAut.conj_symm_apply]
      have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rw [e]
    rw [h] at h1
    exact h1.symm
  · intro h
    ext z
    rw [mem_map_equiv, MulAut.conj_symm_apply, h (g⁻¹ * z * g)]
    have e : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
    rw [e]

theorem mem_normalizer_inf' {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [← map_conj_eq_iff_mem_normalizer] at hA hB ⊢
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, hA, hB]

theorem mem_normalizer_sup' {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [← map_conj_eq_iff_mem_normalizer] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem mem_normalizer_commutator' {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  rw [← map_conj_eq_iff_mem_normalizer] at hA hB ⊢
  rw [Subgroup.map_commutator, hA, hB]

theorem mem_normalizer_normalizer' {A : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G)) :
    g ∈ normalizer ((normalizer (A : Set G) : Subgroup G) : Set G) :=
  Subgroup.le_normalizer hA

theorem mem_normalizer_oTwoPrimeRes {A : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G)) :
    g ∈ normalizer ((oTwoPrimeRes A : Subgroup G) : Set G) := by
  rw [← map_conj_eq_iff_mem_normalizer]
  unfold oTwoPrimeRes
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, ⟨hy, k, hk⟩, rfl⟩
    refine ⟨(mem_normalizer_iff.1 hA y).1 hy, k, ?_⟩
    rw [conj_pow, hk]
    simp
  · rintro ⟨hx, k, hk⟩
    refine ⟨g⁻¹ * x * g, ⟨?_, k, ?_⟩, by group⟩
    · have := (mem_normalizer_iff.1 hA (g⁻¹ * x * g)).2
      have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rw [e] at this
      exact this hx
    · have : (g⁻¹ * x * g) ^ 2 ^ k = g⁻¹ * x ^ 2 ^ k * g := by
        have := conj_pow (a := g⁻¹) (b := x) (i := 2 ^ k)
        simpa using this
      rw [this, hk]
      simp

end Normalizer

section KFour

variable {G : Type} [Group G] {L : Subgroup G} {q : ℕ}

theorem mem_normalizer_kFour (d : TrialityD4Data L q) (t : G) {K : Subgroup G} {y : G}
    (hK : y ∈ normalizer (K : Set G)) (hY : y ∈ normalizer (yamadaY₂ d t : Set G))
    (hM : y ∈ normalizer (yamadaM₆ d t : Set G)) :
    y ∈ normalizer (kFour d t K : Set G) := by
  have hE : y ∈ normalizer (eOne d t K : Set G) := mem_normalizer_inf' hY hK
  have h3 : y ∈ normalizer (kThree d t K : Set G) :=
    mem_normalizer_oTwoPrimeRes (mem_normalizer_inf' hK (mem_normalizer_normalizer' hE))
  have h2 : y ∈ normalizer (kTwo d t K : Set G) := mem_normalizer_sup' h3 hM
  exact mem_normalizer_sup' (mem_normalizer_commutator' h2 h2) h3

end KFour

section Component

variable {H : Type*} [Group H] [Finite H]

theorem map_conj_component_eq_of_odd {K K' : Subgroup H}
    (hK : CFSG.IsComponent K) (hK' : CFSG.IsComponent K') (hne : K' ≠ K)
    (hE : CFSG.layer H = K ⊔ K') {y : H} (hy : Odd (orderOf y)) :
    K.map (MulAut.conj y).toMonoidHom = K := by
  have hcomp : ∀ C : Subgroup H, CFSG.IsComponent C → C = K ∨ C = K' := by
    intro C hC
    by_contra hcon
    push Not at hcon
    have h1 : ⁅K, C⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact (CFSG.LocalCores.distinct_components_commute hC hK).resolve_left hcon.1
    have h2 : ⁅K', C⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact (CFSG.LocalCores.distinct_components_commute hC hK').resolve_left hcon.2
    have hCl : C ≤ CFSG.layer H := le_sSup hC
    rw [hE] at hCl
    have hcent : K ⊔ K' ≤ centralizer (C : Set H) :=
      sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1)
        (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h2)
    have hCC : C ≤ centralizer (C : Set H) := hCl.trans hcent
    obtain ⟨-, -, a, b, hab⟩ := hC.1
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.1 (hCC b.2) a a.2)
  have hconj : ∀ C : Subgroup H, CFSG.IsComponent C →
      CFSG.IsComponent (C.map (MulAut.conj y).toMonoidHom) :=
    fun C hC => CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj y) hC
  rcases hcomp _ (hconj K hK) with h | h
  · exact h
  · exfalso
    have h' : K'.map (MulAut.conj y).toMonoidHom = K := by
      rcases hcomp _ (hconj K' hK') with h' | h'
      · exact h'
      · exfalso
        exact hne ((Subgroup.map_injective (MulAut.conj y).injective) (h'.trans h.symm))
    have hy2 : y ^ 2 ∈ normalizer (K : Set H) := by
      refine mem_normalizer_fintype fun x hx => ?_
      have h1 : y * x * y⁻¹ ∈ K' := by
        rw [← h]
        exact ⟨x, hx, by simp⟩
      have h2 : y * (y * x * y⁻¹) * y⁻¹ ∈ K := by
        rw [← h']
        exact ⟨_, h1, by simp⟩
      have e : y ^ 2 * x * (y ^ 2)⁻¹ = y * (y * x * y⁻¹) * y⁻¹ := by rw [pow_two]; group
      rw [e]
      exact h2
    obtain ⟨n, hn⟩ := hy
    have hyn : y ^ (2 * n + 1) = 1 := by rw [← hn]; exact pow_orderOf_eq_one y
    have hyy : y = (y ^ 2) ^ (n + 1) := by
      rw [← pow_mul, show 2 * (n + 1) = (2 * n + 1) + 1 by ring, pow_succ, hyn, one_mul]
    have hyK : y ∈ normalizer (K : Set H) := by
      rw [hyy]
      exact Subgroup.pow_mem _ hy2 _
    have := map_conj_eq_iff_mem_normalizer.2 hyK
    exact hne (h.symm.trans this)

end Component

section Transport

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {q : ℕ}

theorem mem_normalizer_component {d : TrialityD4Data L q} {t : G} {K : Subgroup G}
    (hK : IsLayerComponent d t K) (ht : t ∈ jZeroCentralizer d) {y : G}
    (hy : y ∈ jZeroCentralizer d) (hodd : Odd (orderOf y)) :
    y ∈ normalizer (K : Set G) := by
  set H : Subgroup G := jZeroCentralizer d with hH
  have hKH : K ≤ H := hK.le
  have hKtH : Kᵍ[t] ≤ H := by
    rintro _ ⟨k, hk, rfl⟩
    show t⁻¹ * k * t⁻¹⁻¹ ∈ H
    exact H.mul_mem (H.mul_mem (H.inv_mem ht) (hKH hk)) (H.inv_mem (H.inv_mem ht))
  set K0 : Subgroup H := K.subgroupOf H with hK0
  set K0' : Subgroup H := (Kᵍ[t]).subgroupOf H with hK0'
  have hmap0 : K0.map H.subtype = K := by
    rw [hK0, Subgroup.subgroupOf_map_subtype, inf_of_le_left hKH]
  have hmap0' : K0'.map H.subtype = Kᵍ[t] := by
    rw [hK0', Subgroup.subgroupOf_map_subtype, inf_of_le_left hKtH]
  have htinv : t⁻¹ ∈ H := H.inv_mem ht
  have hK0'eq : K0' = K0.map (MulAut.conj (⟨t⁻¹, htinv⟩ : H)).toMonoidHom := by
    apply Subgroup.map_injective H.subtype_injective
    rw [hmap0', Subgroup.map_map]
    have hc : H.subtype.comp (MulAut.conj (⟨t⁻¹, htinv⟩ : H)).toMonoidHom =
        (MulAut.conj t⁻¹).toMonoidHom.comp H.subtype := by
      ext x
      simp
    rw [hc, ← Subgroup.map_map, hmap0]
  have hcomp0 : CFSG.IsComponent K0 := hK.isComponent
  have hcomp0' : CFSG.IsComponent K0' := by
    rw [hK0'eq]
    exact CFSG.LocalCores.isComponent_map_mulEquiv _ hcomp0
  have hne : K0' ≠ K0 := by
    intro h
    apply hK.ne
    rw [← hmap0', ← hmap0, h]
  have hE : CFSG.layer ↥H = K0 ⊔ K0' := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, hmap0, hmap0']
    exact hK.layer_eq
  have hyH : Odd (orderOf (⟨y, hy⟩ : H)) := by
    rw [Subgroup.orderOf_mk]
    exact hodd
  have hfix := map_conj_component_eq_of_odd hcomp0 hcomp0' hne hE hyH
  refine mem_normalizer_fintype fun x hx => ?_
  have hx' : (⟨x, hKH hx⟩ : H) ∈ K0 := hx
  have : (MulAut.conj (⟨y, hy⟩ : H)).toMonoidHom ⟨x, hKH hx⟩ ∈
      K0.map (MulAut.conj (⟨y, hy⟩ : H)).toMonoidHom := ⟨_, hx', rfl⟩
  rw [hfix] at this
  exact this

end Transport

section ClaimA

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem mem_normalizer_pCore_kFour_sup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) {y : G}
    (hyD : y ∈ normalizer (yamadaD₅ d t : Set G))
    (hyC : y ∈ centralizer ((jZeroG d : Subgroup G) : Set G))
    (hyP : y ∈ normalizer (yamadaP d t : Set G)) (hodd : Odd (orderOf y)) :
    y ∈ normalizer ((pCoreOf 2 (kFour d t K) ⊔ yamadaD₅ d t : Subgroup G) : Set G) := by
  have hyH : y ∈ jZeroCentralizer d := hyC
  have ht : t ∈ jZeroCentralizer d := h.t_mem_centralizer_J₀ d
  have hKn : y ∈ normalizer (K : Set G) := mem_normalizer_component hK ht hyH hodd
  obtain ⟨-, -, -, hM6⟩ := B1_decomposition h d hp hK
  have hMn : y ∈ normalizer (yamadaM₆ d t : Set G) := hM6 hyP
  obtain ⟨-, -, -, -, -, -, -, -, -, hY2, -⟩ := T5_J₀ h d hp
  have hYn : y ∈ normalizer (yamadaY₂ d t : Set G) := by
    rw [← hY2]
    exact mem_normalizer_inf' hMn (Subgroup.le_normalizer hyH)
  have hK4 : y ∈ normalizer (kFour d t K : Set G) := mem_normalizer_kFour d t hKn hYn hMn
  have hO : y ∈ normalizer ((pCoreOf 2 (kFour d t K) : Subgroup G) : Set G) :=
    ClaimB.normalizer_le_normalizer_pCoreOf 2 _ hK4
  exact mem_normalizer_sup' hO hyD

end ClaimA

theorem sq_add_add_one_dvd_cube_sub_one (x : ℕ) (hx : 1 ≤ x) : x ^ 2 + x + 1 ∣ x ^ 3 - 1 := by
  refine ⟨x - 1, ?_⟩
  have h3 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ hx
  zify [hx, h3]
  ring

end ProductN1LayerD6Aux

theorem D6_of_D5 {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
    (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (pBar d t) (nOneBar d t))
    (hK : kBar d t ≤ nOneBar d t)
    (h4 : (∃ K₁ : Subgroup G, IsN1Factor d t K₁) ∨
      ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = (2 ^ f) ^ 6 ∧
        IsQuotientIso (nOne d t) (yamadaD₅ d t) (Matrix.SpecialLinearGroup (Fin 2) k)) :
    ∃ K₁ : Subgroup G, IsN1Factor d t K₁ := by
  rcases h4 with h4 | ⟨k, hkf, hkfin, hkcard, φ, hφs, hφk⟩
  · exact h4
  · exfalso
    have hlay := hp.layer
    have hf2 := hp.two_le
    haveI : Fintype k := Fintype.ofFinite k
    haveI : CharP k 2 := by
      obtain ⟨n, hn1, hn2⟩ := FiniteField.card k (ringChar k)
      have h1 : Fintype.card k = 2 ^ (6 * f) := by
        rw [← Nat.card_eq_fintype_card, hkcard, ← pow_mul, mul_comm]
      have h2 : ringChar k ∣ 2 ^ (6 * f) := by
        rw [← h1, hn2]
        exact dvd_pow_self _ n.ne_zero
      have h3 : ringChar k = 2 :=
        (Nat.prime_dvd_prime_iff_eq hn1 Nat.prime_two).1 (hn1.dvd_of_dvd_pow h2)
      exact h3 ▸ ringChar.charP k
    obtain ⟨K, hKc, -⟩ := A1_components h d hp
    obtain ⟨hDR, hRP⟩ := ProductN1LayerD6Aux.ClaimB.claimB h d hp hKc
    have hDP : yamadaD₅ d t ≤ yamadaP d t := yamadaD₅_le_yamadaP d t
    have hPD5 : yamadaP d t ≤ normalizer (yamadaD₅ d t : Set G) :=
      h.yamadaP_le_normalizer_yamadaD₅ d hlay
    have hPN : yamadaP d t ≤ nOne d t := by
      have h1 : pBar d t ≤ nOneBar d t := hSyl.le
      have h2 : NormalizerQuotient.lift (pBar d t) = yamadaP d t :=
        NormalizerQuotient.lift_bar hDP hPD5
      rw [← h2]
      exact NormalizerQuotient.lift_mono h1
    obtain ⟨-, hPp, -⟩ := h.yamada_5_32_of_layerHyp d hlay
    have hD2 : IsPGroup 2 (yamadaD₅ d t) := hPp.to_le hDP
    obtain ⟨-, -, -, -, hPcard, -⟩ := D1_centralizer_tbar h d hp
    have hPD : (yamadaD₅ d t).relIndex (yamadaP d t) = 2 ^ (2 * (3 * f)) := by
      rw [← ProductN1HatAux.card_bar hDP hPD5]
      show Nat.card (pBar d t) = _
      rw [hPcard, ← pow_mul]
      congr 1
      ring
    have hk : Nat.card k = 2 ^ (2 * (3 * f)) := by
      rw [hkcard, ← pow_mul]
      congr 1
      ring
    have hJ6 : jZeroG d ≤ d.J₆.map L.subtype := Subgroup.map_mono d.J₀_le_J₆
    have hJc : jZeroG d ≤ cLV d := by
      rintro _ ⟨j, hj, rfl⟩
      exact ⟨j, (d.J₀_le_J₆ hj).2, rfl⟩
    have hcLVN : cLV d ≤ nOne d t := by
      intro x hx
      have hxn : x ∈ normalizer (yamadaD₅ d t : Set G) :=
        ProductN1HatAux.cLV_le_normalizer_D5 h d hlay hx
      exact NormalizerQuotient.mem_lift_of_proj_mem (x := ⟨x, hxn⟩)
        (hK (NormalizerQuotient.proj_mem_bar (x := ⟨x, hxn⟩) hx))
    have hJN : jZeroG d ≤ nOne d t := hJc.trans hcLVN
    have hJP : jZeroG d ≤ normalizer (yamadaP d t : Set G) :=
      hJ6.trans (ProductN1HatAux.J6_le_normalizer_P h d hlay)
    have hJcomm : ∀ a ∈ jZeroG d, ∀ b ∈ jZeroG d, a * b = b * a := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have := d.J_commute (d.J₀_le_J ha) (d.J₀_le_J hb)
      show (a : G) * (b : G) = (b : G) * (a : G)
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, this]
    have hJcardeq : Nat.card (jZeroG d) = (2 ^ f) ^ 2 + 2 ^ f + 1 := by
      rw [show jZeroG d = d.J₀.map L.subtype from rfl,
        Subgroup.card_map_of_injective L.subtype_injective]
      exact d.yamada_three_five_four.2
    have hx1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have hJcard : Nat.card (jZeroG d) ∣ 2 ^ (3 * f) - 1 := by
      rw [hJcardeq, pow_mul']
      exact ProductN1LayerD6Aux.sq_add_add_one_dvd_cube_sub_one _ hx1
    have hJ1 : Nat.card (jZeroG d) ≠ 1 := by
      rw [hJcardeq]
      have : 0 < (2 ^ f) ^ 2 := by positivity
      omega
    have hinv : ∀ y ∈ nOne d t, y ∈ centralizer ((jZeroG d : Subgroup G) : Set G) →
        y ∈ normalizer (yamadaP d t : Set G) → Odd (orderOf y) →
        y ∈ normalizer ((pCoreOf 2 (kFour d t K) ⊔ yamadaD₅ d t : Subgroup G) : Set G) :=
      fun y hy hyC hyP hodd => ProductN1LayerD6Aux.mem_normalizer_pCore_kFour_sup h d hp hKc
        (NormalizerQuotient.lift_le_normalizer _ hy) hyC hyP hodd
    have key := ProductN1LayerD6Aux.eq_or_eq_of_odd_invariant (N := nOne d t)
      (D := yamadaD₅ d t) (P := yamadaP d t) (J := jZeroG d)
      (R := pCoreOf 2 (kFour d t K) ⊔ yamadaD₅ d t) φ hφs hφk hDP hPN hD2 (m := 3 * f)
      (by omega) hk hPD hJN hJP hJcomm hJcard hJ1 hDR.le hRP.le hinv
    rcases key with h1 | h1
    · exact hDR.ne h1.symm
    · exact hRP.ne h1

end D6Aux

section Statements

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem D5_lift (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    (nOneBar d t).Normal ∧
      (nOneBar d t ⊓ CFSG.oddCore (H1bar d t) = ⊥ ∧
        (nOneBar d t).map (piHat d t) = CFSG.layer (H1hat d t)) ∧
      (IsSylowOf 2 (pBar d t) (nOneBar d t) ∧ kBar d t ≤ nOneBar d t) ∧
      ((∃ K₁ : Subgroup G, IsN1Factor d t K₁) ∨
        ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = (2 ^ f) ^ 6 ∧
          IsQuotientIso (nOne d t) (yamadaD₅ d t) (Matrix.SpecialLinearGroup (Fin 2) k)) :=
  ProductN1LayerAux.D5_core GMSK.gmsLinearStandardLayerListKRankOne h d hp

theorem D6_product (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    ∃ K₁ : Subgroup G, IsN1Factor d t K₁ :=
  D6_of_D5 h d hp (D5_lift h d hp).2.2.1.1 (D5_lift h d hp).2.2.1.2 (D5_lift h d hp).2.2.2

end Statements

end CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
