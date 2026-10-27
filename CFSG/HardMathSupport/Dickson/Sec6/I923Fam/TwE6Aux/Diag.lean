module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.E6Aux.Diag
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Diag
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.ClassicalInvolution.Orders.Twisted
public import CFSG.RankThree.PartOne.TCX.Tri.TorusCentral
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.Foundations
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcField
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Reduction
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.OrdinaryRootCentralizerGeneration
public import CFSG.LieType.Chevalley.SignKernelComponentPerfect
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Chevalley.SteinbergBIE7ThreeA1
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate9130

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.Timmesfeld.ExceptionalOrders CFSG.ClassicalInvolution CFSG.HardMathSupport.Lang.Coordinator
  CFSG.RankThree.PartOne.TCX.Tri
open Subgroup

theorem e6Perm_symm : e6Perm.symm = e6Perm := by
  ext i
  fin_cases i <;> rfl

section TwDiag


variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

abbrev TwM := (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ

@[expose] noncomputable def twCompatHom : TwM σ →* (Fin Tag.E6.rank → Kˣ) where
  toFun u := compatDiag TwistTag.E6 σ.toRingHom u
  map_one' := compatDiag_one
  map_mul' := compatDiag_mul

@[expose] def twRho : TwM σ →* TwM σ where
  toFun u := orbitUnitsMap σ.toRingHom (ringEquiv_comm_of_finite σ σ) u
  map_one' := by
    funext a
    exact Units.ext (Subtype.ext (map_one σ))
  map_mul' u v := by
    funext a
    exact Units.ext (Subtype.ext (map_mul σ _ _))

theorem twCompatHom_twRho (u : TwM σ) : twCompatHom σ (twRho σ u) = e6Rho K (twCompatHom σ u) := by
  change compatDiag TwistTag.E6 σ.toRingHom (orbitUnitsMap σ.toRingHom
    (ringEquiv_comm_of_finite σ σ) u) = _
  have h := compatDiag_orbitUnitsMap (t := TwistTag.E6) (σ := σ.toRingHom) (δ := σ)
    (ringEquiv_comm_of_finite σ σ) u
  rw [h]
  funext i
  change Units.map σ.toRingHom.toMonoidHom (compatDiag TwistTag.E6 σ.toRingHom u i) =
    compatDiag TwistTag.E6 σ.toRingHom u (e6Perm.symm i)
  rw [e6Perm_symm]
  exact (compatDiag_perm u i).symm

theorem fieldActor_conj_compatDiagAutHom (u : TwM σ) :
    fieldActor (t := TwistTag.E6) σ σ * compatDiagAutHom TwistTag.E6 K σ.toRingHom u *
        (fieldActor (t := TwistTag.E6) σ σ)⁻¹ =
      compatDiagAutHom TwistTag.E6 K σ.toRingHom (twRho σ u) :=
  mul_inv_eq_iff_eq_mul.2 (fieldActor_mul_compatDiagAutHom σ σ u)

@[expose] def twS : Subgroup (Fin Tag.E6.rank → Kˣ) :=
  compatSubgroup (t := TwistTag.E6) σ.toRingHom

@[expose] def twZ : (Fin Tag.E6.rank → Kˣ) →* (Fin Tag.E6.rank → Kˣ) :=
  zpowMatrix (G := Kˣ) Tag.E6.cartan

theorem twCompatHom_mem (u : TwM σ) : twCompatHom σ u ∈ twS σ := fun i => compatDiag_perm u i

@[expose] noncomputable def twCompatHomS : TwM σ →* ↥(twS σ) :=
  (twCompatHom σ).codRestrict (twS σ) (twCompatHom_mem σ)

theorem twCompatHomS_surjective : Function.Surjective (twCompatHomS σ) := by
  rintro ⟨b, hb⟩
  obtain ⟨u, hu⟩ := exists_compatDiag_eq (t := TwistTag.E6) (σ := σ.toRingHom) hb
  exact ⟨u, Subtype.ext hu⟩

@[expose] noncomputable def twIm : Subgroup (TwM σ) := ((twS σ).map (twZ)).comap (twCompatHom σ)

theorem twIm_index {q : ℕ} (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q) :
    (twIm σ).index = Nat.gcd 3 (q + 1) := by
  classical
  have hσ' : ∀ c, σ.toRingHom c = c ^ q := hσ
  set S := twS σ with hS
  let g : ↥S →* ↥S := ((twZ (K := K)).domRestrict S).codRestrict S
    (fun x => zpowMatrix_cartan_mem_compatSubgroup x.2)
  have hrange : g.range = ((S.map (twZ (K := K))).subgroupOf S) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
  have hIm : twIm σ = ((S.map (twZ (K := K))).subgroupOf S).comap (twCompatHomS σ) := rfl
  have hidx : (twIm σ).index = ((S.map (twZ (K := K))).subgroupOf S).index := by
    rw [hIm]
    exact Subgroup.index_comap_of_surjective _ (twCompatHomS_surjective σ)
  rw [hidx, ← hrange]
  have h1 := Subgroup.card_ker_mul_card_range g
  have h2 := Subgroup.card_mul_index g.range
  have hpos : 0 < Nat.card g.range := Nat.card_pos
  have h3 : g.range.index = Nat.card g.ker := by
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [h2, mul_comm, h1]
  rw [h3]
  have h4 : g.ker = ((S ⊓ (twZ (K := K)).ker).subgroupOf S) := by
    ext x
    constructor
    · intro hx
      have hx' : twZ (K := K) (x : Fin Tag.E6.rank → Kˣ) = 1 := congrArg Subtype.val hx
      exact ⟨x.2, hx'⟩
    · intro hx
      exact Subtype.ext hx.2
  rw [h4, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left :
    S ⊓ (twZ (K := K)).ker ≤ S)).toEquiv]
  exact card_compat_inf_ker_E6_of_card hK hσ'

theorem compatDiagAutHom_mem_inner_of_mem_twIm {u : TwM σ} (hu : u ∈ twIm σ) :
    compatDiagAutHom TwistTag.E6 K σ.toRingHom u ∈ twistedE6Inn K σ := by
  obtain ⟨c, hc, hcb⟩ := hu
  have hT : (torusCoordHom TwistTag.E6.tag K c : ModGL TwistTag.E6.tag K) ∈
      compatTorus (t := TwistTag.E6) σ.toRingHom :=
    (mem_compatTorus σ.toRingHom).2 ⟨c, hc, rfl⟩
  have h := compatTorus_le_graphFixedRootGroup (t := TwistTag.E6) (K := K) σ.toRingHom hT
  rw [torusCoordHom_eq_rootDiagUnit (τ := TwistTag.E6.tag) (K := K) c] at h
  have hcb' : zpowMatrix (G := Kˣ) TwistTag.E6.tag.cartan c = compatDiag TwistTag.E6 σ.toRingHom u :=
    hcb
  rw [hcb'] at h
  refine ⟨⟨_, h⟩, ?_⟩
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [coe_compatDiagAutHom]
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]

@[expose] noncomputable def twKappa : TwM σ →* Kˣ ⧸ e6Cubes K := (e6Kappa K).comp (twCompatHom σ)

theorem twKappa_twIm {u : TwM σ} (hu : u ∈ twIm σ) : twKappa σ u = 1 := by
  obtain ⟨c, hc, hcb⟩ := hu
  change e6Kappa K (twCompatHom σ u) = 1
  rw [← hcb]
  have : twZ (K := K) c = monomialHom (G := Kˣ) Tag.E6.cartan.transpose c := by
    funext j
    simp [twZ, zpowMatrix_apply, monomialHom_apply, Matrix.transpose_apply]
  rw [this]
  exact e6Kappa_monomialHom K c

theorem twKappa_twRho_mul (u : TwM σ) : twKappa σ (twRho σ u * u) = 1 := by
  change e6Kappa K (twCompatHom σ (twRho σ u * u)) = 1
  rw [map_mul, twCompatHom_twRho]
  exact e6Kappa_rho_mul K _

theorem pow_not_mem_cubes {G : Type*} [CommGroup G] [Finite G] {g : G}
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (h3 : 3 ∣ Nat.card G) {n : ℕ} (hn : ¬ 3 ∣ n) :
    g ^ n ∉ (powMonoidHom 3 : G →* G).range := by
  rintro ⟨v, hv⟩
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg v)
  have h1 : g ^ (n : ℤ) = g ^ (m * 3) := by
    rw [zpow_natCast, ← hv, zpow_mul]
    simp
  have h2 := (zpow_eq_zpow_iff_modEq).1 h1
  rw [orderOf_eq_card_of_forall_mem_zpowers hg] at h2
  have h3z : (3 : ℤ) ∣ (Nat.card G : ℤ) := by exact_mod_cast h3
  have h4 := h3z.trans h2.dvd
  omega

theorem exists_twKappa_ne_one {q : ℕ} (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q)
    (h3 : 3 ∣ q + 1) : ∃ u : TwM σ, twKappa σ u ≠ 1 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hσσ : ∀ c : Kˣ, Units.map σ.toMonoidHom (Units.map σ.toMonoidHom c) = c := fun c => by
    refine Units.ext ?_
    change σ (σ (c : K)) = c
    rw [hσ, hσ]
    exact CFSG.LieType.Simplicity.pow_pow_card_sq hK _
  let b : Fin Tag.E6.rank → Kˣ := ![g, 1, 1, 1, 1, Units.map σ.toMonoidHom g]
  have hb : ∀ i, b (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (b i) := by
    intro i
    fin_cases i
    · exact rfl
    · exact (map_one _).symm
    · exact (map_one _).symm
    · exact (map_one _).symm
    · exact (map_one _).symm
    · exact (hσσ g).symm
  obtain ⟨u, hu⟩ := exists_compatDiag_eq (t := TwistTag.E6) (σ := σ.toRingHom) hb
  refine ⟨u, fun h1 => ?_⟩
  change QuotientGroup.mk' (e6Cubes K) (e6Phi K (compatDiag TwistTag.E6 σ.toRingHom u)) = 1 at h1
  rw [hu] at h1
  have hgq : Units.map σ.toMonoidHom g = g ^ q := by
    refine Units.ext ?_
    change σ (g : K) = ((g ^ q : Kˣ) : K)
    rw [hσ]
    simp
  have h2 : e6Phi K b = g ^ (1 + 2 * q) := by
    change ∏ i : Fin 6, (b i) ^ e6Lam i = _
    rw [Fin.prod_univ_six]
    have hgq2 : (Units.map (((σ : K →+* K) : K →* K))) g = g ^ q := hgq
    simp [b, e6Lam, hgq2]
    rw [← pow_mul, show 1 + 2 * q = 1 + q * 2 by ring, pow_add, pow_one]
  rw [h2] at h1
  have hKc : Nat.card Kˣ = q ^ 2 - 1 := by
    have : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  have h3K : 3 ∣ Nat.card Kˣ := by
    rw [hKc]
    have : q ^ 2 % 3 = 1 := by
      rw [Nat.pow_mod]
      have : q % 3 = 2 := by omega
      rw [this]
    omega
  have h4 : ¬ 3 ∣ 1 + 2 * q := by omega
  exact pow_not_mem_cubes hg h3K h4 ((QuotientGroup.eq_one_iff _).1 h1)

theorem compatDiagAutHom_range_le_commutator {q : ℕ} (hK : Nat.card K = q ^ 2)
    (hσ : ∀ c, σ c = c ^ q) (hC : commutator (twistedE6RootGroup K σ) = ⊤) :
    (compatDiagAutHom TwistTag.E6 K σ.toRingHom).range ≤
      commutator (MulAut (twistedE6RootGroup K σ)) := by
  rintro _ ⟨u, rfl⟩
  by_cases h3 : 3 ∣ q + 1
  · have hIm : (twIm σ).index ∣ 3 := by
      rw [twIm_index σ hK hσ]
      exact Nat.gcd_dvd_left _ _
    have hImC : ∀ b ∈ twIm σ, compatDiagAutHom TwistTag.E6 K σ.toRingHom b ∈
        commutator (MulAut (twistedE6RootGroup K σ)) := fun b hb =>
      innerAut_le_commutator_of_perfect hC (compatDiagAutHom_mem_inner_of_mem_twIm σ hb)
    have hκ1 : (∀ b, twKappa σ b = 1) → ¬ 3 ∣ Nat.card (TwM σ) := fun h =>
      absurd h (by
        obtain ⟨u, hu⟩ := exists_twKappa_ne_one σ hK hσ h3
        exact fun hall => hu (hall u))
    exact diag_mem_commutator (G := MulAut (twistedE6RootGroup K σ)) (M := TwM σ)
      (Q := Kˣ ⧸ e6Cubes K) (compatDiagAutHom TwistTag.E6 K σ.toRingHom) (twRho σ)
      (fieldActor (t := TwistTag.E6) σ σ) (fieldActor_conj_compatDiagAutHom σ) (twIm σ) hIm hImC
      (twKappa σ) (e6Kappa_pow_three K) (fun b hb => twKappa_twIm σ hb) (twKappa_twRho_mul σ)
      hκ1 u
  · have hgcd : Nat.gcd 3 (q + 1) = 1 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
    exact innerAut_le_commutator_of_perfect hC (compatDiagAutHom_mem_inner hK hσ hgcd u)

theorem twistedE6Inndiag_le_commutator {q : ℕ} (hK : Nat.card K = q ^ 2)
    (hσ : ∀ c, σ c = c ^ q) (hC : commutator (twistedE6RootGroup K σ) = ⊤) :
    twistedE6Inn K σ ⊔ twistedE6Diag K σ ≤ commutator (MulAut (twistedE6RootGroup K σ)) :=
  sup_le (innerAut_le_commutator_of_perfect hC) (compatDiagAutHom_range_le_commutator σ hK hσ hC)

end TwDiag

end CFSG.HardMathSupport.Dickson.Sec6.I923
