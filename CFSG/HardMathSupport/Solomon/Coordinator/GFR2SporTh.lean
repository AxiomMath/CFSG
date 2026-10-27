module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporComp
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCrit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFive
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThThreeClose
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic
public import Certificates.Certificate36910
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Statements
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR1Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2Layer
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporRed
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.H13.J4OrderBase
public import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions
public import CFSG.RankThree.Native.ONSevenDefs
public import CFSG.RankThree.Native.ONSevenRestrict
public import CFSG.RankThree.PartOne.SPOR.OuterSimple
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import Certificates.Certificate16041
public import Certificates.Certificate2098
public import Certificates.Certificate2103
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate2173
public import Certificates.Certificate2178
public import Certificates.Certificate2179
public import Certificates.Certificate2274
public import Certificates.Certificate8137
public import Certificates.Certificate8138
public import Certificates.Certificate8139
public import Certificates.Certificate8140
public import Certificates.Certificate8141
public import Certificates.Certificate8145
public import Certificates.Certificate8146
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFive
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFiveNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
open scoped commutatorElement

section Generic

private theorem card_le_mul_of_conj {G : Type*} [Group G] [Finite G] {C K : Subgroup G} {u : G}
    (hK : ∀ x ∈ C, x * u * x⁻¹ ∈ K) :
    Nat.card C ≤ Nat.card K * Nat.card ↥(C ⊓ Subgroup.centralizer ({u} : Set G)) := by
  set D : Subgroup ↥C := (C ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf C with hD
  have hDcard : Nat.card D = Nat.card ↥(C ⊓ Subgroup.centralizer ({u} : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmem : ∀ z : ↥C, z ∈ D ↔ (z : G) * u = u * (z : G) := by
    intro z
    rw [hD, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => h.2, fun h => ⟨z.2, h⟩⟩
  have hconj : ∀ x y : ↥C,
      ((x : G) * u * (x : G)⁻¹ = (y : G) * u * (y : G)⁻¹) ↔ x⁻¹ * y ∈ D := by
    intro x y
    rw [hmem]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · intro h
      calc (x : G)⁻¹ * y * u = (x : G)⁻¹ * ((y : G) * u * (y : G)⁻¹) * y := by group
        _ = (x : G)⁻¹ * ((x : G) * u * (x : G)⁻¹) * y := by rw [h]
        _ = u * ((x : G)⁻¹ * y) := by group
    · intro h
      have hz : (x : G)⁻¹ * y * u * ((x : G)⁻¹ * y)⁻¹ = u := by rw [h]; group
      calc (x : G) * u * (x : G)⁻¹
          = (x : G) * ((x : G)⁻¹ * y * u * ((x : G)⁻¹ * y)⁻¹) * (x : G)⁻¹ := by rw [hz]
        _ = (y : G) * u * (y : G)⁻¹ := by group
  let φ : ↥C ⧸ D → K := Quotient.lift (s := QuotientGroup.leftRel D)
    (fun x : ↥C => (⟨(x : G) * u * (x : G)⁻¹, hK x x.2⟩ : K)) (fun x y hxy => by
      apply Subtype.ext
      exact (hconj x y).2 (QuotientGroup.leftRel_apply.1 hxy))
  have hφ : Function.Injective φ := by
    intro q₁ q₂ h
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q₁
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q₂
    have h' : (x : G) * u * (x : G)⁻¹ = (y : G) * u * (y : G)⁻¹ := congrArg Subtype.val h
    exact QuotientGroup.eq.2 ((hconj x y).1 h')
  have h1 : Nat.card (↥C ⧸ D) ≤ Nat.card K := Nat.card_le_card_of_injective φ hφ
  calc Nat.card C = Nat.card (↥C ⧸ D) * Nat.card D :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup D
    _ ≤ Nat.card K * Nat.card D := Nat.mul_le_mul_right _ h1
    _ = _ := by rw [hDcard]

private theorem map_centralizer_singleton_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (x : G) : (Subgroup.centralizer ({x} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set H) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul, hz]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hy

private theorem isSubnormal_map_centralizer_th {G H : Type*} [Group G] [Group H] (φ : G ≃* H)
    (s : G) {K : Subgroup G}
    (hsub : CFSG.Open.IsSubnormal K (Subgroup.centralizer ({s} : Set G))) :
    CFSG.Open.IsSubnormal (K.map φ.toMonoidHom) (Subgroup.centralizer ({φ s} : Set H)) ∧
      Nat.card (K.map φ.toMonoidHom) = Nat.card K := by
  refine ⟨?_, Subgroup.card_map_of_injective φ.injective⟩
  have h := hsub.map φ.toMonoidHom
  rwa [map_centralizer_singleton_mulEquiv φ s] at h

def NoSubnormal1080 (G : Type) [Group G] : Prop :=
  ∀ t : G, orderOf t = 3 → ∀ K : Subgroup G,
    CFSG.Open.IsSubnormal K (Subgroup.centralizer ({t} : Set G)) → Nat.card K = 1080 → False

theorem NoSubnormal1080.of_mulEquiv {G H : Type} [Group G] [Group H] (φ : G ≃* H)
    (hH : NoSubnormal1080 H) : NoSubnormal1080 G := by
  intro s hs K hsub hcard
  obtain ⟨hsub', hcard'⟩ := isSubnormal_map_centralizer_th φ s hsub
  exact hH (φ s) (by rw [MulEquiv.orderOf_eq]; exact hs) _ hsub' (by rw [hcard']; exact hcard)

private theorem card_inf_centralizer_conj {G : Type*} [Group G] (m u s : G) :
    Nat.card ↥(Subgroup.centralizer ({m * s * m⁻¹} : Set G) ⊓
      Subgroup.centralizer ({m * u * m⁻¹} : Set G)) =
    Nat.card ↥(Subgroup.centralizer ({s} : Set G) ⊓ Subgroup.centralizer ({u} : Set G)) := by
  rw [← map_conj_centralizer m s, ← map_conj_centralizer m u,
    ← Subgroup.map_inf _ _ _ (MulAut.conj m).injective, card_map_conj]

private theorem no_subnormal_1080_of_data {G : Type*} [Group G] [Finite G] {s : G}
    (hs : orderOf s = 3) {K : Subgroup G}
    (hsub : CFSG.Open.IsSubnormal K (Subgroup.centralizer ({s} : Set G))) (hK : Nat.card K = 1080)
    (hb : ∀ e : G, orderOf e = 5 → e * s = s * e →
      Nat.card ↥(Subgroup.centralizer ({s} : Set G) ⊓ Subgroup.centralizer ({e} : Set G)) ≤ 30)
    (h37 : 3 ^ 7 ∣ Nat.card (Subgroup.centralizer ({s} : Set G))) : False := by
  set C := Subgroup.centralizer ({s} : Set G) with hC
  have hKC : K ≤ C := le_of_isSubnormal_open hsub
  by_cases h5 : 5 ∣ Nat.card C
  swap
  · exact h5 ((by norm_num : 5 ∣ 1080).trans (hK ▸ Subgroup.card_dvd_of_le hKC))
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 5 h5
  have hu5 : orderOf (u : G) = 5 := by rw [Subgroup.orderOf_coe]; exact hu
  have huC : (u : G) ∈ C := u.2
  have hcommu : (u : G) * s = s * (u : G) := Subgroup.mem_centralizer_singleton_iff.1 huC
  have h25 : ¬ 25 ∣ Nat.card C := by
    intro hd
    obtain ⟨E, hE⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥C) 5 (n := 2) (by simpa using hd)
    have hE'card : Nat.card (E.map C.subtype) = 25 := by
      rw [Subgroup.card_map_of_injective C.subtype_injective, hE]
      norm_num
    have hE'C : E.map C.subtype ≤ C := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' (G := ↥(E.map C.subtype)) 5
      (by rw [hE'card]; norm_num)
    have he5 : orderOf (e : G) = 5 := by rw [Subgroup.orderOf_coe]; exact he
    have heE : (e : G) ∈ E.map C.subtype := e.2
    have heC : (e : G) ∈ C := hE'C heE
    have hes : (e : G) * s = s * (e : G) := Subgroup.mem_centralizer_singleton_iff.1 heC
    have hcomm : ∀ x y : ↥(E.map C.subtype), x * y = y * x :=
      IsPGroup.commutative_of_card_eq_prime_sq (p := 5) (by rw [hE'card]; norm_num)
    have hle : E.map C.subtype ≤ C ⊓ Subgroup.centralizer ({(e : G)} : Set G) := by
      refine le_inf hE'C fun x hx => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (hcomm ⟨x, hx⟩ e)
    have h25' : 25 ∣ Nat.card ↥(C ⊓ Subgroup.centralizer ({(e : G)} : Set G)) :=
      hE'card ▸ Subgroup.card_dvd_of_le hle
    have h5' : 5 ∣ Nat.card ↥(C ⊓ Subgroup.centralizer ({(e : G)} : Set G)) := by
      have hmem : (e : G) ∈ C ⊓ Subgroup.centralizer ({(e : G)} : Set G) :=
        ⟨heC, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
      have := Subgroup.orderOf_dvd_natCard _ hmem
      rwa [he5] at this
    have h3' : 3 ∣ Nat.card ↥(C ⊓ Subgroup.centralizer ({(e : G)} : Set G)) := by
      have hmem : s ∈ C ⊓ Subgroup.centralizer ({(e : G)} : Set G) :=
        ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl,
          Subgroup.mem_centralizer_singleton_iff.2 hes.symm⟩
      have := Subgroup.orderOf_dvd_natCard _ hmem
      rwa [hs] at this
    have h15 : 15 ∣ Nat.card ↥(C ⊓ Subgroup.centralizer ({(e : G)} : Set G)) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 5) h3' h5'
    have hle30 := hb (e : G) he5 hes
    have hpos : 0 < Nat.card ↥(C ⊓ Subgroup.centralizer ({(e : G)} : Set G)) := Nat.card_pos
    omega
  have hrel : ¬ 5 ∣ K.relIndex C := by
    intro hd
    apply h25
    have h := Subgroup.relIndex_mul_card K C
    rw [inf_eq_left.2 hKC, hK] at h
    have h' : 5 * 5 ∣ Nat.card C := h ▸ Nat.mul_dvd_mul hd (by norm_num : 5 ∣ 1080)
    simpa using h'
  have hco : ∀ g ∈ C, orderOf g = 5 → g ∈ K := fun g hg ho =>
    mem_of_isSubnormal_of_coprime hsub hg (by
      rw [ho]
      exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hrel)
  have hKconj : ∀ x ∈ C, x * (u : G) * x⁻¹ ∈ K := fun x hx =>
    hco _ (C.mul_mem (C.mul_mem hx huC) (C.inv_mem hx)) (by
      rw [orderOf_conj_eq x (u : G)]
      exact hu5)
  have hup : Nat.card C ≤ 1080 * 30 :=
    (card_le_mul_of_conj hKconj).trans (hK ▸ Nat.mul_le_mul_left _ (hb (u : G) hu5 hcommu))
  obtain ⟨r, hr⟩ := Subgroup.card_dvd_of_le hKC
  rw [hK] at hr
  have hpos : 0 < Nat.card C := Nat.card_pos
  have h37' : 2187 ∣ Nat.card C := by simpa using h37
  omega

end Generic

set_option quotPrecheck false in
local notation "JTh" => ↥CFSG.Sporadic.Th.J

section Th


local notation "R5" => slpJ a b prog5

local notation "c5" => R5 94 * R5 105 * R5 94 ^ 4 * R5 105 ^ 4


theorem thPump_bound {t : JTh} (ht3 : orderOf t = 3) (htc : t * c5 = c5 * t) :
    Nat.card ↥(Subgroup.centralizer ({c5} : Set JTh) ⊓
      Subgroup.centralizer ({t} : Set JTh)) ≤ 30 :=
  Certificates.certificate36910 ht3 htc

theorem exists_conj_c5 {u : JTh} (hu : orderOf u = 5) : ∃ m : JTh, m * u * m⁻¹ = c5 :=
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFive.exists_conj_c5 hu

set_option maxRecDepth 20000 in
theorem thPump_bound_conj {u s : JTh} (hu : orderOf u = 5) (hs : orderOf s = 3)
    (hus : u * s = s * u) :
    Nat.card ↥(Subgroup.centralizer ({s} : Set JTh) ⊓
      Subgroup.centralizer ({u} : Set JTh)) ≤ 30 := by
  obtain ⟨m, hm⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_c5 hu
  have ht3 : orderOf (m * s * m⁻¹) = 3 := by rw [orderOf_conj_eq]; exact hs
  have htc : (m * s * m⁻¹) * c5 = c5 * (m * s * m⁻¹) := by
    rw [← hm]
    calc m * s * m⁻¹ * (m * u * m⁻¹) = m * (s * u) * m⁻¹ := by group
      _ = m * (u * s) * m⁻¹ := by rw [hus]
      _ = _ := by group
  have h := thPump_bound ht3 htc
  rw [← card_inf_centralizer_conj m u s, hm, inf_comm]
  exact h

set_option maxRecDepth 20000 in
theorem no_subnormal_1080_J
    {s : JTh} (hs : orderOf s = 3) {K : Subgroup JTh}
    (hsub : CFSG.Open.IsSubnormal K (Subgroup.centralizer ({s} : Set JTh)))
    (hK : Nat.card K = 1080) : False := by
  have : Finite JTh := finite_J
  refine no_subnormal_1080_of_data hs hsub hK (fun e he hes => thPump_bound_conj he hs hes) ?_
  obtain ⟨⟨P, hPC, hP3, hP7⟩, -⟩ := thThreeResidual_holds s hs
  obtain ⟨a, ha⟩ := hP3.exists_card_eq
  have ha7 : 7 ≤ a := (Nat.pow_le_pow_iff_right (by norm_num)).1 (ha ▸ hP7)
  exact (pow_dvd_pow 3 ha7).trans (ha ▸ Subgroup.card_dvd_of_le hPC)

theorem noSubnormal1080_J :
    NoSubnormal1080 JTh := fun _ hs _ hsub hK => no_subnormal_1080_J hs hsub hK

end Th

set_option maxRecDepth 20000 in
theorem sporNoPumpup_Th
    (hSpM : SporadicMultipliers) (hOG : UniquenessMaximal.InputONGroup)
    (hOut : SporadicOuterLeTwo) (hbr : SporadicBridges) : SporNoPumpup .Th := by
  let φ : (TauCeti.CFSGIndex.sporadic .Th).Group ≃* ↥CFSG.Sporadic.Th.J :=
    (hbr .Th).some.symm.trans thEquivJ
  haveI : Finite (TauCeti.CFSGIndex.sporadic .Th).Group := Finite.of_equiv _ φ.symm.toEquiv
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.sporadic .Th).Group :=
    @MulEquiv.isSimpleGroup _ _ _ _ (CFSG.Sporadic.Th.Kernel.isSimpleGroup_Th th_kernel_facts)
      (hbr .Th).some.symm
  have hN : NoSubnormal1080 (TauCeti.CFSGIndex.sporadic .Th).Group :=
    NoSubnormal1080.of_mulEquiv (G := (TauCeti.CFSGIndex.sporadic .Th).Group)
      (H := ↥CFSG.Sporadic.Th.J) φ noSubnormal1080_J
  refine sporNoPumpup_of_components hSpM hOG hOut ?_ ?_ ?_ ?_
  · rw [Nat.card_congr φ.toEquiv, CFSG.Sporadic.Th.Max3.natCard_J]
    rfl
  · exact sporadicOPrimeHolds_Th_three _ ⟨(hbr .Th).some.symm⟩
  · intro s hs K hK h
    rcases h with h | ⟨hM, -⟩
    · exact hN s hs K hK.2.1 (card_of_isHatSix h)
    · exact absurd hM (by decide)
  · intro h3
    exact absurd h3 (by decide)

end CFSG.HardMathSupport.Solomon.Coordinator
