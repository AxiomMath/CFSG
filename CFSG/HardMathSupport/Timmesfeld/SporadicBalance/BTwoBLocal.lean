module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeBFour
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterKleinTwo
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2Three
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FiLocal
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseCo2Local
public import CFSG.Monster.B.CTIB.Rep4371Rho
public import CFSG.Monster.B.CTIB.UniqueComponent
public import CFSG.Sporadic.Co2
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FiTransp
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterTwoA
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.SectionAssembly
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.Schreier.RuLocal
public import CFSG.Sporadic.SchreierLemmas.FrattiniProfile
public import CFSG.Sporadic.SmallOddCore.CentSpec
public import CFSG.Sporadic.ThSchreier.ThSchreierCase
public import Certificates.Certificate10027
public import Certificates.Certificate10107
public import Certificates.Certificate10108
public import Certificates.Certificate10110
public import Certificates.Certificate10111
public import Certificates.Certificate13636Base
public import Certificates.Certificate2323
public import Certificates.Certificate8026Base
public import Certificates.Certificate9124
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Monster.GMS
  CFSG.Blueprint.NativeSporadic CFSG.Monster.B

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Generic

variable {G : Type*} [Group G]

theorem pow_two_pow_eq_one_of_local_quotient [Finite G] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Type*} [Group K] {x : G} (F : ↥(Subgroup.centralizer ({x} : Set G)) →* K)
    (hF : Function.Surjective F) (hker : Nat.card F.ker = 2 ^ n) (hK : OPrimeCoreTrivialAt p K)
    {s : G} (hs : orderOf s = p) (hsx : s ∈ Subgroup.centralizer ({x} : Set G))
    {q : G} (hq : q ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)))
    (hqx : q ∈ Subgroup.centralizer ({x} : Set G)) : q ^ (2 ^ n) = 1 := by
  have hN : Nat.Coprime p (Nat.card F.ker) := by
    rw [hker]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  let e := QuotientGroup.quotientKerEquivOfSurjective F hF
  set Y := GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)) ⊓
    Subgroup.centralizer ({x} : Set G) with hY
  have hYH : Y ≤ Subgroup.centralizer ({x} : Set G) := inf_le_right
  have hYs : ∀ y ∈ Y, y * s = s * y := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.1 (GLAPPrimeCoreOf_le _ hy.1)
  have hYn : ∀ g ∈ Subgroup.centralizer ({x} : Set G), g * s = s * g → ∀ y ∈ Y,
      g * y * g⁻¹ ∈ Y := fun g hg hgs y hy =>
    ⟨GLAPPrimeCoreOf_conj_mem g (Subgroup.mem_centralizer_singleton_iff.2 hgs) y hy.1,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hy.2) (Subgroup.inv_mem _ hg)⟩
  have hYc : Nat.Coprime p (Nat.card Y) :=
    (coprime_card_GLAPPrimeCoreOf hp _).coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
  have hmem := mem_of_oPrimeCoreTrivial_quotient hp (H := Subgroup.centralizer ({x} : Set G))
    (N := F.ker) hN e hK hsx hs hYH hYs hYn hYc q ⟨hq, hqx⟩
  have hpow := pow_card_eq_one' (G := ↥F.ker) (x := ⟨⟨q, hqx⟩, hmem⟩)
  rw [hker] at hpow
  have h := congrArg (fun z : ↥F.ker => ((z : ↥(Subgroup.centralizer ({x} : Set G))) : G)) hpow
  simpa using h

end Generic

theorem oPrimeCoreTrivialAt_Co2_three :
    OPrimeCoreTrivialAt 3 Co2 :=
  OPrimeCoreTrivialAt.of_mulEquiv CFSG.Sporadic.Co2Cert.co2PermEquiv Co2T.oPrimeCoreTrivialAt_co2P

section Iso


@[expose] noncomputable def bToShatHom : B →* CFSG.Monster.B.TwoA.Shat := by
  with_reducible_and_instances exact (CTIB.iotaEquiv.trans CTIB.sEquiv).toMonoidHom

@[expose] noncomputable def bCbarHom : B →* Cbar :=
  CTIB.cbarEquiv.symm.toMonoidHom.comp bToShatHom

theorem bCbarHom_apply (x : B) :
    bCbarHom x = CTIB.cbarEquiv.symm ((CTIB.iotaEquiv.trans CTIB.sEquiv) x) := rfl

theorem bCbarHom_injective : Function.Injective bCbarHom := by
  intro x y h
  rw [bCbarHom_apply, bCbarHom_apply] at h
  exact (CTIB.iotaEquiv.trans CTIB.sEquiv).injective (CTIB.cbarEquiv.symm.injective h)

@[expose] noncomputable def xB : B := (CTIB.iotaEquiv.trans CTIB.sEquiv).symm (CTIB.cbarEquiv xbar)

theorem bCbarHom_xB : bCbarHom xB = xbar := by
  rw [bCbarHom_apply, xB, MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]

end Iso

section IsoJ


theorem map_centralizer_xB : (Subgroup.centralizer ({xB} : Set B)).map bCbarHom = Jbar := by
  rw [← centralizer_xbar]
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    rw [← bCbarHom_xB, ← map_mul, ← map_mul, hx]
  · intro hy
    refine ⟨(CTIB.iotaEquiv.trans CTIB.sEquiv).symm (CTIB.cbarEquiv y), ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      apply bCbarHom_injective
      rw [map_mul, map_mul, bCbarHom_xB, bCbarHom_apply, MulEquiv.apply_symm_apply,
        MulEquiv.symm_apply_apply]
      exact hy
    · rw [bCbarHom_apply, MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]

@[expose] noncomputable def centralizerXBEquiv :
    ↥(Subgroup.centralizer ({xB} : Set B)) ≃* ↥Jbar :=
  (Subgroup.equivMapOfInjective _ bCbarHom bCbarHom_injective).trans
    (MulEquiv.subgroupCongr map_centralizer_xB)

@[expose] noncomputable def centralizerXBHom : ↥(Subgroup.centralizer ({xB} : Set B)) →* ↥Jbar := by
  with_reducible_and_instances exact centralizerXBEquiv.toMonoidHom

theorem centralizerXBHom_apply (x : ↥(Subgroup.centralizer ({xB} : Set B))) :
    centralizerXBHom x = centralizerXBEquiv x := rfl

theorem centralizerXBHom_bijective : Function.Bijective centralizerXBHom := by
  refine ⟨fun x y h => ?_, fun y => ⟨centralizerXBEquiv.symm y, ?_⟩⟩
  · rw [centralizerXBHom_apply, centralizerXBHom_apply] at h
    exact centralizerXBEquiv.injective h
  · rw [centralizerXBHom_apply, MulEquiv.apply_symm_apply]

end IsoJ

section IsoCo2


theorem exists_hom_centralizer_xB :
    ∃ F : ↥(Subgroup.centralizer ({xB} : Set B)) →* Co2,
      Function.Surjective F ∧ Nat.card F.ker = 2 ^ 23 := by
  obtain ⟨f, hf, hker⟩ := CFSG.ComponentClassification.BMCase.jbar_exact_sequence
  refine ⟨f.comp centralizerXBHom, hf.comp centralizerXBHom_bijective.2, ?_⟩
  have hker' : (f.comp centralizerXBHom).ker = f.ker.comap centralizerXBHom :=
    MonoidHom.comap_ker _ _
  rw [hker', hker]
  have h1 : Nat.card ↥((Ebar.subgroupOf Jbar).comap centralizerXBHom) =
      Nat.card ↥(Ebar.subgroupOf Jbar) :=
    Nat.card_congr ((Equiv.ofBijective _ centralizerXBHom_bijective).subtypeEquiv
      fun x => Iff.rfl)
  rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Ebar_le_Jbar).toEquiv,
    Ebar_extraspecial.2]

end IsoCo2

section IsoCo2Card


theorem babyInv_one_xB : BabyInv 1 xB := by
  refine ⟨?_, ?_⟩
  · rw [← orderOf_injective bCbarHom bCbarHom_injective xB, bCbarHom_xB]
    exact orderOf_xbar
  · obtain ⟨f, hf, hker⟩ := CFSG.ComponentClassification.BMCase.jbar_exact_sequence
    have h1 := Subgroup.card_ker_mul_card_of_surjective hf
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Ebar_le_Jbar).toEquiv,
      Ebar_extraspecial.2, CFSG.Sporadic.Co2.card_Co2] at h1
    rw [Nat.card_congr (Equiv.ofBijective _ centralizerXBHom_bijective), ← h1]
    simp [babyCentOrder]


end IsoCo2Card

section Local


theorem pow_eq_one_of_mem_centralizer_xB {s : B} (hs : orderOf s = 3)
    (hsx : s ∈ Subgroup.centralizer ({xB} : Set B)) {q : B}
    (hq : q ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set B)))
    (hqx : q ∈ Subgroup.centralizer ({xB} : Set B)) : q ^ (2 ^ 23) = 1 := by
  have hfin : Finite B :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.RankThree.OddKernel.card_B_eq]; norm_num)
  obtain ⟨F, hF, hker⟩ := exists_hom_centralizer_xB
  exact pow_two_pow_eq_one_of_local_quotient Nat.prime_three (by norm_num) F hF hker
    oPrimeCoreTrivialAt_Co2_three hs hsx hq hqx

end Local

section TwoBLocal


theorem bTwoBLocalThree : BTwoBLocalThree := by
  have hfin : Finite B :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.RankThree.OddKernel.card_B_eq]; norm_num)
  intro s t hs ht hts q hq hqt
  obtain ⟨c, hc⟩ := isConj_iff.1 (CFSG.Monster.Existence.babyTableIII.2 1 t xB ht babyInv_one_xB)
  have hs' : orderOf (c * s * c⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hs
  have hsx : c * s * c⁻¹ ∈ Subgroup.centralizer ({xB} : Set B) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hc]
    have h := Subgroup.mem_centralizer_singleton_iff.1 hts
    calc c * s * c⁻¹ * (c * t * c⁻¹) = c * (s * t) * c⁻¹ := by group
      _ = c * (t * s) * c⁻¹ := by rw [h]
      _ = c * t * c⁻¹ * (c * s * c⁻¹) := by group
  have hq' := @conj_mem_gLAPPrimeCoreOf_centralizer B (inferInstance : Group B) 3 c s q hq
  have hqx : c * q * c⁻¹ ∈ Subgroup.centralizer ({xB} : Set B) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hc]
    have h := Subgroup.mem_centralizer_singleton_iff.1 hqt
    calc c * q * c⁻¹ * (c * t * c⁻¹) = c * (q * t) * c⁻¹ := by group
      _ = c * (t * q) * c⁻¹ := by rw [h]
      _ = c * t * c⁻¹ * (c * q * c⁻¹) := by group
  have h1 := pow_eq_one_of_mem_centralizer_xB hs' hsx hq' hqx
  refine ⟨23, ?_⟩
  have h2 : c * q ^ (2 ^ 23) * c⁻¹ = 1 := by
    rw [← conj_pow]
    exact h1
  calc q ^ (2 ^ 23) = c⁻¹ * (c * q ^ (2 ^ 23) * c⁻¹) * c := by group
    _ = 1 := by rw [h2]; group

theorem gLAPPrimeCoreOf_B_eq_bot_of_three_central_twoB {s : B} (hs : orderOf s = 3)
    (h13 : 3 ^ 13 ∣ Nat.card (Subgroup.centralizer ({s} : Set B)))
    {a b : B} (haC : a ∈ Subgroup.centralizer ({s} : Set B))
    (hbC : b ∈ Subgroup.centralizer ({s} : Set B)) (ha : BabyInv 1 a) (hb : BabyInv 1 b)
    (hab : BabyInv 1 (a * b)) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set B)) = ⊥ :=
  gLAPPrimeCoreOf_B_eq_bot_of_three_central_four bTwoBLocalThree hs h13 haC hbC ha hb hab

end TwoBLocal

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
