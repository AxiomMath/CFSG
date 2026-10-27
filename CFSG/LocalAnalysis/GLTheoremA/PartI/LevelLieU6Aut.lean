module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU3
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenVac
import CFSG.LocalAnalysis.GLTheoremA.PComp
import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
import CFSG.LocalAnalysis.GLTheoremA.Pump
import CFSG.LocalAnalysis.GLTheoremA.S6.AltSetup
import CFSG.HardMathSupport.Timmesfeld.Proving.OmegaPiGroup
import CFSG.LocalAnalysis.GLTheoremB.GammaStarConj
import CFSG.Foundations.KCoreOpen
import CFSG.Fischer.F4
public import CFSG.Blueprint.LieModelAPI
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LargeExtraspecial.OfFStar
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1412Levels
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.Models.Transport
public import CFSG.Quasithin.H13.J4Order
import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieU6

open CFSG.Open CFSG.Fischer CFSG.StandardType CFSG.Assembly
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

abbrev M6 : Type := StatedSU 6 (2 ^ 1) F4

abbrev S6 : Type := StatedProj (StatedSU 6 (2 ^ 1) F4)

abbrev mM6 (x : M6) : Matrix (Fin 6) (Fin 6) F4 := ((x : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)

theorem exists_unitary_of_pow_three (β : MulAut S6) (hβ : β ^ 3 = 1) :
    ∃ B : GL (Fin 6) F4, B ∈ primeFormUnitary hF4 (idGram F4 6) ∧
      (∃ c : F4ˣ, B ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c) ∧
      ∀ u v : M6, (v : GL (Fin 6) F4) = B * u * B⁻¹ →
        β (QuotientGroup.mk u) = QuotientGroup.mk v := by
  have hd : 3 ≤ 6 := by norm_num
  have hq : ¬ (6 = 3 ∧ 2 ^ 1 = 2) := by norm_num
  let β' : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) F4 (2 ^ 1))) := β
  have hβ' : β' ^ 3 = 1 := hβ
  obtain ⟨B, hB, hsem⟩ := InndiagSU.exists_isSemilin hF4 hd hq β'
  have hφ : InndiagSU.fieldFactorU hF4 hd hq β' = 1 := by
    set φ := InndiagSU.fieldFactorU hF4 hd hq β' with hφdef
    have h3 : φ ^ 3 = 1 := by rw [hφdef, ← map_pow, hβ', map_one]
    have h2 : φ ^ Nat.card (F4 ≃+* F4) = 1 := pow_card_eq_one'
    rw [card_ringEquiv_F4] at h2
    have := (pow_gcd_eq_one (a := φ)).2 ⟨h3, h2⟩
    rwa [show Nat.gcd 3 2 = 1 from rfl, pow_one] at this
  rw [hφ] at hsem
  have hconj : ∀ u v : M6, (v : GL (Fin 6) F4) = B * u * B⁻¹ →
      β (QuotientGroup.mk u) = QuotientGroup.mk v := by
    intro u v huv
    exact hsem u v (by rw [huv, map_one, MulAut.one_apply])
  refine ⟨B, hB, ?_, hconj⟩
  have hpow := hsem.pow hF4 hB 3
  rw [hβ', one_pow] at hpow
  have hN : InndiagSU.semilinNorm B (1 : F4 ≃+* F4) 3 = B ^ 3 := by
    simp [InndiagSU.semilinNorm, pow_succ]
  rw [hN] at hpow
  have hP : (1 : GL (Fin 6) F4) ∈ primeFormUnitary hF4 (idGram F4 6) := Subgroup.one_mem _
  have hfr := hpow.frame hF4 1 hP
  have hsc := InndiagSU.mem_scalars_of_isSemilin_one hF4 hF4card hd (by decide) Nat.prime_three
    (by norm_num) 1 hP (pow_mem hB 3) (by simpa using hfr)
  obtain ⟨c, hc⟩ := hsc
  exact ⟨c, hc.symm⟩

theorem gramSU_idGram_six : gramSU hF4 (idGram F4 6) = StatedSU 6 (2 ^ 1) F4 :=
  (unitarySU_eq_gramSU hF4 6).symm

@[expose] noncomputable def eGram6 : M6 ≃* gramSU hF4 (idGram F4 6) :=
  MulEquiv.subgroupCongr gramSU_idGram_six.symm

@[expose] noncomputable def conjM6 (A : primeFormUnitary hF4 (idGram F4 6)) : M6 ≃* M6 :=
  (eGram6.trans (primeFormConjSU hF4 (idGram F4 6) A)).trans eGram6.symm

theorem conjM6_apply (A : primeFormUnitary hF4 (idGram F4 6)) (x : M6) :
    ((conjM6 A x : M6) : GL (Fin 6) F4) = (A : GL (Fin 6) F4) * (x : GL (Fin 6) F4) *
      (A : GL (Fin 6) F4)⁻¹ := rfl

@[expose] def CenD (B : GL (Fin 6) F4) : Subgroup M6 :=
  (Subgroup.centralizer ({B} : Set (GL (Fin 6) F4))).subgroupOf (StatedSU 6 (2 ^ 1) F4)

theorem mem_CenD {B : GL (Fin 6) F4} {u : M6} :
    u ∈ CenD B ↔ (u : GL (Fin 6) F4) * B = B * (u : GL (Fin 6) F4) := by
  rw [CenD, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]

theorem fixSubgroup_conjM6 (A : primeFormUnitary hF4 (idGram F4 6)) :
    fixSubgroup (conjM6 A) = CenD (A : GL (Fin 6) F4) := by
  ext x
  rw [mem_fixSubgroup, mem_CenD]
  constructor
  · intro h
    have h1 := congrArg Subtype.val h
    rw [conjM6_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  · intro h
    apply Subtype.ext
    rw [conjM6_apply]
    exact mul_inv_eq_iff_eq_mul.2 h.symm

section Transfer

variable {X Y : Type} [Group X] [Group Y] [Finite X] {p : ℕ}

private theorem map_glaPPrimeCore_le (hp : p.Prime) (f : X →* Y) (hf : Function.Surjective f) :
    (GLAPPrimeCore p X).map f ≤ GLAPPrimeCore p Y := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite Y := Finite.of_surjective f hf
  exact le_sSup ⟨Subgroup.Normal.map inferInstance f hf,
    Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ f) CFSG.pPrimeCore_coprime_card⟩

@[expose] noncomputable def pQuotMap (hp : p.Prime) (π : X →* Y) (J : Subgroup X) :
    PQuot p J →* PQuot p (J.map π) :=
  QuotientGroup.map _ _ (π.subgroupMap J) (by
    rw [← Subgroup.map_le_iff_le_comap]
    exact map_glaPPrimeCore_le hp _ (π.subgroupMap_surjective J))

theorem pQuotMap_surjective (hp : p.Prime) (π : X →* Y) (J : Subgroup X) :
    Function.Surjective (pQuotMap hp π J) := by
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨x, rfl⟩ := π.subgroupMap_surjective J y
  exact ⟨QuotientGroup.mk x, rfl⟩

@[expose] noncomputable def pSimpleMap (hp : p.Prime) (π : X →* Y) (J : Subgroup X) :
    PSimple p J →* PSimple p (J.map π) :=
  QuotientGroup.map _ _ (pQuotMap hp π J) (by
    rw [← Subgroup.map_le_iff_le_comap]
    exact Subgroup.map_center_le_center (pQuotMap_surjective hp π J))

theorem pSimpleMap_surjective (hp : p.Prime) (π : X →* Y) (J : Subgroup X) :
    Function.Surjective (pSimpleMap hp π J) := by
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨x, rfl⟩ := pQuotMap_surjective hp π J y
  exact ⟨QuotientGroup.mk x, rfl⟩

theorem nonempty_pSimple_equiv_map [Finite Y] (hp : p.Prime) (π : X →* Y)
    {U : Subgroup X} {V : Subgroup Y} {J : Subgroup X} (hJ : GLAPComponent p U J)
    (hJπ : GLAPComponent p V (J.map π)) :
    Nonempty (PSimple p J ≃* PSimple p (J.map π)) := by
  haveI : IsSimpleGroup (PSimple p J) := (isQuasisimple_pQuot_of_glaPComponent hp hJ).2
  haveI : IsSimpleGroup (PSimple p (J.map π)) := (isQuasisimple_pQuot_of_glaPComponent hp hJπ).2
  have hinj : Function.Injective (pSimpleMap hp π J) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pSimpleMap hp π J).ker with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := exists_pair_ne (PSimple p (J.map π))
      obtain ⟨a', rfl⟩ := pSimpleMap_surjective hp π J a
      obtain ⟨b', rfl⟩ := pSimpleMap_surjective hp π J b
      apply hab
      have h1 : pSimpleMap hp π J a' = 1 := by
        rw [← MonoidHom.mem_ker, h]
        trivial
      have h2 : pSimpleMap hp π J b' = 1 := by
        rw [← MonoidHom.mem_ker, h]
        trivial
      rw [h1, h2]
  exact ⟨MulEquiv.ofBijective _ ⟨hinj, pSimpleMap_surjective hp π J⟩⟩

end Transfer

theorem exists_component_transfer (β : MulAut S6) (B : primeFormUnitary hF4 (idGram F4 6))
    (hβ : ∀ u v : M6, (v : GL (Fin 6) F4) = B * u * B⁻¹ →
      β (QuotientGroup.mk u) = QuotientGroup.mk v)
    {I : Subgroup S6} (hI : GLAPComponent 3 (fixSubgroup β) I) :
    ∃ J : Subgroup M6, GLAPComponent 3 (CenD (B : GL (Fin 6) F4)) J ∧
      Nonempty (PSimple 3 I ≃* PSimple 3 J) := by
  set π : M6 →* S6 :=
    QuotientGroup.mk' ((StatedScalars (Fin 6) F4).subgroupOf (StatedSU 6 (2 ^ 1) F4)) with hπ
  have hker : π.ker ≤ Subgroup.center M6 := by
    intro z hz
    rw [hπ, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] at hz
    obtain ⟨c, hc⟩ := hz
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    change (g : GL (Fin 6) F4) * z = z * g
    rw [← hc]
    exact (commute_scalar c (g : GL (Fin 6) F4)).eq
  have hαβ : ∀ k, π (conjM6 B k) = β (π k) := fun k => (hβ k (conjM6 B k) rfl).symm
  obtain ⟨J, hJ, hJI⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_glaPComponent_map_fixSubgroup
    π hker (conjM6 B) β hαβ (QuotientGroup.mk'_surjective _) Nat.prime_three hI
  rw [fixSubgroup_conjM6] at hJ
  refine ⟨J, hJ, ?_⟩
  have hJ' : GLAPComponent 3 (fixSubgroup (conjM6 B)) J := by rwa [fixSubgroup_conjM6]
  obtain ⟨e⟩ := nonempty_pSimple_equiv_map Nat.prime_three π hJ' (by rw [hJI]; exact hI)
  rw [hJI] at e
  exact ⟨e.symm⟩

end CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
