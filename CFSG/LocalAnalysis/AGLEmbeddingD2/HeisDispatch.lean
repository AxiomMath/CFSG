module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareDispatch
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisEngine
public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs
import CFSG.LocalAnalysis.AGLEmbeddingD2.FiveCover
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinDBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
import CFSG.RankThree.PartOne.N143.Inspect613Even
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Chevalley.RootCommutatorData
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
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
public import Certificates.Certificate119
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate122
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
public import Certificates.Certificate3951
public import Certificates.Certificate9130
import CFSG.GH74.GLS.Classes
import CFSG.GH74.Statements
import CFSG.LieType.Chevalley.EvenRootCommutatorF4
import CFSG.RankThree.PartOne.N143.SectionCenter
import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.AGLEmbeddingD2.HeisDispatch

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.SquareSmall
  CFSG.AGLEmbeddingD2.SquareDispatch
open CFSG.Blueprint (AdjointQuotient)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

@[expose] def HeisConclusion (Y : Type) [Group Y] [Finite Y] (P5 : ℕ → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (ρ : X →* Y), Function.Surjective ρ →
    ρ.ker ≤ Subgroup.center X → P5 (Nat.card ρ.ker) →
    ∀ (T : Sylow 2 Y) (J : Subgroup Y), Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J →
      J ≠ ⊤ → ∀ P : Subgroup Y, P ≤ J → IsPGroup 5 P → ¬ IsMulCommutative P →
        3 ≤ CFSG.Open.pRank 5 (J.comap ρ)

@[expose] def HeisLinearFamily : Prop :=
  ∀ (m : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (Y : Type) [Group Y] [Finite Y],
    (Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F ≃* Y) →
      HeisConclusion Y (fun k => 5 ∣ k → 5 ∣ m + 1 ∧ 5 ∣ Nat.card F - 1)

@[expose] def HeisSpFamily : Prop :=
  ∀ (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (Y : Type) [Group Y] [Finite Y],
    (Y ≃* StatedProj (StatedSp n F)) → HeisConclusion Y (Nat.Coprime 5)

@[expose] def HeisSUFamily : Prop :=
  ∀ (n f : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = (2 ^ f) ^ 2 → 3 ≤ n →
    ∀ (Y : Type) [Group Y] [Finite Y], (Y ≃* StatedProj (StatedSU n (2 ^ f) F)) →
      HeisConclusion Y (fun k => 5 ∣ k → 5 ∣ n ∧ 5 ∣ 2 ^ f + 1)

@[expose] def HeisSpinPlusFamily : Prop :=
  ∀ (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2], 4 ≤ n →
    ∀ (Y : Type) [Group Y] [Finite Y], (Y ≃* StatedProj (StatedOmega (StatedQuadPlus n F))) →
      HeisConclusion Y (Nat.Coprime 5)

@[expose] def HeisSpinMinusFamily : Prop :=
  ∀ (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (b c : F),
    (∀ s : F, s ^ 2 + b * s + c ≠ 0) → 4 ≤ n →
    ∀ (Y : Type) [Group Y] [Finite Y],
      (Y ≃* StatedProj (StatedOmega (StatedQuadMinus n F b c))) → HeisConclusion Y (Nat.Coprime 5)

@[expose] def HeisG2Family : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (Y : Type) [Group Y] [Finite Y],
    (Y ≃* AdjointQuotient .G2 K) → ∀ (T : Sylow 2 Y) (J : Subgroup Y),
      Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J → J ≠ ⊤ → ∀ P : Subgroup Y, P ≤ J →
        IsPGroup 5 P → IsMulCommutative P

theorem pow_three_dvd_card_of_not_isMulCommutative {G : Type*} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] (hG : IsPGroup p G) (hc : ¬ IsMulCommutative G) : p ^ 3 ∣ Nat.card G := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hG
  rw [hk]
  refine pow_dvd_pow p ?_
  by_contra h3
  apply hc
  interval_cases k
  · rw [pow_zero] at hk
    have := (Nat.card_eq_one_iff_unique.1 hk).1
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  · rw [pow_one] at hk
    have := isCyclic_of_prime_card hk
    exact inferInstance
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hk

theorem false_of_not_dvd_card {G : Type*} [Group G] [Finite G] {H P : Subgroup G} (hPH : P ≤ H)
    (hP : IsPGroup 5 P) (hc : ¬ IsMulCommutative P) (h : ¬ 125 ∣ Nat.card H) : False := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact h ((pow_three_dvd_card_of_not_isMulCommutative hP hc).trans (Subgroup.card_dvd_of_le hPH))

theorem not_dvd_card_alt' {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 8) :
    ¬ 125 ∣ Nat.card (alternatingGroup (Fin n)) := by
  rcases hn with rfl | rfl | rfl <;>
    · rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide

theorem not_dvd_card_of_statedProj' {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] {H : Subgroup (GL ι K)} {Y : Type} [Group Y] (e : Y ≃* StatedProj H) {m : ℕ}
    (h : ¬ m ∣ Nat.card (GL ι K)) : ¬ m ∣ Nat.card Y := by
  intro hm
  apply h
  have h1 : Nat.card Y ∣ Nat.card H := by
    rw [Nat.card_congr e.toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  exact hm.trans (h1.trans (Subgroup.card_subgroup_dvd_card H))

theorem not_dvd_card_GL_two_seven' {K : Type} [Field K] [Fintype K] (hK : Fintype.card K = 7) :
    ¬ 125 ∣ Nat.card (GL (Fin 2) K) := by
  rw [Matrix.card_GL_field, hK]
  decide

theorem not_dvd_card_GL_three_nine' {K : Type} [Field K] [Fintype K] (hK : Fintype.card K = 9) :
    ¬ 125 ∣ Nat.card (GL (Fin 3) K) := by
  rw [Matrix.card_GL_field, hK]
  decide

theorem coprime_five_of_not_dvd {k : ℕ} (h : ¬ 5 ∣ k) : Nat.Coprime 5 k :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 h


theorem three_le_pRank_five_of_classical (hGA : GriessMultipliersAllModels)
    (hL : HeisLinearFamily) (hSp : HeisSpFamily) (hSU : HeisSUFamily)
    (hDp : HeisSpinPlusFamily) (hDm : HeisSpinMinusFamily) (hG2 : HeisG2Family)
    {Lb : Type} [Group Lb] [Finite Lb] (hq : CFSG.IsQuasisimple Lb)
    (hcl : IsClassicalTwoOrG2 (Lb ⧸ Subgroup.center Lb)) (T : Sylow 2 (Lb ⧸ Subgroup.center Lb))
    (J : Subgroup (Lb ⧸ Subgroup.center Lb))
    (hNJ : Subgroup.normalizer
      (((T : Subgroup (Lb ⧸ Subgroup.center Lb)) : Set (Lb ⧸ Subgroup.center Lb))) ≤ J)
    (hJ : J ≠ ⊤) {P : Subgroup (Lb ⧸ Subgroup.center Lb)} (hPJ : P ≤ J) (hP : IsPGroup 5 P)
    (hPc : ¬ IsMulCommutative P) :
    3 ≤ CFSG.Open.pRank 5 (J.comap (QuotientGroup.mk' (Subgroup.center Lb))) := by
  set ρ := QuotientGroup.mk' (Subgroup.center Lb) with hρdef
  have hρ : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  have hker : ρ.ker = Subgroup.center Lb := QuotientGroup.ker_mk' _
  have hρker : ρ.ker ≤ Subgroup.center Lb := hker.le
  have hsmall : ¬ 125 ∣ Nat.card (Lb ⧸ Subgroup.center Lb) → False := fun h125 =>
    false_of_not_dvd_card (H := ⊤) le_top hP hPc (by rwa [Subgroup.card_top])
  rcases hcl with ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨⟨d, hv⟩, hdd, ⟨e⟩⟩
  · have h5cov : 5 ∣ Nat.card ρ.ker → CFSG.RankThree.PartOne.N143.PrimeCoverLieIndex 5 d :=
      fun h5 => FiveCover.primeCoverLie_of_griess_of_five_le hGA Nat.prime_five le_rfl ⟨d, hv⟩
        hq e (hker ▸ h5)
    cases d with
    | A r q =>
      change q.p = 2 at hd
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hd
      have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
        rw [TauCeti.PrimePower.card_def, GaloisField.card q.p q.exponent q.exponent_pos.ne']
      refine hL r (GaloisField q.p q.exponent) _
        ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).symm.trans e.symm) _ ρ hρ
        hρker (fun h5 => ?_) T J hNJ hJ P hPJ hP hPc
      obtain ⟨h1, h2⟩ := h5cov h5
      exact ⟨h1, hK ▸ h2⟩
    | twistedA r q =>
      change q.p = 2 at hd
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
      rw [hd] at h
      obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e'⟩⟩ := h
      have := Fintype.ofFinite F
      have : CharP F 2 := charP_of_card_eq_prime_pow (f := q.exponent * 2)
        (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
      refine hSU (r + 1) q.exponent F hcard (by omega) _ e' _ ρ hρ hρker (fun h5 => ?_) T J hNJ
        hJ P hPJ hP hPc
      obtain ⟨h1, h2⟩ := h5cov h5
      have hqc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hd]
      exact ⟨h1, hqc ▸ h2⟩
    | B r q =>
      change q.p = 2 at hd
      have hr := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
        ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
      have h : StatedClassicalModel (Lb ⧸ Subgroup.center Lb) .PSp r q.p q.exponent := by
        by_cases h2 : r = 2
        · subst h2
          exact CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
        · exact CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hd
            (by omega) e
      rw [hd] at h
      obtain ⟨-, F, hF, hFfin, hcard, ⟨e'⟩⟩ := h
      have := Fintype.ofFinite F
      have : CharP F 2 :=
        charP_of_card_eq_prime_pow (f := q.exponent)
          (by rw [← Nat.card_eq_fintype_card]; exact hcard)
      exact hSp r F _ e' _ ρ hρ hρker (coprime_five_of_not_dvd fun h5 => (h5cov h5).elim) T J
        hNJ hJ P hPJ hP hPc
    | C r q => exact hd.elim
    | D r q =>
      change q.p = 2 at hd
      have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hd e
      rw [hd] at h
      obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, ⟨e'⟩⟩ := h
      have := Fintype.ofFinite F
      have : CharP F 2 :=
        charP_of_card_eq_prime_pow (f := q.exponent)
          (by rw [← Nat.card_eq_fintype_card]; exact hcard)
      exact hDp r F hn _ e' _ ρ hρ hρker (coprime_five_of_not_dvd fun h5 => (h5cov h5).elim) T J
        hNJ hJ P hPJ hP hPc
    | twistedD r q =>
      change q.p = 2 at hd
      have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hd e
      rw [hd] at h
      obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e'⟩⟩ := h
      have := Fintype.ofFinite F
      have : CharP F 2 :=
        charP_of_card_eq_prime_pow (f := q.exponent)
          (by rw [← Nat.card_eq_fintype_card]; exact hcard)
      exact hDm r F b c hirr hn _ e' _ ρ hρ hρker
        (coprime_five_of_not_dvd fun h5 => (h5cov h5).elim) T J hNJ hJ P hPJ hP hPc
    | G2 q =>
      exfalso
      change q.p = 2 at hd
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hd
      have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
        rw [TauCeti.PrimePower.card_def, GaloisField.card q.p q.exponent q.exponent_pos.ne']
      obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hd
        (GaloisField q.p q.exponent) hK
      exact hPc (hG2 (GaloisField q.p q.exponent) _ (e.trans b.symm) T J hNJ hJ P hPJ
        hP)
    | _ => exact hd.elim
  · exact (hsmall (by rw [Nat.card_congr e.toEquiv]; exact not_dvd_card_alt' hn)).elim
  · exfalso
    rcases hdd with ⟨q, hq7, hdq⟩ | ⟨q, hq3, hdq⟩
    · change d = .A 1 q at hdq
      subst hdq
      obtain ⟨hp, hf⟩ := CFSG.AGLEmbedding.ParabHub.primePower_eq_of_card_eq Nat.prime_seven hq7
      have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      rw [hp, hf] at h
      obtain ⟨-, F, hF, hFfin, hcard, ⟨e'⟩⟩ := h
      have := Fintype.ofFinite F
      exact hsmall (not_dvd_card_of_statedProj' e'
        (not_dvd_card_GL_two_seven' (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)))
    · change d = .twistedA 2 q at hdq
      subst hdq
      obtain ⟨hp, hf⟩ := CFSG.AGLEmbedding.ParabHub.primePower_eq_of_card_eq Nat.prime_three hq3
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      rw [hp, hf] at h
      obtain ⟨-, F, hF, hFfin, hcard, ⟨e'⟩⟩ := h
      have := Fintype.ofFinite F
      exact hsmall (not_dvd_card_of_statedProj' e'
        (not_dvd_card_GL_three_nine' (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)))

end CFSG.AGLEmbeddingD2.HeisDispatch
