module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrCover
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Syl
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXPkMap
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTCover
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TwoCore
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FA8FinQ
public import CFSG.Blueprint.OddStandardExact
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.GH74.Defs
public import CFSG.Goldschmidt.BasicG
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Standard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCplxConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaConj
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.Bender1970.S3.Setup
public import CFSG.Walter.JRFacts
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Decomposition

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {A B : Type} [Group A] [Finite A] [Group B] [Finite B] {ρ : A →* B}

theorem sec5pu_oddCore_eq_bot {P : Type} [Group P] [Finite P] (hP : IsSL23Mod P)
    (hcard : Nat.card P = 24) : CFSG.oddCore P = ⊥ := by
  obtain ⟨e⟩ := hP
  have hq : Nat.card (P ⧸ CFSG.oddCore P) = 24 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore P)
  rw [hcard, hq] at h
  exact Subgroup.eq_bot_of_card_eq _ (by omega)

theorem sec5pu_map_twoCoreIn_le (K : Subgroup A) (ρ : A →* B) :
    (twoCoreIn K).map ρ ≤ twoCoreIn (K.map ρ) := by
  have hle : (twoCoreIn K).map ρ ≤ K.map ρ := Subgroup.map_mono (twoCoreIn_le_self K)
  refine le_twoCoreIn_of_normal hle ((isPGroup_twoCoreIn K).map ρ) ?_
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro h p hh hp
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hh
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hp
  refine Subgroup.mem_map.mpr ⟨k * t * k⁻¹, ?_, by simp⟩
  exact (Subgroup.normal_subgroupOf_iff (twoCoreIn_le_self K)).mp
    (normal_subgroupOf_twoCoreIn K) t k ht hk

theorem sec5pu_oddCore_le_center (h : OddCentralCover ρ) {K : Subgroup A}
    (hbot : CFSG.oddCore ↥(K.map ρ) = ⊥) : CFSG.oddCore ↥K ≤ Subgroup.center ↥K := by
  have hc := sec63PT_oddCentralCover_subgroupMap h K
  have hcomap := sec63PT_comap_oddCore_eq (ρ.subgroupMap K) hc.surjective hc.odd_card_ker
  intro x hx
  rw [← hcomap, hbot] at hx
  have hx1 : ρ (x : A) = 1 := by
    have h1 := Subgroup.mem_comap.mp hx
    rw [Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  have hxc : (x : A) ∈ Subgroup.center A := h.ker_le_center (MonoidHom.mem_ker.mpr hx1)
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_center_iff.mp hxc g)

theorem sec5pu_pow_two_pow {M : Type*} [Group M] {x : M} {k m : ℕ} (hk : x ^ 2 ^ k = 1)
    (hm : k ≤ m) : x ^ 2 ^ m = 1 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [pow_add, pow_mul, hk, one_pow]

theorem sec5pu_map_twoCoreIn (h : OddCentralCover ρ) {K : Subgroup A} {y : A}
    (hy : orderOf y = 2) (hyK : y ∈ K) (hK : IsSL23Mod ↥K) (hcard : Nat.card ↥(K.map ρ) = 24) :
    (twoCoreIn K).map ρ = twoCoreIn (K.map ρ) := by
  have hKmod : IsSL23Mod ↥(K.map ρ) := l34g_x_isSL23Mod_map h hK
  have hbot : CFSG.oddCore ↥(K.map ρ) = ⊥ := sec5pu_oddCore_eq_bot hKmod hcard
  have hO := sec5pu_oddCore_le_center h hbot
  obtain ⟨f, hfinj, -, hfK⟩ := exists_quaternion_of_isSL23Mod hK hyK hy
  have hQ8 : Nat.card (QuaternionGroup 2) = 8 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hS : Nat.card ↥f.range = 8 := by
    rw [← hQ8]
    exact (Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv).symm
  have hS₀ : f.range ≤ twoCoreIn K := le_pCore_of_isSL23Mod hK hO hfK hS
  have hρf : Function.Injective (ρ.comp f) := by
    intro a b hab
    have h8 : ∀ q : QuaternionGroup 2, f q ^ 2 ^ 3 = 1 := by
      intro q
      rw [← map_pow]
      have : q ^ 2 ^ 3 = 1 := by
        have h' : q ^ Nat.card (QuaternionGroup 2) = 1 := pow_card_eq_one'
        rw [hQ8] at h'
        exact h'
      rw [this, map_one]
    exact hfinj (fa8fin_cover_inj h (h8 a) (h8 b) hab)
  have hcard8 : Nat.card ↥(f.range.map ρ) = 8 := by
    rw [← MonoidHom.range_comp, ← hQ8]
    exact (Nat.card_congr (MonoidHom.ofInjective hρf).toEquiv).symm
  have hle8 : Nat.card ↥(twoCoreIn (K.map ρ)) ≤ 8 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (isPGroup_twoCoreIn (K.map ρ)).exists_card_eq
    have hdvd : Nat.card ↥(twoCoreIn (K.map ρ)) ∣ 24 :=
      hcard ▸ Subgroup.card_dvd_of_le (twoCoreIn_le_self (K.map ρ))
    rw [hn] at hdvd ⊢
    have hn5 : n < 5 := by
      by_contra hcon
      have h32 : 2 ^ 5 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
      have := (h32.trans hdvd)
      omega
    interval_cases n <;> simp_all
  refine le_antisymm (sec5pu_map_twoCoreIn_le K ρ) ?_
  intro x hx
  have hge : Nat.card ↥(twoCoreIn (K.map ρ)) ≤ Nat.card ↥((twoCoreIn K).map ρ) :=
    hle8.trans (hcard8 ▸ Subgroup.card_le_of_le (Subgroup.map_mono hS₀))
  have := Subgroup.eq_of_le_of_card_ge (sec5pu_map_twoCoreIn_le K ρ) hge
  rw [this]
  exact hx

theorem sec5pu_twoCoreIn_eq (h : OddCentralCover ρ) {K K' : Subgroup A} {y : A}
    (hy : orderOf y = 2) (hyK : y ∈ K) (hyK' : y ∈ K') (hK : IsSL23Mod ↥K)
    (hK' : IsSL23Mod ↥K') (hmap : K.map ρ = K'.map ρ) (hcard : Nat.card ↥(K.map ρ) = 24) :
    twoCoreIn K = twoCoreIn K' := by
  have h1 := sec5pu_map_twoCoreIn h hy hyK hK hcard
  have h2 := sec5pu_map_twoCoreIn h hy hyK' hK' (by rw [← hmap]; exact hcard)
  have heq : (twoCoreIn K).map ρ = (twoCoreIn K').map ρ := by rw [h1, h2, hmap]
  have key : ∀ M M' : Subgroup A, (twoCoreIn M).map ρ = (twoCoreIn M').map ρ →
      twoCoreIn M ≤ twoCoreIn M' := by
    intro M M' hMM x hx
    have hρx : ρ x ∈ (twoCoreIn M').map ρ := hMM ▸ Subgroup.mem_map_of_mem ρ hx
    obtain ⟨x', hx', hxx'⟩ := Subgroup.mem_map.mp hρx
    obtain ⟨k, hk⟩ := isPGroup_twoCoreIn M ⟨x, hx⟩
    obtain ⟨k', hk'⟩ := isPGroup_twoCoreIn M' ⟨x', hx'⟩
    have hk1 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hk2 : x' ^ 2 ^ k' = 1 := by simpa using congrArg Subtype.val hk'
    have := fa8fin_cover_inj h (k := max k k') (sec5pu_pow_two_pow hk2 (le_max_right _ _))
      (sec5pu_pow_two_pow hk1 (le_max_left _ _)) hxx'
    rw [← this]
    exact hx'
  exact le_antisymm (key K K' heq) (key K' K heq.symm)

theorem sec5pu_map_twoCoreIn_subgroupOf {G : Type} [Group G] {L K : Subgroup G} (hKL : K ≤ L) :
    (twoCoreIn (K.subgroupOf L)).map L.subtype = twoCoreIn K := by
  unfold twoCoreIn CFSG.inSubgroup
  have h2 := CFSG.pCore_map_iso 2 (Subgroup.subgroupOfEquivOfLe hKL)
  rw [Subgroup.map_map]
  conv_rhs => rw [← h2]
  rw [Subgroup.map_map]
  rfl

end CFSG.OddStandard.SmallF3.Omega
