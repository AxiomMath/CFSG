module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GFacts
public import CFSG.Open.GriessAllModelsStatement
import CFSG.Models.Blueprint
import CFSG.RankThree.PerfectCover.HopfFormula
import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.Blueprint.Multiplier
open CFSG.Open (StatedLieTag)
open scoped commutatorElement

private theorem l34g_card_center_dvd_hopf {L : Type} [Group L] [Finite L]
    (hL : CFSG.IsQuasisimple L) :
    Nat.card (center L) ∣ Nat.card (CFSG.Open.griessHopfMultiplier (L ⧸ center L)) := by
  have : Group.IsPerfect L := hL.1
  have : Group.IsPerfect (L ⧸ center L) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center L))
      (QuotientGroup.mk'_surjective _)
  obtain ⟨-, h, -, -, -, -, e, -⟩ :=
    CFSG.RankThree.PerfectCover.perfect_central_kernel_quotient_of_hopf_multiplier
      (S := L ⧸ center L) (QuotientGroup.mk' (center L)) (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk'])
  rw [Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv]
  have hk : Nat.card (center L) = Nat.card (QuotientGroup.mk' (center L)).ker := by
    rw [QuotientGroup.ker_mk']
  rw [hk, ← Nat.card_congr e.toEquiv]
  exact Subgroup.card_quotient_dvd_card _

private theorem l34g_card_generic_exceptional (t : StatedLieTag) (n p f : ℕ) :
    Nat.card (generic t n p f × exceptional t n p f) =
      ((genericOrders t n p f).1 * (genericOrders t n p f).2) *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  simp only [generic, exceptional, Nat.card_prod,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod _) ≃ _), Nat.card_zmod]

private theorem l34g_card_center_dvd_table (hGA : CFSG.Open.GriessAllModelsStatement)
    {L : Type} [Group L] [Finite L] (hL : CFSG.IsQuasisimple L) {t : StatedLieTag} {n p f : ℕ}
    (hm : CFSG.Models.LieModel (L ⧸ center L) t n p f) :
    Nat.card (center L) ∣ ((genericOrders t n p f).1 * (genericOrders t n p f).2) *
      ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  obtain ⟨-, ⟨e⟩⟩ := hGA _ t n p f hm
  have hcard : Nat.card (CFSG.Open.griessHopfMultiplier (L ⧸ center L)) =
      ((genericOrders t n p f).1 * (genericOrders t n p f).2) *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
    rw [Nat.card_congr e.toEquiv, l34g_card_generic_exceptional]
  have h1 := l34g_card_center_dvd_hopf hL
  rwa [hcard] at h1

private theorem l34g_odd_card_oddCore (X : Type) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

private theorem l34g_oddCore_le_center {L : Type} [Group L] (hq : CFSG.IsQuasisimple L)
    (hne : oddCore L ≠ ⊤) : oddCore L ≤ center L := by
  haveI : (oddCore L).Normal := oddCore_normal L
  let : IsSimpleGroup (L ⧸ center L) := hq.2.1
  have hnormal : ((oddCore L).map (QuotientGroup.mk' (center L))).Normal :=
    Subgroup.Normal.map inferInstance (QuotientGroup.mk' (center L))
      (QuotientGroup.mk'_surjective _)
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  · have hkernel : oddCore L ≤ (QuotientGroup.mk' (center L)).ker :=
      (oddCore L).map_eq_bot_iff.mp hbot
    simpa only [QuotientGroup.ker_mk'] using hkernel
  · exfalso
    have hsup : oddCore L ⊔ center L = ⊤ := by
      have hcomap := Subgroup.comap_map_eq (QuotientGroup.mk' (center L)) (oddCore L)
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
      exact hcomap.symm
    have hderived : commutator L ≤ oddCore L :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [hq.1.commutator_eq_top] at hderived
    exact hne (top_unique hderived)

private theorem l34g_center_eq_oddCore_of_simple {L : Type} [Group L] [Finite L]
    (hq : CFSG.IsQuasisimple L) (hs : IsSimpleGroup (L ⧸ oddCore L)) :
    center L = oddCore L := by
  haveI : Group.IsPerfect L := hq.1
  haveI := hs
  have hne : oddCore L ≠ ⊤ := by
    intro htop
    have hsub : Subsingleton (L ⧸ oddCore L) := by
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    exact not_subsingleton (L ⧸ oddCore L) hsub
  have hle : oddCore L ≤ center L := l34g_oddCore_le_center hq hne
  refine le_antisymm (fun x hx => ?_) hle
  have hQ : center (L ⧸ oddCore L) = ⊥ := by
    haveI : Group.IsPerfect (L ⧸ oddCore L) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (oddCore L))
        (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (L ⧸ oddCore L)) with h | h
    · exact h
    · exfalso
      haveI : IsMulCommutative (L ⧸ oddCore L) := center_eq_top_iff.mp h
      exact Group.IsPerfect.not_isMulCommutative (L ⧸ oddCore L) inferInstance
  have hxQ : (QuotientGroup.mk x : L ⧸ oddCore L) ∈ center (L ⧸ oddCore L) := by
    refine mem_center_iff.mpr fun q => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp hx y]
  rw [hQ, mem_bot] at hxQ
  exact (QuotientGroup.eq_one_iff x).mp hxQ

private theorem l34g_isPGroup_oddCore_of_card_dvd {L : Type} [Group L] [Finite L]
    {a b : ℕ} (hOZ : oddCore L ≤ center L) (hdvd : Nat.card (center L) ∣ 2 ^ a * 3 ^ b) :
    IsPGroup 3 ↥(oddCore L) := by
  have hdvd' : Nat.card ↥(oddCore L) ∣ 2 ^ a * 3 ^ b :=
    (Subgroup.card_dvd_of_le hOZ).trans hdvd
  have hodd : Odd (Nat.card ↥(oddCore L)) := l34g_odd_card_oddCore L
  have hcop : Nat.Coprime (Nat.card ↥(oddCore L)) (2 ^ a) :=
    (Nat.coprime_two_left.mpr hodd).symm.pow_right a
  have h3 : Nat.card ↥(oddCore L) ∣ 3 ^ b := hcop.dvd_of_dvd_mul_left hdvd'
  exact IsPGroup.of_card_dvd_pow h3

private theorem l34g_isPGroup_of_classicalModel (hGA : CFSG.Open.GriessAllModelsStatement)
    {L : Type} [Group L] [Finite L] (hq : CFSG.IsQuasisimple L) {t : StatedLieTag} {n p f : ℕ}
    (hm : LieModel (L ⧸ oddCore L) t n p f) (hn : n ≠ 0) {a b : ℕ}
    (htable : ((genericOrders t n p f).1 * (genericOrders t n p f).2) *
      ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) = 2 ^ a * 3 ^ b) :
    IsPGroup 3 ↥(oddCore L) := by
  have hs : IsSimpleGroup (L ⧸ oddCore L) :=
    (CFSG.LieType.Simplicity.fam_classical_converse (L ⧸ oddCore L)
      ⟨t, n, p, f, hm.statedClassicalModel_of_ne_zero hn⟩).2.2
  have hc : center L = oddCore L := l34g_center_eq_oddCore_of_simple hq hs
  have hlie : LieModel (L ⧸ center L) t n p f :=
    LieModel.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hc).symm hm
  have hM : CFSG.Models.LieModel (L ⧸ center L) t n p f :=
    CFSG.Models.LieModel.of_blueprint_of_ne_zero hn hlie
  have hdvd := l34g_card_center_dvd_table hGA hq hM
  rw [htable] at hdvd
  exact l34g_isPGroup_oddCore_of_card_dvd hc.ge hdvd

theorem l34g_schurOdd3_of_griess (hGA : CFSG.Open.GriessAllModelsStatement) : Asc82SchurOdd3 := by
  intro G _ _ X hX
  unfold InFStar IsFStarGroup IsFGroup at hX
  rcases hX with ⟨hq, hΩ | hU43⟩ | ⟨hq, hStar⟩
  · rcases hΩ with hm | hm | hm | hm | hm | hm
    · exact l34g_isPGroup_of_classicalModel (a := 1) (b := 0) hGA hq hm (by norm_num)
        (by norm_num [genericOrders, exceptionalOrders])
    · exact l34g_isPGroup_of_classicalModel (a := 1) (b := 0) hGA hq hm (by norm_num)
        (by norm_num [genericOrders, exceptionalOrders])
    · exact l34g_isPGroup_of_classicalModel (a := 2) (b := 2) hGA hq hm (by norm_num)
        (by norm_num [genericOrders, exceptionalOrders])
    · exact l34g_isPGroup_of_classicalModel (a := 1) (b := 1) hGA hq hm (by norm_num)
        (by norm_num [genericOrders, exceptionalOrders])
    · exact l34g_isPGroup_of_classicalModel (a := 2) (b := 0) hGA hq hm (by norm_num)
        (by norm_num [genericOrders, exceptionalOrders])
    · exact l34g_isPGroup_of_classicalModel (a := 1) (b := 0) hGA hq hm (by norm_num)
        (by norm_num [genericOrders, exceptionalOrders])
  · obtain ⟨hZcard, hm⟩ := hU43
    have hne : oddCore ↥X ≠ ⊤ := by
      intro htop
      haveI : Subsingleton (↥X ⧸ oddCore ↥X) := by
        rw [htop]
        exact QuotientGroup.subsingleton_quotient_top
      have h1 : Nat.card (center (↥X ⧸ oddCore ↥X)) = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
      omega
    have hOZ : oddCore ↥X ≤ center ↥X := l34g_oddCore_le_center hq hne
    let Q := ↥X ⧸ oddCore ↥X
    let π : ↥X →* Q := QuotientGroup.mk' (oddCore ↥X)
    let K : Subgroup ↥X := Subgroup.comap π (center Q)
    have hcomm_le : ⁅K, (⊤ : Subgroup ↥X)⁆ ≤ oddCore ↥X := by
      rw [Subgroup.commutator_le]
      intro x hx y _
      rw [← QuotientGroup.ker_mk' (oddCore ↥X), MonoidHom.mem_ker]
      change π ⁅x, y⁆ = 1
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        ((Subgroup.mem_center_iff.mp (Subgroup.mem_comap.mp hx)) (π y)).symm
    have hKtop_bot : ⁅⁅K, (⊤ : Subgroup ↥X)⁆, (⊤ : Subgroup ↥X)⁆ = ⊥ := by
      rw [eq_bot_iff]
      exact (Subgroup.commutator_mono_left (hcomm_le.trans hOZ)).trans
        (le_of_eq (Subgroup.commutator_center_left (H := (⊤ : Subgroup ↥X))))
    have h1 : ⁅⁅(⊤ : Subgroup ↥X), K⁆, (⊤ : Subgroup ↥X)⁆ = ⊥ := by
      rw [Subgroup.commutator_comm (⊤ : Subgroup ↥X) K]
      exact hKtop_bot
    have h2 : ⁅⁅K, (⊤ : Subgroup ↥X)⁆, (⊤ : Subgroup ↥X)⁆ = ⊥ := hKtop_bot
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate
      (H₁ := (⊤ : Subgroup ↥X)) (H₂ := (⊤ : Subgroup ↥X)) (H₃ := K) h1 h2
    have hperf : ⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆ = ⊤ := hq.1.commutator_eq_top
    rw [hperf] at h3
    have hK_le_center : K ≤ center ↥X :=
      Subgroup.commutator_top_left_eq_bot_iff_le_center.mp h3
    have hcenter_le : center ↥X ≤ K := by
      intro z hz
      refine Subgroup.mem_comap.mpr ?_
      exact Subgroup.map_center_le_center (f := π) (QuotientGroup.mk'_surjective _)
        (Subgroup.mem_map_of_mem π hz)
    have hc : center ↥X = K := le_antisymm hcenter_le hK_le_center
    have hlie : LieModel (↥X ⧸ center ↥X) .PSU 4 3 1 := by
      have hker : (((QuotientGroup.mk' (center Q)).comp π)).ker = center ↥X := by
        rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
        exact hc.symm
      have hsurj : Function.Surjective ((QuotientGroup.mk' (center Q)).comp π) :=
        (QuotientGroup.mk'_surjective (center Q)).comp (QuotientGroup.mk'_surjective _)
      have e : ↥X ⧸ center ↥X ≃* Q ⧸ center Q :=
        (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective _ hsurj)
      exact LieModel.of_mulEquiv e.symm hm
    have hM : CFSG.Models.LieModel (↥X ⧸ center ↥X) .PSU 4 3 1 :=
      CFSG.Models.LieModel.of_blueprint_of_ne_zero (by norm_num : (4 : ℕ) ≠ 0) hlie
    have hdvd := l34g_card_center_dvd_table hGA hq hM
    have htab : ((genericOrders .PSU 4 3 1).1 * (genericOrders .PSU 4 3 1).2) *
        ((exceptionalOrders .PSU 4 3 1).1 * (exceptionalOrders .PSU 4 3 1).2) =
        2 ^ 2 * 3 ^ 2 := by norm_num [genericOrders, exceptionalOrders]
    rw [htab] at hdvd
    exact l34g_isPGroup_oddCore_of_card_dvd hOZ hdvd
  · rcases hStar with hm | hm | hm | hm
    · exact l34g_isPGroup_of_classicalModel (a := 1) (b := 1) hGA hq hm (by norm_num)
        (by norm_num [genericOrders, exceptionalOrders])
    · exact l34g_isPGroup_of_classicalModel (a := 1) (b := 0) hGA hq hm (by norm_num)
        (by norm_num [genericOrders, exceptionalOrders])
    · exact l34g_isPGroup_of_classicalModel (a := 0) (b := 0) hGA hq hm (by norm_num)
        (by norm_num [genericOrders, exceptionalOrders])
    · exact l34g_isPGroup_of_classicalModel (a := 0) (b := 0) hGA hq hm (by norm_num)
        (by norm_num [genericOrders, exceptionalOrders])

end CFSG.OddStandard.SmallF3.Omega
