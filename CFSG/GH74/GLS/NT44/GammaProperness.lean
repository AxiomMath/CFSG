module

public import CFSG.GH74.GLS.NT44.CommonActor
import CFSG.GH74.GLS.NT44.ConjugateClosure
import CFSG.GH74.GLS.NT44.AllYCore
import CFSG.GH74.GLS.NT44.CoreNormalizer
import CFSG.GH74.Generic.BProg.Theta32
import CFSG.GH74.Generic.BProg.Sig32
import CFSG.GH74.GLS.C3.Layer1.Th2Cent5
import CFSG.GH74.Generic.BProg.Stability
public import CFSG.Dihedral.DisconnectedInvolutionGraph.InvolutionRootSupport
public import CFSG.GH74.GLS.C3.Layer1.Back91Core
public import CFSG.GH74.GLS.C3.Layer1.Th2Struct
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrTwoLocalTools

public section

set_option autoImplicit false

namespace CFSG.GH74.GLS.NT44

open Subgroup CFSG CFSG.GH74.GLS CFSG.ABGLocalTools
open CFSG.GH74.GLS.Stage1.Thm4
open scoped Pointwise

theorem gammaK_conjugate_closure_ne_top_of_le_rigid_center_sylow
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {fullQ : Type} [Group fullQ]
    {T W J : Subgroup G} {x : G}
    (hnonab : ∃ b c : G, b * c ≠ c * b)
    (hL34 : CFSG.GH74.GLS.IsL34Quotient fullQ)
    (hx2 : orderOf x = 2)
    (hmax : ∀ z : G, orderOf z = 2 →
      (CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ z).ncard ≤
        (CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x).ncard)
    (hJ : J ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)
    (hcenter : Nat.card (Subgroup.center fullQ) = 16)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤)
    (hxT : x ∈ T)
    (hTC : T ≤ Subgroup.centralizer ({x} : Set G))
    (hW : CFSG.ABGLocalTools.IsSylowOf 2 W
      (CFSG.GH74.GLS.zStar (CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x)))
    (hWT : W ≤ T)
    (hZW : Subgroup.closure {z : G | z ∈ T ∧ IsConj x z} ≤ W) :
    CFSG.GH74.GLS.gammaK 2
      (Subgroup.closure {z : G | z ∈ T ∧ IsConj x z}) 1 ≠ ⊤ := by
  classical
  let Z : Subgroup G := Subgroup.closure {z : G | z ∈ T ∧ IsConj x z}
  let NZ : Subgroup G := Subgroup.normalizer (Z : Set G)
  obtain ⟨A, hZA, _hAT, hA, hbal, hweak⟩ :=
    exists_balanced_actor_of_conjugate_closure_le_rigid_center_sylow
      (G := G) (fullQ := fullQ) (T := T) (W := W) (J := J) (x := x)
      hnonab hL34 hx2 hmax hJ hcenter hT hxT hTC hW hWT hZW
  obtain ⟨hZel, hZrank⟩ :=
    elementary_rank_conjugate_closure_of_le_zStar hnonab hT hx2
      (le_inf (hZW.trans hWT) (hZW.trans hW.le))
  have hZ2 : IsPGroup 2 Z := hW.isPGroup.to_le hZW
  have hxZ : x ∈ Z := Subgroup.subset_closure ⟨hxT, IsConj.refl x⟩
  have hZne : Z ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hxZ
    simp [hxZ] at hx2
  have hfactor : ∀ Y : Subgroup G, Y ≤ Z → Y ≠ ⊥ →
      (Subgroup.normalizer (Y : Set G) : Set G) =
        ((CFSG.pPrimeCore 2 ↥(Subgroup.normalizer (Y : Set G))).map
          (Subgroup.normalizer (Y : Set G)).subtype : Set G) *
        ((Subgroup.normalizer (Y : Set G) ⊓ NZ : Subgroup G) : Set G) := by
    intro Y hYZ hYne
    have hcore := le_layerCore_normalizer_of_le_rigid_center_sylow
      hnonab hx2 hmax hW (hYZ.trans hZW) hYne
    exact oddCore_mul_normalizer_conjugacyClosure_of_le_layerCore
      T x hT (Subgroup.normalizer (Y : Set G)) (hZW.trans hcore)
  have hfinish : ∀ N : Subgroup G, Subgroup.normalizer (Z : Set G) ≤ N →
      (∀ z ∈ Z, z ≠ 1 → Subgroup.centralizer ({z} : Set G) ≤ N) →
      N ≠ ⊤ → gammaK 2 Z 1 ≠ ⊤ := by
    intro N hNZ hC hNtop
    have hgamma : gammaK 2 Z 1 ≤ N := by
      refine iSup_le fun Y => iSup_le fun hYZ => iSup_le fun hYr => ?_
      have hYne : Y ≠ ⊥ := by
        intro hYbot
        rw [hYbot, CFSG.GH74.GLS.C3.Layer1.Back.pRank_bot_eq_zero] at hYr
        omega
      obtain ⟨y, hy, hy1⟩ := (Y.bot_or_exists_ne_one).resolve_left hYne
      have hodd : (CFSG.pPrimeCore 2 ↥(Subgroup.normalizer (Y : Set G))).map
          (Subgroup.normalizer (Y : Set G)).subtype ≤ N :=
        (CFSG.ComponentClassification.UnbalancedCorr.pPrimeCore_normalizer_le_centralizer
          (hZ2.to_le hYZ)).trans
            ((Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hy)).trans
              (hC y (hYZ hy) hy1))
      intro n hn
      change n ∈ (Subgroup.normalizer (Y : Set G) : Set G) at hn
      rw [hfactor Y hYZ hYne] at hn
      obtain ⟨o, ho, b, hb, rfl⟩ := hn
      exact N.mul_mem (hodd ho) (hNZ hb.2)
    intro htop
    exact hNtop (eq_top_iff.mpr (htop ▸ hgamma))
  have cyclic_AG : ∀ w : G, orderOf w = 2 →
      AG (Subgroup.zpowers w) =
        CFSG.GH74.GLS.pPrimeCoreOf 2 (Subgroup.centralizer ({w} : Set G)) := by
    intro w hw2
    have hw1 : w ≠ 1 := by
      intro hw
      simp [hw] at hw2
    unfold AG
    apply le_antisymm
    · exact iInf_le_of_le w (iInf_le_of_le ⟨Subgroup.mem_zpowers w, hw1⟩ le_rfl)
    · refine le_iInf fun b => le_iInf fun hb => ?_
      have hbw := (CFSG.GH74.GLS.mem_zpowers_two hw2 hb.1).resolve_left hb.2
      subst b
      exact le_rfl
  have cyclic_transport : ∀ {w : G}, orderOf w = 2 →
      ((Subgroup.normalizer (Subgroup.zpowers w : Set G) : Set G) =
        ((CFSG.pPrimeCore 2 ↥(Subgroup.normalizer (Subgroup.zpowers w : Set G))).map
          (Subgroup.normalizer (Subgroup.zpowers w : Set G)).subtype : Set G) *
        ((Subgroup.normalizer (Subgroup.zpowers w : Set G) ⊓ NZ : Subgroup G) : Set G)) →
      (Subgroup.centralizer ({w} : Set G) : Set G) =
        (CFSG.GH74.GLS.pPrimeCoreOf 2 (Subgroup.centralizer ({w} : Set G)) : Set G) *
        ((Subgroup.centralizer ({w} : Set G) ⊓ NZ : Subgroup G) : Set G) := by
    intro w hw2 hfac
    have hN :=
      CFSG.DisconnectedInvolutionGraph.Helpers.involution_zpowers_normalizer_eq_centralizer
        (⟨w, hw2⟩ : CFSG.DisconnectedInvolutionGraph.Helpers.Involution G)
    change Subgroup.normalizer (Subgroup.zpowers w : Set G) =
      Subgroup.centralizer ({w} : Set G) at hN
    have hcore := congrArg
      (fun H : Subgroup G => (CFSG.pPrimeCore 2 ↥H).map H.subtype) hN
    simpa only [hN, hcore, CFSG.GH74.GLS.pPrimeCoreOf] using hfac
  have commutator_in_theta : ∀ {w : G}, w ∈ Z → orderOf w = 2 →
      ⁅CFSG.GH74.GLS.pPrimeCoreOf 2 (Subgroup.centralizer ({w} : Set G)), Z⁆ ≤
        thetaHalf 1 A := by
    intro w hwZ hw2
    have hD : IsE 1 A (Subgroup.zpowers w) :=
      ⟨Subgroup.zpowers_le.mpr (hZA hwZ),
        Th2.isElementaryAbelian_zpowers_of_orderOf_two hw2,
        by rw [Th2.pRank_zpowers_of_orderOf_two hw2]⟩
    have h := Th2Sig10.commutator_AG_le_thetaHalf_self hD
    rw [cyclic_AG w hw2] at h
    exact (Subgroup.commutator_mono le_rfl hZA).trans h
  have odd_core_coprime_factor : ∀ {w : G}, w ∈ Z →
      ⁅CFSG.GH74.GLS.pPrimeCoreOf 2 (Subgroup.centralizer ({w} : Set G)), Z⁆ ⊔
        (CFSG.GH74.GLS.pPrimeCoreOf 2 (Subgroup.centralizer ({w} : Set G)) ⊓
          Subgroup.centralizer (Z : Set G)) =
        CFSG.GH74.GLS.pPrimeCoreOf 2 (Subgroup.centralizer ({w} : Set G)) := by
    intro w hw
    have hZC : Z ≤ Subgroup.centralizer ({w} : Set G) := by
      intro q hq
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Th2Sig8.mul_comm_of_isElementaryAbelian hZel hq hw
    have hnorm : Z ≤
        Subgroup.normalizer
          (CFSG.GH74.GLS.pPrimeCoreOf 2 (Subgroup.centralizer ({w} : Set G)) : Set G) := by
      intro q hq
      exact TwoThin.mem_normalizer_pPrimeCoreOf (le_normalizer (hZC hq))
    exact CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization
      2 Nat.prime_two Z (CFSG.GH74.GLS.pPrimeCoreOf 2 (Subgroup.centralizer ({w} : Set G)))
      hZ2 hnorm
      (TwoThin.card_pPrimeCoreOf_odd (Subgroup.centralizer ({w} : Set G))).coprime_two_left
  have centralizer_from_factors : ∀ (N : Subgroup G) {w : G},
      (Subgroup.centralizer ({w} : Set G) : Set G) =
        (CFSG.GH74.GLS.pPrimeCoreOf 2 (Subgroup.centralizer ({w} : Set G)) : Set G) *
        ((Subgroup.centralizer ({w} : Set G) ⊓ NZ : Subgroup G) : Set G) →
      CFSG.GH74.GLS.pPrimeCoreOf 2 (Subgroup.centralizer ({w} : Set G)) ≤ N →
      NZ ≤ N → Subgroup.centralizer ({w} : Set G) ≤ N := by
    intro N w hfac hodd hNZ n hn
    change n ∈ (Subgroup.centralizer ({w} : Set G) : Set G) at hn
    rw [hfac] at hn
    obtain ⟨o, ho, b, hb, rfl⟩ := hn
    exact N.mul_mem (hodd ho) (hNZ hb.2)
  by_cases hcommZ : ∀ z ∈ Z, z ≠ 1 →
      ⁅CFSG.GH74.GLS.pPrimeCoreOf 2 (Subgroup.centralizer ({z} : Set G)), Z⁆ = ⊥
  · have hC : ∀ z ∈ Z, z ≠ 1 → Subgroup.centralizer ({z} : Set G) ≤ NZ := by
      intro z hz hz1
      have hz2 : orderOf z = 2 :=
        CFSG.GH74.Generic.BProg.orderOf_eq_two_of_mem hZel hz hz1
      have hYne : Subgroup.zpowers z ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hz1
      have hfac := cyclic_transport hz2
        (hfactor (Subgroup.zpowers z) (Subgroup.zpowers_le.mpr hz) hYne)
      exact centralizer_from_factors NZ hfac
        ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcommZ z hz hz1)).trans
          (Subgroup.centralizer_le_normalizer (Z : Set G)))
        le_rfl
    have hNZtop : NZ ≠ ⊤ :=
      CFSG.ComponentClassification.UnbalancedCorr.normalizer_ne_top_of_isSimpleGroup
        hnonab hZne hZ2
    exact hfinish NZ le_rfl hC hNZtop
  · push Not at hcommZ
    obtain ⟨z, hzZ, hz1, hcomm⟩ := hcommZ
    have hz2 : orderOf z = 2 :=
      CFSG.GH74.Generic.BProg.orderOf_eq_two_of_mem hZel hzZ hz1
    have htheta_comm :
        ⁅CFSG.GH74.GLS.pPrimeCoreOf 2 (Subgroup.centralizer ({z} : Set G)), Z⁆ ≤
          thetaHalf 1 A := commutator_in_theta hzZ hz2
    have hTheta_ne : thetaHalf 1 A ≠ ⊥ := by
      intro hbot
      rw [hbot] at htheta_comm
      exact hcomm (le_bot_iff.mp htheta_comm)
    have hTheta_odd : Odd (Nat.card ↥(thetaHalf 1 A)) :=
      b_ig_21_6_three_halves G A hA hweak
    have hTheta_proper : thetaHalf 1 A ≠ ⊤ := by
      intro htop
      have hcard : Nat.card ↥(⊤ : Subgroup G) = Nat.card G :=
        Nat.card_congr Subgroup.topEquiv.toEquiv
      have hodd : Odd (Nat.card G) := by
        have h := hTheta_odd
        rw [htop, hcard] at h
        exact h
      have h2 : 2 ∣ Nat.card G := by simpa only [hx2] using orderOf_dvd_natCard x
      obtain ⟨k, hk⟩ := h2
      obtain ⟨l, hl⟩ := hodd
      omega
    have hNTheta_ne : Subgroup.normalizer (thetaHalf 1 A : Set G) ≠ ⊤ :=
      Th2.normalizer_ne_top_of_simple inferInstance hTheta_ne hTheta_proper
    have hNZle : NZ ≤ Subgroup.normalizer (thetaHalf 1 A : Set G) :=
      CFSG.GH74.Generic.BProg.normalizer_le_normalizer_thetaHalf_one
        hA hbal hweak ⟨hZA, hZel, hZrank⟩
    have hC : ∀ w ∈ Z, w ≠ 1 →
        Subgroup.centralizer ({w} : Set G) ≤
          Subgroup.normalizer (thetaHalf 1 A : Set G) := by
      intro w hw hw1
      have hw2 : orderOf w = 2 :=
        CFSG.GH74.Generic.BProg.orderOf_eq_two_of_mem hZel hw hw1
      have hwTheta :
          ⁅CFSG.GH74.GLS.pPrimeCoreOf 2 (Subgroup.centralizer ({w} : Set G)), Z⁆ ≤
            thetaHalf 1 A := commutator_in_theta hw hw2
      have hO : CFSG.GH74.GLS.pPrimeCoreOf 2 (Subgroup.centralizer ({w} : Set G)) ≤
          Subgroup.normalizer (thetaHalf 1 A : Set G) := by
        rw [← odd_core_coprime_factor hw]
        refine sup_le (hwTheta.trans le_normalizer) ?_
        exact inf_le_right.trans
          ((Subgroup.centralizer_le_normalizer (Z : Set G)).trans hNZle)
      have hYne : Subgroup.zpowers w ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hw1
      have hfac := cyclic_transport hw2
        (hfactor (Subgroup.zpowers w) (Subgroup.zpowers_le.mpr hw) hYne)
      exact centralizer_from_factors
        (Subgroup.normalizer (thetaHalf 1 A : Set G)) hfac hO hNZle
    exact hfinish (Subgroup.normalizer (thetaHalf 1 A : Set G)) hNZle hC hNTheta_ne

end CFSG.GH74.GLS.NT44
