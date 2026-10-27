module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi22Shape
public import CFSG.Sporadic.Fi23.Centralizer
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFi22Five
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporFi22
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporRed
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FiRefine
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterRowFusion
public import CFSG.LocalAnalysis.GLTheoremA.S6.AltSetup
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
public import CFSG.Sporadic.Fi22
public import CFSG.Sporadic.FischerOddCore.Fi23T2Card
public import CFSG.Sporadic.Schreier.J4SRank
public import Certificates.Certificate131101Base
public import Certificates.Certificate13620Base
public import Certificates.Data.Fi22PairSize

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabFi23

open CFSG.HardMathSupport.Solomon.Coordinator.YS08 CFSG.Sporadic.Fi23
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three
  CFSG.HardMathSupport.Dickson.I271.TabFi22Cent CFSG.Monster.B.Fischer

local notation "J22" => CFSG.Sporadic.Fi22.J

theorem card_centralizer_congr {G H : Type*} [Group G] [Group H] (e : G ≃* H) (t : G) :
    Nat.card ↥(Subgroup.centralizer ({t} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({e t} : Set H)) := by
  refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun g => ?_)
  have e1 := @Subgroup.mem_centralizer_singleton_iff G _ t g
  have e2 := @Subgroup.mem_centralizer_singleton_iff H _ (e t) (e g)
  rw [e1]
  show g * t = t * g ↔ (e g) ∈ Subgroup.centralizer ({e t} : Set H)
  rw [e2, ← map_mul, ← map_mul]
  exact e.injective.eq_iff.symm

theorem card_centralizer_conj {G : Type*} [Group G] (c t : G) :
    Nat.card ↥(Subgroup.centralizer ({c * t * c⁻¹} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({t} : Set G)) := by
  have h := card_centralizer_congr (MulAut.conj c) t
  rw [MulAut.conj_apply] at h
  exact h.symm

section Classes


theorem fixN_iotaJ (t : J22) :
    Fi22Copy.fixN (Fi22Copy.iotaJ t) = Fi22Copy.fixN (pi22 t) := by
  rw [Fi22Copy.iotaJ_eq_conj, Fi22Copy.fixN_conj]
  rfl

theorem classify_card {t : J22} (ht : orderOf t = 3) :
    ∃ k < 4, ((k = 0 ∧ Fi22Copy.fixN (pi22 t) = 0) ∨ (k = 1 ∧ Fi22Copy.fixN (pi22 t) = 27) ∨
      (k = 2 ∧ Fi22Copy.fixN (pi22 t) = 36) ∨ (k = 3 ∧ Fi22Copy.fixN (pi22 t) = 126)) ∧
      Nat.card ↥(Subgroup.centralizer ({t} : Set J22)) =
        Nat.card ↥(Subgroup.centralizer ({xRep k} : Set J22)) := by
  obtain ⟨k, hk, hconj⟩ := fi22_classify t ht
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  refine ⟨k, hk, ?_, ?_⟩
  · have hf : Fi22Copy.fixN (pi22 t) = Fi22Copy.fixN (Fi22Copy.iotaJ (xRep k)) := by
      rw [← fixN_iotaJ, ← hc, map_mul, map_mul, map_inv, Fi22Copy.fixN_conj]
    obtain ⟨h0, h1, h2, h3⟩ := Fi22Copy.fixN_xRep
    interval_cases k
    · exact Or.inl ⟨rfl, hf.trans h0⟩
    · exact Or.inr (Or.inl ⟨rfl, hf.trans h1⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, hf.trans h2⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, hf.trans h3⟩))
  · rw [← hc, card_centralizer_conj]

theorem card_centralizer_xRep_three :
    Nat.card ↥(Subgroup.centralizer ({xRep 3} : Set J22)) = 3 * 6531840 := by
  set t' : J22 := eJP.symm xP with ht'
  have hxP : eJP t' = xP := by rw [ht']; exact eJP.apply_symm_apply xP
  have ho : orderOf t' = 3 := by rw [ht', MulEquiv.orderOf_eq]; exact orderOf_xP
  have h1 : Fi22Copy.iotaJ t' = xPerm := by
    have := eJP_apply t'
    rw [hxP] at this
    exact this.symm
  have hf : Fi22Copy.fixN (pi22 t') = 126 := by
    rw [← fixN_iotaJ, h1, TabFi22Small.fixN_eq_card, fixCard_xPerm]
  obtain ⟨k, hk, hkf, hcard⟩ := classify_card ho
  have hk3 : k = 3 := by
    rcases hkf with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> omega
  subst hk3
  have h2 : Nat.card ↥(Subgroup.centralizer ({xP} : Set ↥fi22P)) = 3 * 6531840 := by
    have h3 := map_centralizer_subtype' fi22P xP
    have h4 : ((xP : ↥fi22P) : Equiv.Perm (Fin 3510)) = xPerm := rfl
    rw [h4] at h3
    rw [← TabFi22Cent.card_cent_eq, ← h3,
      Subgroup.card_map_of_injective fi22P.subtype_injective]
  have hc : Nat.card ↥(Subgroup.centralizer ({t'} : Set J22)) =
      Nat.card ↥(Subgroup.centralizer ({eJP t'} : Set ↥fi22P)) := by
    apply card_centralizer_congr
  rw [hxP] at hc
  rw [← hcard, hc]
  exact h2

theorem card_cent_dvd_of_fixN {t : J22} (ht : orderOf t = 3)
    (hf : Fi22Copy.fixN (pi22 t) = 0 ∨ Fi22Copy.fixN (pi22 t) = 27 ∨
      Fi22Copy.fixN (pi22 t) = 36) :
    Nat.card ↥(Subgroup.centralizer ({t} : Set J22)) ∣ 2 ^ 17 * 3 ^ 9 := by
  obtain ⟨k, hk, hkf, hcard⟩ := classify_card ht
  have hk3 : k < 3 := by
    rcases hkf with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> omega
  rw [hcard]
  exact tabFi22_card_centralizer_xRep_dvd hk3

theorem card_cent_eq_of_fixN {t : J22} (ht : orderOf t = 3)
    (hf : Fi22Copy.fixN (pi22 t) = 126) :
    Nat.card ↥(Subgroup.centralizer ({t} : Set J22)) = 3 * 6531840 := by
  obtain ⟨k, hk, hkf, hcard⟩ := classify_card ht
  have hk3 : k = 3 := by
    rcases hkf with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> omega
  subst hk3
  rw [hcard]
  exact card_centralizer_xRep_three

end Classes

end CFSG.HardMathSupport.Dickson.I271.TabFi23
