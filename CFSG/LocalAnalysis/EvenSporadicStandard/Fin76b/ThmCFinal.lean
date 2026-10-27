module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCAssemble
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCOuter2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCSimple

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Finkelstein77 (innAut)
open CFSG.Sporadic.Schreier (j3P j3PermEquiv)

@[expose] def Fin76bOuterRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T : Subgroup G) (Q : Sylow 2 G)
    (x : G), StdHyp G L → (IsSporadic L .J2 ∨ IsSporadic L .J3) →
    (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    (L ⊔ centralizer (L : Set G)).relIndex (normalizer (L : Set G)) = 2 →
    OuterConfig G L z t T → T ≤ (Q : Subgroup G) → x ∈ (Q : Subgroup G) → x ∉ T →
    x ∈ normalizer (T : Set G) → x * z * x⁻¹ = z * t → x * t * x⁻¹ = t →
    (∀ q ∈ (Q : Subgroup G), q * t = t * q) → (Q : Subgroup G) ⊓ centralizer ({z} : Set G) = T →
    z ∈ (commutator ↥(centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype →
    False

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_outerRest (hR : Fin76bOuterRest) (h : StdHyp G L)
    (hJ : IsSporadic L .J2 ∨ IsSporadic L .J3)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hZ : center L = ⊥)
    (hcZ : center (L ⧸ center L) = ⊥) (hOD : OuterData (L ⧸ center L))
    (hout : (innAut (L ⧸ center L)).index ∣ 2)
    (hidx : (L ⊔ centralizer (L : Set G)).relIndex (normalizer (L : Set G)) = 2) : False := by
  have := h.simple
  obtain ⟨z, t, T, hcfg⟩ := exists_outerConfig h hS hZ hcZ hOD hout hidx
  obtain ⟨Q, x, hTQ, hxQ, hxT, hxN, hxz, hxt⟩ := hcfg.exists_swap h.nonabelian
  have htQ := hcfg.t_central_Q Q.isPGroup' hTQ hxQ hxz hxt
  have hcomm := hcfg.z_mem_commutator h.nonabelian
  exact hR G L z t T Q x h hJ hS hidx hcfg hTQ hxQ hxT hxN hxz hxt htQ
    (hcfg.inf_centralizer_eq Q.isPGroup' hTQ) ⟨_, hcomm, rfl⟩

theorem fin76bThmCSimple_of_outerRest
    (hR : Fin76bOuterRest) (hOJ2 : OuterData ↥ComponentClassification.J2Cover.Models.P)
    (hOJ3 : OuterData ↥j3P) : Fin76bThmCSimple := by
  intro G _ _ L h hJ hS hidx
  rcases hJ with hL | hL
  · obtain ⟨e⟩ := hL
    have hcN : center NativeSporadic.J2 = ⊥ := HypOne.center_eq_bot_of_mulEquiv
      ComponentClassification.J2Cover.nativeEquivP.symm
      ComponentClassification.J2Cover.center_P
    have hZ : center L = ⊥ := HypOne.center_eq_bot_of_mulEquiv e.symm hcN
    have hq : IsSporadic (L ⧸ center L) .J2 := isSporadic_quotient_of_center_eq_bot hZ ⟨e⟩
    obtain ⟨eq⟩ := hq
    have hcZ : center (L ⧸ center L) = ⊥ := HypOne.center_eq_bot_of_mulEquiv eq.symm hcN
    have hout : (innAut (L ⧸ center L)).index ∣ 2 :=
      index_dvd_two_of_mulEquiv eq hcN ComponentClassification.J2Cover.j2_mulAut_card
    exact false_of_outerRest hR h (Or.inl ⟨e⟩) hS hZ hcZ
      (hOJ2.of_mulEquiv ((MulEquiv.subgroupCongr
        ComponentClassification.J2Cover.Models.P_eq_autP).trans
          (ComponentClassification.J2Cover.nativeEquivP.symm.trans eq.symm))) hout hidx
  · obtain ⟨e⟩ := hL
    have hcP : center j3P = ⊥ := HypOne.J3.center_j3P
    have hZ : center L = ⊥ := HypOne.center_eq_bot_of_mulEquiv (e.trans j3PermEquiv).symm hcP
    have hq : IsSporadic (L ⧸ center L) .J3 := isSporadic_quotient_of_center_eq_bot hZ ⟨e⟩
    obtain ⟨eq⟩ := hq
    have hcZ : center (L ⧸ center L) = ⊥ :=
      HypOne.center_eq_bot_of_mulEquiv (eq.trans j3PermEquiv).symm hcP
    have hout : (innAut (L ⧸ center L)).index ∣ 2 := by
      obtain ⟨-, -, -, -, hAut⟩ :=
        CFSG.Sporadic.SmallOddCore.ctuc_j3_full_automorphism_permutation_model
      exact index_dvd_two_of_mulEquiv (eq.trans j3PermEquiv) hcP
        (by rw [hAut, CFSG.Sporadic.Schreier.card_j3P])
    exact false_of_outerRest hR h (Or.inr ⟨e⟩) hS hZ hcZ
      (hOJ3.of_mulEquiv (j3PermEquiv.symm.trans eq.symm)) hout hidx

end CFSG.EvenSporadicStandard.Fin76b
