module

public import CFSG.LocalAnalysis.OddStandard.Solomon75OddCore
public import CFSG.LocalAnalysis.OddStandard.GH71.Setup

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.OddStandard.Solomon75
  CFSG.OddStandard.Solomon75.CoreAux

variable {G : Type} [Group G] [Finite G] {z : G} {S U : Subgroup G} {u : G}

namespace Ctx71

theorem cover_of_involution (h : Ctx71 G z S U u) {v : G} (hv : orderOf v = 2) :
    IsDoubleCoverOfAlt (CentralizerBar v) 11 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (h.one_class z v h.orderOf_z hv)
  rw [← hg]
  exact isDoubleCoverOfAlt_centQuot_conj g h.cover

theorem balanced_of_pair (h : Ctx71 G z S U u) (hB : AlternatingBalanceData 11)
    (hD : pPrimeCoreOf 2 (Cen z) ⊓ Cen u ≤ pPrimeCoreOf 2 (Cen u)) : OddCoreBalanced G := by
  have := h.simple
  have hcore : oddCoreOf (cen z) ⊓ cen u ≤ oddCoreOf (cen u) := hD
  have hnonab := h.nonab
  have ht := h.orderOf_z
  have hcov : IsDoubleCoverOfAlt (CentQuot z) 11 := h.cover
  have hzt : u ≠ z := h.u_ne_z
  have huC : u ∈ cen z := h.S_le h.u_S
  intro x y hx hy hxy hne
  obtain ⟨g, hg⟩ := exists_conj_of_involution hnonab ht (by norm_num) hcov hB x hx
  set y' := g⁻¹ * y * g with hy'
  have hy'2 : orderOf y' = 2 := by
    rw [hy', ← hy]
    simpa using orderOf_conj_eq' g⁻¹ y
  have hy'C : y' ∈ cen z := by
    rw [mem_centralizer_singleton_iff]
    have h1 : x * y = y * x := hxy
    rw [hg] at h1
    calc y' * z = g⁻¹ * (y * (g * z * g⁻¹)) * g := by rw [hy']; group
      _ = g⁻¹ * ((g * z * g⁻¹) * y) * g := by rw [← h1]
      _ = z * y' := by rw [hy']; group
  have hy't : y' ≠ z := by
    intro h'
    apply hne
    rw [hg, ← h', hy']
    group
  obtain ⟨m, hm, hmy⟩ := exists_conj_in_cen ht hcov (hB.one_class (CentQuot z) hcov) hy'C
    huC hy'2 h.orderOf_u hy't hzt
  have hmt : m * z = z * m := mem_centralizer_singleton_iff.mp hm
  have hmt' : m⁻¹ * z * m = z := by
    calc m⁻¹ * z * m = m⁻¹ * (z * m) := by group
      _ = m⁻¹ * (m * z) := by rw [hmt]
      _ = z := by group
  have hx' : x = (g * m⁻¹) * z * (g * m⁻¹)⁻¹ := by
    calc x = g * z * g⁻¹ := hg
      _ = g * (m⁻¹ * z * m) * g⁻¹ := by rw [hmt']
      _ = (g * m⁻¹) * z * (g * m⁻¹)⁻¹ := by group
  have hy'' : y = (g * m⁻¹) * u * (g * m⁻¹)⁻¹ := by
    have h1 : y' = m⁻¹ * u * m := by rw [← hmy]; group
    calc y = g * y' * g⁻¹ := by rw [hy']; group
      _ = (g * m⁻¹) * u * (g * m⁻¹)⁻¹ := by rw [h1]; group
  rw [hx', hy'']
  exact balance_conj (g * m⁻¹) hcore


theorem oddCore_eq_bot_of_pair (h : Ctx71 G z S U u) (hD' : CoverSylowData 11)
    (hB : AlternatingBalanceData 11)
    (hD : pPrimeCoreOf 2 (Cen z) ⊓ Cen u ≤ pPrimeCoreOf 2 (Cen u)) :
    pPrimeCore 2 ↥(centralizer ({z} : Set G)) = ⊥ := by
  have := h.simple
  exact oddCore_eq_bot_of_balanced aschbacherProperTwoGeneratedCore (by norm_num) hD' h.nonab
    h.orderOf_z h.cover
    (exists_conj_of_involution h.nonab h.orderOf_z (by norm_num) h.cover hB)
    (h.balanced_of_pair hB hD)

end Ctx71

end CFSG.OddStandard.GH71
