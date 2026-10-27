module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.M22Engine
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.KEngine2

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.M23Std

theorem m22_setup
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : StdHyp G L) (hL : IsSporadic L .M22)
    {z : G} (hz : z ∈ centralizer (L : Set G)) (hz2 : orderOf z = 2)
    (hC : centralizer ({z} : Set G) ≤ L ⊔ zpowers z) :
    ∃ (t : G) (F L1 N : Subgroup G), t ∈ L ∧ Setup L z t F L1 N ∧ (∀ x ∈ L1, ¬ IsConj z x) ∧
      (∀ k ∈ Ksub z F, IsConj z k → ∃ f ∈ F, k = z * f) ∧
      NormQuot (alternatingGroup (Fin 6)) (normalizer (F : Set G) ⊓ L) F ∧ FixFour L F := by
  have := h.simple
  obtain ⟨t, m, T1, F1, F2, htL, hOne, hD, hN, hX, hgood, hA6, hFix⟩ :=
    m22_localData h hL hz hz2 hC
  have hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z) := fun u hu hu2 hu1 =>
    fused_all h.nonabelian hOne hu hu2 hu1
  have htr := exists_normalizer_conj_eq_mul h.nonabelian hOne hD hN.trans
  have hR := m22_rankFour hL
  obtain ⟨L1, -, hFL1, hcard, hsq, hcomm, -, hK, -, hcz, hnormE, hnc, -, -, -, hBu, hnormK,
      hconj⟩ :=
    K_goodK_of_data h.nonabelian hOne hD hN hX hR hgood
  obtain ⟨N, hNle, hNnorm, hNodd, hNdisj, hNsup⟩ := hBu
  have hsurj := phiHom_surjective hOne hZ hN htr
  refine ⟨t, F1, L1, N, htL, ⟨hOne, hN, hZ, hFL1, hcard, hsq, hcomm, hK, hcz, hnormE, hnormK,
    hNle, hNnorm, hNodd, hNdisj, hNsup, fun f hf => ?_⟩, hnc, hconj, hA6, hFix⟩
  obtain ⟨κ, hκ⟩ := hsurj ⟨f, hf⟩
  exact ⟨κ, κ.2, congrArg Subtype.val hκ⟩

end CFSG.EvenSporadicStandard.M22Std
