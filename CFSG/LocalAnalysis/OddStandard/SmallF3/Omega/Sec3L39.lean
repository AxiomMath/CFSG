module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PocketLemmas
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Misc2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Lemma32

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma39_of_36 (h36 : Asc82Lemma36) : Asc82Lemma39 := by
  intro G _ _ t L hS u K hu huL huK hK hT
  have hKq : IsQuasisimple K := hK.isQuasisimple
  have hKF : InF K := ⟨hKq, Or.inr hT⟩
  have hKFS : InFStar K := inFStar_of_inF hKF
  have hnorm := conjugate_eq_self_of_lemma36 h36 hS
  have ht_u : t * u = u * t :=
    Subgroup.mem_centralizer_iff.mp (hS.component.le huL) t (Set.mem_singleton t)
  have htCu : t ∈ centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact ht_u.symm
  have hK2 : IsComponentIn K (centralizer ({t, u} : Set G)) := by
    rw [centralizer_pair_eq_inf]
    exact IsComponentIn.of_normal_inf_centralizer hS.component.le hnorm hK
  obtain ⟨I, hI, hle⟩ := hS.lBalance t u hS.involution hu ht_u K hK2
  have hI_F : InFStar I := hS.a2 t u hS.involution hu ht_u K I hK2 hI hle hKFS
  by_cases hIt : CFSG.conjugate I t = I
  ·
    have hKI : K ≤ I := by
      calc K ≤ I ⊔ CFSG.conjugate I t := hle
        _ = I ⊔ I := by rw [hIt]
        _ = I := sup_idem I
    have hcent : ∀ a ∈ I, a * u = u * a := fun a ha =>
      (Subgroup.mem_centralizer_iff.mp (hI.le ha) u (Set.mem_singleton u)).symm
    have hIT : IsTwoU43 (I ⧸ oddCore I) := isTwoU43_of_mem_center hI_F hu (hKI huK) hcent
    have hKIeq : K = I := eq_of_le_of_isTwoU43 hKI hKq hI.isQuasisimple hT hIT
    refine ⟨?_, hKFS, ?_⟩
    · rw [hKIeq]
      exact hI
    · intro I' hI' hI'F
      exact (h36 G t L hS u K hu (by rw [hKIeq]; exact hI) (Or.inl hKF)).2 I' hI' hI'F
  ·
    have hItc : IsComponentIn (CFSG.conjugate I t) (centralizer ({u} : Set G)) :=
      hI.conjugate htCu
    by_cases hIF : InF I
    ·
      exact absurd ((h36 G t L hS u I hu hI (Or.inl hIF)).2
        (CFSG.conjugate I t) hItc (InFStar.conjugate hI_F t)) hIt
    ·
      have hcomm : ∀ a ∈ I, ∀ b ∈ CFSG.conjugate I t, a * b = b * a :=
        hI.commute_of_ne hItc (Ne.symm hIt)
      have h1 : Nat.card (K ⧸ oddCore K) ∣
          Nat.card ((I ⊔ CFSG.conjugate I t : Subgroup G) ⧸
            oddCore (I ⊔ CFSG.conjugate I t : Subgroup G)) :=
        card_quotient_oddCore_dvd hle
      have h2 : Nat.card ((I ⊔ CFSG.conjugate I t : Subgroup G) ⧸
          oddCore (I ⊔ CFSG.conjugate I t : Subgroup G)) ∣
          Nat.card (I ⧸ oddCore I) *
            Nat.card (CFSG.conjugate I t ⧸ oddCore (CFSG.conjugate I t)) :=
        card_quotient_oddCore_sup_dvd hcomm
      rw [card_quotient_oddCore_conjugate I t] at h2
      have hdvd : Nat.card (K ⧸ oddCore K) ∣
          Nat.card (I ⧸ oddCore I) * Nat.card (I ⧸ oddCore I) := h1.trans h2
      rw [card_of_isTwoU43 hT] at hdvd
      rcases card_quotient_oddCore_of_isFStarGroup_not_isFGroup hI_F hIF with h | h | h | h
      · rw [h] at hdvd; exact absurd hdvd (by decide +kernel)
      · rw [h] at hdvd; exact absurd hdvd (by decide +kernel)
      · rw [h] at hdvd; exact absurd hdvd (by decide +kernel)
      · rw [h] at hdvd; exact absurd hdvd (by decide +kernel)

end CFSG.OddStandard.SmallF3.Omega
