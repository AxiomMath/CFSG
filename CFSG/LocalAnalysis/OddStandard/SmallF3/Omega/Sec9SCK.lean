module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Lemma32
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PocketLemmas
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4ChainDiag
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Helpers
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6ShapesDef

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

private theorem sec9c_mem_normalizer_of_conjugate_eq {H : Subgroup G} {c : G}
    (h : CFSG.conjugate H c = H) : c ∈ normalizer (H : Set G) := by
  have h2 : c⁻¹ ∈ normalizer (H : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact h
  simpa using (Subgroup.inv_mem (normalizer (H : Set G)) h2)

private theorem sec9c_odd_card_oddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

private theorem sec9c_simple_oddCore_of_shape {X : Subgroup G}
    (h : IsOmega5 X ∨ IsOmega6Plus X ∨ IsOmega6Minus X) :
    IsSimpleGroup (X ⧸ oddCore X) := by
  rcases h with h | h | h
  · exact (CFSG.LieType.Simplicity.fam_classical_converse (X ⧸ oddCore X)
      ⟨.PSp, 2, 3, 1, h.statedClassicalModel_of_ne_zero (by norm_num)⟩).2.2
  · exact (CFSG.LieType.Simplicity.fam_classical_converse (X ⧸ oddCore X)
      ⟨.PSL, 4, 3, 1, h.statedClassicalModel_of_ne_zero (by norm_num)⟩).2.2
  · exact (CFSG.LieType.Simplicity.fam_classical_converse (X ⧸ oddCore X)
      ⟨.PSU, 4, 3, 1, h.statedClassicalModel_of_ne_zero (by norm_num)⟩).2.2

private theorem sec9c_inF_of_ctrQ_dvd {K : Subgroup G} (hK : InFStar K)
    (hq : IsQuasisimple K) (hdvd : 25920 ∣ ctrQ K) : InF K := by
  rcases ctrQ_cases_of_inFStar hK with
    ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ |
      ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, hc⟩
  · exact ⟨hq, Or.inl (Or.inl h)⟩
  · exact ⟨hq, Or.inl (Or.inr (Or.inl h))⟩
  · rcases h with h | h
    · exact ⟨hq, Or.inl (Or.inr (Or.inr (Or.inl h)))⟩
    · exact ⟨hq, Or.inr h⟩
  · exact ⟨hq, Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
  · exact ⟨hq, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))⟩
  · exact ⟨hq, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))⟩
  · rw [hc] at hdvd
    exact absurd hdvd (by decide +kernel)
  · rw [hc] at hdvd
    exact absurd hdvd (by decide +kernel)
  · rw [hc] at hdvd
    exact absurd hdvd (by decide +kernel)
  · rw [hc] at hdvd
    exact absurd hdvd (by decide +kernel)

theorem sec9c_not_dvd_of_shape {K : Subgroup G} (hK : IsQuasisimple K)
    (h : IsOmega5 K ∨ IsOmega6Plus K ∨ IsOmega6Minus K) : ¬ 2 ^ 8 ∣ Nat.card K := by
  have hsimple : IsSimpleGroup (K ⧸ oddCore K) := sec9c_simple_oddCore_of_shape h
  have hcenter : center K = oddCore K := center_eq_oddCore_of_simple hK hsimple
  have hcard : Nat.card K = ctrQ K * Nat.card (center K) := by
    unfold ctrQ
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥K)
  have hodd : Odd (Nat.card (center K)) := by
    rw [hcenter]
    exact sec9c_odd_card_oddCore ↥K
  have hcop : Nat.Coprime (2 ^ 8) (Nat.card (center K)) :=
    (Nat.coprime_two_left.mpr hodd).pow_left 8
  intro h8
  have hdiv : 2 ^ 8 ∣ ctrQ K := by
    rw [hcard] at h8
    exact (hcop.dvd_mul_right).mp h8
  rcases h with h5 | h6p | h6m
  · rw [ctrQ_of_psp4 hK h5] at hdiv
    norm_num at hdiv
  · rw [ctrQ_of_l43 hK h6p] at hdiv
    norm_num at hdiv
  · rw [ctrQ_of_u43 hK h6m] at hdiv
    norm_num at hdiv

theorem sec9c_exists_K (hsh : Asc82Shapes) (h36 : Asc82Lemma36) (h6 : Asc82Tab6M)
    {t : G} {L : Subgroup G} (hS : Sec3SettingLB G t L) (hL : IsOmega6Minus L) {s : G}
    (hs2 : orderOf s = 2) (hst : s ∈ centralizer ({t} : Set G))
    (hα : ∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 1 α) :
    ∃ K : Subgroup G, layerCent L s ≤ K ∧
      (∀ g ∈ centralizer ({s} : Set G), ∀ k ∈ K, g * k * g⁻¹ ∈ K) ∧ ¬ 2 ^ 8 ∣ Nat.card K := by
  let J : Subgroup G := layerCent L s
  have hnorm : ∀ c ∈ centralizer ({t} : Set G), CFSG.conjugate L c = L :=
    conjugate_eq_self_of_lemma36 h36 hS
  have hsN : s ∈ normalizer (L : Set G) := sec9c_mem_normalizer_of_conjugate_eq (hnorm s hst)
  have hLM : IsOm6M L := ⟨hS.component.isQuasisimple, hL⟩
  have hJ5 : IsOmega5 J := h6.layer_i1 G L hLM s hs2 hsN hα
  have hJL : IsComponentIn J (L ⊓ centralizer ({s} : Set G)) :=
    isComponentIn_layerCent (Or.inl hJ5)
  have hJc : IsComponentIn J (centralizer ({t, s} : Set G)) := by
    rw [centralizer_pair_eq_inf t s]
    exact IsComponentIn.of_normal_inf_centralizer hS.component.le hnorm hJL
  have hcomm : t * s = s * t := (Subgroup.mem_centralizer_singleton_iff.mp hst).symm
  have htCs : t ∈ centralizer ({s} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have hJF : InF J := ⟨hJc.isQuasisimple, Or.inl (Or.inl hJ5)⟩
  obtain ⟨K, hK, hJle⟩ := hS.lBalance t s hS.involution hs2 hcomm J hJc
  have hKstar : InFStar K := hS.a2 t s hS.involution hs2 hcomm J K hJc hK hJle (inFStar_of_inF hJF)
  have hmain : ∃ I : Subgroup G, IsComponentIn I (centralizer ({s} : Set G)) ∧ J ≤ I ∧ InF I := by
    have hK' : IsComponentIn (CFSG.conjugate K t) (centralizer ({s} : Set G)) := hK.conjugate htCs
    have hK'F : InFStar (CFSG.conjugate K t) := hKstar.conjugate t
    by_cases hKeq : CFSG.conjugate K t = K
    · have hJK : J ≤ K := by
        have h := hJle
        rw [hKeq, sup_idem] at h
        exact h
      exact ⟨K, hK, hJK, inF_of_le_of_inFStar hJK hJF hKstar⟩
    · have hne : CFSG.conjugate K t ≠ K := hKeq
      have hcommKK' : ∀ a ∈ K, ∀ b ∈ CFSG.conjugate K t, a * b = b * a :=
        hK.commute_of_ne hK' (Ne.symm hne)
      rcases ctrQ_dvd_of_le_sup_of_commute hJc.isQuasisimple hcommKK' hJle with hJK' | ⟨hdvd, _⟩
      · exact ⟨CFSG.conjugate K t, hK', hJK', inF_of_le_of_inFStar hJK' hJF hK'F⟩
      · exfalso
        have hJq : ctrQ J = 25920 := ctrQ_of_psp4 hJc.isQuasisimple hJ5
        have hKF : InF K := sec9c_inF_of_ctrQ_dvd hKstar hK.isQuasisimple (by
          rw [← hJq]; exact hdvd)
        exact hne ((h36 G t L hS s K hs2 hK (Or.inl hKF)).2 (CFSG.conjugate K t) hK' hK'F)
  obtain ⟨I, hI, hJI, hIF⟩ := hmain
  have hshI := hsh G s I (sec3SettingLB_of_component hS hs2 hI hIF)
  have huniq : ∀ I' : Subgroup G, IsComponentIn I' (centralizer ({s} : Set G)) →
      InFStar I' → I' = I :=
    (h36 G t L hS s I hs2 hI (Or.inl hIF)).2
  refine ⟨I, hJI, ?_, sec9c_not_dvd_of_shape hI.isQuasisimple hshI⟩
  intro g hg k hk
  have hg' : g⁻¹ ∈ centralizer ({s} : Set G) := (centralizer ({s} : Set G)).inv_mem hg
  have hconjI : IsComponentIn (CFSG.conjugate I g⁻¹) (centralizer ({s} : Set G)) :=
    hI.conjugate hg'
  have hconjIF : InFStar (CFSG.conjugate I g⁻¹) := (inFStar_of_inF hIF).conjugate g⁻¹
  have heq : CFSG.conjugate I g⁻¹ = I := huniq _ hconjI hconjIF
  have hmem : g * k * g⁻¹ ∈ CFSG.conjugate I g⁻¹ := by
    unfold CFSG.conjugate
    rw [inv_inv]
    exact Subgroup.mem_map.mpr ⟨k, hk, by simp [MulAut.conj_apply]⟩
  rwa [heq] at hmem

end CFSG.OddStandard.SmallF3.Omega
