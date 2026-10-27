module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16Dyn
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

@[expose] def A6OuterTypes : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H K P X : Subgroup G) (s : G),
    Nonempty (↥K ≃* alternatingGroup (Fin 6)) → K ≤ H → IsSylowTwoOf P K → P ≤ X → X ≤ K →
      X ≠ P → X ≠ K → s ∈ H ⊓ Subgroup.normalizer (K : Set G) →
      s ∈ Subgroup.normalizer (P : Set G) → s ∉ Subgroup.normalizer (X : Set G) →
        Nonempty (↥(autOn H K) ≃* ↥A6Models.m10) ∨ Nonempty (↥(autOn H K) ≃* ↥A6Models.pgl29) ∨
          Nonempty (↥(autOn H K) ≃* ↥A6Models.autA6)

theorem lemma2516 (hA6 : A6OuterTypes) : Lemma2516 := by
  intro G _ _ T M hs N t zK h
  obtain ⟨-, -, -, -, hcases⟩ := h.list252
  have h258 := h.facts258
  have hsimple : IsSimpleGroup ↥N.K := h258.simple
  have hpc : CFSG.pCore 2 ↥N.K = ⊥ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact Unc25K1.normal_pGroup_eq_bot_of_simple hsimple (Unc25K1.exists_noncomm_K N) _
      CFSG.pCore_isPGroup
  let e0 : (↥N.K ⧸ CFSG.pCore 2 ↥N.K) ≃* ↥N.K :=
    (QuotientGroup.quotientMulEquivOfEq hpc).trans QuotientGroup.quotientBot
  have hqL : ∀ {n : ℕ}, StatedClassicalModel ↥N.K .PSL 3 2 n →
      StatedClassicalModel (↥N.K ⧸ CFSG.pCore 2 ↥N.K) .PSL 3 2 n := fun {n} hm =>
    CFSG.SectionRank.statedClassicalModel_of_mulEquiv (t := .PSL) e0 hm
  have hqS : ∀ {n : ℕ}, StatedClassicalModel ↥N.K .PSp 2 2 n →
      StatedClassicalModel (↥N.K ⧸ CFSG.pCore 2 ↥N.K) .PSp 2 2 n := fun {n} hm =>
    CFSG.SectionRank.statedClassicalModel_of_mulEquiv (t := .PSp) e0 hm
  have hSM : N.S ≤ M := (N.tuple.sylow_inf.1).trans inf_le_right
  have hKH : N.K ≤ N.H := N.K_le_H
  have hSK : IsSylowTwoOf N.SK N.K := N.SK_sylow
  rcases hcases with ⟨hB, -⟩ | ⟨hRank, hDyn, hBor⟩ | ⟨hLM, -⟩ | ⟨hFM, -⟩
  · exact absurd hB N.nonBender
  · rcases hRank with ⟨n, hn1, hm⟩ | ⟨n, hn2, hm⟩ | ⟨⟨e6⟩⟩ | hm4
    · have hn : n = 1 := h.concl257 n (Or.inl (hqL hm))
      subst hn
      obtain ⟨hcard, hcent⟩ := Unc25K1.card_centralizer_eight_of_L32 hm
      obtain ⟨P, X, hP, -, hNP, hPX, hXK, hXP, hXK', s, hs', hsP, hsX⟩ :=
        Unc25K1.exists_moving_elem hSM (Or.inl hcard) hcent hSK h258.SK_shape
          h258.four_normalizer hBor hDyn
      exact Or.inr (Or.inl ⟨hm, Unc25K1.autOn_eq_top_of_outer hKH
        (Unc25K1.outer_card_dvd_two_of_L32 hm) hNP hP.1 hPX hXK
        ⟨N.S_le_H hs'.1, hs'.2⟩ hsP hsX⟩)
    · exfalso
      have := h.concl257 n (Or.inr (hqS hm))
      omega
    · obtain ⟨hcard, hcent⟩ := Unc25K1.card_centralizer_eight_of_A6 e6
      obtain ⟨P, X, hP, -, hNP, hPX, hXK, hXP, hXK', s, hs', hsP, hsX⟩ :=
        Unc25K1.exists_moving_elem hSM (Or.inr hcard) hcent hSK h258.SK_shape
          h258.four_normalizer hBor hDyn
      exact Or.inr (Or.inr ⟨⟨e6⟩, hA6 G N.H N.K P X s ⟨e6⟩ hKH hP hPX hXK hXP hXK'
        ⟨N.S_le_H hs'.1, hs'.2⟩ hsP hsX⟩)
    · exfalso
      have := h.concl257 2 (Or.inl hm4)
      omega
  · exfalso
    rcases hLM with hL | hM
    · exact h.concl2515.2 hL
    · exact h.concl2515.1 hM
  · exact Or.inl hFM

end CFSG.QuasithinUnique
