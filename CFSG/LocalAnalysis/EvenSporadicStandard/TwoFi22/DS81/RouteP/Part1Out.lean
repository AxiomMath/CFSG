module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Lemmas

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open Subgroup CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

variable {G : Type} [Group G] [Finite G] {L E : Subgroup G} {t : G}

theorem part1_out
    (hSch : CatalogOuterSolvable) (hB : DS81Lemma210Strong) (hF : FiniteFacts)
    (h : Std G L E t) :
    ∃ (z : G) (R : Subgroup G), IsZ E t z ∧ orderOf z = 2 ∧ ¬ IsConj t z ∧ t ∈ R ∧
      R ≤ normalizer (E : Set G) ∧ normalizer (R : Set G) = centralizer ({z} : Set G) ∧
      CFSG.IsExtraspecial 2 ↥R ∧ Nat.card ↥R = 2 ^ 13 ∧
      (center ↥R).map R.subtype = zpowers z ∧
      TwoFi22.O2In (centralizer ({z} : Set G)) = R := by
  obtain ⟨z, hz⟩ := lemma_3_2_exists hF h
  obtain ⟨-, hnc, -⟩ := lemma_3_2 hF h hz
  obtain ⟨hext, hcard, -, hcenter⟩ := lemma_3_8 hF h hz
  have hJR := lemma_3_4 hF h hz
  have hRP := lemma_3_5 hF h hz
  have hO := lemma_3_12 hSch hB hF h hz
  exact ⟨z, Rg t z, hz, orderOf_eq_prime (h.klein hz).z_sq (h.klein hz).z_ne, hnc,
    hJR.V_le_R t_mem_Vtz, hRP.R_le_P.trans ((Pg_le_CNz E z).trans (CNz_le_Nrm E z)),
    hO.normalizer_eq, hext, hcard, hcenter, hO.O2_eq⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
