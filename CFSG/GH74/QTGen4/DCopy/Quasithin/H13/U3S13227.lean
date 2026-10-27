module

public import CFSG.Quasithin.H13.U3S13227
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3C137Z

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem s134_lemma13_2_2_seven_F4 (hC137 : C137StatementFiveZ_F4)
    (h1332 : Stmt13_3_2_F4) (S : A6.Setting134 G T L V) :
    CharNormal (baum (r1Of T L V)) (L ⊔ T) ∨ H13.IsA6Block L := by
  by_cases hT6 : ∀ t : ↥(normalizer (V : Set G)), (t : G) ∈ T → Perm.sign (S.frame.ρ t) = 1
  ·
    left
    have hJ := s134_thompsonJ_r1Of_eq S hT6
    have hJB : thompsonJ (baum (r1Of T L V)) = thompsonJ (r1Of T L V) :=
      B6.thompsonJ_eq_of_le (B6.thompsonJ_le_baum _) inf_le_left
    refine ⟨thompsonJ (r1Of T L V), B6.thompsonJ_le_baum _, ?_, ?_, ?_⟩
    · intro h
      have hV := (s134_lemma13_2_2_six S).2.2
      rw [h] at hV
      exact S.irr.2.1 (le_bot_iff.1 hV)
    · rw [← hJB]
      exact S1414.characteristic_thompsonJ _
    · rw [hJ]
      exact (le_normalizer_pCoreOf 2 (L ⊔ T)).trans
        (CFSG.Quasithin.normalizer_le_normalizer_thompsonJ _)

  obtain ⟨h5, -, -, -⟩ := h1332 G T L S.h13 L S.h13.faithful
  have htype := a6_or_hatA6_of_isA6On S.frame.L_le (s134_pCoreOf_L_le S) h5 (s134_isA6On S)
  have hcharL : CharTwo L := A5.charTwo_of_faithful S.h13.qtke.2.1 S.h13.sylow S.h13.faithful
  have hX := charTwo_sup_of_normalizes S.h13.sylow.1 S.T_le_NL hcharL
  have hsyl := A5.isSylowTwoOf_of_le S.h13.sylow (le_sup_right : T ≤ L ⊔ T)
  have hLT : ∀ x ∈ L ⊔ T, ∃ l ∈ L, ∃ t ∈ T, x = l * t := fun x hx => s134_mul_decomp S hx
  have hVL : ⁅V, L⁆ ≠ ⊥ := by rw [S.irr.2.2.2.1]; exact S.irr.2.1
  have hdyn := s134_alternatingNatural S
  have hM := s134_L1T_eq_NLTV1 S
  have hZ8 : ∀ l : Subgroup G, Nat.card ↥l = 4 * Nat.card ↥(V ⊓ centralizer (L : Set G)) →
      Nat.card ↥l = 8 := fun l h => by rw [h, S.card_ZV]
  rcases htype with he | hhat
  · have P := s134Plus_L1 S he
    rcases hC137 G (L ⊔ T) T V L (L₁Of L (fsuV1 T V) ⊔ T)
        ((L ⊔ T) ⊓ normalizer (fsuV1 T V : Set G)) hX hsyl hLT S.h13.faithful.1.2.1 hcharL
        (Or.inr (Or.inl he)) (Or.inr (Or.inr hdyn)) le_sup_right hM.le
        (s134_NLTV1_lt S) (s134_NLTV1_max S) (Or.inl hM) (s134_reduced S) hVL
        (fun h => absurd h (s134_not_L32 S)) with h | h | ⟨h4, -⟩ | ⟨-, ⟨l, hZl, hlV, hl4, hlN⟩, -⟩
    · left
      rwa [P.pCoreOf_eq_r1Of] at h
    · exact Or.inr (h.2.1 he)
    · exact absurd h4 (s134_card_autOn_ne S)
    · exact (P.no_line hZl hlV (hZ8 l hl4) (le_sup_left.trans hlN)).elim
  · have P := s134Plus_l1plus S hhat
    have hPM : l1plus T L V ⊔ T ≤ (L ⊔ T) ⊓ normalizer (fsuV1 T V : Set G) :=
      (sup_le_sup_right P.le_L1 T).trans hM.le
    rcases hC137 G (L ⊔ T) T V L (l1plus T L V ⊔ T)
        ((L ⊔ T) ⊓ normalizer (fsuV1 T V : Set G)) hX hsyl hLT S.h13.faithful.1.2.1 hcharL
        (Or.inr (Or.inr (Or.inl hhat))) (Or.inr (Or.inr hdyn)) le_sup_right hPM
        (s134_NLTV1_lt S) (s134_NLTV1_max S)
        (Or.inr ⟨hhat, hM ▸ P.hat_index hhat, P.not_oTwoUpper_le_o2Z⟩) (s134_reduced S) hVL
        (fun h => absurd h (s134_not_L32 S)) with h | h | ⟨h4, -⟩ | ⟨-, ⟨l, hZl, hlV, hl4, hlN⟩, -⟩
    · left
      rwa [P.pCoreOf_eq_r1Of] at h
    · exact absurd (h.2.2.1 hhat) (s134_not_isHatBlock S hhat)
    · exact absurd h4 (s134_card_autOn_ne S)
    · exact (P.no_line hZl hlV (hZ8 l hl4) (le_sup_left.trans hlN)).elim

end CFSG.Quasithin.H13.U3
