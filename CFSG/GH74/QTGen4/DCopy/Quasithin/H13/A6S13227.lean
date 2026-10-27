module

public import CFSG.Quasithin.H13.A6S13227
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3C137Five
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L15A

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise IsMulCommutative

theorem stmt13_2_2_7_holds_F4 (h1332 : Stmt13_3_2_F4)
    (hC137 : U3.C137StatementFive_F4) : U3.Stmt13_2_2_7_F4 := by
  intro G _ _ T L V Lp hH hV hZV hLp1 hLp2 hA6
  obtain ⟨h5, ⟨hTL, -, -, -⟩, ⟨-, hall⟩, -⟩ := h1332 G T L hH L hH.faithful
  obtain ⟨-, -, -, hab, hmod⟩ := hall V hV
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hV.2.2.1
  have hO : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) := by
    refine (pCoreOf_le_pCoreOf_sup hTL).trans ?_
    intro k hk
    exact Subgroup.mem_centralizer_iff.2 fun v hv =>
      ((U3.mem_reducedAggregate' (hV.1 hv)).2.1 k hk).symm
  have := hab
  obtain ⟨e6⟩ := hA6
  have hdvd := card_autOn_dvd_quot hLV hO
  rw [Nat.card_congr e6.toEquiv, card_alt6] at hdvd
  have h6 : AlternatingNatural (V := ↥V) (autOn L V) ⊤ ⊥ 6 := by
    rcases hmod with ⟨hn5, -⟩ | ⟨hn6, -⟩ | ⟨-, hc2, -⟩ | ⟨hl, -, -⟩ | ⟨hu, -, -⟩
    · exfalso
      obtain ⟨e5⟩ := nonempty_mulEquiv_of_realizes (altDn_faithful (by norm_num)) hn5
      have h1 := Nat.card_congr (e6.symm.trans e5).toEquiv
      rw [card_alt6] at h1
      have h2 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
        rw [nat_card_alternatingGroup]; simp [Nat.factorial]
      exact absurd (h1.trans h2) (by norm_num)
    · exact hn6
    · exfalso
      rw [hZV, Subgroup.card_bot] at hc2
      omega
    · exfalso
      obtain ⟨e3⟩ := nonempty_equiv_SL32_of_lieModel hl
      rw [Nat.card_congr e3.toEquiv, HSType.card_SL_three_two] at hdvd
      norm_num at hdvd
    · exfalso
      rw [card_of_lieModel_PSU_three_three hu] at hdvd
      norm_num at hdvd
  obtain ⟨S⟩ := U3.setting4_of_case_b_F4 h1332 hH hV hZV h6
  have hcharL : CharTwo L := A5.charTwo_of_faithful hH.qtke.2.1 hH.sylow hH.faithful
  have hX := charTwo_sup_of_normalizes hH.sylow.1 hTL hcharL
  have hsyl := A5.isSylowTwoOf_of_le hH.sylow (le_sup_right : T ≤ L ⊔ T)
  have hLT : ∀ x ∈ L ⊔ T, ∃ l ∈ L, ∃ t ∈ T, x = l * t := fun x hx => S.mul_decomp hx
  have htype := U3.a6_or_hatA6_of_isA6On hLV hO h5 ⟨e6⟩
  have hVL : ⁅V, L⁆ ≠ ⊥ := by rw [hV.2.2.2.1]; exact hV.2.1
  have hL32 : ¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 := fun hl => by
    obtain ⟨e3⟩ := nonempty_equiv_SL32_of_lieModel hl
    rw [Nat.card_congr e3.toEquiv, HSType.card_SL_three_two] at hdvd
    norm_num at hdvd
  have hM := S.L1T_eq_NLTV1
  by_cases hhat : IsHatA6 L
  · have hLp := hLp1 hhat
    subst hLp
    have P := S14.plusData_l1plus S (S.hatL1Plus hhat)
    have hPM : l1plus T L V ⊔ T ≤ (L ⊔ T) ⊓ Subgroup.normalizer (fsuV1 T V : Set G) :=
      (sup_le_sup_right P.le_L1 T).trans hM.le
    rcases hC137 G (L ⊔ T) T V L (l1plus T L V ⊔ T)
        ((L ⊔ T) ⊓ Subgroup.normalizer (fsuV1 T V : Set G)) hX hsyl hLT hH.faithful.1.2.1 hcharL
        (Or.inr (Or.inr (Or.inl hhat))) (Or.inr (Or.inr ⟨hab, h6⟩)) le_sup_right hPM
        S.NLTV1_lt S.NLTV1_max
        (Or.inr ⟨hhat, hM ▸ S.hat_index hhat P, S.not_oTwoUpper_le_o2Z P⟩) S.reduced hVL
        (fun h => absurd h hL32) with h | h | ⟨h4, -⟩ | ⟨-, ⟨l, -, hlV, hl4, hlN⟩, -⟩
    · exact Or.inl h
    · exact absurd (h.2.2.1 hhat) (S.not_isHatBlock hhat)
    · exact absurd h4 S.card_autOn_ne
    · rw [hZV, Subgroup.card_bot, mul_one] at hl4
      exact (S.no_line P hlV hl4 (le_sup_left.trans hlN)).elim
  · have hLp := hLp2 hhat
    subst hLp
    have P := S14.plusData_L1 S hhat
    obtain ⟨e⟩ := htype.resolve_right hhat
    rcases hC137 G (L ⊔ T) T V L (S.L1 ⊔ T)
        ((L ⊔ T) ⊓ Subgroup.normalizer (fsuV1 T V : Set G)) hX hsyl hLT hH.faithful.1.2.1 hcharL
        (Or.inr (Or.inl ⟨e⟩)) (Or.inr (Or.inr ⟨hab, h6⟩)) le_sup_right hM.le
        S.NLTV1_lt S.NLTV1_max (Or.inl hM) S.reduced hVL (fun h => absurd h hL32) with
      h | h | ⟨h4, -⟩ | ⟨-, ⟨l, -, hlV, hl4, hlN⟩, -⟩
    · exact Or.inl h
    · exact Or.inr (h.2.1 ⟨e⟩)
    · exact absurd h4 S.card_autOn_ne
    · rw [hZV, Subgroup.card_bot, mul_one] at hl4
      exact (S.no_line P hlV hl4 (le_sup_left.trans hlN)).elim

end CFSG.Quasithin.H13.A6
