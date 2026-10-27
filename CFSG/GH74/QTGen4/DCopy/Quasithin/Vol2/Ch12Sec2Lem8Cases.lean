module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8Cases
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13.Lem8

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.L34

theorem cases_of_hyp1223_F4 (h1222 : Stmt12_2_2_F4) {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]
    {T L V : Subgroup G} (hH : Hyp1223 G T L V) :
    (∃ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 5) ∧
        Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) ∨
      LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 ∨
      ∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸
        Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin n)) := by
  obtain ⟨-, -, hall⟩ := ((h1222 G T hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨-, -, -, hcomm, hmod⟩ := hall V hH.irrPlus
  have hq := hH.quasisimple
  rcases hmod with ⟨n, hn, ⟨e⟩, -⟩ | ⟨⟨e⟩, -, -⟩ | ⟨⟨e⟩, -, -⟩ |
      ⟨n, hn5, hn8, ⟨φ, hφ, -⟩, -⟩ | ⟨-, φ, hφ, -⟩ | ⟨hU, -⟩ | ⟨-, -, hA6, -⟩
  · exact Or.inl ⟨n, hn, ⟨e⟩⟩
  · exact Or.inl ⟨3, Or.inl rfl, ⟨e⟩⟩
  · exact Or.inl ⟨5, Or.inr (Or.inr rfl), ⟨e⟩⟩
  · have hle := pCore_le_ker_of_surjective_alternating hn5 φ hφ
    have : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; exact hn5)
    obtain ⟨-, e, -⟩ := SteinbergBM.five_quasisimple_centerless_image hq
      (alternatingGroup_nonabelian (by omega)) (QuotientGroup.lift (CFSG.pCore 2 ↥L) φ hle)
      (QuotientGroup.lift_surjective_of_surjective _ φ hφ hle)
    exact Or.inr (Or.inr ⟨n, hn5, hn8, ⟨e⟩⟩)
  · have hle := pCore_le_ker_of_surjective_alternating (by norm_num) φ hφ
    have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
    obtain ⟨-, e, -⟩ := SteinbergBM.five_quasisimple_centerless_image hq
      (alternatingGroup_nonabelian (by norm_num)) (QuotientGroup.lift (CFSG.pCore 2 ↥L) φ hle)
      (QuotientGroup.lift_surjective_of_surjective _ φ hφ hle)
    exact Or.inr (Or.inr ⟨7, by norm_num, by norm_num, ⟨e⟩⟩)
  · exact Or.inr (Or.inl hU)
  · exact Or.inr (Or.inr ⟨6, by norm_num, by norm_num, hA6⟩)

theorem rankTwoFacts_or_small_F4 (h1222 : Stmt12_2_2_F4) {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]
    {T L V : Subgroup G} (hH : Hyp1223 G T L V) :
    (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 5)) ∨
      LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1) ∨ RankTwoFacts (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have hq := hH.quasisimple
  obtain ⟨-, -, hodd⟩ := SteinbergBM.five_core_quotient_center_odd hq
  rcases cases_of_hyp1223_F4 h1222 hH with ⟨n, hn, ⟨e⟩⟩ | hU | ⟨n, hn5, hn8, ⟨e⟩⟩
  · rcases hn with rfl | rfl | rfl
    · exact Or.inl (Or.inr (lieModel_psl_of_mulEquiv_sl_zmod_two le_rfl e))
    · exact Or.inr (rankTwoFacts_sl_four e)
    · exact Or.inr (rankTwoFacts_sl_five e)
  · exact Or.inr (rankTwoFacts_psu hq hU)
  · have hn' : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
    obtain ⟨h58, h67, -⟩ := five_alternating_small_central_cover_reduction hq hodd hn' e
    rcases hn' with rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inl (h58 (Or.inl rfl)).2)
    · obtain ⟨-, h1, h3⟩ := h67 (Or.inl rfl)
      by_cases hc : Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 1
      · obtain ⟨e'⟩ := h1 hc
        exact Or.inr (rankTwoFacts_alt (Or.inl rfl) e')
      · obtain ⟨hp, hZ, ⟨e'⟩⟩ := h3 hc
        exact Or.inr (rankTwoFacts_hat (Or.inl rfl) hp hZ e')
    · obtain ⟨-, h1, h3⟩ := h67 (Or.inr rfl)
      by_cases hc : Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 1
      · obtain ⟨e'⟩ := h1 hc
        exact Or.inr (rankTwoFacts_alt (Or.inr (Or.inl rfl)) e')
      · obtain ⟨hp, hZ, ⟨e'⟩⟩ := h3 hc
        exact Or.inr (rankTwoFacts_hat (Or.inr rfl) hp hZ e')
    · obtain ⟨-, ⟨e'⟩⟩ := h58 (Or.inr rfl)
      exact Or.inr (rankTwoFacts_alt (Or.inr (Or.inr rfl)) e')

end CFSG.Quasithin.H13.Lem8
