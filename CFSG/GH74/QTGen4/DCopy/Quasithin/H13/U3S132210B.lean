module

public import CFSG.Quasithin.H13.U3S132210B
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3C137Z

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem s134_lemma13_2_2_ten_F4 (hC137 : C137StatementFiveZ_F4)
    (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) :
    CharNormal (baum T) (L ⊔ T) ∨
      (H13.IsA6Block L ∧ ∀ A : Subgroup G, IsMaxElemAbelian (pCoreOf 2 (L ⊔ T)) A →
        IsMaxElemAbelian T A) ∨
      ¬ thompsonJi T 1 ≤ centralizer (v2Of S : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : IsSylowTwoOf T (L ⊔ T) := A5.isSylowTwoOf_of_le S.h13.sylow le_sup_right
  have hQ := s134_cT S
  by_cases hJV : ∀ A : Subgroup G, IsMaxElemAbelian T A → A ≤ centralizer (V : Set G)
  ·
    left
    have hJQ : thompsonJ T ≤ pCoreOf 2 (L ⊔ T) := by
      rw [← hQ]
      exact iSup₂_le fun A hA => le_inf hA.1 (hJV A hA)
    have hJeq := B6.thompsonJ_eq_of_le hJQ (pCoreOf_two_le_of_isSylowTwoOf hTsyl)
    have hJB : thompsonJ (baum T) = thompsonJ T :=
      B6.thompsonJ_eq_of_le (B6.thompsonJ_le_baum _) inf_le_left
    refine ⟨thompsonJ T, B6.thompsonJ_le_baum _, ?_, ?_, ?_⟩
    · exact S1414.thompsonJ_ne_bot S.h13.sylow.1 fun h =>
        S.irr.2.1 (le_bot_iff.1 (h ▸ S.V_le_T))
    · rw [← hJB]
      exact S1414.characteristic_thompsonJ _
    · rw [← hJeq]
      exact (le_normalizer_pCoreOf 2 (L ⊔ T)).trans
        (CFSG.Quasithin.normalizer_le_normalizer_thompsonJ _)
  by_cases hJ1 : thompsonJi T 1 ≤ centralizer (v2Of S : Set G)
  swap
  · exact Or.inr (Or.inr hJ1)
  push Not at hJV
  obtain ⟨A₀, hA₀, hA₀C⟩ := hJV
  obtain ⟨-, hA₀eq⟩ := s134_offender S he hJ1 hA₀ hA₀C

  have hJV2 : thompsonJ T ≤ T ⊓ centralizer (v2Of S : Set G) :=
    iSup₂_le fun A hA => le_inf hA.1 ((s134_le_thompsonJi_one S hA).trans hJ1)
  have hV2V : v2Of S ≤ V := S.pre_le_V _
  have hV2e : IsElemAbelian 2 (v2Of S) := B6.isElemAbelian_iff.2
    ⟨fun a ha b hb => (B6.isElemAbelian_iff.1 (s134_elemAbelian_V S)).1 a (hV2V ha) b (hV2V hb),
      fun a ha => (s134_elemAbelian_V S).2 a (hV2V ha)⟩
  have hbaum : baum T = baum (T ⊓ centralizer (v2Of S : Set G)) :=
    baum_eq_baum_centralizer hV2e (hV2V.trans S.V_le_T) hJV2

  have hcharL : CharTwo L := A5.charTwo_of_faithful S.h13.qtke.2.1 S.h13.sylow S.h13.faithful
  have hX := charTwo_sup_of_normalizes S.h13.sylow.1 S.T_le_NL hcharL
  have hLT : ∀ x ∈ L ⊔ T, ∃ l ∈ L, ∃ t ∈ T, x = l * t := fun x hx => s134_mul_decomp S hx
  have hVL : ⁅V, L⁆ ≠ ⊥ := by rw [S.irr.2.2.2.1]; exact S.irr.2.1
  have hM := s134_L2T_eq_NLTV2 S
  rcases hC137 G (L ⊔ T) T V L (l2Of S ⊔ T) ((L ⊔ T) ⊓ normalizer (v2Of S : Set G)) hX hTsyl
      hLT S.h13.faithful.1.2.1 hcharL (Or.inr (Or.inl he))
      (Or.inr (Or.inr (s134_alternatingNatural S))) le_sup_right hM.le (s134_NLTV2_lt S)
      (s134_NLTV2_max S) (Or.inl hM) (s134_reduced S) hVL
      (fun h => absurd h (s134_not_L32 S)) with h | h | ⟨h4, -⟩ | ⟨-, -, -, A, hA, hA2⟩
  · left
    rwa [s134_pCoreOf_L2T S he, ← hbaum] at h
  · refine Or.inr (Or.inl ⟨h.2.1 he, fun A hA => ?_⟩)
    have h3 := (B24_three (s134_elemAbelian_V S) S.V_le_T hA₀ hA₀eq).2.2.1
    rw [hQ] at h3
    exact h3 A hA
  · exact absurd h4 (s134_card_autOn_ne S)
  · exfalso
    have hAN : A ≤ normalizer (V : Set G) := hA.1.trans S.frame.T_le
    rw [card_autOn_eq_relIndex hAN] at hA2
    by_cases hAC : A ≤ centralizer (V : Set G)
    · rw [inf_eq_left.2 hAC, relIndex_self] at hA2
      omega
    · rw [(s134_offender S he hJ1 hA hAC).1] at hA2
      omega

end CFSG.Quasithin.H13.U3
