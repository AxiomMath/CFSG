module

public import CFSG.Quasithin.H13.NQS1345A
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Inputs13_3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem le_normalizer_of_faithful_F4 (h1332 : Stmt13_3_2_F4) (S : A6.Setting134 G T L V)
    {H K : Subgroup G} (hH : InH T H) (hKH : K ≤ H) (hKf : quasithinIsFaithfulLocal T K) :
    H ≤ normalizer (K : Set G) := by
  obtain ⟨-, ⟨-, -, -, huniq⟩, -, -⟩ := h1332 G T L S.h13 K hKf
  obtain ⟨M', hM', hHM'⟩ := exists_inM_of_pCoreOf_ne_bot hH.2
  rw [← huniq M' hM' ((sup_le hKH hH.1).trans hHM')]
  exact hHM'

theorem not_le_of_mem_cComp_F4 (h1332 : Stmt13_3_2_F4) (h1338 : A6.Stmt13_3_8_F4)
    (S : A6.Setting134 G T L V) {H K : Subgroup G} (hH : InH T H)
    (hHM : ¬ H ≤ normalizer (L : Set G)) (hK : K ∈ cComp H) : ¬ K ≤ normalizer (L : Set G) := by
  intro hKM
  have hKH : K ≤ H := le_of_mem_cComp hK
  by_cases hall : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ normalizer (L : Set G)
  · have hYM : conjClosure K H ≤ normalizer (L : Set G) := conjClosure_le hall
    have hYH : conjClosure K H ≤ H :=
      conjClosure_le fun h hh k hk => mul_mem (mul_mem hh (hKH hk)) (inv_mem hh)
    have h23 := (h1338 G T L L H (conjClosure K H) S.h13 S.h13.faithful hH hHM
      (oTwoRes_conjClosure (perfect_of_mem_cComp hK)) hYH (le_normalizer_conjClosure K H)
      hYM).2
    exact ne_bot_of_mem_cComp hK (eq_bot_of_perfect_of_le (A5.isSolvable_of_isTwoThreeGroup h23)
      (perfect_of_mem_cComp hK) (le_conjClosure K H))
  · push Not at hall
    obtain ⟨h, hh, k, hk, hkM⟩ := hall
    have hK' : K.map (MulAut.conj h).toMonoidHom ∈ cComp H :=
      CFSG.Quasithin.map_conj_mem_cComp hK hh
    have hk' : h * k * h⁻¹ ∈ K.map (MulAut.conj h).toMonoidHom := ⟨k, hk, rfl⟩
    have hK'f := faithful_of_not_le S hH hK' fun hle => hkM (hle hk')
    have hHN := le_normalizer_of_faithful_F4 h1332 S hH (le_of_mem_cComp hK') hK'f
    obtain ⟨k₂, hk₂, he⟩ := (mem_normalizer_iff.mp (hHN hh) _).mp hk'
    have he' : k₂ = h * k * h⁻¹ := by
      have : h * k₂ * h⁻¹ = h * (h * k * h⁻¹) * h⁻¹ := he
      simpa using this
    exact hkM (hKM (he' ▸ hk₂))

theorem not_lieModel_PSU_F4 (h1332 : Stmt13_3_2_F4) (h13316 : Stmt13_3_16_F4)
    (S : A6.Setting134 G T L V) {K : Subgroup G} (hKf : quasithinIsFaithfulLocal T K) :
    ¬ LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSU 3 3 1 := by
  intro hU
  have hnA5 : ¬ quasithinO2QuotientIso K (alternatingGroup (Fin 5)) := by
    rw [quasithinO2QuotientIso_iff]
    rintro ⟨e⟩
    have h1 := card_of_lieModel_PSU_three_three hU
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin] at h1
    exact absurd h1 (by decide)
  exact h13316 G T K ((h1332 G T L S.h13 K hKf).2.2.2 (Or.inl hnA5)) hU

theorem one_two_F4 (h1332 : Stmt13_3_2_F4) (h13316 : Stmt13_3_16_F4) (h1338 : A6.Stmt13_3_8_F4)
    (S : A6.Setting134 G T L V) {H K : Subgroup G} (hH : InH T H)
    (hHM : ¬ H ≤ normalizer (L : Set G)) (hK : K ∈ cComp H) :
    (quasithinIsMaximalLocal T K ∧ quasithinIsFaithfulLocal T K) ∧
      H ≤ normalizer (K : Set G) ∧
      (Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
        LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∨
        Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)) ∨ A6.IsHatA6 K) ∧
      ¬ K ≤ normalizer (L : Set G) ∧ ¬ L ≤ normalizer (K : Set G) ∧
      ¬ K ≤ centralizer ((V ⊓ centralizer (L : Set G) : Subgroup G) : Set G) := by
  have hKM := not_le_of_mem_cComp_F4 h1332 h1338 S hH hHM hK
  have hKf := faithful_of_not_le S hH hK hKM
  obtain ⟨hQ5, ⟨hTK, hKmax, hNKmax, -⟩, -, -⟩ := h1332 G T L S.h13 K hKf
  have hnU := not_lieModel_PSU_F4 h1332 h13316 S hKf
  refine ⟨⟨hKmax, hKf⟩, le_normalizer_of_faithful_F4 h1332 S hH (le_of_mem_cComp hK) hKf, ?_, hKM,
    fun hLK => ?_, fun hKC => hKM (hKC.trans S.centralizer_ZV_le)⟩
  · rcases hQ5 with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · exact absurd h hnU
  · have := S.uniqueM.2 (normalizer (K : Set G)) ⟨hNKmax, sup_le hLK hTK⟩
    exact hKM (le_normalizer.trans this.le)

end CFSG.Quasithin.H13.NQS134
