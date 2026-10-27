module

public import CFSG.Quasithin.EmptyFaithful.S151TCOrd
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.C2Seven

public section

namespace CFSG.Quasithin.S151TC

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
  CFSG.Quasithin.S151TB

theorem c27_g_of_card168_F4 {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] (hC27 : ASC27Statement_F4 G)
    {H R M K : Subgroup G} (hyp : HypC23 H R M) (hK : K ∈ cComp H)
    (hq : CFSG.IsQuasisimple (LStar K)) (hch : CharTwo K) (hnle : ¬ K ≤ M)
    (hRN : R ≤ Subgroup.normalizer (K : Set G)) (hcard : Nat.card (LStar K) = 168) :
    (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), 1 ≤ n ∧ Fintype.card F = 2 ^ n ∧
        Nonempty (↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) ≃*
          ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))) ∧
      IsMaxParabolic2 (autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))
        (autOn (M ⊓ K) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) ∧
      IsMSPair (K ⊔ R) R := by
  obtain ⟨h1, -, h3⟩ :=
    hC27 H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) hyp hK hq hch hnle hRN rfl
  rcases h3 with ⟨-, hcases⟩ | ⟨⟨n, α, hn5, hn8, -, hα, -⟩, -⟩ | ⟨hHat, -⟩ | ⟨hexc, -⟩ |
    ⟨hAS, -⟩ | ⟨hG2, -, -⟩ | hg | ⟨hh, -, -⟩
  · exfalso
    rcases hcases with ⟨⟨n, hn, hlin⟩, -⟩ | ⟨hA5, -⟩ | ⟨hA7, -⟩ | ⟨hA7, -⟩
    · exact (sl2_card_ne hn).1 ((card_lStar_of_isLin2Type hlin).symm.trans hcard)
    · rw [card_lStar_of_isAltType (by norm_num) hA5] at hcard
      revert hcard
      decide
    · rw [card_lStar_of_isAltType (by norm_num) hA7] at hcard
      revert hcard
      decide
    · rw [card_lStar_of_isAltType (by norm_num) hA7] at hcard
      revert hcard
      decide
  · exfalso
    exact (alt_card_ne hn5 hn8).1
      ((card_lStar_of_isAltBlockTypeWith (by omega) hα).symm.trans hcard)
  · exfalso
    rw [card_lStar_of_isHatA6Block hHat] at hcard
    revert hcard
    decide
  · exfalso
    rw [card_lStar_of_isExcA7Block hexc] at hcard
    revert hcard
    decide
  · exfalso
    rcases hAS with ⟨-, α, hα⟩ | hsp4
    · rw [card_lStar_of_isAltBlockTypeWith (by norm_num) hα] at hcard
      revert hcard
      decide
    · rw [card_lStar_of_isSp4Block hsp4] at hcard
      revert hcard
      decide
  · exfalso
    rw [card_lStar_of_isG2Block hG2] at hcard
    revert hcard
    decide
  · exact hg
  · exfalso
    rcases hh with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · have hd := card_dvd_lStar_of_autOn hRN h1 e
      rw [hcard, CFSG.Quasithin.Vol2.Ch10.SecA.card_statedSL,
        CFSG.Quasithin.Vol2.Ch10.SecA.card_SL_four_of_two (Nat.card_zmod 2)] at hd
      revert hd
      decide
    · have hd := card_dvd_lStar_of_autOn hRN h1 e
      rw [hcard, CFSG.Quasithin.Vol2.Ch10.SecA.card_statedSL,
        CFSG.Quasithin.Vol2.Ch10.SecA.card_SL_five_of_two (Nat.card_zmod 2)] at hd
      revert hd
      decide

theorem c27_c_of_card1080_F4 {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] (hC27 : ASC27Statement_F4 G)
    {H R M K : Subgroup G} (hyp : HypC23 H R M) (hK : K ∈ cComp H)
    (hq : CFSG.IsQuasisimple (LStar K)) (hch : CharTwo K) (hnle : ¬ K ≤ M)
    (hRN : R ≤ Subgroup.normalizer (K : Set G)) (hcard : Nat.card (LStar K) = 1080) :
    IsHatA6Block K ∧ M.relIndex K = 15 ∧
      ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 4 ∧
        ∃ (ρ : ↥K →* Matrix.GeneralLinearGroup (Fin 3) F)
          (e : ↥(blockU K) ≃* Multiplicative (Fin 3 → F)),
          (∀ (k : ↥K) (u v : ↥(blockU K)), (v : G) = k * u * k⁻¹ →
            Multiplicative.toAdd (e v) =
              ((ρ k : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
                (Multiplicative.toAdd (e u))) ∧
          ∃ W : Submodule F (Fin 3 → F), Module.finrank F W = 2 ∧
            ∀ k : ↥K, (k : G) ∈ M ↔ ∀ w ∈ W,
              ((ρ k : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w
                ∈ W := by
  obtain ⟨h1, -, h3⟩ :=
    hC27 H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) hyp hK hq hch hnle hRN rfl
  rcases h3 with ⟨-, hcases⟩ | ⟨⟨n, α, hn5, hn8, -, hα, -⟩, -⟩ | hc | ⟨hexc, -⟩ |
    ⟨hAS, -⟩ | ⟨hG2, -, -⟩ | ⟨⟨n, F, _, _, hn1, hF, ⟨e⟩⟩, -, -⟩ | ⟨hh, -, -⟩
  · exfalso
    rcases hcases with ⟨⟨n, hn, hlin⟩, -⟩ | ⟨hA5, -⟩ | ⟨hA7, -⟩ | ⟨hA7, -⟩
    · exact (sl2_card_ne hn).2 ((card_lStar_of_isLin2Type hlin).symm.trans hcard)
    · rw [card_lStar_of_isAltType (by norm_num) hA5] at hcard
      revert hcard
      decide
    · rw [card_lStar_of_isAltType (by norm_num) hA7] at hcard
      revert hcard
      decide
    · rw [card_lStar_of_isAltType (by norm_num) hA7] at hcard
      revert hcard
      decide
  · exfalso
    exact (alt_card_ne hn5 hn8).2
      ((card_lStar_of_isAltBlockTypeWith (by omega) hα).symm.trans hcard)
  · exact hc
  · exfalso
    rw [card_lStar_of_isExcA7Block hexc] at hcard
    revert hcard
    decide
  · exfalso
    rcases hAS with ⟨-, α, hα⟩ | hsp4
    · rw [card_lStar_of_isAltBlockTypeWith (by norm_num) hα] at hcard
      revert hcard
      decide
    · rw [card_lStar_of_isSp4Block hsp4] at hcard
      revert hcard
      decide
  · exfalso
    rw [card_lStar_of_isG2Block hG2] at hcard
    revert hcard
    decide
  · exfalso
    have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
    have hd := card_dvd_lStar_of_autOn hRN h1 e
    rw [hcard, CFSG.Quasithin.Vol2.Ch10.SecA.card_statedSL,
      CFSG.Quasithin.Vol2.Ch10.SecA.card_SL_three_pow hFn] at hd
    exact sl3_card_not_dvd_1080 hn1 hd
  · exfalso
    rcases hh with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · have hd := card_dvd_lStar_of_autOn hRN h1 e
      rw [hcard, CFSG.Quasithin.Vol2.Ch10.SecA.card_statedSL,
        CFSG.Quasithin.Vol2.Ch10.SecA.card_SL_four_of_two (Nat.card_zmod 2)] at hd
      revert hd
      decide
    · have hd := card_dvd_lStar_of_autOn hRN h1 e
      rw [hcard, CFSG.Quasithin.Vol2.Ch10.SecA.card_statedSL,
        CFSG.Quasithin.Vol2.Ch10.SecA.card_SL_five_of_two (Nat.card_zmod 2)] at hd
      revert hd
      decide

end CFSG.Quasithin.S151TC
