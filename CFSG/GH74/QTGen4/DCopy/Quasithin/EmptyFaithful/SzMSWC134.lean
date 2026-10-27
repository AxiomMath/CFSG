module

public import CFSG.Quasithin.EmptyFaithful.SzMSWC134
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.SzMSWConcl
public import CFSG.GH74.QTGen4.DCopy.Quasithin.MS93.ASC134
public import CFSG.Quasithin.MS93.ASC134C5
public import CFSG.Quasithin.MS93.ASC134NC5

public section

namespace CFSG.Quasithin.SzMSW

open CFSG.Quasithin CFSG.Quasithin.MS93 CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped Pointwise

section Statement

variable {G : Type} [Group G]

@[expose] def AS_C_1_34_corrW_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (G₀ R L : Subgroup G), IsMSPair G₀ R → L ∈ cComp G₀ →
    (G₀ : Set G) = (L : Set G) * (R : Set G) →
    (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ^ n ∧ IsModO2Surj L α) →
      ∃ i : ℕ, IsC134CaseCorrW i G₀ R L

theorem AS_C_1_34_corr_of_W_F4 (h : AS_C_1_34_corrW_F4) : AS_C_1_34_corr_F4 := by
  intro G _ _ G₀ R L hMS hL hG hsl3
  obtain ⟨i, hi⟩ := h G G₀ R L hMS hL hG hsl3
  exact ⟨i, hi.corr⟩

end Statement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem asC134_corrW_of_ms93ASW_of_simple_F4
    (hS : RankTwoLieSimple)
    (hNC5 : C134NotCentralizer5) (hNC11 : C134NotCentralizer11) (hNC13 : C134NotCentralizer13)
    (hms : MS93ASW_F4) : AS_C_1_34_corrW_F4 := by
  intro G _ _ G₀ R L hMS hL hG hsl3
  obtain ⟨n, F, _, _, α, hF, hα⟩ := hsl3
  have h := puHyp_of_msPair_of_simple hS hMS hL hG
  rcases hms G G₀ R L h with
    h2 | h3 | h4 | ⟨hX5, h5⟩ | h6 | h8 | h10 | ⟨hX11, h11⟩ | ⟨hX13, h13, hW⟩
  · exact (not_case2_of_sl3 h h2 hF hα).elim
  · exact (not_case3_of_sl3 h h3 hF hα).elim
  · exact ⟨1, isSL3Block_of_case4 h h4⟩
  · refine ⟨2, ?_, hNC5 G G₀ R L hMS hL hG h hX5 h5⟩
    obtain ⟨n', F', _, _, α', hF', hmod, hn⟩ := isModO2Surj_of_case5 h h5
    exact ⟨n', F', inferInstance, inferInstance, α', hF', hmod, hn⟩
  · exact (not_case6_of_sl3 h h6 hF hα).elim
  · exact ⟨5, isC134Case5_of_case8 hMS hL hG h h8⟩
  · exact (not_case10_of_sl3 h h10 hF hα).elim
  · refine ⟨3, ?_, hNC11 G G₀ R L hMS hL hG h hX11 h11⟩
    obtain ⟨n', F', _, _, α', hF', hα', h1, h2, -⟩ := h11
    exact ⟨n', F', inferInstance, inferInstance, α', hF',
      isModO2Surj_of_case11_data h hα' h1 h2, h1, h2⟩
  · refine ⟨4, ⟨?_, hNC13 G G₀ R L hMS hL hG h hX13 h13⟩, hW⟩
    obtain ⟨n', F', _, _, α', hF', hα', hcard, hE, hZeq, hdisj, hU, hΦ, hC, hVC, -⟩ := h13
    exact ⟨n', F', inferInstance, inferInstance, α', hF',
      isModO2Surj_of_case13_data h hα' hZeq hU hΦ hC hVC, isE2_c134CQ_of_case13 hcard hE, hZeq,
      hdisj, hU, hΦ, hC, hVC⟩

theorem asC134_corrW_of_ms93ASW_F4
    (hms : MS93ASW_F4) : AS_C_1_34_corrW_F4 :=
  asC134_corrW_of_ms93ASW_of_simple_F4 rankTwoLieSimple_holds c134NotCentralizer5_holds
    c134NotCentralizer11_holds c134NotCentralizer13_holds hms

end CFSG.Quasithin.SzMSW
