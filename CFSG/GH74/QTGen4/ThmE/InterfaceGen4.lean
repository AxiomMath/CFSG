module

public import CFSG.GH74.QTGen4.ThmE.MS93Gen4

public section

namespace CFSG.GH74.QTGen4.ThmE

open CFSG.Quasithin CFSG.Quasithin.MS93 CFSG.GH74 CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.MS93.S45 CFSG.Quasithin.SzMSW CFSG.Quasithin.MS93.S34D
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S46 CFSG.Quasithin.MS93.S46R

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

open CFSG.Quasithin.ASInputs CFSG.QuasithinUnique
open scoped Pointwise

@[expose] def AS_C_1_32Gen4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Gen4 G → ∀ (G₀ R L : Subgroup G), IsMSPair G₀ R →
    L ∈ cComp G₀ → (G₀ : Set G) = (L : Set G) * (R : Set G) →
      IsG2Block L ∨ IsAltBlockType L 6 ∨ IsSp4Block L ∨ IsHatA6Block L ∨
        ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
          Fintype.card F = 2 ^ n ∧ IsModO2Surj L α

@[expose] def AS_C_1_34_corrWGen4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Gen4 G → ∀ (G₀ R L : Subgroup G), IsMSPair G₀ R →
    L ∈ cComp G₀ → (G₀ : Set G) = (L : Set G) * (R : Set G) →
    (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ^ n ∧ IsModO2Surj L α) →
      ∃ i : ℕ, IsC134CaseCorrW i G₀ R L

@[expose] def AS_C_1_34_corrGen4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Gen4 G → ∀ (G₀ R L : Subgroup G), IsMSPair G₀ R →
    L ∈ cComp G₀ → (G₀ : Set G) = (L : Set G) * (R : Set G) →
    (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ^ n ∧ IsModO2Surj L α) →
      ∃ i : ℕ, IsC134CaseCorr i G₀ R L

theorem AS_C_1_34_corrGen4_of_W (h : AS_C_1_34_corrWGen4) : AS_C_1_34_corrGen4 := by
  intro G _ _ hG G₀ R L hMS hL hGL hsl3
  obtain ⟨i, hi⟩ := h G hG G₀ R L hMS hL hGL hsl3
  exact ⟨i, hi.corr⟩

theorem asC132Gen4_of_ms93ASWGen4
    (hS : RankTwoLieSimple) (hms : MS93ASWGen4) :
    AS_C_1_32Gen4 := by
  intro G _ _ hG G₀ R L hMS hL hGL
  have h := puHyp_of_msPair_of_simple hS hMS hL hGL
  rcases (hms G hG G₀ R L h).toConclAS with
    h2 | h3 | h4 | ⟨-, h5⟩ | h6 | h8 | h10 | ⟨-, h11⟩ | ⟨-, h13⟩
  · exact Or.inr (Or.inl (isAltBlockType_of_case2 h h2))
  · rcases hMS.2.1 with ha | hb
    · exact Or.inr (Or.inr (Or.inl (isSp4Block_of_case3 h h3 (isOddRadical_of_msPair h.le ha))))
    · exact absurd h3 (not_case3_of_g2Two h hb.2.2.1)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (isModO2Surj_of_case4 h h4))))
  · obtain ⟨n, F, _, _, α, hF, hmod, -⟩ := isModO2Surj_of_case5 h h5
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨n, F, inferInstance, inferInstance, α, hF, hmod⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (isHatA6Block_of_case6 h h6))))
  · obtain ⟨α, hmod, -⟩ := isModO2Surj_of_case8 h h8
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨1, ZMod 2, inferInstance, inferInstance, α,
      by rw [ZMod.card, pow_one], hmod⟩)))
  · exact Or.inl (isG2Block_of_case10 h h10)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (isModO2Surj_of_case11 h h11))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (isModO2Surj_of_case13 h h13))))

theorem asC134_corrWGen4_of_ms93ASWGen4
    (hS : RankTwoLieSimple) (hNC5 : C134NotCentralizer5) (hNC11 : C134NotCentralizer11)
    (hNC13 : C134NotCentralizer13) (hms : MS93ASWGen4) : AS_C_1_34_corrWGen4 := by
  intro G _ _ hG G₀ R L hMS hL hGL hsl3
  obtain ⟨n, F, _, _, α, hF, hα⟩ := hsl3
  have h := puHyp_of_msPair_of_simple hS hMS hL hGL
  rcases hms G hG G₀ R L h with
    h2 | h3 | h4 | ⟨hX5, h5⟩ | h6 | h8 | h10 | ⟨hX11, h11⟩ | ⟨hX13, h13, hW⟩
  · exact (not_case2_of_sl3 h h2 hF hα).elim
  · exact (not_case3_of_sl3 h h3 hF hα).elim
  · exact ⟨1, isSL3Block_of_case4 h h4⟩
  · refine ⟨2, ?_, hNC5 G G₀ R L hMS hL hGL h hX5 h5⟩
    obtain ⟨n', F', _, _, α', hF', hmod, hn⟩ := isModO2Surj_of_case5 h h5
    exact ⟨n', F', inferInstance, inferInstance, α', hF', hmod, hn⟩
  · exact (not_case6_of_sl3 h h6 hF hα).elim
  · exact ⟨5, isC134Case5_of_case8 hMS hL hGL h h8⟩
  · exact (not_case10_of_sl3 h h10 hF hα).elim
  · refine ⟨3, ?_, hNC11 G G₀ R L hMS hL hGL h hX11 h11⟩
    obtain ⟨n', F', _, _, α', hF', hα', h1, h2, -⟩ := h11
    exact ⟨n', F', inferInstance, inferInstance, α', hF',
      isModO2Surj_of_case11_data h hα' h1 h2, h1, h2⟩
  · refine ⟨4, ⟨?_, hNC13 G G₀ R L hMS hL hGL h hX13 h13⟩, hW⟩
    obtain ⟨n', F', _, _, α', hF', hα', hcard, hE, hZeq, hdisj, hU, hΦ, hC, hVC, -⟩ := h13
    exact ⟨n', F', inferInstance, inferInstance, α', hF',
      isModO2Surj_of_case13_data h hα' hZeq hU hΦ hC hVC, isE2_c134CQ_of_case13 hcard hE, hZeq,
      hdisj, hU, hΦ, hC, hVC⟩

open CFSG.Quasithin.ASInputs CFSG.QuasithinUnique
open scoped Pointwise

@[expose] def AS_C_1_34_corrAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (G₀ R L : Subgroup G), IsMSPair G₀ R → L ∈ cComp G₀ →
    (G₀ : Set G) = (L : Set G) * (R : Set G) →
    (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ^ n ∧ IsModO2Surj L α) →
      ∃ i : ℕ, IsC134CaseCorr i G₀ R L

theorem AS_C_1_34_corrAt_of_gen4 (h : AS_C_1_34_corrGen4) {G : Type} [Group G] [Finite G]
    (hG : Gen4 G) : AS_C_1_34_corrAt G := h G hG

end CFSG.GH74.QTGen4.ThmE
