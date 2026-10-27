module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIInn
public import CFSG.LocalAnalysis.StandardType.GGRecipeField
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmega
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestSz
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestTri
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestTwE6
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestReeF4

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace MI

open CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.RecipeFieldLinear CFSG.StandardType.RecipeFieldSU
  CFSG.StandardType.RecipeFieldSp CFSG.StandardType.RecipeFieldOmega
  CFSG.StandardType.RecipeFieldE6 CFSG.StandardType.RecipeFieldExcInn
  CFSG.StandardType.RawAutTri CFSG.StandardType.RawAutTwE6 CFSG.StandardType.RawAutSz
  CFSG.StandardType.RawAutReeF4


theorem anyLinear {p : ℕ} (hp1 : p ≠ 1) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hS : GGLinearRecipeLabel lab) : CFSG.StandardType.LargeEvenLabelAll lab (GGRawInnField p) := by
  intro Q₀ h
  obtain ⟨t, l, n⟩ := lab
  rcases hS with ht | ⟨ht, hl⟩ | ⟨ht, hl⟩ <;> dsimp only at ht <;> subst ht
  · obtain ⟨hl1, hl2⟩ : 1 ≤ l ∧ (l = 1 → 2 ≤ n) := hlab.2
    dsimp only [CFSG.StandardType.LargeEvenRawDatum] at h ⊢
    refine NbrGraphLinear.recipeLinear_all (fun K _ _ hK => ?_) h
    exact ggRawInnField_linear (by omega) (three_le_or_four_le_of_typeA hl1 hl2 hK) hp1
  · dsimp only at hl
    subst hl
    simp only [CFSG.StandardType.LargeEvenRawDatum, ↓reduceIte] at h ⊢
    refine NbrGraphLinear.recipeLinear_all (fun K _ _ _ => ?_) h
    exact ggRawInnField_linear (by omega) (Or.inl (by omega)) hp1
  · dsimp only at hl
    subst hl
    simp only [CFSG.StandardType.LargeEvenRawDatum, ↓reduceIte] at h ⊢
    refine NbrGraphLinear.recipeLinear_all (fun K _ _ hK => ?_) h
    exact ggRawInnField_linear le_rfl (Or.inr (four_le_card_of_sq hlab.1 hK)) hp1

theorem anyUnitary {p : ℕ} (hp1 : p ≠ 1) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hS : GGInndiagUnitaryLabel lab) :
    CFSG.StandardType.LargeEvenLabelAll lab (GGRawInnField p) :=
  largeEvenLabelAll_unitary hlab hS fun _ _ _ _ _ hn hd hq hK =>
    ggRawInnField_unitary (unitaryFieldData_of_card hn hK) hK hd hq hp1

theorem anySymplectic {p : ℕ} (hp1 : p ≠ 1) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hS : GGSymplecticRecipeLabel lab) :
    CFSG.StandardType.LargeEvenLabelAll lab (GGRawInnField p) := by
  intro Q₀ h
  obtain ⟨t, l, n⟩ := lab
  rcases hS with ht | ht <;> dsimp only at ht <;> subst ht
  · have hl2 : 2 ≤ l := hlab.2.1
    have : NeZero l := ⟨by omega⟩
    dsimp only [CFSG.StandardType.LargeEvenRawDatum] at h ⊢
    refine NbrGraphSymplectic.recipeSymplectic_all (fun K _ _ hK => ?_) h
    have : CharP K 2 := charP_two_of_card hK
    exact ggRawInnField_symplectic hp1
  · have hl2 : 2 ≤ l := hlab.2.1
    have : NeZero l := ⟨by omega⟩
    dsimp only [CFSG.StandardType.LargeEvenRawDatum] at h ⊢
    refine NbrGraphSymplectic.recipeSymplectic_all (fun K _ _ hK => ?_) h
    have : CharP K 2 := charP_two_of_card hK
    exact ggRawInnField_symplectic hp1

theorem anyOmegaPlus {p : ℕ} (hp1 : p ≠ 1) {lab : LargeEvenLabel} (hS : GGOmegaPlusLabel lab) :
    CFSG.StandardType.LargeEvenLabelAll lab (GGRawInnField p) := by
  obtain ⟨ht, h4⟩ := hS
  exact largeEvenLabelAll_omegaPlus ht h4 fun _ _ _ _ _ => ggRawInnField_omegaPlus (by omega) hp1

theorem anyOmegaMinus {p : ℕ} (hp1 : p ≠ 1) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hS : GGOmegaMinusLabel lab) :
    CFSG.StandardType.LargeEvenLabelAll lab (GGRawInnField p) :=
  largeEvenLabelAll_omegaMinus hS.1 hS.2 fun _ _ _ _ hK _ _ hirr =>
    ggRawInnField_omegaMinus hS.2 hirr hK hlab.1 hp1

theorem anyB2der {p : ℕ} (hp1 : p ≠ 1) {lab : LargeEvenLabel} (hS : GGB2derLabel lab) :
    CFSG.StandardType.LargeEvenLabelAll lab (GGRawInnField p) :=
  largeEvenLabelAll_b2der hS fun _ _ _ hK => (ggRawAll_b2der hK hp1).1

theorem anyE6 {p : ℕ} (hp1 : p ≠ 1) {lab : LargeEvenLabel} (hS : lab.tag = .E6) :
    CFSG.StandardType.LargeEvenLabelAll lab (GGRawInnField p) := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hS
  subst hS
  exact recipeChevalley_and (fun K _ _ _ => ggRawInnField_E6 K hp1) hQ

theorem anyExcInn {p : ℕ} (hp1 : p ≠ 1) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hS : GGRecipeExcInnLabel lab) :
    CFSG.StandardType.LargeEvenLabelAll lab (GGRawInnField p) := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  rcases hS with ht | ht | ht <;> dsimp only at ht <;> subst ht
  · obtain ⟨-, hn2⟩ := hl
    exact recipeChevalley_and (fun K _ _ hK =>
      ggRawInnField_excInn .G2 hn K hK (Or.inl ⟨rfl, hn2⟩) hp1) hQ
  · exact recipeChevalley_and (fun K _ _ hK =>
      ggRawInnField_excInn .E7 hn K hK (Or.inr (Or.inl rfl)) hp1) hQ
  · exact recipeChevalley_and (fun K _ _ hK =>
      ggRawInnField_excInn .E8 hn K hK (Or.inr (Or.inr rfl)) hp1) hQ

theorem anyF4 {p : ℕ} (hp1 : p ≠ 1) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hS : lab.tag = .F4) : CFSG.StandardType.LargeEvenLabelAll lab (GGRawInnField p) := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at hS
  subst hS
  exact recipeChevalley_and (fun K _ _ hK => ggRawInnField_F4 hn K hK hp1) hQ

theorem anyTriD4 {p : ℕ} (hp1 : p ≠ 1) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hS : lab.tag = .triD4) : CFSG.StandardType.LargeEvenLabelAll lab (GGRawInnField p) := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at hS
  subst hS
  exact recipeTwisted_and (fun K _ _ hK => ggRawInnField_triD4 hn K hK hp1) hQ

theorem anyTwE6 {p : ℕ} (hp1 : p ≠ 1) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hS : lab.tag = .twE6) : CFSG.StandardType.LargeEvenLabelAll lab (GGRawInnField p) := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at hS
  subst hS
  exact recipeTwisted_and (fun K _ _ hK => ggRawInnField_twE6 hn K hK hp1) hQ

theorem anyTwB2 {p : ℕ} (hp1 : p ≠ 1) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hS : lab.tag = .twB2) : CFSG.StandardType.LargeEvenLabelAll lab (GGRawInnField p) := by
  intro Q h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hS
  subst hS
  have hn3 : 3 ≤ n := hlab.2.2.2
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at h ⊢
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, ggRawInnField_suzuki (by omega) hK hp1⟩

theorem anyTwF4 {p : ℕ} (hp1 : p ≠ 1) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hS : lab.tag = .twF4) : CFSG.StandardType.LargeEvenLabelAll lab (GGRawInnField p) := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hS
  subst hS
  have hn3 : 3 ≤ n := hlab.2.2.2
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQK⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQK, fun hs hna => ?_⟩
  exact ggRawInnField_twF4_of_diag (by omega) hK
    (ggTwistedF4DiagInput_holds _ (by omega) K hK hs) hp1 hs hna

theorem legacyRawInnAny {p : ℕ} (hp1 : p ≠ 1) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hd : ¬ DerivedLab lab) :
    CFSG.StandardType.LargeEvenLabelAll lab (GGRawInnField p) := by
  obtain ⟨t, l, n⟩ := lab
  cases t with
  | A => exact anyLinear hp1 hlab (Or.inl rfl)
  | twA => exact anyUnitary hp1 hlab (Or.inl rfl)
  | B => exact anySymplectic hp1 hlab (Or.inl rfl)
  | C => exact anySymplectic hp1 hlab (Or.inr rfl)
  | D =>
    have hl : 3 ≤ l := hlab.2
    by_cases h3 : l = 3
    · exact anyLinear hp1 hlab (Or.inr (Or.inl ⟨rfl, h3⟩))
    · exact anyOmegaPlus hp1 (lab := ⟨.D, l, n⟩) ⟨rfl, show 4 ≤ l by omega⟩
  | twD =>
    have hl : 2 ≤ l := hlab.2
    by_cases h2 : l = 2
    · exact anyLinear hp1 hlab (Or.inr (Or.inr ⟨rfl, h2⟩))
    · by_cases h3 : l = 3
      · exact anyUnitary hp1 hlab (Or.inr ⟨rfl, h3⟩)
      · exact anyOmegaMinus hp1 hlab (lab := ⟨.twD, l, n⟩) ⟨rfl, show 4 ≤ l by omega⟩
  | E6 => exact anyE6 hp1 rfl
  | E7 => exact anyExcInn hp1 hlab (Or.inr (Or.inl rfl))
  | E8 => exact anyExcInn hp1 hlab (Or.inr (Or.inr rfl))
  | F4 => exact anyF4 hp1 hlab rfl
  | G2 => exact anyExcInn hp1 hlab (Or.inl rfl)
  | twE6 => exact anyTwE6 hp1 hlab rfl
  | triD4 => exact anyTriD4 hp1 hlab rfl
  | twB2 => exact anyTwB2 hp1 hlab rfl
  | twF4 => exact anyTwF4 hp1 hlab rfl
  | B2der => exact anyB2der hp1 (lab := ⟨.B2der, l, n⟩) rfl
  | G2der => exact absurd (Or.inl rfl) hd
  | twF4der => exact absurd (Or.inr rfl) hd

theorem canonRawInnAny {p : ℕ} (hp1 : p ≠ 1) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) : CAll lab (GGRawInnField p) := by
  by_cases hd : DerivedLab lab
  · obtain ⟨t, l, n⟩ := lab
    rcases hd with hd | hd
    · dsimp only at hd
      subst hd
      intro Q h
      dsimp only [CFSG.Assembly.LargeEvenRawDatum] at h ⊢
      obtain ⟨K, hF, hfin, hK, hQ⟩ := h
      exact ⟨K, hF, hfin, hK, hQ, chevParentID_rawInnField _ hK _ _ hp1⟩
    · dsimp only at hd
      subst hd
      obtain ⟨-, -, hn1⟩ := hlab
      have hn1' : n = 1 := hn1
      subst hn1'
      intro Q h
      dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeTwF4Inherited] at h ⊢
      obtain ⟨K, hF, hfin, hK, hQ⟩ := h
      have hK2 : Nat.card K = 2 := by simpa using hK
      refine ⟨K, hF, hfin, hK, hQ, ?_⟩
      simp only [show (1 - 1) / 2 = 0 from rfl, if_true]
      exact chevParentID_rawInnField _ hK2 _ _ hp1
  · exact (canonAll_iff_legacyAll hlab hd _).2 (legacyRawInnAny hp1 hlab hd)

end MI

end CFSG.LocalAnalysis.GLTheoremA
