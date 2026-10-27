module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15221Hstar
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152Stmts

public section

namespace CFSG.Quasithin.S15221

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem Y0_le_M_F4 (h08 : StageLemma15208_F4) {T Mc M : Subgroup G} (hs : Setting152 T Mc M)
    {Y₀ : Subgroup G} (hTY : T ≤ Subgroup.normalizer (Y₀ : Set G))
    (h3 : (pCoreOf 2 Y₀).relIndex Y₀ = 3) (hne : pCoreOf 2 Y₀ ≠ ⊥) : Y₀ ≤ M := by
  by_contra hY
  have hT2 : IsPGroup 2 T := hs.qtfe.sylow.1
  have hN : InH T (Y₀ ⊔ T) := by
    refine ⟨le_sup_right, ?_⟩
    have hle : pCoreOf 2 Y₀ ≤ pCoreOf 2 (Y₀ ⊔ T) := by
      refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Y₀).trans le_sup_left) ?_
        (pCoreOf_isPGroup 2 Y₀)
      exact sup_le (le_normalizer_pCoreOf 2 Y₀) (hTY.trans (normalizer_le_normalizer_pCoreOf 2 Y₀))
    intro hbot
    exact hne (le_bot_iff.mp (hbot ▸ hle))
  have hNM : ¬ Y₀ ⊔ T ≤ M := fun h => hY (le_sup_left.trans h)
  obtain ⟨H', hH', hH'le⟩ := exists_isHStar_le hN hNM
  obtain ⟨e⟩ := h08 G T Mc M hs H' hH'
  have h72 : Nat.card (OTwoQuot H') = 72 := by
    rw [Nat.card_congr e.toEquiv]
    exact S152N.W3.card_eq
  have h9 : 9 ∣ Nat.card ↥(Y₀ ⊔ T) := by
    have h1 : Nat.card (OTwoQuot H') ∣ Nat.card H' := Subgroup.card_quotient_dvd_card _
    have h2 : Nat.card H' ∣ Nat.card ↥(Y₀ ⊔ T) := Subgroup.card_dvd_of_le hH'le
    exact Dvd.dvd.trans (by rw [h72]; norm_num) (h1.trans h2)
  exact not_nine_dvd_sup hTY hT2 h3 h9

theorem Y0_le_cv_F4 (h08 : StageLemma15208_F4) {T Mc M H : Subgroup G}
    {B₀ : Subgroup (MulAut (V154 T Mc M))} {I : Subgroup G} (hs : Setting152 T Mc M)
    (hD : Inputs152 T Mc M H B₀ I) {Y₀ : Subgroup G}
    (hTY : T ≤ Subgroup.normalizer (Y₀ : Set G)) (hY : Y₀ = oTwoUpper Y₀)
    (h3 : (pCoreOf 2 Y₀).relIndex Y₀ = 3) (hne : pCoreOf 2 Y₀ ≠ ⊥) (hYMc : Y₀ ≤ Mc) :
    Y₀ ≤ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) := by
  have hYM : Y₀ ≤ M := Y0_le_M_F4 h08 hs hTY h3 hne
  have := oTwoUpper_le_cv_of_le_Mc hs hD hYM hYMc
  rwa [← hY] at this

end CFSG.Quasithin.S15221
