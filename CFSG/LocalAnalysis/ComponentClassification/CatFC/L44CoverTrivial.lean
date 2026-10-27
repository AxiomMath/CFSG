module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Mult

public section

namespace CFSG.ComponentClassification.CatFC

theorem card_generic_exceptional_psl44 :
    Nat.card (CFSG.Blueprint.Multiplier.generic .PSL 4 2 2 ×
      CFSG.Blueprint.Multiplier.exceptional .PSL 4 2 2) = 1 := by
  have hg : CFSG.Blueprint.Multiplier.genericOrders .PSL 4 2 2 = (1, 1) := by decide
  have he : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 4 2 2 = (1, 1) := by decide
  have h1 : Nat.card (Multiplicative (ZMod 1)) = 1 := by
    rw [Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_zmod]
  simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional, hg, he,
    Nat.card_prod, h1, mul_one]

theorem center_eq_bot_of_quasisimple_psl44 {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.IsQuasisimple Y) (hL : CFSG.Blueprint.LieModel (Y ⧸ Subgroup.center Y) .PSL 4 2 2) :
    Subgroup.center Y = ⊥ := by
  haveI : Group.IsPerfect Y := hY.1
  have hM : CFSG.Models.LieModel (Y ⧸ Subgroup.center Y) .PSL 4 2 2 :=
    CFSG.ComponentClassification.CatFactsL4U4.Cover82.Mult.models_lieModel hL
  obtain ⟨-, ⟨e⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.GriessClassical.griess_classical_of_large .PSL hM
      (Or.inl rfl)
  have hcard : Nat.card (CFSG.Open.griessHopfMultiplier (Y ⧸ Subgroup.center Y)) = 1 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_generic_exceptional_psl44
  have hdvd := CFSG.ComponentClassification.CatFactsL4U4.Cover82.Mult.card_center_dvd_hopfMultiplier
    (Q := Y) (S := Y ⧸ Subgroup.center Y) (MulEquiv.refl (Y ⧸ Subgroup.center Y))
  rw [hcard] at hdvd
  exact Subgroup.card_eq_one.1 (Nat.dvd_one.1 hdvd)

end CFSG.ComponentClassification.CatFC
