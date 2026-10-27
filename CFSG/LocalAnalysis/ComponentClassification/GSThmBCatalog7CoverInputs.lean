module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4CoverMult
public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

@[expose] def Sp4CenterPPartInput : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → IsQuasisimple Y →
    Blueprint.LieModel (Y ⧸ center Y) .PSp 2 p f → ¬ p ∣ Nat.card (center Y)

theorem sp4CenterPPartInput_of_allModels (hGA : TBLit.GriessMultipliersAllModels) :
    Sp4CenterPPartInput := by
  intro Y _ _ p f hp hp2 hY hm hdvd
  have hcardM := CatFactsSp4.card_griessHopfMultiplier_psp_two hGA hp hp2
    (CatFactsSp4.models_lieModel_of_lieModel_psp hm)
  have : Group.IsPerfect Y := hY.1
  have hd := CatFactsSp4.card_center_dvd_hopfMultiplier (MulEquiv.refl (Y ⧸ center Y))
  rw [Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess _).symm.toEquiv,
    hcardM] at hd
  have h2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hdvd.trans hd)
  exact hp2 h2

end CFSG.ComponentClassification.GSThmB
