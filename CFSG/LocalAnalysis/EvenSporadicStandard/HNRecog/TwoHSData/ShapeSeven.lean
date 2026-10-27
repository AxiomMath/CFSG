module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ProdCentral
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Elem2Rec

public section

namespace CFSG.EvenSporadicStandard.HNRecog.TwoHSData

open Subgroup

theorem isShapeCentralizerSeven_of_data {G : Type} [Group G] [Finite G] (X V S : Subgroup G)
    (hVX : V ≤ X) (hSX : S ≤ X) (hX : Nat.card ↥X = 28) (hV : Nat.card ↥V = 4)
    (hS : Nat.card ↥S = 7) (hVcen : ∀ v ∈ V, ∀ x ∈ X, x * v = v * x)
    (hVsq : ∀ v ∈ V, v * v = 1) (hVS : ∀ v ∈ V, v ∈ S → v = 1) :
    IsShapeCentralizerSeven ↥X := by
  have hcard : Nat.card ↥X = Nat.card ↥V * Nat.card ↥S := by
    rw [hX, hV, hS]
  obtain ⟨eXS⟩ := nonempty_mulEquiv_prod_of_central X V S hVX hSX hVcen hVS hcard
  obtain ⟨eV⟩ :=
    nonempty_mulEquiv_elem2 (G := ↥V) 2 (fun v => Subtype.ext (hVsq v.1 v.2))
      (by rw [hV]; norm_num)
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have eS : ↥S ≃* Multiplicative (ZMod 7) :=
    mulEquivOfPrimeCardEq (p := 7) hS (by simp [Nat.card_zmod])
  exact ⟨(eXS.trans (MulEquiv.prodCongr eV eS)).trans MulEquiv.prodComm⟩

end CFSG.EvenSporadicStandard.HNRecog.TwoHSData
