module

public import CFSG.ClassicalInvolution.Q3.TL3S8BCount
public import CFSG.ClassicalInvolution.Q3.TL3S8BCore

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

@[expose] def TightThm6SylowBelow (IH : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IH (Nat.card G) →
    ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G), TightDatum R S t → TightFStarOK G t →
      Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2) → ∀ T : Subgroup G,
      IsSylow2Of T
        (Subgroup.normalizer (((S : Subgroup R).map R.subtype : Subgroup G) : Set G)) →
      IsSylow2Of T ⊤ → Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore R)) →
        TwoSubgroupsFourGenerated (genFittingFStar G)

theorem TightThm6SylowBelow.mono {IH IH' : ℕ → Prop} (h : ∀ n, IH' n → IH n)
    (hI : TightThm6SylowBelow IH) : TightThm6SylowBelow IH' :=
  fun G _ _ hb => hI G (h _ hb)

theorem tightThm6Sylow_of_core {IH : ℕ → Prop} (hB3 : GoldschmidtB3Tmp)
    (h11b : TightC19_11b IH) : TightThm6SylowBelow IH := by
  intro G _ _ hbelow R S t hd hF hq T hT hTG he
  by_contra hn
  obtain ⟨T', -, h⟩ := TightSylowStd.exists_of_sylowCase hd hq he hn hT hTG
  obtain ⟨W, hW, -⟩ := h.exists_w69
  have hS3 := h.muIsoS3' hF hB3 hW
  have hmu := h.not_allTypeTwo_of_muIsoS3 hW hS3
  exact hn (h.twoSubgroupsFourGenerated_of_e2Prime (h.tightE2Prime_of_core hF h11b hbelow hmu))

end CFSG.ClassicalInvolution.Q3
