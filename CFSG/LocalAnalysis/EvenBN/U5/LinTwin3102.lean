module

public import CFSG.LocalAnalysis.EvenBN.U5.LinLayer
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofTenTwo

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf)

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem lin_card_centerIn_M₂ (hl : d.LinCtx) {R : Subgroup G} (hR : IsSylowOf 2 R d.M₂) :
    Nat.card (CFSG.centerIn R) ≤ (2 ^ f) ^ 2 := by
  obtain ⟨R₁, R₂, hrad⟩ := lin_exists_radicals_of_isSylowOf_M₂ hl hR
  exact le_of_eq hrad.card_center

section Certified


theorem lin_sec3102 (hl : d.LinCtx) (k : d.Know93) (hO : d.Sec3101OrdersAll) :
    d.Sec3_10_two :=
  sec3102_of_hyp hl.toCaseHyp k hO (fun hR => lin_card_centerIn_M₂ hl hR)

end Certified

end Data

end CFSG.LocalAnalysis.EvenBN.U5
