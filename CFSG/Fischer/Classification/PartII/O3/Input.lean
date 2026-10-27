module

public import CFSG.Fischer.Classification.PartII.O3.Kill
public import CFSG.Fischer.Classification.PartII.O3.Single

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer

theorem o3Input_of_confAt
    (hK : ∀ (X : Type) [Group X] (E : Set X), O3.Setting X E → ∀ (φ : O3.Pt → X) (w₁ w₂ : X)
      (r₁ r₂ : O3.Pt), O3.ConfAt E φ w₁ w₂ r₁ r₂ → False) : O3Input := by
  refine o3Input_of_ncard_le_three fun G _ D hH hnab d hd _ h3 => ?_
  have hS : O3.Setting G D := ⟨hH, hnab, d, hd, O3.Pair.exists_core_move hH.pair h3⟩
  by_cases hpw : ∀ y ∈ LocalClass D d, ∀ z ∈ LocalClass D d, y ≠ z → y * z ≠ z * y
  · exact hS.ncard_localClass_le_three_of_pairwise hd hpw
  · push Not at hpw
    obtain ⟨y, hy, z, hz, hyz, hc⟩ := hpw
    obtain ⟨a, ha, b, hb, hab, w, hw, v, hv, hnv⟩ := hS.exists_nonwit hd hy hz hyz hc
    obtain ⟨_, -, -, -, -, -, hconf⟩ := hS.exists_confAt_of_nonwit ha hb hab hw hv hnv
    exact (hK G D hS _ _ _ _ _ hconf).elim

theorem o3InputI : O3InputI :=
  o3InputI_of (o3Input_of_confAt fun _ _ _ hS _ _ _ _ _ hc => hc.false hS)

end CFSG.Fischer.Classification
