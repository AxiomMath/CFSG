module

public import CFSG.GH74.GLS.SP.GlueBN
public import CFSG.GH74.GLS.SP.Final

public noncomputable section

namespace CFSG.GH74.GLS.SP

open CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def SPGlueData (G : Type) [Group G] (F : Type) [Field F] (hF : 4 ≤ Nat.card F) : Prop :=
  ∃ (H : Subgroup G) (r₁ r₂ : G) (U : Subgroup G) (root : ℤ → Subgroup G)
    (R : RGD2 4 H r₁ r₂ U root), (H ⊔ U) ⊔ R.N = ⊤ ∧
    ∃ φ : U ≃* (modelSystem F hF).U, ∀ i : ℤ, 1 ≤ i → i ≤ 4 → ∀ x : U,
      (x : G) ∈ root i ↔
        ((φ x : (modelSystem F hF).U) : StatedProj (StatedSp 2 F)) ∈ (modelSystem F hF).root i

theorem spRankTwoData_of_glueData {G : Type} [Group G] [IsSimpleGroup G] {F : Type} [Field F]
    {hF : 4 ≤ Nat.card F} (h : SPGlueData G F hF) : SPRankTwoData G F hF := by
  obtain ⟨H, r₁, r₂, U, root, R, hgen, φ, hφ⟩ := h
  exact ⟨(R.toPre hgen).toSystemOfSimple, φ, hφ⟩

theorem sp_of_glueData {G : Type} [Group G] [IsSimpleGroup G] {F : Type} [Field F]
    {hF : 4 ≤ Nat.card F} (h : SPGlueData G F hF) : Nonempty (G ≃* StatedProj (StatedSp 2 F)) :=
  sp_of_rankTwoData hF (spRankTwoData_of_glueData h)

@[expose] def SPLocalGlue : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G →
    ∀ (Gs : Type) [Group Gs] (F : Type) [Field F] [Finite F] (hF : 4 ≤ Nat.card F),
      Odd (Nat.card F) → Nonempty (Gs ≃* StatedProj (StatedSp 2 F)) →
        IsTwoCentralClassicalType G Gs → SPGlueData G F hF

theorem spLocal_of_glue (h : SPLocalGlue) : SPLocal := by
  intro G _ _ hK Gs _ F _ _ hF hodd e hT
  have := hK.1
  exact spRankTwoData_of_glueData (h G hK Gs F hF hodd e hT)

theorem S_stage5_SP_of_localGlue (h : SPLocalGlue) : S_stage5_SP :=
  S_stage5_SP_of_local (spLocal_of_glue h)

end CFSG.GH74.GLS.SP
