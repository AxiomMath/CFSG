module

public import CFSG.GH74.GLS.SP.Assembly

public noncomputable section

namespace CFSG.GH74.GLS.SP

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

abbrev TwoCentralPred : Type 1 := ∀ (G : Type) [Group G] (Gs : Type) [Group Gs], Prop

@[expose] def S_stage5_SP_for (T : TwoCentralPred) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G →
    ∀ (Gs : Type) [Group Gs], (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 < p ^ f ∧ LieModel Gs .PSp 2 p f) →
      T G Gs → Nonempty (G ≃* Gs)

@[expose] def SPLocalGlueFor (T : TwoCentralPred) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G →
    ∀ (Gs : Type) [Group Gs] (F : Type) [Field F] [Finite F] (hF : 4 ≤ Nat.card F),
      Odd (Nat.card F) → Nonempty (Gs ≃* StatedProj (StatedSp 2 F)) →
        T G Gs → SPGlueData G F hF

theorem S_stage5_SP_for_of_localGlueFor {T : TwoCentralPred} (h : SPLocalGlueFor T) :
    S_stage5_SP_for T := by
  intro G _ _ hK Gs _ ⟨p, f, hp, hp2, hq, hLie⟩ hT
  obtain ⟨K, _, _, hcard, ⟨e⟩⟩ := exists_model_of_lieModel_psp hLie
  have hodd : Odd (Nat.card K) := by
    rw [hcard]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hK4 : 4 ≤ Nat.card K := by rw [hcard]; omega
  have := hK.1
  obtain ⟨e2⟩ := sp_of_glueData (h G hK Gs K hK4 hodd ⟨e⟩ hT)
  exact ⟨e2.trans e.symm⟩

theorem S_stage5_SP_eq_for : S_stage5_SP = S_stage5_SP_for IsTwoCentralClassicalType := rfl

theorem SPLocalGlue_eq_for : SPLocalGlue = SPLocalGlueFor IsTwoCentralClassicalType := rfl

end CFSG.GH74.GLS.SP
