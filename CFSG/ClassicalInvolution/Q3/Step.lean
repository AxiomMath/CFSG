module

public import CFSG.ClassicalInvolution.Q3.Split

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

@[expose] def ConnectedBranch3 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CIT3Below (Nat.card Y) → classicalInvolutionOddCore Y = ⊥ →
    ∀ Λ : Set (Subgroup Y), InClass3 Λ → NonCommConnected Λ → LieSystem3 Y Λ

theorem cit3Step_of_connectedBranch (h : ConnectedBranch3) (n : ℕ) : CIT3Step n := by
  intro hBelow Y _ _ hY Λ hΛ
  have hBelow' : CIT3Below (Nat.card Y) := by rw [hY]; exact hBelow
  by_cases hO : classicalInvolutionOddCore Y = ⊥
  · by_cases hconn : NonCommConnected Λ
    · exact lieSystemMod3_of_lieSystem3_corefree hO (h Y hBelow' hO Λ hΛ hconn)
    · exact lieSystemMod3_of_lieSystem3_corefree hO
        (lieSystem3_of_not_connected hBelow' hO hΛ hconn)
  · exact lieSystemMod3_of_oddQuotient hBelow' hO hΛ

theorem cit3Inductive_of_connectedBranch (h : ConnectedBranch3) : CIT3Inductive :=
  cit3Inductive_of_step (cit3Step_of_connectedBranch h)

theorem lieSystem3_of_equiv_sl2Three {Y : Type} [Group Y] (e : SL(2, ZMod 3) ≃* Y) :
    LieSystem3 Y {⊤} := by
  have hcard : Nat.card (⊤ : Subgroup Y) = 24 := by
    rw [Subgroup.card_top, ← Nat.card_congr e.toEquiv, natCard_sl2Three]
  refine ⟨Unit, inferInstance, ⟨{
    kind := fun _ => CompData.sl23
    valid := fun _ => Or.inr (Or.inl rfl)
    hom := fun _ => e.toMonoidHom
    ker_le_center := fun _ => by
      rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]
      exact bot_le
    commute := fun i j h => absurd (Subsingleton.elim i j) h
    generate := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨y, rfl⟩ := e.surjective x
      exact Subgroup.mem_iSup_of_mem () ⟨y, rfl⟩
    fundamental := by
      intro L hL
      rw [Set.mem_singleton_iff] at hL
      subst hL
      refine ⟨(), ⊤, rfl, ?_⟩
      rw [Subgroup.map_top_of_surjective _ e.surjective]
    meets := fun _ => ⟨⊤, rfl, by
      rw [Subgroup.map_top_of_surjective _ e.surjective]
      rfl⟩
    card_eq := by
      intro L hL
      rw [Set.mem_singleton_iff] at hL
      subst hL
      exact hcard }⟩⟩

end CFSG.ClassicalInvolution.Q3
