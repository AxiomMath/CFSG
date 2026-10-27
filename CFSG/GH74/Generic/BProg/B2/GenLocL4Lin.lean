module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4Inner
public import CFSG.GH74.Generic.BProg.B2.GenLocL4Lift
public import CFSG.GH74.Generic.BProg.B2.GenLocBasicIso4

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification Subgroup

namespace GenLocL4Lin

@[expose] def Sl4OuterStmt (F : Type) [Field F] [Finite F] : Prop :=
  ringChar F ≠ 2 → Nat.card F % 4 = 3 → 7 ≤ Nat.card F →
    ∀ {A : Type} [Group A] [Finite A] (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F)),
      IsRank23 A →
      (∃ a : A, ¬ ∃ x : GL (Fin 4) F, ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
        ((α a g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
          (x : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
            ((x⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) →
      SectionalTwoRankLE ↥(innJoin α) 4 → gammaAct α = ⊤

theorem ringChar_ne_two {F : Type} [Field F] [Finite F] (hF4 : Nat.card F % 4 = 3) :
    ringChar F ≠ 2 := fun h => by
  have := Fintype.ofFinite F
  have hr := FiniteField.even_card_of_char_two h
  rw [← Nat.card_eq_fintype_card] at hr
  omega

end GenLocL4Lin

section Lin

variable {F : Type} [Field F] [Finite F]

theorem gammaAct_sl4_lin_of_classes (hF4 : Nat.card F % 4 = 3) (h7 : 7 ≤ Nat.card F)
    (hQuat : GenLocL4Inner.Sl4QuatStmt F) (hOut : GenLocL4Lin.Sl4OuterStmt F)
    {A : Type} [Group A] [Finite A] (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F))
    (hA : IsRank23 A) (hsect : SectionalTwoRankLE ↥(innJoin α) 4) : gammaAct α = ⊤ := by
  have hF := GenLocL4Lin.ringChar_ne_two hF4
  by_cases hin : ∀ c : A, ∃ x : GL (Fin 4) F, ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      ((α c g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (x : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
          ((x⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
  · exact GenLocL4Inner.gammaAct_sl4_inner_of_quat hF hF4 h7 hQuat α hA hin hsect
  · exact hOut hF hF4 h7 α hA (not_forall.1 hin) hsect

theorem sl4Gen_of_classes (hF4 : Nat.card F % 4 = 3) (h7 : 7 ≤ Nat.card F)
    (hQuat : GenLocL4Inner.Sl4QuatStmt F) (hOut : GenLocL4Lin.Sl4OuterStmt F) :
    GenLocL4Lift.Sl4GenStmt F :=
  fun α hA hsect => gammaAct_sl4_lin_of_classes hF4 h7 hQuat hOut α hA hsect

theorem genLoc4_sl4_lin_of_classes {J : Type} [Group J] (hF4 : Nat.card F % 4 = 3)
    (h7 : 7 ≤ Nat.card F) (hQuat : GenLocL4Inner.Sl4QuatStmt F)
    (hOut : GenLocL4Lin.Sl4OuterStmt F) (e : J ≃* Matrix.SpecialLinearGroup (Fin 4) F) : GenLoc4 J :=
  GenLoc4.of_mulEquiv e.symm (GenLocL4Lift.genLoc4_sl4 (sl4Gen_of_classes hF4 h7 hQuat hOut))

end Lin

theorem genLoc4_l4_lin_of_classes {J : Type} [Group J] {p f : ℕ} (hJ : LieModel J .PSL 4 p f)
    (hq4 : p ^ f % 4 = 3) (hq7 : 7 ≤ p ^ f)
    (hQuat : ∀ (F : Type) [Field F] [Finite F], GenLocL4Inner.Sl4QuatStmt F)
    (hOut : ∀ (F : Type) [Field F] [Finite F], GenLocL4Lin.Sl4OuterStmt F) : GenLoc4 J := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hJ
  have hF4 : Nat.card F % 4 = 3 := by rw [hF]; exact hq4
  have h7 : 7 ≤ Nat.card F := by rw [hF]; exact hq7
  exact GenLoc4.of_mulEquiv e.symm (GenLocL4Lift.genLoc4_projectiveSL4
    (sl4Gen_of_classes hF4 h7 (hQuat F) (hOut F)))

end CFSG.GH74.Generic.BProg.B2
