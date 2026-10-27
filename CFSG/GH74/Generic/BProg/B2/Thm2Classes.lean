module

public import CFSG.GH74.Generic.BProg.B2.Thm2Two
public import CFSG.GH74.Generic.BProg.B2.GenLocU4Fam
public import CFSG.GH74.Generic.BProg.B2.GenLocL4Final

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup

section Classes

theorem genLoc4_isSL4Model_of_classes' {J : Type} [Group J] (hJ : CFSG.GH74.L5U5.IsSL4Model J)
    (hlin : ∀ (F : Type) [Field F] [Finite F], Nat.card F % 4 = 3 →
      GenLoc4 (Matrix.SpecialLinearGroup (Fin 4) F))
    (hExt : ∀ (F : Type) [Field F] [Finite F] (p f : ℕ), GenLocU4Inner.Su4ExtStmt F p f)
    (hQuat : ∀ (F : Type) [Field F] [Finite F] (p f : ℕ), GenLocU4Inner.Su4QuatStmt F p f)
    (hOut : ∀ (F : Type) [Field F] [Finite F] (p f : ℕ), GenLocU4Fam.Su4OuterStmt F p f) : GenLoc4 J := by
  rcases hJ with ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨q, F, _, _, hF, hq, ⟨e⟩⟩
  · exact GenLoc4.of_mulEquiv (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 F).symm).symm (hlin F hF)
  · exact GenLocU4Fam.genLoc4_su4_of_classes hF hq (hExt F) (hQuat F) (hOut F) e

theorem weakSig2NormG4_qShape1
    (hlin : ∀ (F : Type) [Field F] [Finite F], Nat.card F % 4 = 3 →
      GenLoc4 (Matrix.SpecialLinearGroup (Fin 4) F))
    (hExt : ∀ (F : Type) [Field F] [Finite F] (p f : ℕ), GenLocU4Inner.Su4ExtStmt F p f)
    (hQuat : ∀ (F : Type) [Field F] [Finite F] (p f : ℕ), GenLocU4Inner.Su4QuatStmt F p f)
    (hOut : ∀ (F : Type) [Field F] [Finite F] (p f : ℕ), GenLocU4Fam.Su4OuterStmt F p f)
    {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J) (h : QShape1 J) : WeakSig2NormG4 J :=
  FamilyGeneric.weakSig2NormG4_of_genLoc4_qs hq (genLoc4_isSL4Model_of_classes' h hlin hExt hQuat hOut)

theorem weakSig2NormG4_puL4m
    (hExt : ∀ (F : Type) [Field F] [Finite F] (p f : ℕ), GenLocU4Inner.Su4ExtStmt F p f)
    (hQuat : ∀ (F : Type) [Field F] [Finite F] (p f : ℕ), GenLocU4Inner.Su4QuatStmt F p f)
    (hOut : ∀ (F : Type) [Field F] [Finite F] (p f : ℕ), GenLocU4Fam.Su4OuterStmt F p f)
    {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J) (h : TA7.PuL4m J) : WeakSig2NormG4 J := by
  obtain ⟨p, f, hp, hp2, -, h3, ⟨h4, hJ⟩ | ⟨h4, hJ⟩⟩ := h
  · exact FamilyGeneric.weakSig2NormG4_of_genLoc4_qs hq (genLoc4_l4_lin_of_gt_three hJ h3 h4)
  · exact FamilyGeneric.weakSig2NormG4_of_genLoc4_qs hq
      (GenLocU4Fam.genLoc4_psu4_of_classes hp hp2 h4 hJ (fun F _ _ => hExt F p f)
        (fun F _ _ => hQuat F p f) (fun F _ _ => hOut F p f))

end Classes

section Final4

theorem stage2Thm2C_of_classes
    (hlin : ∀ (F : Type) [Field F] [Finite F], Nat.card F % 4 = 3 →
      GenLoc4 (Matrix.SpecialLinearGroup (Fin 4) F))
    (hExt : ∀ (F : Type) [Field F] [Finite F] (p f : ℕ), GenLocU4Inner.Su4ExtStmt F p f)
    (hQuat : ∀ (F : Type) [Field F] [Finite F] (p f : ℕ), GenLocU4Inner.Su4QuatStmt F p f)
    (hOut : ∀ (F : Type) [Field F] [Finite F] (p f : ℕ), GenLocU4Fam.Su4OuterStmt F p f) :
    Stage2Thm2C :=
  stage2Thm2C_of_inputs_l4_s1 (fun _ _ _ hq h => weakSig2NormG4_puL4m hExt hQuat hOut hq h)
    (fun _ _ _ hq h => weakSig2NormG4_qShape1 hlin hExt hQuat hOut hq h)

end Final4

end CFSG.GH74.Generic.BProg.B2
