module

public import CFSG.GH74.E2.ComponentsShape
public import CFSG.Quasithin.EmptyFaithful.E22SUK1
public import CFSG.LargeExtraspecial.S12TriG2
public import CFSG.GH74.GLS.LU.Local.FiveSL2

public section

namespace CFSG.HardMathSupport.Foote.FamilyReduction

open CFSG Subgroup CFSG.Blueprint

variable {K : Type} [Group K]

theorem card_quotCenter_sl5 (e : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) ≃* K) :
    Nat.card (K ⧸ Subgroup.center K) = 60 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K)
  rw [CFSG.GH74.GLS.LU.Local.Five.sl2_five_card e,
    CFSG.GH74.GLS.LU.Local.Five.sl2_five_center_card e] at h
  omega

theorem isSimpleGroup_quotCenter_sl5 (e : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) ≃* K) :
    IsSimpleGroup (K ⧸ Subgroup.center K) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h4 : 4 ≤ Nat.card (ZMod 5) := by rw [Nat.card_zmod]; norm_num
  exact CFSG.Quasithin.E22S.UK1.isSimpleGroup_quotient_center_of_equiv_sl2 h4 e.symm

theorem nonempty_alt5_of_sl5 (e : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) ≃* K) :
    Nonempty ((K ⧸ Subgroup.center K) ≃* alternatingGroup (Fin 5)) := by
  have : Finite K := Finite.of_equiv _ e.toEquiv
  have := isSimpleGroup_quotCenter_sl5 e
  exact CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    (card_quotCenter_sl5 e)

theorem lieModel_psl_two_five_of_sl5
    (e : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) ≃* K) :
    LieModel (K ⧸ Subgroup.center K) .PSL 2 5 1 :=
  CFSG.GH74.E2.lieModel_psl_two_five_of_alt (nonempty_alt5_of_sl5 e)

end CFSG.HardMathSupport.Foote.FamilyReduction
