module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Crit
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.GH74.Generic.Context

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GorensteinWalter

theorem ivk93m12_card_aut_psl2 {K : Type} [Field K] [Finite K] :
    Nat.card (MulAut (PSL2 K)) = Nat.card K * (Nat.card K ^ 2 - 1) * Nat.card (K ≃+* K) := by
  rw [← Nat.card_congr
      (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearEquivAut K).toEquiv,
    Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, pgl2_card_formula K]

theorem ivk93m12_l28 : Ivk93M12Empty (fun X _ => LieModel X .PSL 2 2 3) := by
  intro J _ _ hJ y D
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSL hJ
  let e' : J ≃* PSL2 F := e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  have hAutF : Nat.card (F ≃+* F) = 3 := by
    obtain ⟨-, -, -, -, h, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        Nat.prime_two (n := 3) (by norm_num) hF
    exact h
  have hAut : Nat.card (MulAut J) = 1512 := by
    rw [Nat.card_congr (MulAut.congr e').toEquiv, ivk93m12_card_aut_psl2, hAutF, hF]
    norm_num
  exact D.false_of_card_aut (by rw [hAut]; norm_num)

end CFSG.GH74.GLS.IVK.Proofs2
