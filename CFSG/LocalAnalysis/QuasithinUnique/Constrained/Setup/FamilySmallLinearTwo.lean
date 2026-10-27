module

public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.LocalAnalysis.ComponentInitial.CertSmallLinear
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG CFSG.GorensteinWalter CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

theorem SL_two_four_equiv_alternating_five
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) K ≃* alternatingGroup (Fin 5)) := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have hcenter : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
    rw [eq_bot_iff]
    intro A hA
    obtain ⟨r, hr, hAr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
    rw [Subgroup.mem_bot]
    have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
    have hr2 : r ^ 2 = 1 := by simpa using hr
    have hr1 : r = 1 := by
      have h3 : (r - 1) ^ 2 = 0 := by linear_combination hr2 - (r - 1) * h2
      exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h3)
    rw [hr1, map_one] at hAr
    exact Subtype.ext hAr.symm
  obtain ⟨e⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K (Or.inl hK)
  let e1 : Matrix.SpecialLinearGroup (Fin 2) K ≃* PSL2 K :=
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).symm
  exact ⟨e1.trans (((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).trans
    e))⟩

end CFSG.QuasithinUnique.Setup.Family
