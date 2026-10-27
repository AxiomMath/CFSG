module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.ExcFiveToralAux.SylowFrame
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveTw

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.TauCetiBridge
  CFSG.HardMathSupport.Timmesfeld.DefChar Polynomial
open scoped Matrix

set_option linter.unusedSectionVars false

section Orders


theorem innerPlaneBalance_adjointE6_five_of_dvd_add_one
    (hres : LangTorusPlaneBalance Tag.E6 e6PhiTwoWeyl 5 fun q => 5 ∣ q + 1)
    (K : Type) [Field K] [Finite K] (h5 : 5 ∣ Nat.card K + 1) :
    InnerPlaneBalance 5 (adjointGroup Tag.E6 K) := by
  obtain ⟨Fr, hFr, g0, hg0C, hg0, hconj⟩ :=
    exists_langFrame_untwisted_sylow 3 (Or.inl ⟨rfl, rfl⟩) K Nat.prime_five (by norm_num)
      e6PhiTwoWeyl (wordProd_smul_eq_wordMat_mulVec Tag.E6 e6TwoWord) (n := 2) (by norm_num)
      e6Two_pow (charpoly_eval_ne_zero_of_blocks Finite.one_lt_card _ e6Two_charpoly)
      (factorization_card_adjointE6_eq_of_dvd_add_one K h5).le
  exact innerPlaneBalance_of_conj_sylow Nat.prime_five
    (mulAut_conj_injective_adjointGroup (τ := Tag.E6) (K := K)) _ hconj
    fun D₁ hpow₁ hcard₁ hP₁ H hH => hres K h5 Fr hFr g0 hg0C hg0 D₁ hpow₁ hcard₁ hP₁ H hH

theorem innerPlaneBalance_twistedE6_five_of_dvd_sub_one
    (hres : TwistedE6LangTorusPlaneBalance twE6PhiOneWeyl 5 fun q => 5 ∣ q - 1) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (h5 : 5 ∣ ℓ ^ f - 1) :
    InnerPlaneBalance 5 (twistedE6RootGroup K σ) := by
  obtain ⟨Fr, hFr, g0, hg0C, hg0, hconj⟩ :=
    exists_langFrame_twistedE6_sylow hℓ hf K hK σ hσ Nat.prime_five (by norm_num)
      twE6PhiOneWeyl twE6PhiOneWeyl_smul (n := 2) (by norm_num) twE6One_pow
      (charpoly_eval_ne_zero_of_blocks (Nat.one_lt_pow (by omega) hℓ.one_lt) _ twE6One_charpoly)
      (factorization_card_twistedE6_eq_of_dvd_sub_one hℓ hf K hK σ hσ h5).le
  exact innerPlaneBalance_of_conj_sylow Nat.prime_five
    (CFSG.LieType.Chevalley.mulAut_conj_injective_of_center_eq_bot
      (CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot σ.surjective)) _ hconj
    fun D₁ hpow₁ hcard₁ hP₁ H hH =>
      hres ℓ f hℓ hf h5 K hK σ hσ Fr hFr g0 hg0C hg0 D₁ hpow₁ hcard₁ hP₁ H hH

end Orders

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
