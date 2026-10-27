module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLRed
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA.MI

theorem matFieldImage_eq_one_of_card_two {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (hK : Nat.card K = 2) {H : Subgroup (GL ι K)} {R : Type} [Group R] (π : ↥H →* R)
    (hπ : Function.Surjective π) {φ : MulAut R} (hφ : φ ∈ LargeEvenMatFieldImage π) : φ = 1 := by
  obtain ⟨σ, hσ⟩ := hφ
  ext y
  obtain ⟨h, rfl⟩ := hπ y
  have hrel : ((h : GL ι K) : Matrix ι ι K) = ((h : GL ι K) : Matrix ι ι K).map σ := by
    ext i j
    exact (ringEquiv_apply_eq_of_card_two hK σ _).symm
  have := hσ h h hrel
  simpa using this

theorem false_of_order_of_eq_one {R : Type} [Group R] {f : MulAut R} {p : ℕ} (hp : p.Prime)
    (hf : f = 1) (hord : orderOf f = p) : False := by
  rw [hf, orderOf_one] at hord
  exact hp.one_lt.ne hord

theorem i2015NLOnDerived_holds : I2015NLOnDerived := by
  intro lab hlab ht p hp hp2 h3 _ Q hQ
  obtain ⟨t, r, n⟩ := lab
  dsimp only at ht
  rcases ht with rfl | rfl | rfl
  · dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hF, hfin, hK, hQ'⟩ := hQ
    refine ⟨K, hF, hfin, hK, hQ', fun _ _ f hf hord _ => ?_⟩
    exact (false_of_order_of_eq_one hp (matFieldImage_eq_one_of_card_two hK _
      (QuotientGroup.mk'_surjective _) hf) hord).elim
  · dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeG2Derived] at hQ ⊢
    obtain ⟨K, hF, hfin, hK, hQ'⟩ := hQ
    refine ⟨K, hF, hfin, hK, hQ', fun _ _ f hf hord _ => ?_⟩
    exact (false_of_order_of_eq_one hp (chevFieldImage_eq_one_of_card_two hK _ hf) hord).elim
  · have hn1 : n = 1 := hlab.2.2
    subst hn1
    dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeTwF4Inherited] at hQ ⊢
    obtain ⟨K, hF, hfin, hK, hQ'⟩ := hQ
    refine ⟨K, hF, hfin, hK, hQ', fun _ _ f hf hord _ => ?_⟩
    have hK' : Nat.card K = 2 := by simpa using hK
    exact (false_of_order_of_eq_one hp (chevFieldImage_eq_one_of_card_two hK' _ hf) hord).elim

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
