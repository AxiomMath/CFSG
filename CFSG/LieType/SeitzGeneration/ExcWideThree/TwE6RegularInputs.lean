module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagTwisted
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Diag

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Open
  CFSG.AGLEmbeddingD2 CFSG.Fischer TauCeti CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Pure

theorem mem_fixUnion_of_fixed {G : Type*} [Group G] {E : Subgroup (MulAut G)} {y : MulAut G}
    (hy : y ∈ E) (hy1 : y ≠ 1) {g : G} (hg : y g = g) : g ∈ fixUnion E :=
  ⟨Subgroup.zpowers y, Subgroup.zpowers_le.2 hy, mt Subgroup.zpowers_eq_bot.1 hy1,
    fun φ hφ => (Subgroup.zpowers_le.2 (mem_fixAut.2 hg)) hφ⟩

theorem twE6_exists_pow_ringChar_of_card_sq (K : Type) [Field K] [Finite K] (q : ℕ)
    (hK : Nat.card K = q ^ 2) (hq : 2 ≤ q) :
    Nat.Prime (ringChar K) ∧ ∃ f : ℕ, 1 ≤ f ∧ q = ringChar K ^ f := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
  have hdvd : q ∣ ringChar K ^ (n : ℕ) := by
    rw [← hcard, ← Nat.card_eq_fintype_card, hK]
    exact dvd_pow_self q two_ne_zero
  obtain ⟨m, -, hqm⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  refine ⟨hp, m, ?_, hqm⟩
  by_contra h0
  have hm0 : m = 0 := by omega
  rw [hm0, pow_zero] at hqm
  omega

end Pure

section Twisted

@[expose] def TwLangData.Kills {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (D : TwLangData K σ q A)
    (α : Fin TwistTag.E6.tag.rank → ℤ) : Prop :=
  ∀ x ∈ A, ∃ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
    rootDiagUnit TwistTag.E6.tag a = D.g0⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K))
        (D.c * x * D.c⁻¹ : ModGL TwistTag.E6.tag K) * D.g0 ∧ rootChar a α = 1

@[expose] def TwLangData.IsRegular {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (D : TwLangData K σ q A) : Prop :=
  ¬ ∃ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α ∧ D.Kills α

theorem three_dvd_of_not_le_innerAut (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (hσ : ∀ c, σ c = c ^ q) (hK : Nat.card K = q ^ 2)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ)))
    (hE : E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ) (hnin : ¬ E ≤ innerAut (twistedE6RootGroup K σ)) :
    3 ∣ q + 1 := by
  by_contra h3
  have hg : Nat.gcd 3 (q + 1) = 1 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  have hΔ : twistedE6Diag K σ ≤ twistedE6Inn K σ := by
    rintro _ ⟨u, rfl⟩
    exact CFSG.HardMathSupport.Lang.Coordinator.compatDiagAutHom_mem_inner hK hσ hg u
  rw [sup_eq_left.2 hΔ] at hE
  exact hnin hE

end Twisted

end CFSG.LieType.SeitzGeneration.ExcWideThree
