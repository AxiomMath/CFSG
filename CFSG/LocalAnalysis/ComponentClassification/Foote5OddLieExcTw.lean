module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcTools
public import CFSG.LieType.Ree.SmallReeOuterThreeKernel

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.Assembly.LowTwoRank

@[expose] def TwistedE6InnerCoreInput :
    Prop :=
  ∀ (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (p ^ f) ^ 2 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) →
      ∀ g : twistedE6RootGroup K σ, g ^ 2 = 1 → g ≠ 1 → OuterCoreAt (MulAut.conj g)

@[expose] def TwistedE6GraphCoreInput :
    Prop :=
  ∀ (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (p ^ f) ^ 2 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) →
      ∀ (g : twistedE6RootGroup K σ)
        (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ),
        (MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u *
          fieldActor (t := TwistTag.E6) σ σ) ^ 2 = 1 →
        OuterCoreAt (MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u *
          fieldActor (t := TwistTag.E6) σ σ)

theorem outerCoreAt_twistedE6
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (hinn : TwistedE6InnerCoreInput) (hgr : TwistedE6GraphCoreInput)
    (α : MulAut (twistedE6RootGroup K σ)) (hα : orderOf α = 2) : OuterCoreAt α := by
  have hα2 : α ^ 2 = 1 := sq_eq_one_of_orderOf hα
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, -, -, -, hinv⟩, -, -, hZ, -, -⟩ :=
    twisted_E6_odd_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  rcases hinv α hα2 with ⟨g, rfl⟩ | ⟨-, g, u, rfl⟩
  ·
    have hg2 : g ^ 2 = 1 := conj_injective hZ (by rw [map_pow, hα2, map_one])
    have hg1 : g ≠ 1 := by
      rintro rfl
      rw [map_one, orderOf_one] at hα
      exact absurd hα (by norm_num)
    exact hinn p f hp hp2 hf K hK σ hσ g hg2 hg1
  ·
    exact hgr p f hp hp2 hf K hK σ hσ g u hα2

theorem oddLieCoreFamilyInput_twistedE6
    (hinn : TwistedE6InnerCoreInput) (hgr : TwistedE6GraphCoreInput) :
    OddLieCoreFamilyInput .twistedE6 := by
  refine oddLieCoreFamilyInput_of_outerCoreAt fun S _ _ _ _ n p f hp hp2 _ hm i hi => ?_
  rcases hm with ⟨hcl, -⟩ | ⟨-, -, hY⟩ | ⟨-, hrt, -⟩ | ⟨-, hsz, -⟩
  · exact absurd hcl (by decide)
  · obtain ⟨⟨-, hf, -⟩, hm'⟩ := hY
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .E6 hp hf hm'
    exact outerCoreAt_of_congr e (outerCoreAt_twistedE6 hp hp2 hf hK σ hσ hinn hgr _
      ((MulEquiv.orderOf_eq (MulAut.congr e) i).trans hi))
  · exact absurd hrt (by decide)
  · exact absurd hsz (by decide)

@[expose] def SmallReeInnerCoreInput :
    Prop :=
  ∀ (a : ℕ), 1 ≤ a → ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.G2.prime],
    Nat.card K = 3 ^ (2 * a + 1) → ∀ t : ReeTag.G2.reeGamma K a, t ^ 2 = 1 → t ≠ 1 →
      OuterCoreAt (MulAut.conj t)

theorem exists_conj_eq_of_smallRee
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]
    (hK : Nat.card K = 3 ^ (2 * a + 1)) {i : MulAut (ReeTag.G2.reeGamma K a)}
    (hi : orderOf i = 2) : ∃ t : ReeTag.G2.reeGamma K a, t ^ 2 = 1 ∧ t ≠ 1 ∧ MulAut.conj t = i := by
  obtain ⟨-, -, -, -, hoddO, -⟩ := small_Ree_outer_three_kernel_field_complement a ha K hK
  have hZ := (small_Ree_fixed_group_center_trivial a K hK).1
  have h1 : orderOf (QuotientGroup.mk' (OuterAutomorphisms.inner (ReeTag.G2.reeGamma K a)) i) =
      1 := by
    have h2 : orderOf (QuotientGroup.mk' (OuterAutomorphisms.inner (ReeTag.G2.reeGamma K a)) i) ∣
        2 := by
      rw [← hi]
      exact orderOf_map_dvd _ i
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact h
    · exfalso
      have h3 := orderOf_dvd_natCard
        (QuotientGroup.mk' (OuterAutomorphisms.inner (ReeTag.G2.reeGamma K a)) i)
      rw [h] at h3
      exact (Nat.not_even_iff_odd.2 hoddO) (even_iff_two_dvd.2 h3)
  have hin : i ∈ OuterAutomorphisms.inner (ReeTag.G2.reeGamma K a) := by
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  obtain ⟨t, rfl⟩ := hin
  refine ⟨t, conj_injective hZ ?_, ?_, rfl⟩
  · rw [map_pow, map_one, ← hi, pow_orderOf_eq_one]
  · rintro rfl
    rw [map_one, orderOf_one] at hi
    exact absurd hi (by norm_num)

theorem oddLieCoreFamilyInput_twistedG2
    (hinn : SmallReeInnerCoreInput) : OddLieCoreFamilyInput .twistedG2 := by
  refine oddLieCoreFamilyInput_of_outerCoreAt fun S _ _ _ _ n p f hp hp2 _ hm i hi => ?_
  rcases hm with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, -, hY⟩ | ⟨-, hsz, -⟩
  · exact absurd hcl (by decide)
  · exact absurd hce (by decide)
  · obtain ⟨-, -, rfl, ⟨a, ha, hfa⟩, hiso⟩ := small_Ree_model_Schreier S p f hY
    obtain ⟨-, a', hfa', K, _, _, hK, hw⟩ := hY
    have ha' : a' = a := by omega
    subst ha'
    have : CharP K ReeTag.G2.prime :=
      LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
        (by omega) hK
    obtain ⟨E⟩ := hiso a' K hfa hK hw
    have hK' : Nat.card K = 3 ^ (2 * a' + 1) := by rw [hK, hfa]
    obtain ⟨t, ht2, ht1, hti⟩ := exists_conj_eq_of_smallRee ha hK'
      ((MulEquiv.orderOf_eq (MulAut.congr E) i).trans hi)
    refine outerCoreAt_of_congr E ?_
    rw [← hti]
    exact hinn a' ha K hK' t ht2 ht1
  · exact absurd hsz (by decide)

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
