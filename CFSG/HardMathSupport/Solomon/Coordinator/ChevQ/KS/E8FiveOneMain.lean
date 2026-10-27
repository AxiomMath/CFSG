module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveOneHeisC
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveToral

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8Five

namespace One

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Twist

set_option linter.unusedSectionVars false

section Main

theorem exists_primitiveRoot_five (K : Type) [Field K] [Finite K] (h5 : 5 ∣ Nat.card K - 1) :
    ∃ ζ : K, IsPrimitiveRoot ζ 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hdvd : 5 ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    exact h5
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 5 hdvd
  exact ⟨(ω : K), IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hω)⟩

theorem exists_conj_cube_cases (hH : HeisReduction) (K : Type) [Field K] [Finite K]
    (h5 : 5 ∣ Nat.card K - 1) {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    (E₀ : Subgroup (adjointGroup Tag.E8 K)) (hE₀ : CFSG.Open.IsElemAbelian 5 E₀)
    (hc : Nat.card E₀ = 5 ^ 3) :
    NormalizesRGroup (ringChar K) E₀ ∨
      ∃ (a : Fin Tag.E8.rank → Kˣ) (g : adjointGroup Tag.E8 K),
        E₀ = cj g (griessCubeT hζ a) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hQ : IsPGroup 5 E₀ := IsPGroup.of_card (n := 3) hc
  obtain ⟨c, hcN, hcW⟩ := exists_conj_monomialN_weyl_le K h5 hQ
  set E₁ := cj c E₀ with hE₁
  have hE₁N : E₁ ≤ monomialN K := fun x hx => by
    obtain ⟨e, he, rfl⟩ := hx
    exact hcN e he
  have hE₁S : wImg K E₁ ≤ sylowW := by
    intro w hw
    obtain ⟨x, hx, hxN, rfl⟩ := mem_wImg.1 hw
    obtain ⟨e, he, rfl⟩ := hx
    have := hcW e he
    exact this
  have hE₁a : CFSG.Open.IsElemAbelian 5 E₁ := isElemAbelian_cj hE₀ c
  have hE₁c : Nat.card E₁ = 5 ^ 3 := by rw [hE₁, card_cj]; exact hc
  have hback : ∀ (E₂ : Subgroup (adjointGroup Tag.E8 K)) (g : adjointGroup Tag.E8 K),
      E₂ = cj g E₁ →
      (NormalizesRGroup (ringChar K) E₂ ∨ ∃ (a : Fin Tag.E8.rank → Kˣ) (g' : adjointGroup Tag.E8 K),
        E₂ = cj g' (griessCubeT hζ a)) →
      NormalizesRGroup (ringChar K) E₀ ∨ ∃ (a : Fin Tag.E8.rank → Kˣ) (g' : adjointGroup Tag.E8 K),
        E₀ = cj g' (griessCubeT hζ a) := by
    intro E₂ g hE₂ h
    rcases h with h | ⟨a, g', hg'⟩
    · left
      apply normalizesRGroup_of_conj (ringChar K) E₀ (g * c)
      rw [hE₂, hE₁, cj_cj] at h
      exact h
    · right
      refine ⟨a, (g * c)⁻¹ * g', ?_⟩
      have h2 : E₂ = cj (g * c) E₀ := by rw [hE₂, hE₁, cj_cj]
      rw [← cj_cj, ← hg', h2, cj_inv_cj]
  by_cases hle : Nat.card (wImg K E₁) ≤ 5
  · exact hback E₁ 1 (by rw [cj_one]) (cyclic_cases hζ hE₁a hE₁c hE₁N hE₁S hle)
  · have hdvd : Nat.card (wImg K E₁) ∣ 25 := by
      rw [← card_sylowW]
      exact Subgroup.card_dvd_of_le hE₁S
    have hcard25 : Nat.card (wImg K E₁) = 25 := by
      have h := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases hc' : Nat.card (wImg K E₁) <;> simp_all
    have hW : wImg K E₁ = sylowW :=
      Subgroup.eq_of_le_of_card_ge hE₁S (by rw [hcard25, card_sylowW])
    obtain ⟨c', hc'N, hc'S, hc'c⟩ := hH K h5 hζ E₁ hE₁a hE₁c hE₁N hW
    exact hback (cj c' E₁) c' rfl (cyclic_cases hζ (isElemAbelian_cj hE₁a c')
      (by rw [card_cj]; exact hE₁c) hc'N hc'S hc'c)

theorem five_dvd_sub_one_of_orderOf_eq_one {K : Type} [Field K] [Finite K]
    (he : orderOf ((Nat.card K : ℕ) : ZMod 5) = 1) : 5 ∣ Nat.card K - 1 := by
  have hq : ((Nat.card K : ℕ) : ZMod 5) = 1 := orderOf_eq_one_iff.1 he
  have h1 : 1 ≤ Nat.card K := Nat.card_pos
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1, hq, Nat.cast_one, sub_self]

theorem e8OneFiveNonToralGriess_of_heis (hH : HeisReduction) : E8OneFiveNonToralGriess := by
  intro K _ _ he E₀ hE₀ hc _ hN
  have h5 := five_dvd_sub_one_of_orderOf_eq_one he
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_five K h5
  rcases exists_conj_cube_cases hH K h5 hζ E₀ hE₀ hc with h | ⟨a, g, hg⟩
  · exact absurd h hN
  · exact ⟨ζ, hζ, a, g, hg⟩

end Main

end One

section Final

theorem e8OneFiveNonToralGriess_holds : E8OneFiveNonToralGriess :=
  One.e8OneFiveNonToralGriess_of_heis One.heisReduction_holds

end Final

end KSE8Five

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
