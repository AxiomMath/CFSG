module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockSylowThreeAutCore
public import CFSG.LocalAnalysis.AGLEmbedding.BlockOutNine
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviFam
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviSULift
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits

@[expose] def SuOddThreeDvdStatement (hGA : CFSG.Open.GriessAllModelsStatement) : Prop :=
  ∀ {Y₁ X : Type} [Group Y₁] [Finite Y₁] [Group X], Group.IsPerfect Y₁ →
    ∀ (ρ₁ : Y₁ →* X), Function.Surjective ρ₁ → ρ₁.ker ≤ Subgroup.center Y₁ →
      IsPGroup 3 ρ₁.ker → Subgroup.center X = ⊥ → ∀ {n : ℕ},
      StatedClassicalModel X .PSU n 2 1 → ¬ Even n →
      Nat.card X = CFSG.Open.ordTwistedA (n - 1) (2 ^ 1) →
      ∀ (T₁ : Sylow 2 Y₁) (J₁ : Subgroup Y₁),
        Subgroup.normalizer ((T₁ : Subgroup Y₁) : Set Y₁) ≤ J₁ →
        J₁ ≠ Subgroup.normalizer ((T₁ : Subgroup Y₁) : Set Y₁) →
        (∀ U : Subgroup Y₁, U ≤ J₁ → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) →
        3 ∣ J₁.index

theorem threeSubgroups_of_model_two (hGA : CFSG.Open.GriessAllModelsStatement)
    (hExc : SuOddThreeDvdStatement hGA) {Y₁ X : Type} [Group Y₁] [Finite Y₁] [Group X]
    (hY₁ : Group.IsPerfect Y₁) (ρ₁ : Y₁ →* X) (hρ₁ : Function.Surjective ρ₁)
    (hk : ρ₁.ker ≤ Subgroup.center Y₁) (h3 : IsPGroup 3 ρ₁.ker) (hX : Subgroup.center X = ⊥)
    {t : StatedLieTag} {n : ℕ} (hc : StatedClassicalModel X t n 2 1)
    (ht : t = .PSL ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .PSU)
    (hcard : t = .PSU → Nat.card X = CFSG.Open.ordTwistedA (n - 1) (2 ^ 1))
    (T₁ : Sylow 2 Y₁) (J₁ : Subgroup Y₁)
    (hNJ : Subgroup.normalizer ((T₁ : Subgroup Y₁) : Set Y₁) ≤ J₁)
    (hJ : J₁ ≠ Subgroup.normalizer ((T₁ : Subgroup Y₁) : Set Y₁))
    (hperf : ∀ U : Subgroup Y₁, U ≤ J₁ → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) :
    (∀ U : Subgroup Y₁, U ≤ J₁ → IsPGroup 3 U → IsElemAbelian 3 U) ∨ 3 ∣ J₁.index := by
  have : Finite X := Finite.of_surjective ρ₁ hρ₁
  obtain ⟨hTb, hNb, hJb, hperfb⟩ := map_overgroup_of_central hρ₁ hk T₁ hNJ hJ hperf
  obtain ⟨Tb, hTb'⟩ := exists_sylow_of_isSylowTwoOf_top hTb
  rw [← hTb'] at hNb hJb
  have hiso : t ≠ .PSU → ∀ U : Subgroup Y₁, U ≤ J₁ → IsPGroup 3 U → IsElemAbelian 3 U :=
    fun htu => by
    have ht' : t = .PSL ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus := by
      rcases ht with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      · exact absurd h htu
    have hb := ker_eq_bot_of_coprime_hopfMultiplier hY₁ ρ₁ hρ₁ hk h3
      (coprime_three_card_hopfMultiplier_of_model_two hGA hc ht')
    refine isElemAbelian_of_map (ρ := ρ₁) (by rw [hb, Subgroup.card_bot]; norm_num) ?_
    rcases ht' with rfl | rfl | rfl | rfl
    · exact isElemAbelian_of_model_psl_two hc Tb _ hNb hJb hperfb
    · exact isElemAbelian_of_model_psp_two hc Tb _ hNb hJb hperfb
    · exact isElemAbelian_of_model_pomegaPlus_two hc Tb _ hNb hJb hperfb
    · exact isElemAbelian_of_model_pomegaMinus_two hc Tb _ hNb hJb hperfb
  by_cases htu : t = .PSU
  · subst htu
    obtain ⟨⟨-, -, hn, hne⟩, F, hF, hFfin, hcardF, ⟨e⟩⟩ := id hc
    have := Fintype.ofFinite F
    have : CharP F 2 := charP_of_card_eq_prime_pow (f := 1 * 2)
      (by rw [← Nat.card_eq_fintype_card, hcardF, pow_mul])
    have hn4 : 4 ≤ n := by
      by_contra h4
      exact hne (by rw [show n = 3 by omega]; rfl)
    obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hcardF
    have hB := borelQuotient_su hcardF (by omega) ζ hζ e
    obtain ⟨α, hα, hαker⟩ := exists_lift_su hGA hcardF hn4 hc hX _ hB.surj
      (fun z hz => hB.ker_central z hz) hY₁ ρ₁ hρ₁ hk h3
    by_cases he : Even n
    · exact Or.inl (isElemAbelian_of_su_even hcardF hn4 he α hα hαker T₁ J₁ hNJ hJ hperf)
    · exact Or.inr (hExc hY₁ ρ₁ hρ₁ hk h3 hX hc he (hcard rfl) T₁ J₁ hNJ hJ hperf)
  · exact Or.inl (hiso htu)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
