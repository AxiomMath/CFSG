module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeSylowDefs
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviFam
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviSmall
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviSUOdd
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge

public section

namespace CFSG.AGLEmbedding

open CFSG.QuasithinUnique CFSG.AGLEmbedding.ParabHub CFSG.Assembly.LowTwoRank
  CFSG.RankThreeCoreUniqueness.Helpers CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

theorem exists_model_of_indexTwo {X : Type} [Group X] (d : TauCeti.ValidLieTypeIndex)
    (hd : IsClassicalOrG2IndexTwo d.1) (e : X ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ∃ (t : StatedLieTag) (n : ℕ),
      (t = .PSL ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .PSU) ∧
        StatedClassicalModel X t n 2 1 := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q =>
    change q.card = 2 at hd
    obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_two hd
    have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    rw [hp, hf] at h
    exact ⟨_, _, Or.inl rfl, h⟩
  | twistedA r q =>
    change q.card = 2 at hd
    obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_two hd
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    rw [hp, hf] at h
    exact ⟨_, _, Or.inr (Or.inr (Or.inr (Or.inr rfl))), h⟩
  | B r q =>
    change q.card = 2 at hd
    obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_two hd
    have hr := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    by_cases h2 : r = 2
    · subst h2
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
      rw [hp, hf] at h
      exact ⟨_, _, Or.inr (Or.inl rfl), h⟩
    · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp
        (by omega) e
      rw [hp, hf] at h
      exact ⟨_, _, Or.inr (Or.inl rfl), h⟩
  | C r q => exact hd.elim
  | D r q =>
    change q.card = 2 at hd
    obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_two hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hp e
    rw [hp, hf] at h
    exact ⟨_, _, Or.inr (Or.inr (Or.inl rfl)), h⟩
  | twistedD r q =>
    change q.card = 2 at hd
    obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_two hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hp e
    rw [hp, hf] at h
    exact ⟨_, _, Or.inr (Or.inr (Or.inr (Or.inl rfl))), h⟩
  | G2 q =>
    change q.card = 2 at hd
    have hq3 : 3 ≤ q.card :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    omega
  | _ => exact hd.elim

theorem threeDichotomy_of_model_two (hGA : CFSG.Open.GriessAllModelsStatement) {Y₁ X : Type}
    [Group Y₁] [Finite Y₁] [Group X] (hY₁ : Group.IsPerfect Y₁) (ρ₁ : Y₁ →* X)
    (hρ₁ : Function.Surjective ρ₁) (hk : ρ₁.ker ≤ Subgroup.center Y₁) (h3 : IsPGroup 3 ρ₁.ker)
    (hX : Subgroup.center X = ⊥)
    {t : StatedLieTag} {n : ℕ} (hc : StatedClassicalModel X t n 2 1)
    (ht : t = .PSL ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .PSU)
    (T₁ : Sylow 2 Y₁) (J₁ : Subgroup Y₁)
    (hNJ : Subgroup.normalizer ((T₁ : Subgroup Y₁) : Set Y₁) ≤ J₁)
    (hJ : J₁ ≠ Subgroup.normalizer ((T₁ : Subgroup Y₁) : Set Y₁))
    (hperf : ∀ U : Subgroup Y₁, U ≤ J₁ → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) :
    ThreeDichotomy J₁ := by
  have : Finite X := Finite.of_surjective ρ₁ hρ₁
  obtain ⟨hTb, hNb, hJb, hperfb⟩ := map_overgroup_of_central hρ₁ hk T₁ hNJ hJ hperf
  obtain ⟨Tb, hTb'⟩ := exists_sylow_of_isSylowTwoOf_top hTb
  rw [← hTb'] at hNb hJb
  have hiso : t ≠ .PSU → ThreeDichotomy J₁ := fun htu => by
    have ht' : t = .PSL ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus := by
      rcases ht with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      · exact absurd h htu
    have hb := ker_eq_bot_of_coprime_hopfMultiplier hY₁ ρ₁ hρ₁ hk h3
      (coprime_three_card_hopfMultiplier_of_model_two hGA hc ht')
    refine ThreeDichotomy.of_map hρ₁ (hb ▸ bot_le) (by rw [hb, Subgroup.card_bot]; norm_num)
      (Or.inl ?_)
    rcases ht' with rfl | rfl | rfl | rfl
    · exact isElemAbelian_of_model_psl_two hc Tb _ hNb hJb hperfb
    · exact isElemAbelian_of_model_psp_two hc Tb _ hNb hJb hperfb
    · exact isElemAbelian_of_model_pomegaPlus_two hc Tb _ hNb hJb hperfb
    · exact isElemAbelian_of_model_pomegaMinus_two hc Tb _ hNb hJb hperfb
  by_cases htu : t = .PSU
  · subst htu
    obtain ⟨⟨-, -, hn, hne⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := id hc
    have := Fintype.ofFinite F
    have : CharP F 2 := charP_of_card_eq_prime_pow (f := 1 * 2)
      (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
    have hn4 : 4 ≤ n := by
      by_contra h4
      exact hne (by rw [show n = 3 by omega]; rfl)
    obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hcard
    have hB := borelQuotient_su hcard (by omega) ζ hζ e
    obtain ⟨α, hα, hαker⟩ := exists_lift_su hGA hcard hn4 hc hX _ hB.surj
      (fun z hz => hB.ker_central z hz) hY₁ ρ₁ hρ₁ hk h3
    by_cases he : Even n
    · exact Or.inl (isElemAbelian_of_su_even hcard hn4 he α hα hαker T₁ J₁ hNJ hJ hperf)
    · exact threeDichotomy_of_su_odd hcard (by
        rcases Nat.even_or_odd n with h | h
        · exact absurd h he
        · obtain ⟨k, rfl⟩ := h
          omega) he α hα hαker T₁ J₁ hNJ hJ hperf
  · exact hiso htu


theorem kFactParabolicThreeSylowSmall_of (hGA : CFSG.Open.GriessAllModelsStatement) :
    KFactParabolicThreeSylowSmall := by
  intro Y _ _ hY hcl T J hT hNJ hJ hperf
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, rfl⟩ := exists_sylow_of_isSylowTwoOf_top hT
  refine ThreeDichotomy.clauses ?_
  have : Group.IsPerfect Y := ⟨hY.1⟩
  set O : Subgroup Y := primeComplementCore (G := Y) 3 with hOdef
  rcases le_center_or_eq_top_of_normal_quasisimple hY O with hO | hO
  · have hρ₀ : Function.Surjective (QuotientGroup.mk' O) := QuotientGroup.mk'_surjective O
    have hker₀ : (QuotientGroup.mk' O).ker = O := QuotientGroup.ker_mk' O
    refine ThreeDichotomy.of_map hρ₀ ?_ (by rw [hker₀]; exact primeComplementCore_coprime 3) ?_
    · rw [hker₀]
      exact hO.trans ((Subgroup.center_le_normalizer _).trans hNJ)
    obtain ⟨hT₁, hN₁, hJ₁, hperf₁⟩ :=
      map_overgroup_of_central hρ₀ (hker₀.le.trans hO) S hNJ hJ hperf
    obtain ⟨S₁, hS₁⟩ := exists_sylow_of_isSylowTwoOf_top hT₁
    rw [← hS₁] at hN₁ hJ₁
    have hY₁ : Group.IsPerfect (Y ⧸ O) := Group.IsPerfect.ofSurjective hρ₀
    have hX := center_centerQuotient_eq_bot hY
    obtain ⟨hTb, hNb, hJb, hperfb⟩ := map_overgroup_of_central
      (QuotientGroup.mk'_surjective (Subgroup.center Y)) (QuotientGroup.ker_mk' _).le S hNJ hJ
      hperf
    rcases kFactParabolicThreeCensus _ hcl _ _ hTb hNb hJb hperfb with ⟨d, hd, ⟨e⟩⟩ | hsmall
    · obtain ⟨t, n, ht, hc⟩ := exists_model_of_indexTwo d hd e
      exact threeDichotomy_of_model_two hGA hY₁ _ (quotCenterOfLeCenter_surjective hO)
        (ker_quotCenterOfLeCenter_le_center hO) (isPGroup_ker_quotCenterOfLeCenter hO) hX hc ht S₁ _
        hN₁ hJ₁ hperf₁
    · exact threeDichotomy_of_small hGA hY₁ _ (quotCenterOfLeCenter_surjective hO)
        (ker_quotCenterOfLeCenter_le_center hO) (isPGroup_ker_quotCenterOfLeCenter hO) hX hsmall
        S₁ _ hN₁ hJ₁ hperf₁
  · left
    intro U _ hU
    refine isElemAbelian_of_card_dvd_three ?_
    have hcop : Nat.Coprime 3 (Nat.card (⊤ : Subgroup Y)) := hO ▸ primeComplementCore_coprime 3
    obtain ⟨k, hk⟩ := hU.exists_card_eq
    have hdvd : Nat.card U ∣ Nat.card (⊤ : Subgroup Y) := Subgroup.card_dvd_of_le le_top
    rw [hk] at hdvd ⊢
    rcases k with _ | k
    · norm_num
    · exact absurd ((dvd_pow_self 3 (Nat.succ_ne_zero k)).trans hdvd)
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop)

section Final


theorem kFactParabolicThreeSylowSmall : KFactParabolicThreeSylowSmall :=
  kFactParabolicThreeSylowSmall_of
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds

end Final

end CFSG.AGLEmbedding
