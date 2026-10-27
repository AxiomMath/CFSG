module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldD4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTriality

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration

section D4Family


@[expose] def regimeTrialityD4Field (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ q : TauCeti.PrimePower, idx.1 = .trialityD4 q ∧ 5 ≤ p ∧ p ∣ q.card ^ 6 - 1 ∧ p ∣ q.exponent

theorem crossCharFamAt_trialityD4_field : CrossCharFamAt .trialityD4 regimeTrialityD4Field := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨q, hd, hp5, hdq, hpf⟩
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨e⟩⟩ := exists_catEquiv_trialityD4 q hv
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  rw [hqc] at hdq
  have hΘ : ∃ Θ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* (K ≃+* K),
      ∀ α g δ, α = MulAut.conj g * fieldActor σ δ → Θ α = δ := by
    by_cases h2 : q.p = 2
    · have hK3' : Nat.card K = (2 ^ q.exponent) ^ 3 := by rw [← h2]; exact hK
      have hσ' : ∀ c, σ c = c ^ (2 ^ q.exponent) := by rw [← h2]; exact hσ
      obtain ⟨-, -, ⟨Θ, hΘ, -⟩, -⟩ :=
        even_triality_exact_automorphism_normal_form q.exponent_pos K hK3' σ hσ'
      exact ⟨Θ, hΘ⟩
    · obtain ⟨-, -, ⟨Θ, hΘ, -⟩, -⟩ :=
        odd_triality_exact_automorphism_normal_form q.prime_p h2 q.exponent_pos K hK σ hσ
      exact ⟨Θ, hΘ⟩
  obtain ⟨Θ, hΘ⟩ := hΘ
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hZ := exceptional_fixed_center_trivial TwistTag.D4 K σ
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  have hr : RankLE2 p (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    RankLE2.of_mulEquiv e (rankLE2_cat_trialityD4 q hv hp hp5 hpq)
  refine IsLocallyBalancedAbs.of_mulEquiv e (isLocallyBalancedAbs_of_fieldCore hp hinj
    (fun D hD hcard hin => false_of_inner_cube_of_rankLE2 hp hinj hr hD hcard hin) ?_)
  intro x hxp hxo
  have : Fact p.Prime := ⟨hp⟩
  exact fieldCoreAt_D4 q.prime_p q.exponent_pos K hK σ hσ Θ hΘ hp (by omega)
    (fun δ hδ => not_coprime_card_trialityFieldImage q.prime_p q.exponent_pos K hK σ hσ hp
      (by omega) hpf hdq δ hδ)
    (orderOf_eq_prime hxp fun h => hxo (by rw [h]; exact one_mem _)) hxo

end D4Family

end CFSG.HardMathSupport.Timmesfeld.CrossChar
