module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.LieType.SeitzGeneration.ExcTwistedClasses
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Three
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

section Outer


theorem exists_hom_ringAut_twistedE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    ∃ Θ : MulAut (twistedE6RootGroup K σ) →* RingAut K, ∀ x ∈ Θ.ker, x ^ p = 1 →
      x ∈ (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)).range := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, hcube, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  refine ⟨Θ, fun x hx hxp => ?_⟩
  rw [hker] at hx
  set J := twistedE6Inn K σ ⊔ twistedE6Diag K σ with hJ
  have hcop : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)
  have hxp' : (⟨x, hx⟩ : J) ^ p = 1 := Subtype.ext (by simpa using hxp)
  have ha : (QuotientGroup.mk ⟨x, hx⟩ : J ⧸ (twistedE6Inn K σ).subgroupOf J) = 1 :=
    (pow_eq_one_iff_of_coprime hcop).1
      ⟨hcube _, by rw [← QuotientGroup.mk_pow, hxp', QuotientGroup.mk_one]⟩
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 ha)

end Outer

section Cat


theorem crossCharFamAt_twistedE6 :
    CrossCharFamAt .twistedE6 (regimeExc TauCeti.LieTypeIndex.twistedE6 degCountTw) := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨q, hd, hcnt⟩
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hp5 := five_le_of_count_le (k := 1) (a := degCountTw) (by decide) hp hp2
    (not_dvd_card_of_ne hp hpq) hcnt
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero 2 (pow_ne_zero _ q.prime_p.ne_zero))
  obtain ⟨Θ, hΘ⟩ := exists_hom_ringAut_twistedE6 q.prime_p q.exponent_pos K hK σ hσ hp
    (by omega)
  have : IsCyclic (RingAut K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  exact isLocallyBalancedAbs_of_rankLE1 e Θ hp hΘ (conj_injective_cat_twistedE6 q hv)
    (rankLE1_cat_twistedE6 q hv hp hpq hcnt)

theorem rankLE2_cat_twistedE6 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) {p : ℕ} (hp : p.Prime)
    (hcnt : degCountTw (orderOf ((q.card : ℕ) : ZMod p)) = 2) :
    RankLE2 p (Cat ⟨.twistedE6 q, hv⟩) := by
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  rw [TauCeti.PrimePower.card_def] at hcnt
  obtain ⟨n, hn⟩ : ∃ n, orderOf (((q.p ^ q.exponent : ℕ)) : ZMod p) = n := ⟨_, rfl⟩
  rw [hn] at hcnt
  refine RankLE2.of_mulEquiv e.symm ?_
  rcases degCountTw_eq_two hcnt with rfl | rfl
  · exact (sylowTorus_twistedE6_three q.prime_p q.exponent_pos K hK σ hσ hp hn).rankLE2 hp le_rfl
  · exact (sylowTorus_twistedE6_four q.prime_p q.exponent_pos K hK σ hσ hp hn).rankLE2 hp le_rfl

theorem crossCharFamAt_twistedE6_inner :
    CrossCharFamAt .twistedE6 (regimeExcInner TauCeti.LieTypeIndex.twistedE6 degCountTw) := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨q, hd, hcnt, hf⟩
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hp5 := five_le_of_count_le (k := 2) (a := degCountTw) (by decide) hp hp2
    (not_dvd_card_of_ne hp hpq) hcnt.le
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero 2 (pow_ne_zero _ q.prime_p.ne_zero))
  obtain ⟨Θ, hΘ⟩ := exists_hom_ringAut_twistedE6 q.prime_p q.exponent_pos K hK σ hσ hp
    (by omega)
  have hK2 : Nat.card K = q.p ^ (q.exponent * 2) := by rw [hK, ← pow_mul]
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      q.prime_p (by have := q.exponent_pos; omega) hK2
  have hcop : Nat.Coprime p (Nat.card (RingAut K)) := by
    rw [hcard]
    exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hp).2 hf)
      (Nat.coprime_two_right.2 (hp.odd_of_ne_two hp2))
  exact isLocallyBalancedAbs_of_rankLE2 e Θ hp hcop hΘ (conj_injective_cat_twistedE6 q hv)
    (rankLE2_cat_twistedE6 q hv hp hcnt)

theorem crossCharFamAt_twistedE6_vac :
    CrossCharFamAt .twistedE6 (regimeExcVac TauCeti.LieTypeIndex.twistedE6 degCountTw) :=
  crossCharFamAt_twistedE6.or crossCharFamAt_twistedE6_inner

end Cat

end CFSG.HardMathSupport.Timmesfeld.CrossChar
