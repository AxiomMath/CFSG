module

public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.RankThree.Chevalley.SteinbergCDTrialityTwelveLocalCore
public import CFSG.RankThree.PartOne.CTP.SeitzMaxAbstract

public noncomputable section

namespace CFSG.HardMathSupport.Lang.Coordinator

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.SteinbergBT
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def OuterFixedOrderTrialityThree : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (n ℓ f : ℕ),
    StatedLieAdmissible .trialityD4 n ℓ f → CFSG.Blueprint.LieModel K .trialityD4 n ℓ f →
    ∀ α : MulAut K, α ^ 3 = 1 → α ∉ inner K →
      (∃ f₀ : ℕ, f = 3 * f₀ ∧
        Nat.card (fixedSubgroup α) ∣ lieOrderNumerator .trialityD4 n (ℓ ^ f₀)) ∨
      Nat.card (fixedSubgroup α) ∣ lieOrderNumerator .G2 0 (ℓ ^ f)

section


theorem trialityD4_outer_fixed_order {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hp : p.Prime)
    (hp5 : 5 ≤ p) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hαp : α ^ p = 1)
    (hαin : α ∉ inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    ∃ f₀ : ℕ, f = p * f₀ ∧
      Nat.card (fixedSubgroup α) ∣ lieOrderNumerator .trialityD4 0 (ℓ ^ f₀) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hα1 : α ≠ 1 := fun h => hαin (h ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
  have hαord : orderOf α = p := orderOf_eq_prime hαp hα1
  obtain ⟨-, hcyc, Θ, hΘ, -⟩ := triality_normal_form_data hℓ hf K hK σ hσ
  obtain ⟨hηord, hpf, ⟨h₀, hh₀⟩, -⟩ :=
    triality_noninner_large_prime_field_descent_and_local_core_trivial hℓ hf K hK σ hσ Θ hΘ hp
      (by omega) ⊤ le_top ⟨α, Subgroup.mem_top _⟩ hαin
      (by rw [Subgroup.orderOf_mk]; exact hαord)
  obtain ⟨f', hff'⟩ := hpf
  have hd : 1 ≤ f' := by
    rcases Nat.eq_zero_or_pos f' with h | h
    · rw [h, mul_zero] at hff'
      omega
    · exact h
  refine ⟨f', hff', ?_⟩
  have hm3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  obtain ⟨φ, hφ, hφord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ
      (by omega : 1 ≤ 3 * f) hK3
  obtain ⟨δc, hδcdef⟩ : ∃ δc, φ ^ (3 * f') = δc := ⟨_, rfl⟩
  have hδc : ∀ c, δc c = c ^ ℓ ^ (3 * f') := fun c => by
    rw [← hδcdef]
    exact ringAut_pow_apply_of_frobenius hφ _ c
  have hδcord : orderOf δc = p := by
    rw [← hδcdef, orderOf_pow_of_dvd (by omega) (by rw [hφord, hff']; exact ⟨p, by ring⟩),
      hφord, hff', show 3 * (p * f') = 3 * f' * p by ring, Nat.mul_div_cancel_left p (by omega)]
  have hzp : Subgroup.zpowers (Θ α) = Subgroup.zpowers δc := by
    have h1 : Nat.card (Subgroup.zpowers (Θ α)) = p := by rw [Nat.card_zpowers]; exact hηord
    have h2 : Nat.card (Subgroup.zpowers δc) = p := by rw [Nat.card_zpowers, hδcord]
    have : Finite (Subgroup.zpowers (Θ α)) :=
      Nat.finite_of_card_ne_zero (by rw [h1]; exact hp.ne_zero)
    have : Finite (Subgroup.zpowers δc) :=
      Nat.finite_of_card_ne_zero (by rw [h2]; exact hp.ne_zero)
    exact IsCyclic.subgroup_eq_iff_card_eq.mpr (h1.trans h2.symm)
  have hcard1 : Nat.card (fixedSubgroup α) =
      Nat.card (fixedSubgroup (fieldActor (t := TwistTag.D4) σ (Θ α))) :=
    card_fixedSubgroup_eq_of_intertwine (MulAut.conj h₀) α _ fun x => by
      have h1 : MulAut.conj h₀ * α * (MulAut.conj h₀)⁻¹ = fieldActor σ (Θ α) := hh₀
      rw [← h1]
      simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
  have hfix_eq : fixedSubgroup (fieldActor (t := TwistTag.D4) σ (Θ α)) = fixedSubgroup (fieldActor (t := TwistTag.D4) σ δc) := by
    have h := CFSG.RankThree.PartOne.CTP.fixedSubgroup_eq_of_zpowers_eq
      (fieldActorHom (t := TwistTag.D4) σ) hzp
    ext x
    exact SetLike.ext_iff.1 h x
  rw [hcard1, hfix_eq]
  have hK' : Nat.card K = ℓ ^ (3 * f' * p) := by
    rw [hK3, hff']
    ring_nf
  have hσ' : ∀ c, σ c = c ^ ℓ ^ (f' * p) := fun c => by rw [hσ c, hff', mul_comm p f']
  obtain ⟨-, -, hk, hres, -, -, hfixJ, -⟩ :=
    triality_canonical_field_full_centralizer_and_pointwise_kernel hℓ hd hp.two_le hm3 K hK' σ hσ'
      δc hδc
  have e3 : ↥(fixedSubgroup (fieldActor (t := TwistTag.D4) σ δc)) ≃*
      ↥(trialityFieldImage σ δc) :=
    (Subgroup.equivMapOfInjective _ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective).trans
      (MulEquiv.subgroupCongr hfixJ)
  have e4 : ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield δc)
      (fixSubfieldRestrict σ δc).toRingHom) ≃* ↥(trialityFieldImage σ δc) :=
    Subgroup.equivMapOfInjective _ _ (baseChangeGL_injective (fixSubfield δc).subtype)
  rw [Nat.card_congr e3.toEquiv, ← Nat.card_congr e4.toEquiv]
  have : Finite (fixSubfield δc) := Subtype.finite
  have : Fintype (fixSubfield δc) := Fintype.ofFinite _
  have hcardK0 : Fintype.card (fixSubfield δc) = ℓ ^ (3 * f') := by
    rw [← Nat.card_eq_fintype_card, hk]
  have hσ0pow : ∀ c : fixSubfield δc, fixSubfieldRestrict σ δc c = c ^ ℓ ^ (f' * p) := fun c =>
    Subtype.ext (by rw [hres c, hσ', SubmonoidClass.coe_pow])
  have hj : p % 3 = 1 ∨ p % 3 = 2 := by
    have h3 : p % 3 ≠ 0 := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.dvd_of_mod_eq_zero h)
      omega
    omega
  have hpowj : ∀ c : fixSubfield δc, c ^ (ℓ ^ (3 * f')) ^ (p / 3) = c := fun c => by
    have h := FiniteField.pow_card_pow (p / 3) c
    rwa [hcardK0] at h
  have hσ0 : ∀ c : fixSubfield δc,
      (fixSubfieldRestrict σ δc).toRingHom c = c ^ (ℓ ^ f') ^ (p % 3) := fun c => by
    have h2 : ℓ ^ (f' * p) = (ℓ ^ (3 * f')) ^ (p / 3) * (ℓ ^ f') ^ (p % 3) := by
      rw [← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      calc f' * p = f' * (3 * (p / 3) + p % 3) := by rw [Nat.div_add_mod]
        _ = 3 * f' * (p / 3) + f' * (p % 3) := by ring
    have h3 : (fixSubfieldRestrict σ δc).toRingHom c = c ^ ℓ ^ (f' * p) := hσ0pow c
    rw [h3, h2, pow_mul, hpowj c]
  obtain ⟨hC, -, -⟩ := triality_both_orientations_exact_finite_order ℓ f' hℓ hd (fixSubfield δc)
    (by rw [hk, ← pow_mul, mul_comm]) (p % 3) hj (fixSubfieldRestrict σ δc).toRingHom hσ0
  rw [hC]
  exact dvd_of_eq (by simp only [lieOrderNumerator]; ring)

theorem outerFixedOrder_trialityD4_of_ne_three (K : Type) [Group K] [Finite K] (n ℓ f : ℕ) :
    StatedLieAdmissible .trialityD4 n ℓ f → CFSG.Blueprint.LieModel K .trialityD4 n ℓ f →
    (StatedLieTag.trialityD4 ≠ .Tits) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ lieOrderDivisor .trialityD4 n (ℓ ^ f) →
      ¬ (StatedLieTag.trialityD4 = .POmegaPlus ∧ n = 4 ∧ p = 3) → p ≠ 3 →
    ∀ α : MulAut K, α ^ p = 1 → α ∉ inner K →
      ∃ f₀ : ℕ, f = p * f₀ ∧
        Nat.card (fixedSubgroup α) ∣ lieOrderNumerator .trialityD4 n (ℓ ^ f₀) := by
  intro hadm hmodel _ p hp hp2 _ _ hp3 α hαp hαin
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by norm_num)
    omega
  obtain ⟨hℓ, hf, hn⟩ := hadm
  have hchev : ChevalleyExceptionalModel K .trialityD4 ℓ f := by
    rcases hmodel with ⟨ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact h
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hn0 : n = 0 := hn
  subst hn0
  obtain ⟨K', _, _, σ, hcard, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hℓ hf hchev.2
  have hβp : MulAut.congr e α ^ p = 1 := by rw [← map_pow, hαp, map_one]
  have hβout : MulAut.congr e α ∉ inner (graphFixedRootGroup TwistTag.D4 K' σ.toRingHom) :=
    fun hin => hαin ((congr_mem_inner_iff e α).mp hin)
  rw [← card_fixedSubgroup_congr e α]
  exact trialityD4_outer_fixed_order hℓ hf hp hp5 K' hcard σ hσ _ hβp hβout

theorem outerFixedOrderBoundAt_trialityD4_of_three (h3 : OuterFixedOrderTrialityThree) :
    OuterFixedOrderBoundAt .trialityD4 := by
  intro K _ _ n ℓ f hadm hmodel hne p hp hp2 hdiv hD4 α hαp hαin
  by_cases hp3 : p = 3
  · subst hp3
    rcases h3 K n ℓ f hadm hmodel α hαp hαin with h | h
    · exact Or.inl h
    · exact Or.inr ⟨rfl, rfl, h⟩
  · exact Or.inl (outerFixedOrder_trialityD4_of_ne_three K n ℓ f hadm hmodel hne p hp hp2 hdiv hD4
      hp3 α hαp hαin)

end

end CFSG.HardMathSupport.Lang.Coordinator
