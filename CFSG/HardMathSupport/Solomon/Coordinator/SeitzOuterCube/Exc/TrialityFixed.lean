module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.FixPlaneTwBase
public import CFSG.RankThree.Chevalley.SteinbergCBTrialityTransposition
public import CFSG.RankThree.Chevalley.SteinbergBTTrialityCanonicalField

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2 CFSG.RankThree.PartOne.CTP
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge TauCeti

section Fixed


theorem graphFixedRootGroup_trialityD4_equiv_cat {q₀ : PrimePower}
    (hv₀ : (LieTypeIndex.trialityD4 q₀).Valid) {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = q₀.card ^ 3) (τ : k ≃+* k)
    (hτ : (∀ c, τ c = c ^ q₀.card) ∨ ∀ c, τ c = c ^ (q₀.card ^ 2)) :
    Nonempty (↥(graphFixedRootGroup TwistTag.D4 k τ.toRingHom) ≃* Cat ⟨.trialityD4 q₀, hv₀⟩) := by
  have : Fintype k := Fintype.ofFinite k
  have hq3 : ∀ c : k, c ^ q₀.card ^ 3 = c := fun c => by
    rw [← hk, Nat.card_eq_fintype_card, FiniteField.pow_card]
  rcases hτ with h | h
  · obtain ⟨e⟩ := catEquiv_graphFixedRootGroup_of_data TwistTag.D4
      Even.chevalleyBridgesAll.trialityD4 q₀ hv₀ k hk τ h
    exact ⟨e.symm⟩
  · have hsymm : ∀ c, τ.symm c = c ^ q₀.card := fun c => by
      refine τ.symm_apply_eq.2 ?_
      rw [h, ← pow_mul, show q₀.card * q₀.card ^ 2 = q₀.card ^ 3 by ring, hq3]
    obtain ⟨e⟩ := catEquiv_graphFixedRootGroup_of_data TwistTag.D4
      Even.chevalleyBridgesAll.trialityD4 q₀ hv₀ k hk τ.symm hsymm
    obtain ⟨f, -⟩ := CFSG.RankThree.Chevalley.exists_mulEquiv_of_map_eq
      (CFSG.RankThree.Chevalley.trialityTranspositionAut k)
      (CFSG.RankThree.Chevalley.map_trialityTranspositionAut_graphFixedRootGroup τ)
    exact ⟨f.trans e.symm⟩

theorem trialityD4_fixedSubgroup_equiv_cat {q q₀ : PrimePower} {p : ℕ}
    (hqq : q.card = q₀.card ^ p) (hp : p.Prime) (hp5 : 5 ≤ p) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = q.card ^ 3) (σ : K ≃+* K) (hσ : ∀ x, σ x = x ^ q.card) {η : K ≃+* K}
    (hη : orderOf η = p) (hF : Nat.card (fixSubfield η) = q₀.card ^ 3)
    (hv₀ : (LieTypeIndex.trialityD4 q₀).Valid) :
    Nonempty (↥(fixedSubgroup (fieldActor (t := TwistTag.D4) σ η)) ≃*
      Cat ⟨.trialityD4 q₀, hv₀⟩) := by
  classical
  have hℓ : q₀.p.Prime := q₀.prime_p
  have hd : 1 ≤ q₀.exponent := q₀.exponent_pos
  have hm3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  have hpos : 1 ≤ 3 * q₀.exponent * p := Nat.mul_pos (Nat.mul_pos (by norm_num) hd) hp.pos
  have hKpow : Nat.card K = q₀.p ^ (3 * q₀.exponent * p) := by
    rw [hK, hqq, PrimePower.card_def, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have hσ' : ∀ c, σ c = c ^ q₀.p ^ (q₀.exponent * p) := fun c => by
    rw [hσ, hqq, PrimePower.card_def, ← pow_mul]
  obtain ⟨φ, hφ, hφord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ hpos
      hKpow
  obtain ⟨δc, hδcdef⟩ : ∃ δc, φ ^ (3 * q₀.exponent) = δc := ⟨_, rfl⟩
  have hδc : ∀ c, δc c = c ^ q₀.p ^ (3 * q₀.exponent) := fun c => by
    rw [← hδcdef]
    exact ringAut_pow_apply_of_frobenius hφ _ c
  have hδcord : orderOf δc = p := by
    rw [← hδcdef, orderOf_pow_of_dvd (by omega) (by rw [hφord]; exact Dvd.intro p rfl), hφord,
      Nat.mul_div_cancel_left p (by omega)]
  have hzp : Subgroup.zpowers η = Subgroup.zpowers δc :=
    zpowers_ringEquiv_eq_of_orderOf hℓ hpos hKpow hη hδcord
  have hfix : fixedSubgroup (fieldActor (t := TwistTag.D4) σ η) =
      fixedSubgroup (fieldActor (t := TwistTag.D4) σ δc) :=
    fixedSubgroup_eq_of_zpowers_eq (fieldActorHom (t := TwistTag.D4) σ) hzp
  obtain ⟨-, -, hk, hres, -, -, hfixJ, -⟩ :=
    CFSG.RankThree.Chevalley.triality_canonical_field_full_centralizer_and_pointwise_kernel hℓ hd
      hp.two_le hm3 K hKpow σ hσ' δc hδc
  let e3 : ↥(fixedSubgroup (fieldActor (t := TwistTag.D4) σ δc)) ≃*
      ↥(trialityFieldImage σ δc) :=
    (Subgroup.equivMapOfInjective _ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective).trans
      (MulEquiv.subgroupCongr hfixJ)
  let e4 : ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield δc)
      (fixSubfieldRestrict σ δc).toRingHom) ≃* ↥(trialityFieldImage σ δc) :=
    Subgroup.equivMapOfInjective _ _ (baseChangeGL_injective (fixSubfield δc).subtype)
  have hkeq : fixSubfield η = fixSubfield δc :=
    fixedField_eq_of_orderOf hℓ hpos hKpow hη hδcord
  have hk₀ : Nat.card (fixSubfield δc) = q₀.card ^ 3 := by
    rw [← hkeq]
    exact hF
  have : Fintype (fixSubfield δc) := Fintype.ofFinite _
  have hpowj : ∀ c : fixSubfield δc, c ^ (q₀.p ^ (3 * q₀.exponent)) ^ (p / 3) = c := fun c => by
    have h := FiniteField.pow_card_pow (p / 3) c
    rwa [← Nat.card_eq_fintype_card, hk] at h
  have hτpow : ∀ c : fixSubfield δc,
      fixSubfieldRestrict σ δc c = c ^ q₀.card ^ (p % 3) := fun c => by
    have h1 : fixSubfieldRestrict σ δc c = c ^ q₀.p ^ (q₀.exponent * p) :=
      Subtype.ext (by rw [hres c, hσ', SubmonoidClass.coe_pow])
    have h2 : q₀.p ^ (q₀.exponent * p) =
        (q₀.p ^ (3 * q₀.exponent)) ^ (p / 3) * q₀.card ^ (p % 3) := by
      rw [PrimePower.card_def, ← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      calc q₀.exponent * p = q₀.exponent * (3 * (p / 3) + p % 3) := by rw [Nat.div_add_mod]
        _ = 3 * q₀.exponent * (p / 3) + q₀.exponent * (p % 3) := by ring
    rw [h1, h2, pow_mul, hpowj c]
  have hj : p % 3 = 1 ∨ p % 3 = 2 := by
    have h0 : p % 3 ≠ 0 := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.dvd_of_mod_eq_zero h)
      omega
    omega
  have hτ : (∀ c, fixSubfieldRestrict σ δc c = c ^ q₀.card) ∨
      ∀ c, fixSubfieldRestrict σ δc c = c ^ (q₀.card ^ 2) := by
    rcases hj with h | h
    · exact Or.inl fun c => by rw [hτpow c, h, pow_one]
    · exact Or.inr fun c => by rw [hτpow c, h]
  obtain ⟨e5⟩ := graphFixedRootGroup_trialityD4_equiv_cat hv₀ hk₀ (fixSubfieldRestrict σ δc) hτ
  exact ⟨((MulEquiv.subgroupCongr hfix).trans e3).trans (e4.symm.trans e5)⟩

end Fixed

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc
