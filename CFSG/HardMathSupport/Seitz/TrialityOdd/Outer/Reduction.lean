module

public import CFSG.LieType.SeitzGeneration.ExcOuterTriality
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityNoninnerDescent

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.SteinbergBT CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.SEITZ2
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

open CFSG.LocalAnalysis.ComponentInitial (finite_field_automorphism_fixed_field_cardinality)


@[expose] def SubfieldPairD4Odd : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 3 → ∀ (σ : K ≃+* K), (∀ c, σ c = c ^ ℓ ^ f) →
      ∀ (δ : K ≃+* K) (p : ℕ), p.Prime → 5 ≤ p → orderOf δ = p →
        ∀ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
          (fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ)).map (MulAut.conj g).toMonoidHom ≠
            fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ) →
          Subgroup.closure ((fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ) :
            Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∪
            ((fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ)).map (MulAut.conj g).toMonoidHom :
              Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) = ⊤ ∨
            ¬ p ∣ Nat.card (fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ))

section Main

variable {ℓ f : ℕ} {K : Type} [Field K] [Finite K] {σ : K ≃+* K}

theorem eq_one_of_central_fixed_fieldActor_gen {p : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ ℓ ^ f)
    {δ : K ≃+* K} (hδ : orderOf δ = p) {x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hx : x ∈ fixedSubgroup (fieldActor σ δ))
    (hc : ∀ y ∈ fixedSubgroup (fieldActor σ δ), x * y = y * x) : x = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hf3 : 1 ≤ 3 * f := by omega
  obtain ⟨φ, hφ, hφord, -, hcardAut, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality hℓ hf3 hK3
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have hpf3 : p ∣ 3 * f := by
    rw [← hδ, ← hcardAut]
    exact orderOf_dvd_natCard δ
  have hpf : p ∣ f := by
    rcases (Nat.Prime.dvd_mul hp).1 hpf3 with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h
      omega
    · exact h
  obtain ⟨f', hff'⟩ := hpf
  have hf'1 : 1 ≤ f' := by
    rcases Nat.eq_zero_or_pos f' with h | h
    · rw [h] at hff'
      omega
    · exact h
  have hm3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  obtain ⟨δc, hδcdef⟩ : ∃ δc, φ ^ (3 * f') = δc := ⟨_, rfl⟩
  have hδc : ∀ c, δc c = c ^ ℓ ^ (3 * f') := fun c => by
    rw [← hδcdef]
    exact ringAut_pow_apply_of_frobenius hφ _ c
  have hδcord : orderOf δc = p := by
    rw [← hδcdef, orderOf_pow_of_dvd (by omega) (by rw [hφord, hff']; exact ⟨p, by ring⟩),
      hφord, hff', show 3 * (p * f') = 3 * f' * p by ring, Nat.mul_div_cancel_left p (by omega)]
  have hzp : Subgroup.zpowers δ = Subgroup.zpowers δc :=
    zpowers_ringEquiv_eq_of_orderOf hℓ hf3 hK3 hδ hδcord
  have hfix : fixedSubgroup (fieldActor σ δ) = fixedSubgroup (fieldActor σ δc) :=
    fixedSubgroup_eq_of_zpowers_eq (fieldActorHom (t := TwistTag.D4) σ) hzp
  rw [hfix] at hx hc
  have hK' : Nat.card K = ℓ ^ (3 * f' * p) := by rw [hK3, hff']; ring_nf
  have hσ' : ∀ c, σ c = c ^ ℓ ^ (f' * p) := fun c => by rw [hσ, hff', mul_comm f' p]
  obtain ⟨-, -, -, -, -, -, hfixJ, hsimple, hnc, -⟩ :=
    triality_canonical_field_full_centralizer_and_pointwise_kernel hℓ hf'1
      hp.two_le hm3 K hK' σ hσ' δc hδc
  set J := trialityFieldImage σ δc
  let e3 : ↥(fixedSubgroup (fieldActor σ δc)) ≃* ↥J :=
    (Subgroup.equivMapOfInjective _ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective).trans
      (MulEquiv.subgroupCongr hfixJ)
  have hnc' : ∃ a b : ↥J, a * b ≠ b * a := by
    push Not at hnc
    exact hnc
  have : IsSimpleGroup ↥J := hsimple
  have hZ : Subgroup.center ↥J = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥J) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc'
      apply hab
      have : a ∈ Subgroup.center ↥J := h ▸ Subgroup.mem_top a
      exact ((Subgroup.mem_center_iff.1 this) b).symm
  have hz : e3 ⟨x, hx⟩ ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, hy⟩ : ∃ y : ↥(fixedSubgroup (fieldActor σ δc)), e3 y = g :=
      ⟨e3.symm g, e3.apply_symm_apply g⟩
    rw [← hy, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc y y.2).symm
  rw [hZ, Subgroup.mem_bot] at hz
  have h1 : (⟨x, hx⟩ : ↥(fixedSubgroup (fieldActor σ δc))) = 1 :=
    e3.injective (by rw [hz, map_one])
  exact congrArg Subtype.val h1

end Main


section Data


theorem fieldAutData_trialityD4_odd (hpair : SubfieldPairD4Odd) {ℓ f p : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hp : p.Prime) (hp5 : 5 ≤ p) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] {σ : K ≃+* K} (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ ℓ ^ f) :
    FieldAutData (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, -, ⟨Θ, hΘ, hsurj, hker, -⟩, hcyc, -⟩ :=
    odd_triality_exact_automorphism_normal_form hℓ hℓ2 hf K hK σ hσ
  have hcycOut : IsCyclic (Outer (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    isCyclic_outer_of_hom Θ hsurj hker
  refine fieldAutData_of_standard
    (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →* MulAut _).range
    {g | ∃ δ : K ≃+* K, orderOf δ = p ∧ g = fieldActor σ δ} ?_ ?_ ?_ ?_ ?_
  · intro E hE hEc
    have := hE
    exact exists_conj_mem_of_plane_of_cyclic_outer hp hcycOut E hEc
  · intro α hα
    obtain ⟨hord, hout⟩ := hα
    obtain ⟨hηord, -, ⟨h₀, hh₀⟩, -⟩ :=
      triality_noninner_large_prime_field_descent_and_local_core_trivial hℓ hf K hK σ
        hσ Θ hΘ hp (by omega) ⊤ le_top ⟨α, Subgroup.mem_top _⟩
        (fun ⟨g, hg⟩ => hout g hg.symm) (by rw [Subgroup.orderOf_mk]; exact hord)
    refine ⟨(MulAut.conj h₀)⁻¹, ?_, fieldActor σ (Θ α), ⟨Θ α, hηord, rfl⟩, ?_⟩
    · exact (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →* MulAut _).range.inv_mem
        ⟨h₀, rfl⟩
    · rw [← hh₀]
      group
  · rintro _ ⟨δ, hδ, rfl⟩ _ ⟨τ, hτ, rfl⟩
    exact fixedSubgroup_eq_of_zpowers_eq (fieldActorHom (t := TwistTag.D4) σ)
      (zpowers_ringEquiv_eq_of_orderOf hℓ (by omega) hK3 hδ hτ)
  · rintro _ ⟨δ, hδ, rfl⟩ _ x hx hc
    exact eq_one_of_central_fixed_fieldActor_gen hℓ hp hp5 hf hK hσ hδ hx hc
  · rintro _ ⟨δ, hδ, rfl⟩ d ⟨g, rfl⟩ hne
    exact hpair ℓ f hℓ hℓ2 hf K hK σ hσ δ p hp hp5 hδ g hne

end Data


section Index

open CFSG.RankThree.PartOne.Census3 (IsoLie)

open CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge TauCeti


theorem exists_trialityD4_model_odd {q : TauCeti.PrimePower} (hq : q.p ≠ 2) {K : Type} [Group K]
    (hiso : IsoLie K (.trialityD4 q)) :
    ∃ (X : Type) (_ : Field X) (_ : Finite X) (σ : X ≃+* X),
      Nat.card X = (q.p ^ q.exponent) ^ 3 ∧ (∀ c, σ c = c ^ (q.p ^ q.exponent)) ∧
      Nonempty (K ≃* graphFixedRootGroup TwistTag.D4 X σ.toRingHom) := by
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  exact exists_mulEquiv_graphFixedRootGroup_card .D4 q.prime_p q.exponent_pos
    (twistedModel_of_bridge Twisted.twistedBridge_trialityD4 q hv hq (by decide) e0)

theorem extSeitzAtOuter_trialityD4_odd_of_pair (hpair : SubfieldPairD4Odd)
    {q : TauCeti.PrimePower} (hq : q.p ≠ 2) : ExtSeitzAtOuter (.trialityD4 q) := by
  intro K _ _ _ hnab hiso p hp hp5 hpd E hE hc hout
  obtain ⟨X, _, _, σ, hX, hσ, ⟨e⟩⟩ := exists_trialityD4_model_odd hq hiso
  have hd : FieldAutData K p :=
    (fieldAutData_trialityD4_odd hpair q.prime_p hq hp hp5 q.exponent_pos hX hσ).of_mulEquiv e hp
  left
  exact closure_fixUnion_eq_top_of_fieldAutData hnab hp hd E hc hout

theorem seitzExcOuterNarrowTrialityOdd_of_pair (hpair : SubfieldPairD4Odd) :
    SeitzExcOuterNarrowTrialityOdd :=
  seitzExcOuterNarrowForAt_of_family (c := fun a : {q : PrimePower // q.p ≠ 2} =>
      LieTypeIndex.trialityD4 a.1) (P := fun _ _ => True) (F := IsTrialityIndex)
    (fun _ hv => finite_isSimpleGroup_cat_trialityD4 hv)
    (fun a K _ _ _ hnab hiso p hp hp5 hpd _ E hE hcard hout =>
      extSeitzAtOuter_trialityD4_odd_of_pair hpair a.2 K hnab hiso p hp hp5 hpd E hE hcard hout
        |> fun h => h)
    (fun d p _ hQ => by
      obtain ⟨hp5, q, rfl, hq⟩ := hQ
      exact ⟨⟨q, hq⟩, rfl, hp5, trivial⟩)

end Index

end CFSG.HardMathSupport.Seitz.TrialityOdd
