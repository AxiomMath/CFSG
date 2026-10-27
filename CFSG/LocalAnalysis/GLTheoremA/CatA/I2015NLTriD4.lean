module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLCore
import CFSG.LocalAnalysis.StandardType.GGRawAutRestTri
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalTrialityMain
import CFSG.SignalizerFunctorTheorem.NonLocal.TrialityTwo

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.Assembly CFSG.StandardType
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (NonLocalized)

private theorem nonLocalized_map_triD4 {X : Type*} [Group X] {J : Subgroup X} (γ : MulAut X)
    (hJ : NonLocalized J) : NonLocalized (J.map γ.toMonoidHom) := by
  intro T hT hs hle
  refine hJ (T.map γ.symm.toMonoidHom) (fun h => hT ?_) ?_ fun j hj => ?_
  · rwa [Subgroup.map_eq_bot_iff_of_injective _ γ.symm.injective] at h
  · haveI := hs
    exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective γ.symm.toMonoidHom T)
  · have hγj : γ j ∈ Subgroup.normalizer (T : Set X) := hle ⟨j, hj, rfl⟩
    rw [Subgroup.mem_normalizer_iff] at hγj ⊢
    intro t
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, MulEquiv.symm_symm, map_mul, map_mul,
      map_inv]
    exact hγj (γ t)

section Model

set_option linter.unusedSectionVars false


theorem triD4_exists_nonLocalized_fix {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hp : p.Prime)
    (hp5 : 5 ≤ p) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hαp : α ^ p = 1)
    (hαin : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    ∃ D : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      D ≤ fixedSubgroup α ∧ IsSimpleGroup ↥D ∧ (∃ x y : ↥D, x * y ≠ y * x) ∧ NonLocalized D := by
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
  have hfix_eq : fixedSubgroup (fieldActor (t := TwistTag.D4) σ (Θ α)) =
      fixedSubgroup (fieldActor (t := TwistTag.D4) σ δc) := by
    have h := CFSG.RankThree.PartOne.CTP.fixedSubgroup_eq_of_zpowers_eq
      (fieldActorHom (t := TwistTag.D4) σ) hzp
    ext x
    exact SetLike.ext_iff.1 h x
  have hK' : Nat.card K = ℓ ^ (3 * f' * p) := by
    rw [hK3, hff']
    ring_nf
  have hσ' : ∀ c, σ c = c ^ ℓ ^ (f' * p) := fun c => by rw [hσ c, hff', mul_comm p f']
  obtain ⟨-, -, -, -, -, -, hfixJ, hsJ, hnJ, -⟩ :=
    triality_canonical_field_full_centralizer_and_pointwise_kernel hℓ hd hp.two_le hm3 K hK' σ hσ'
      δc hδc
  have hNL := CFSG.SignalizerFunctorTheorem.CatalogBridge.subfieldNonLocalizedTriality_of
    CFSG.SignalizerFunctorTheorem.NonLocal.subfieldNonLocalizedTrialityTwo ℓ f' p hℓ hd hp
    (by omega) K hK' σ δc hσ' hδc
  obtain ⟨J₀, hJ₀⟩ : ∃ J₀ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      J₀ = fixedSubgroup (fieldActor (t := TwistTag.D4) σ δc) := ⟨_, rfl⟩
  have hJ₀eq : J₀.map (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype =
      trialityFieldImage σ δc := by rw [hJ₀]; exact hfixJ
  have hsub : (trialityFieldImage σ δc).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
      J₀ := by
    ext x
    rw [Subgroup.mem_subgroupOf, ← hJ₀eq]
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact (Subtype.ext hyx) ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have e3 : ↥J₀ ≃* ↥(trialityFieldImage σ δc) :=
    (Subgroup.equivMapOfInjective _ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective).trans
      (MulEquiv.subgroupCongr hJ₀eq)
  have hsJ₀ : IsSimpleGroup ↥J₀ := e3.isSimpleGroup
  have hnJ₀ : ∃ x y : ↥J₀, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    exact hnJ fun a b => e3.symm.injective (by rw [map_mul, map_mul]; exact hcon _ _)
  have hNL₀ : NonLocalized J₀ := hsub ▸ hNL
  have hconj : MulAut.conj h₀ * α * (MulAut.conj h₀)⁻¹ =
      fieldActor (t := TwistTag.D4) σ (Θ α) := hh₀
  let γ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := (MulAut.conj h₀)⁻¹
  let eγ := J₀.equivMapOfInjective γ.toMonoidHom γ.injective
  refine ⟨J₀.map γ.toMonoidHom, ?_, eγ.symm.isSimpleGroup, ?_, nonLocalized_map_triD4 γ hNL₀⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    have hx' : fieldActor (t := TwistTag.D4) σ (Θ α) x = x := by
      have : x ∈ fixedSubgroup (fieldActor (t := TwistTag.D4) σ (Θ α)) := by
        rw [hfix_eq, ← hJ₀]
        exact hx
      exact this
    show α (γ x) = γ x
    apply (MulAut.conj h₀).injective
    have h1 := congrArg (fun φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) => φ x) hconj
    simp only [MulAut.mul_apply, hx'] at h1
    rw [h1]
    exact (MulAut.apply_inv_self _ _ x).symm
  · obtain ⟨x, y, hxy⟩ := hnJ₀
    exact ⟨eγ x, eγ y, fun h => hxy (eγ.injective (by rw [map_mul, map_mul]; exact h))⟩

theorem nlWitness_triD4 {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    [Finite (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n))]
    {f : MulAut (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n))}
    (hord : orderOf f = p)
    (hinn : f ∉ (MulAut.conj : LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K
      LargeEvenRhoD4 n) →* MulAut _).range) : NLWitness f := by
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by norm_num)
    omega
  have hchev : ChevalleyExceptionalModel
      (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n))
      .trialityD4 2 n :=
    ⟨⟨Nat.prime_two, hn, rfl⟩, twistedChevalleyModel_largeEven .D4 hK⟩
  obtain ⟨K', _, _, σ, hcard', hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hn hchev.2
  have hfp : f ^ p = 1 := hord ▸ pow_orderOf_eq_one f
  have hβp : MulAut.congr e f ^ p = 1 := by rw [← map_pow, hfp, map_one]
  have hβout : MulAut.congr e f ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (graphFixedRootGroup TwistTag.D4 K' σ.toRingHom) :=
    fun hin => hinn ((CFSG.LocalAnalysis.GLTheoremA.FQ.congr_mem_range_conj e f).1 hin)
  obtain ⟨D, hD, hDs, hDn, hDNL⟩ := triD4_exists_nonLocalized_fix Nat.prime_two hn hp hp5 K'
    hcard' σ hσ (MulAut.congr e f) hβp hβout
  haveI : Finite (graphFixedRootGroup TwistTag.D4 K' σ.toRingHom) :=
    Finite.of_equiv _ e.toEquiv
  refine nlWitness_of_nonLocalized e hDs hDn hDNL ?_
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
  have h2 : MulAut.congr e f x = x := hD hx
  have h1 : e (f (e.symm x)) = x := h2
  show f (e.symm x) = e.symm x
  apply e.injective
  rw [h1, e.apply_symm_apply]

end Model

section Family

set_option linter.unusedSectionVars false


theorem i2015NLOnTriD4_holds : I2015NLOnTriD4 := by
  intro lab hlab ht
  refine atLabelWhen_of_witness hlab ?_
    (fun p _ h => by rw [ht] at h; exact absurd h.1 (by decide))
  intro p hp hp2 h3 _ _ Q hQ
  obtain ⟨t, _, n⟩ := lab
  dsimp only at ht
  subst ht
  obtain ⟨hn, -⟩ := hlab
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, hF, hfin, hK, hQ'⟩ := hQ
  refine ⟨K, hF, hfin, hK, hQ', fun hs hna _ f hf hord hfinR _ => ?_⟩
  have hinn : f ∉ (MulAut.conj : LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K
      LargeEvenRhoD4 n) →* MulAut _).range := by
    obtain ⟨-, -, hconj, hF'⟩ := RawAutTri.ggRawInnField_triD4 hn K hK hp.one_lt.ne' hs hna
    rintro ⟨r, rfl⟩
    exact hF' _ hf hord (hconj r)
  exact nlWitness_triD4 hn hK hp hp2 (fun h => h3 ⟨rfl, h⟩) hord hinn

end Family

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
