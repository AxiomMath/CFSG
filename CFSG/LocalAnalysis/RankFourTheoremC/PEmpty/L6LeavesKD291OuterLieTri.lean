module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieTw
import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTrialityOrient
import CFSG.RankThree.Chevalley.SteinbergCDTrialityTwelveLocalCore
import CFSG.RankThree.PartOne.CTP.SeitzMaxAbstract
import CFSG.LocalAnalysis.SectionRank.ExceptionalModels
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric
import CFSG.Blueprint.LieModelAPI
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export
  (exists_mulEquiv_graphFixedRootGroup_frobenius_sq_D4)

theorem pow_pow_eq_pow_pow_mod_three {k : Type} [Field k] [Finite k] {q : ℕ}
    (hk : Nat.card k = q ^ 3) (m : ℕ) (c : k) : c ^ (q ^ m) = c ^ (q ^ (m % 3)) := by
  have : Fintype k := Fintype.ofFinite k
  have hq : Fintype.card k = q ^ 3 := by rw [← Nat.card_eq_fintype_card, hk]
  have h1 : c ^ ((q ^ 3) ^ (m / 3)) = c := by
    rw [← hq]
    exact FiniteField.pow_card_pow _ c
  have h2 : q ^ m = (q ^ 3) ^ (m / 3) * q ^ (m % 3) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  rw [h2, pow_mul, h1]

section


theorem four_le_pRank_graphFixedRootGroup_D4 {p d : ℕ} (hp : p.Prime) (hd : 1 ≤ d)
    (k : Type) [Field k] [Finite k] (hk : Nat.card k = (p ^ d) ^ 3) (σ₀ : k ≃+* k)
    (hσ₀ : (∀ c, σ₀ c = c ^ (p ^ d)) ∨ (∀ c, σ₀ c = c ^ (p ^ d) ^ 2)) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup (graphFixedRootGroup TwistTag.D4 k σ₀.toRingHom)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨fr, hfr, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp
      (by omega : 1 ≤ 3 * d) (by rw [hk, ← pow_mul, mul_comm] : Nat.card k = p ^ (3 * d))
  obtain ⟨σ₁, hσ₁⟩ : ∃ σ₁ : k ≃+* k, ∀ c, σ₁ c = c ^ p ^ d :=
    ⟨fr ^ d, fun c => ringAut_pow_apply_of_frobenius hfr d c⟩
  have hmodel := twistedModel_graphFixedRootGroup (t := TwistTag.D4) hp hd k hk σ₁ hσ₁
  have h4 := CFSG.SectionRank.four_le_pRank_of_trialityD4Model hd hmodel
  obtain ⟨e⟩ : Nonempty (graphFixedRootGroup TwistTag.D4 k σ₀.toRingHom ≃*
      graphFixedRootGroup TwistTag.D4 k σ₁.toRingHom) := by
    rcases hσ₀ with h | h
    · have : σ₀ = σ₁ := RingEquiv.ext fun c => by rw [h, hσ₁]
      subst this
      exact ⟨MulEquiv.refl _⟩
    · exact exists_mulEquiv_graphFixedRootGroup_frobenius_sq_D4 k hk σ₀ σ₁ h hσ₁
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 e]
  exact h4

theorem two_le_pRank_fixed_graphFixed_D4 {p f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) {β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hβ : β ^ p = 1) (hβin : β ∉ inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    2 ≤ CFSG.Open.pRank p (fixedSubgroup β) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hβ1 : β ≠ 1 := fun h =>
    hβin (h ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = p := orderOf_eq_prime hβ hβ1
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, hcyc, Θ, hΘ, -⟩ :=
    CFSG.RankThree.Chevalley.triality_normal_form_data hp hf K hK σ hσ
  obtain ⟨hηord, hpf, ⟨h₀, hh₀⟩, -⟩ :=
    CFSG.RankThree.Chevalley.triality_noninner_large_prime_field_descent_and_local_core_trivial
      hp hf K hK σ hσ Θ hΘ hp (by omega) ⊤ le_top ⟨β, Subgroup.mem_top _⟩ hβin
      (by rw [Subgroup.orderOf_mk]; exact hβord)
  have hh₀' : MulAut.conj h₀ * β * (MulAut.conj h₀)⁻¹ =
      fieldActor (t := TwistTag.D4) σ (Θ β) := hh₀
  obtain ⟨f', hff'⟩ := hpf
  have hd : 1 ≤ f' := by
    rcases Nat.eq_zero_or_pos f' with h | h
    · rw [h, mul_zero] at hff'
      omega
    · exact h
  obtain ⟨φ, hφ, hφord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp
      (by omega : 1 ≤ 3 * f) hK3
  obtain ⟨δc, hδcdef⟩ : ∃ δc, φ ^ (3 * f') = δc := ⟨_, rfl⟩
  have hδc : ∀ c, δc c = c ^ p ^ (3 * f') := fun c => by
    rw [← hδcdef]
    exact ringAut_pow_apply_of_frobenius hφ _ c
  have hδcord : orderOf δc = p := by
    rw [← hδcdef, orderOf_pow_of_dvd (by omega)
      (by rw [hφord, hff']; exact ⟨p, by ring⟩), hφord, hff',
      show 3 * (p * f') = 3 * f' * p by ring, Nat.mul_div_cancel_left p (by omega)]
  have hzp : Subgroup.zpowers (Θ β) = Subgroup.zpowers δc := by
    have h1 : Nat.card (Subgroup.zpowers (Θ β)) = p := by
      rw [Nat.card_zpowers]; exact hηord
    have h2 : Nat.card (Subgroup.zpowers δc) = p := by rw [Nat.card_zpowers, hδcord]
    have : Finite (Subgroup.zpowers (Θ β)) :=
      Nat.finite_of_card_ne_zero (by rw [h1]; exact hp.ne_zero)
    have : Finite (Subgroup.zpowers δc) :=
      Nat.finite_of_card_ne_zero (by rw [h2]; exact hp.ne_zero)
    exact IsCyclic.subgroup_eq_iff_card_eq.mpr (h1.trans h2.symm)
  have hfix_eq : fixedSubgroup (fieldActor (t := TwistTag.D4) σ (Θ β)) =
      fixedSubgroup (fieldActor (t := TwistTag.D4) σ δc) := by
    have h := CFSG.RankThree.PartOne.CTP.fixedSubgroup_eq_of_zpowers_eq
      (fieldActorHom (t := TwistTag.D4) σ) hzp
    ext x
    exact SetLike.ext_iff.1 h x
  have hm3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  have hK' : Nat.card K = p ^ (3 * f' * p) := by
    rw [hK3, hff']; congr 1; ring
  have hσ' : ∀ c, σ c = c ^ p ^ (f' * p) := fun c => by
    rw [hσ c, hff', mul_comm p f']
  obtain ⟨-, -, hkc, hres, -, -, hfixJ, -, -, -⟩ :=
    CFSG.RankThree.Chevalley.triality_canonical_field_full_centralizer_and_pointwise_kernel hp hd
      hp.two_le hm3 K hK' σ hσ' δc hδc
  have hk' : Nat.card (fixSubfield δc) = (p ^ f') ^ 3 := by rw [hkc, ← pow_mul, mul_comm]
  have hσ₀ : ∀ c : fixSubfield δc, fixSubfieldRestrict σ δc c = c ^ (p ^ f') ^ p := fun c =>
    Subtype.ext (by rw [hres, hσ', pow_mul]; rfl)
  have hndvd : ¬ 3 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h
    omega
  have hσ₀' : (∀ c : fixSubfield δc, fixSubfieldRestrict σ δc c = c ^ (p ^ f')) ∨
      (∀ c : fixSubfield δc, fixSubfieldRestrict σ δc c = c ^ (p ^ f') ^ 2) := by
    have hmod : p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases hmod with h | h
    · left
      intro c
      rw [hσ₀ c, pow_pow_eq_pow_pow_mod_three hk' p c, h, pow_one]
    · right
      intro c
      rw [hσ₀ c, pow_pow_eq_pow_pow_mod_three hk' p c, h]
  have h4 := four_le_pRank_graphFixedRootGroup_D4 hp hd (fixSubfield δc) hk'
    (fixSubfieldRestrict σ δc) hσ₀'
  let e3 : ↥(fixedSubgroup (fieldActor (t := TwistTag.D4) σ δc)) ≃* ↥(trialityFieldImage σ δc) :=
    (Subgroup.equivMapOfInjective _ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective).trans
      (MulEquiv.subgroupCongr hfixJ)
  let eJ : ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield δc)
      (fixSubfieldRestrict σ δc).toRingHom) ≃* ↥(trialityFieldImage σ δc) :=
    Subgroup.equivMapOfInjective _ (baseChangeGL (τ := TwistTag.D4.tag) (fixSubfield δc).subtype)
      (baseChangeGL_injective _)
  have h5 : CFSG.Open.pRank p (fixedSubgroup (fieldActor (t := TwistTag.D4) σ δc)) =
      CFSG.Open.pRank p (⊤ : Subgroup ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield δc)
        (fixSubfieldRestrict σ δc).toRingHom)) :=
    (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.open_pRank_eq_pRank_top _).trans
      ((CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 e3).trans
        (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 eJ.symm))
  have h6 : CFSG.Open.pRank p (fixedSubgroup (fieldActor (t := TwistTag.D4) σ (Θ β))) ≤
      CFSG.Open.pRank p (fixedSubgroup β) :=
    pRank_fixed_le_of_intertwine hp1 (MulAut.conj h₀) β (fieldActor σ (Θ β))
      (intertwine_of_conj' hh₀')
  rw [hfix_eq] at h6
  omega

open CFSG.HardMathSupport.Lang.Coordinator in
theorem two_le_pRank_fixed_trialityD4 {ℓ f p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpℓ : p = ℓ)
    (hf : 1 ≤ f) {S : Type} [Group S] [Finite S]
    (hchev : ChevalleyExceptionalModel S .trialityD4 ℓ f)
    (β : MulAut S) (hβ : β ^ p = 1) (hβin : β ∉ inner S) :
    2 ≤ CFSG.Open.pRank p (fixedSubgroup β) := by
  subst hpℓ
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e'⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 hp hf hchev.2
  have hα : MulAut.congr e' β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hαin : MulAut.congr e' β ∉ inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    fun hin => hβin ((congr_mem_inner_iff e' β).mp hin)
  have h1 := two_le_pRank_fixed_graphFixed_D4 hp hp5 hf K hK σ hσ hα hαin
  have h2 : CFSG.Open.pRank p (fixedSubgroup (MulAut.congr e' β)) ≤
      CFSG.Open.pRank p (fixedSubgroup β) :=
    pRank_fixed_le_of_intertwine hp1 e' β (MulAut.congr e' β) fun x => by
      rw [MulAut.congr_apply]
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  omega

theorem outerFixedRankDefAt_trialityD4 : OuterFixedRankDefAt .trialityD4 := by
  intro K _ _ n ℓ f hadm hmodel hT p hp hp5 hℓ α hαp hαin
  subst hℓ
  obtain ⟨-, hf, -⟩ := hadm
  obtain ⟨-, hch⟩ := (CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)).1 hmodel
  exact Or.inl (two_le_pRank_fixed_trialityD4 hp hp5 rfl hf hch α hαp hαin)

end

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
