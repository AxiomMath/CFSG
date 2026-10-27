module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieRes
import CFSG.RankThree.Chevalley.SteinbergCDTrialityTwelveLocalCore
import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
import CFSG.Adapters.TauCetiExceptional.TwistedD4Push
import CFSG.RankThree.PartOne.CTP.SeitzMaxAbstract
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerSimple

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter

open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem perfectInLayer_of_fixSubgroup_eq {S : Type*} [Group S] {β γ : MulAut S}
    (h : fixSubgroup β = fixSubgroup γ) (hβ : PerfectInLayer β) : PerfectInLayer γ := by
  intro P hP hPP
  rw [← h]
  exact hβ P (by rw [h]; exact hP) hPP

section Core


private theorem perfectInLayer_graphFixed_outer {p f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    {β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hβ : β ^ p = 1)
    (hβin : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    PerfectInLayer β := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hβ1 : β ≠ 1 := fun h =>
    hβin (h ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = p := orderOf_eq_prime hβ hβ1
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, hcyc, Θ, hΘ, -⟩ := CFSG.RankThree.Chevalley.triality_normal_form_data hp hf K hK σ hσ
  obtain ⟨hηord, hpf, ⟨h₀, hh₀⟩, -⟩ :=
    CFSG.RankThree.Chevalley.triality_noninner_large_prime_field_descent_and_local_core_trivial
      hp hf K hK σ hσ Θ hΘ hp
      (by omega) ⊤ le_top ⟨β, Subgroup.mem_top _⟩ hβin
      (by rw [Subgroup.orderOf_mk]; exact hβord)
  have hh₀' : MulAut.conj h₀ * β * (MulAut.conj h₀)⁻¹ = fieldActor (t := TwistTag.D4) σ (Θ β) := hh₀
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
  have hfix_eq :
      fixSubgroup (fieldActor (t := TwistTag.D4) σ (Θ β)) =
        fixSubgroup (fieldActor (t := TwistTag.D4) σ δc) := by
    have h := CFSG.RankThree.PartOne.CTP.fixedSubgroup_eq_of_zpowers_eq
      (fieldActorHom (t := TwistTag.D4) σ) hzp
    ext x
    exact SetLike.ext_iff.1 h x
  have hm3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  have hK' : Nat.card K = p ^ (3 * f' * p) := by
    rw [hK3, hff']; congr 1; ring
  have hσ' : ∀ c, σ c = c ^ p ^ (f' * p) := fun c => by
    rw [hσ c, hff', mul_comm p f']
  obtain ⟨-, -, -, -, -, -, hfixJ, hsimpJ, hncJ, -⟩ :=
    CFSG.RankThree.Chevalley.triality_canonical_field_full_centralizer_and_pointwise_kernel hp hd
      hp.two_le hm3 K hK' σ hσ' δc hδc
  haveI := hsimpJ
  have e3 : ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ δc)) ≃* ↥(trialityFieldImage σ δc) :=
    (Subgroup.equivMapOfInjective _ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective).trans
      (MulEquiv.subgroupCongr hfixJ)
  have hsimE : IsSimpleGroup ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ δc)) := e3.isSimpleGroup
  have hncE : ∃ a b : ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ δc)), a * b ≠ b * a := by
    simp only [not_forall, ne_eq] at hncJ
    obtain ⟨a, b, hab⟩ := hncJ
    refine ⟨e3.symm a, e3.symm b, fun h => hab ?_⟩
    have h' := congrArg e3 h
    simp only [map_mul, MulEquiv.apply_symm_apply] at h'
    exact h'
  have hPfix : PerfectInLayer (fieldActor (t := TwistTag.D4) σ δc) :=
    LieSemisimple.perfectInLayer_of_isSimpleGroup _ hsimE hncE
  have hPΘ : PerfectInLayer (fieldActor (t := TwistTag.D4) σ (Θ β)) :=
    perfectInLayer_of_fixSubgroup_eq hfix_eq.symm hPfix
  have h := LieSemisimple.perfectInLayer_conj (MulAut.conj h₀)⁻¹ _ hPΘ
  rw [← hh₀'] at h
  rwa [show (MulAut.conj h₀)⁻¹ * (MulAut.conj h₀ * β * (MulAut.conj h₀)⁻¹) *
      (MulAut.conj h₀)⁻¹⁻¹ = β by group] at h

end Core

theorem perfectInLayer_trialityD4_outer
    (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpc : p = q.p)
    (hp3 : p ≠ 3)
    {β : MulAut S} (hβ : β ^ p = 1) (hout : ∀ a : S, MulAut.conj a ≠ β) :
    PerfectInLayer β := by
  classical
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by norm_num)
    omega
  obtain ⟨f, hfq⟩ : ∃ f, q.exponent = f := ⟨_, rfl⟩
  have hf : 1 ≤ f := by
    rw [← hfq]
    exact q.exponent_pos
  have hqcard : q.card = p ^ f := by rw [TauCeti.PrimePower.card_def, ← hpc, hfq]
  have hp2' : q.p ≠ 2 := by
    rw [← hpc]
    exact hp2
  haveI : Fact p.Prime := ⟨hp⟩
  have hK₀ : Nat.card (GaloisField p (3 * f)) = (p ^ f) ^ 3 := by
    rw [GaloisField.card p (3 * f) (by omega), ← pow_mul, mul_comm]
  have hσ₀ : ∀ c : GaloisField p (3 * f),
      iterateFrobenius (GaloisField p (3 * f)) p f c = c ^ p ^ f := fun c => by
    rw [iterateFrobenius_def]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Twisted.twistedBridge_trialityD4 q hv hp2'
    (GaloisField p (3 * f)) (by rw [hK₀, hqcard]; rfl)
    (iterateFrobenius (GaloisField p (3 * f)) p f)
    (fun c => by rw [hqcard]; exact hσ₀ c)
  have hmodel : TwistedChevalleyModel S TwistTag.D4 (p ^ f) := by
    unfold TwistedChevalleyModel
    exact ⟨GaloisField p (3 * f), inferInstance, inferInstance, hK₀,
      iterateFrobenius (GaloisField p (3 * f)) p f, hσ₀, ⟨e.trans b.symm⟩⟩
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e₁⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 hp hf hmodel
  have hαp : MulAut.congr e₁ β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hαin : MulAut.congr e₁ β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    rintro ⟨g, hg⟩
    apply hout (e₁.symm g)
    apply (MulAut.congr e₁).injective
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e₁.apply_symm_apply]
    exact hg
  exact LieSemisimple.perfectInLayer_of_congr e₁ β
    (perfectInLayer_graphFixed_outer hp hp5 hf K hK σ hσ hαp hαin)

end CFSG.HardMathSupport.Dickson.DefCharOuter

