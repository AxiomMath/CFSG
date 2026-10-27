module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTrialityGe5Aux
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcInterface
import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExceptionalBase
import CFSG.RankThree.Chevalley.SteinbergCDTrialityTwelveLocalCore
import CFSG.RankThree.PartOne.CTP.SeitzMaxAbstract
public import CFSG.LieType.Chevalley.DiagramCoordinateFixedStructure
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Dickson.I271 (isChevSimple_of_mulEquiv)

section Core


theorem outerCentData_fieldActor_triality {p f' : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hf' : 1 ≤ f') (K : Type) [Field K] [Finite K] (hK : Nat.card K = p ^ (3 * f' * p))
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ p ^ (f' * p)) (δ : K ≃+* K)
    (hδ : ∀ c, δ c = c ^ p ^ (3 * f')) :
    OuterCentData p (fieldActor (t := TwistTag.D4) σ δ) := by
  classical
  have hm3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 hp3
  obtain ⟨hord, -, hk, -, -, -, hmap, hsimple, hnc, -, -, -, -, hcent, -⟩ :=
    CFSG.RankThree.Chevalley.triality_canonical_field_full_centralizer_and_pointwise_kernel hp
      hf' hp.two_le hm3 K hK σ hσ δ hδ
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  set δ₀ := fieldActor (t := TwistTag.D4) σ δ
  haveI := hsimple
  have e3 : ↥(fixSubgroup δ₀) ≃* ↥(trialityFieldImage σ δ) :=
    (Subgroup.equivMapOfInjective _ C.subtype C.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  have hsimE : IsSimpleGroup ↥(fixSubgroup δ₀) := e3.isSimpleGroup
  have hncE : ∃ a b : ↥(fixSubgroup δ₀), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    apply hnc
    intro a b
    have h := hcon (e3.symm a) (e3.symm b)
    apply e3.symm.injective
    rw [map_mul, map_mul]
    exact h
  have hk3 : Nat.card (fixSubfield δ) = (p ^ f') ^ 3 := by rw [hk, ← pow_mul, mul_comm]
  haveI : Finite (fixSubfield δ) := Subtype.finite
  obtain ⟨r, hr, hσr⟩ := exists_cubic_exponent hp hp3 (fixSubfield δ) hk σ hσ
  have hG₀ := chevSimple_graphFixedRootGroup_cubic hp hp2 hf' (fixSubfield δ) hk3
    (fixSubfieldRestrict σ δ) hr fun c => Subtype.ext (hσr c)
  have eJ : graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
      (fixSubfieldRestrict σ δ).toRingHom ≃* ↥(trialityFieldImage σ δ) :=
    Subgroup.equivMapOfInjective _ (baseChangeGL (τ := TwistTag.D4.tag) (fixSubfield δ).subtype)
      (baseChangeGL_injective _)
  have eM : ↥(fixSubgroup δ₀) ≃* graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
      (fixSubfieldRestrict σ δ).toRingHom := e3.trans eJ.symm
  have hchevE : IsChevSimple p ↥(fixSubgroup δ₀) := isChevSimple_of_mulEquiv eM.symm hG₀.1
  have hdvdE : p ∣ Nat.card ↥(fixSubgroup δ₀) := by
    rw [Nat.card_congr eM.toEquiv]
    exact hG₀.2.1
  have hJfix : ∀ j : C, (j : ModGL TwistTag.D4.tag K) ∈ trialityFieldImage σ δ → δ₀ j = j := by
    intro j hj
    have hj' : (j : ModGL TwistTag.D4.tag K) ∈
        (δ₀.toMonoidHom.eqLocus (MonoidHom.id _)).map C.subtype := by
      rw [hmap]
      exact hj
    obtain ⟨x, hx, hxj⟩ := hj'
    have : x = j := Subtype.ext hxj
    subst this
    exact hx
  have hstab : ∀ w : MulAut C, w * δ₀ = δ₀ * w → (∀ x ∈ fixSubgroup δ₀, w x = x) →
      w ∈ Subgroup.zpowers δ₀ := by
    intro w hw hfix
    rw [← hcent]
    refine ⟨Subgroup.mem_centralizer_singleton_iff.2 hw, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨j, hj, rfl⟩
    have hwj : w j = j := hfix j (hJfix j (Subgroup.mem_subgroupOf.1 hj))
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hwj]
  exact OuterCentData.ofSimpleNormal hp
    (SimpleNormalData.ofSimple hsimE hncE hchevE hdvdE)
    (fun _ => cent_of_stabilizer hp hord le_rfl hstab) (fun h3 => absurd h3 hp3)

theorem outerCentData_graphFixed_outer {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    {β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hβ : orderOf β = p)
    (hβin : β ∉ innerAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    OuterCentData p β := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp4 : 3 < p := by
    have := hp.two_le
    omega
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, hcyc, Θ, hΘ, -⟩ := CFSG.RankThree.Chevalley.triality_normal_form_data hp hf K hK σ hσ
  obtain ⟨hηord, hpf, ⟨h₀, hh₀⟩, -⟩ :=
    CFSG.RankThree.Chevalley.triality_noninner_large_prime_field_descent_and_local_core_trivial
      hp hf K hK σ hσ Θ hΘ hp hp4 ⊤ le_top ⟨β, Subgroup.mem_top _⟩ hβin
      (by rw [Subgroup.orderOf_mk]; exact hβ)
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
  have hfix_eq :
      fixSubgroup (fieldActor (t := TwistTag.D4) σ (Θ β)) =
        fixSubgroup (fieldActor (t := TwistTag.D4) σ δc) := by
    have h := CFSG.RankThree.PartOne.CTP.fixedSubgroup_eq_of_zpowers_eq
      (fieldActorHom (t := TwistTag.D4) σ) hzp
    ext x
    exact SetLike.ext_iff.1 h x
  have hK' : Nat.card K = p ^ (3 * f' * p) := by
    rw [hK3, hff']; congr 1; ring
  have hσ' : ∀ c, σ c = c ^ p ^ (f' * p) := fun c => by
    rw [hσ c, hff', mul_comm p f']
  have hδ₀ : OuterCentData p (fieldActor (t := TwistTag.D4) σ δc) :=
    outerCentData_fieldActor_triality hp hp2 hp3 hd K hK' σ hσ' δc hδc
  have hfo : IsOfFinOrder (Θ β) := orderOf_pos_iff.1 (by rw [hηord]; exact hp.pos)
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (Θ β) ^ r = δc := by
    have h1 : δc ∈ Subgroup.zpowers (Θ β) := by
      rw [hzp]
      exact Subgroup.mem_zpowers δc
    exact (Submonoid.mem_powers_iff _ _).1 (hfo.mem_powers_iff_mem_zpowers.2 h1)
  have hpow : fieldActor (t := TwistTag.D4) σ (Θ β) ^ r =
      fieldActor (t := TwistTag.D4) σ δc := by
    rw [← hr]
    exact (map_pow (fieldActorHom (t := TwistTag.D4) σ) (Θ β) r).symm
  have hη₀ : OuterCentData p (fieldActor (t := TwistTag.D4) σ (Θ β)) := by
    refine OuterCentData.of_pow r (by rw [hpow]; exact hδ₀) ?_
    rw [hpow]
    exact hfix_eq.symm
  have hconj : OuterCentData p (MulAut.conj h₀ * β * (MulAut.conj h₀)⁻¹) := by
    rw [hh₀']
    exact hη₀
  exact OuterCentData.of_conj_aut hp (MulAut.conj h₀) hconj

theorem outerCentData_trialityD4_ne_three (S : Type) [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a)
    (idx : TauCeti.ValidLieTypeIndex) (htag : IsExcTrialityD4 idx.1)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group))
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpc : p = idx.1.characteristic)
    (β : MulAut S) (hβ : orderOf β = p) (hout : β ∉ innerAut S) : OuterCentData p β := by
  classical
  clear hS hnc
  obtain ⟨e⟩ := he
  obtain ⟨d, hv⟩ := idx
  cases d with
  | trialityD4 q =>
    have hpq : p = q.p := hpc.trans (TauCeti.LieTypeIndex.characteristic_trialityD4 q)
    obtain ⟨f, hfq⟩ : ∃ f, q.exponent = f := ⟨_, rfl⟩
    have hf : 1 ≤ f := by
      rw [← hfq]
      exact q.exponent_pos
    have hqcard : q.card = p ^ f := by rw [TauCeti.PrimePower.card_def, ← hpq, hfq]
    have hp2' : q.p ≠ 2 := by
      rw [← hpq]
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
    refine OuterCentData.of_congr hp e₁ ?_
    have hαord : orderOf (MulAut.congr e₁ β) = p := by
      rw [MulEquiv.orderOf_eq]
      exact hβ
    have hαin : MulAut.congr e₁ β ∉ innerAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
      rintro ⟨g, hg⟩
      apply hout
      refine ⟨e₁.symm g, ?_⟩
      apply (MulAut.congr e₁).injective
      rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e₁.apply_symm_apply]
      exact hg
    exact outerCentData_graphFixed_outer hp hp2 hp3 hf K hK σ hσ hαord hαin
  | _ => exact htag.elim

end Core

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
