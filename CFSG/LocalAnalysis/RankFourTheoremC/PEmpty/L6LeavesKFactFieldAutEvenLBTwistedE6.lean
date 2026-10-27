module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrderArith
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Descent
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Diag
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Fixed

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Open (StatedLieTag StatedLieAdmissible ordTwistedE6)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.HardMathSupport.Lang.Coordinator
  (card_fixedSubgroup_eq_of_intertwine card_fixedSubgroup_congr congr_mem_inner_iff
    exists_subfield_card_of_card_eq twisted_E6_field_descent_data_of_prime_order
    mem_inner_of_mem_inn_sup_diag)

theorem ordTwistedE6_dvd_card_fixedSubgroup_fieldActor
    {ℓ d p : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d) (hp : p.Prime) (hp2 : p ≠ 2) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = ℓ ^ (2 * (d * p))) (σ ε : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ ℓ ^ (d * p)) (hε : ∀ c, ε c = c ^ ℓ ^ (d * (p + 1))) :
    ordTwistedE6 (ℓ ^ d) ∣ Nat.card (fixedSubgroup (fieldActor (t := TwistTag.E6) σ ε)) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have h2dp : 1 ≤ 2 * (d * p) := by have := Nat.mul_pos hd hp.pos; omega
  have : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ h2dp hK
  obtain ⟨S, hS⟩ := exists_subfield_card_of_card_eq hℓ hd hp.pos K hK
  have hS2 : Nat.card S = (ℓ ^ d) ^ 2 := by rw [hS, ← pow_mul, mul_comm]
  have : Finite S := Subtype.finite
  have : Fintype S := Fintype.ofFinite S
  have : CharP S ℓ := inferInstance
  have hSpow : ∀ (c : S) (n : ℕ), (c : K) ^ (ℓ ^ (2 * d)) ^ n = c := fun c n => by
    have h := FiniteField.pow_card_pow n c
    rw [← Nat.card_eq_fintype_card, hS] at h
    have h2 := congrArg (fun x : S => (x : K)) h
    simpa only [SubmonoidClass.coe_pow] using h2
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
  let ι : S →+* K := S.subtype
  let σ₀ : S →+* S := iterateFrobenius S ℓ d
  have hσ₀ : ∀ c, σ₀ c = c ^ ℓ ^ d := fun c => rfl
  have hσι : ∀ c : S, σ.toRingHom (ι c) = ι (σ₀ c) := fun c => by
    change σ (c : K) = ((c ^ ℓ ^ d : S) : K)
    rw [hσ, SubmonoidClass.coe_pow]
    have h1 : ℓ ^ (d * p) = ℓ ^ d * (ℓ ^ (2 * d)) ^ m := by
      rw [← pow_mul, ← pow_add]
      congr 1
      rw [hm]
      ring
    rw [h1, pow_mul', hSpow c m]
  have hεS : ∀ c : S, ε (c : K) = c := fun c => by
    rw [hε]
    have h1 : ℓ ^ (d * (p + 1)) = (ℓ ^ (2 * d)) ^ (m + 1) := by
      rw [← pow_mul]
      congr 1
      rw [hm]
      ring
    rw [h1]
    exact hSpow c (m + 1)
  have hει : ε.toRingHom.comp ι = ι := RingHom.ext fun c => hεS c
  have hσ₀surj : Function.Surjective σ₀ := Finite.surjective_of_injective σ₀.injective
  have hJC : (graphFixedRootGroup TwistTag.E6 S σ₀).map (baseChangeGL ι) ≤
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    map_baseChangeGL_graphFixedRootGroup_le (t := TwistTag.E6) (σ := σ₀) (Fr := σ.toRingHom)
      (ι := ι) hσ₀surj hσι
  set C := graphFixedRootGroup TwistTag.E6 K σ.toRingHom with hC
  set H : Subgroup (ModGL TwistTag.E6.tag K) :=
    (fixedSubgroup (fieldActor (t := TwistTag.E6) σ ε)).map C.subtype with hH
  have hJH : (graphFixedRootGroup TwistTag.E6 S σ₀).map (baseChangeGL ι) ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    have hxC : baseChangeGL ι x ∈ C := hJC ⟨x, hx, rfl⟩
    refine ⟨⟨baseChangeGL ι x, hxC⟩, ?_, rfl⟩
    show fieldActor σ ε ⟨baseChangeGL ι x, hxC⟩ = ⟨baseChangeGL ι x, hxC⟩
    refine Subtype.ext ?_
    rw [coe_fieldActor]
    show Units.map (entrywiseHom ε.toRingHom) (baseChangeGL ι x) = baseChangeGL ι x
    rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL, hει]
  have hcardJ : Nat.card ((graphFixedRootGroup TwistTag.E6 S σ₀).map (baseChangeGL ι)) =
      ordTwistedE6 (ℓ ^ d) := by
    rw [Subgroup.card_map_of_injective (baseChangeGL_injective ι)]
    exact CFSG.ClassicalInvolution.card_graphFixedRootGroup_E6 hℓ hd hS2 σ₀ hσ₀
  have hcardH : Nat.card H = Nat.card (fixedSubgroup (fieldActor (t := TwistTag.E6) σ ε)) :=
    Subgroup.card_map_of_injective C.subtype_injective
  rw [← hcardJ, ← hcardH]
  exact Subgroup.card_dvd_of_le hJH

theorem ordTwistedE6_dvd_card_fixed_of_rootGroup
    {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2) (K : Type) [Field K]
    [Finite K] (hcard : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hdiv : ¬ p ∣ Nat.gcd 3 (ℓ ^ f + 1)) (β : MulAut (twistedE6RootGroup K σ))
    (hβp : β ^ p = 1) (hβout : β ∉ twistedE6Inn K σ) :
    ∃ d : ℕ, f = p * d ∧ ordTwistedE6 (ℓ ^ d) ∣ Nat.card (fixedSubgroup β) := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -, hcube, -⟩, -, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hcard σ hσ
  have hη1 : Θ β ≠ 1 := by
    intro h1
    have hmem : β ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
      rw [← hker, MonoidHom.mem_ker]
      exact h1
    exact hβout (mem_inner_of_mem_inn_sup_diag hp hcard hσ hdiv hcube hβp hmem)
  have hK2 : Nat.card K = ℓ ^ (2 * f) := by rw [hcard, ← pow_mul, mul_comm]
  obtain ⟨d, hd, hd0, r, s, T, ε, -, hε, hrs, ψ, hψ, -⟩ :=
    twisted_E6_field_descent_data_of_prime_order hℓ hf K hK2 σ hσ Θ hΘ hp hp2 β hβp hη1
  refine ⟨d, hd, ?_⟩
  have hle : fixedSubgroup (β ^ r) ≤ fixedSubgroup β := by
    intro x hx
    have hx' : (β ^ r) x = x := hx
    have hpow : ∀ n : ℕ, ((β ^ r) ^ n) x = x := by
      intro n
      induction n with
      | zero => rfl
      | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, hx']
    show β x = x
    calc β x = ((β ^ r) ^ s) x := by rw [hrs]
      _ = x := hpow s
  have hconj : Nat.card (fixedSubgroup (β ^ r)) =
      Nat.card (fixedSubgroup (fieldActor (t := TwistTag.E6) σ ε)) :=
    card_fixedSubgroup_eq_of_intertwine (ψ : twistedE6RootGroup K σ ≃* twistedE6RootGroup K σ)
      (β ^ r) _ fun x => by
        have h := congrArg (fun g : MulAut (twistedE6RootGroup K σ) => g (ψ x)) hψ
        simpa [MulAut.mul_apply] using h.symm
  have hσ' : ∀ c, σ c = c ^ ℓ ^ (d * p) := fun c => by rw [hσ, hd, mul_comm]
  have hdvd := ordTwistedE6_dvd_card_fixedSubgroup_fieldActor hℓ hd0 hp hp2 K
    (by rw [hK2, hd, show 2 * (p * d) = 2 * (d * p) by ring]) σ ε hσ' hε
  exact hdvd.trans (hconj ▸ Subgroup.card_dvd_of_le hle)

theorem fixedLowerBoundAt_twistedE6
    : FixedLowerBoundAt .twistedE6 := by
  intro K _ _ n ℓ f f₀ p hadm hmodel ht hp hp5 hpK hdiv hf α hαp hαin
  obtain ⟨hℓ, hf1, hn⟩ := hadm
  have hchev : ChevalleyExceptionalModel K .twistedE6 ℓ f := by
    rcases hmodel with ⟨ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact h
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hdiv' : ¬ p ∣ Nat.gcd 3 (ℓ ^ f + 1) := hdiv
  have hp2 : p ≠ 2 := by omega
  obtain ⟨K', _, _, σ, hcard, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_E6 hchev
  set β : MulAut (twistedE6RootGroup K' σ) := MulAut.congr e α with hβdef
  have hβp : β ^ p = 1 := by rw [hβdef, ← map_pow, hαp, map_one]
  have hβout : β ∉ twistedE6Inn K' σ := fun hin => hαin ((congr_mem_inner_iff e α).mp hin)
  obtain ⟨d, hd, hdvd⟩ :=
    ordTwistedE6_dvd_card_fixed_of_rootGroup hℓ hf1 hp hp2 K' hcard σ hσ hdiv' β hβp hβout
  have hf₀ : f₀ = d := Nat.eq_of_mul_eq_mul_left hp.pos (hf.symm.trans hd)
  have hf0 : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h | h
    · rw [h, mul_zero] at hf
      omega
    · exact h
  have hn0 : n = 0 := hn
  subst hn0
  rw [← card_fixedSubgroup_congr e α, hf₀]
  rw [hf₀] at hf0
  have hdvd' := CFSG.ComponentClassification.CatLeafProof.lieOrderDivisor_dvd_numerator
    (t := .twistedE6) (n := 0) (p := ℓ) (f := d) ⟨hℓ, hf0, rfl⟩
  have hnum : ordTwistedE6 (ℓ ^ d) * lieOrderDivisor .twistedE6 0 (ℓ ^ d) =
      lieOrderNumerator .twistedE6 0 (ℓ ^ d) := Nat.div_mul_cancel hdvd'
  rw [← hnum, mul_comm]
  exact Nat.mul_dvd_mul_left _ hdvd

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
