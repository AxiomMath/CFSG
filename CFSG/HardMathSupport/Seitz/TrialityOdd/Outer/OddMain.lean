module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Outer.OddCore
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Outer.OddField
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Outer.Reduction

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.SEITZ7 CFSG.RankThree.PartOne.SEITZ2 CFSG.RankThree.PartOne
open CFSG.LocalAnalysis.ComponentInitial (finite_field_automorphism_fixed_field_cardinality)


section Pair

variable {K : Type} [Field K] [Finite K]

theorem pair_odd {ℓ f0 p : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hf0 : 1 ≤ f0) (hK : Nat.card K = (ℓ ^ (f0 * p)) ^ 3) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ ℓ ^ (f0 * p)) {δ : K ≃+* K} (hδ : ∀ c, δ c = c ^ ℓ ^ (3 * f0))
    (g : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hne : (fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ)).map
        (MulAut.conj g).toMonoidHom ≠ fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ)) :
    Subgroup.closure ((fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∪
      ((fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ)).map (MulAut.conj g).toMonoidHom :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) = ⊤ := by
  have hK' : Nat.card K = ℓ ^ (3 * f0 * p) := by
    rw [hK, ← pow_mul]
    congr 1
    ring
  have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ (k := 3 * f0 * p) (Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)) hK'
  have hr3 : 3 ≤ ℓ := by
    have := hℓ.two_le
    omega
  obtain ⟨k, F0, hfix, hrat, hF0, hcard, hspan⟩ := field_data_odd hℓ hp hp5 hf0 hK' hσ hδ
  have hσq : ∀ c, σ.toRingHom c = c ^ (ℓ ^ (f0 * p)) := hσ
  have hq2 : 2 ≤ ℓ ^ (f0 * p) := by
    calc 2 ≤ ℓ := hℓ.two_le
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ (f0 * p) := Nat.pow_le_pow_right (by omega) (by nlinarith)
  have hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c := sigma_three_of_card hK hσq
  have hC0 : graphFixedRootGroup TwistTag.D4 K σ.toRingHom =
      (twistedGroup σ.toRingHom).map (adjointGroup d4 K).subtype :=
    (finite_fixed_root_group_perfect TwistTag.D4 hℓ (f := f0 * p) (by nlinarith) K hK
      σ.toRingHom hσq).2.2.1.symm.trans
      (commutator_twistedFixedGroup_eq_map σ.toRingHom hq2 hK hσq)
  have S : D4SetupO σ.toRingHom δ.toRingHom k F0 p :=
    { hσ3 := hσ3
      hcomm := fun c => by
        show δ (σ c) = σ (δ c)
        rw [hσ, hσ, map_pow]
      hfix := hfix
      rat := hrat
      hF0 := hF0
      prime := hp
      ne2 := by omega
      card := hcard
      span := hspan
      stab := SEITZ8.stab_of_bridge σ δ hC0 }
  have hg : SEITZ8.eGamma hC0 g ∉ SEITZ8.Rg σ.toRingHom δ.toRingHom := fun h =>
    hne (SEITZ8.map_conj_eq_of_mem ((SEITZ8.mem_fixedSubgroup_iff σ δ hC0 g).2 h))
  exact SEITZ8.closure_transport (SEITZ8.eGamma hC0) _ _ (SEITZ8.mem_fixedSubgroup_iff σ δ hC0) g
    (closure_eq_top_odd hr3 S (SEITZ8.eGamma hC0 g) hg)

end Pair

section Wrapper


theorem subfieldPairD4Odd_proof : SubfieldPairD4Odd := by
  intro ℓ f hℓ hℓ2 hf K _ _ hK σ hσ δ p hp hp5 hδ g hne
  classical
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
  obtain ⟨δc, hδcdef⟩ : ∃ δc, φ ^ (3 * f') = δc := ⟨_, rfl⟩
  have hδc : ∀ c, δc c = c ^ ℓ ^ (3 * f') := fun c => by
    rw [← hδcdef]
    exact ringAut_pow_apply_of_frobenius hφ _ c
  have hδcord : orderOf δc = p := by
    rw [← hδcdef, orderOf_pow_of_dvd (by omega) (by rw [hφord, hff']; exact ⟨p, by ring⟩),
      hφord, hff', show 3 * (p * f') = 3 * f' * p by ring, Nat.mul_div_cancel_left p (by omega)]
  have hzp : Subgroup.zpowers δ = Subgroup.zpowers δc :=
    zpowers_ringEquiv_eq_of_orderOf hℓ hf3 hK3 hδ hδcord
  have hfix : fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ) =
      fixedSubgroup (fieldActor (t := TwistTag.D4) σ δc) :=
    fixedSubgroup_eq_of_zpowers_eq (fieldActorHom (t := TwistTag.D4) σ) hzp
  left
  rw [hfix] at hne ⊢
  have hKe : Nat.card K = (ℓ ^ (f' * p)) ^ 3 := by rw [hK, hff', mul_comm]
  have hσe : ∀ c, σ c = c ^ ℓ ^ (f' * p) := fun c => by rw [hσ, hff', mul_comm]
  exact pair_odd hℓ hℓ2 hp hp5 hf'1 hKe hσe hδc g hne

end Wrapper

end CFSG.HardMathSupport.Seitz.TrialityOdd
