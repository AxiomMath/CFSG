module

public import CFSG.HardMathSupport.Solomon.Coordinator.ON25Layer

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open
open scoped commutatorElement

theorem on25_quasi_of_central_surj {K K' : Type} [Group K] [Finite K] [Group K']
    (hq : CFSG.Open.IsQuasisimple K) (hZ : IsPGroup 3 (Subgroup.center K))
    (h3 : 3 ∣ Nat.card (K ⧸ Subgroup.center K)) (ρ : K →* K')
    (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ Subgroup.center K) :
    CFSG.Open.IsQuasisimple K' ∧ IsPGroup 3 (Subgroup.center K') ∧ 3 ∣ Nat.card K' := by
  haveI : Finite K' := Finite.of_surjective ρ hρ
  have hp : Nat.Prime 3 := Nat.prime_three
  have hperf : (⁅(⊤ : Subgroup K'), ⊤⁆ : Subgroup K') = ⊤ := by
    have h1 := Subgroup.map_commutator (f := ρ) (⊤ : Subgroup K) ⊤
    have e : (⁅(⊤ : Subgroup K), ⊤⁆ : Subgroup K) = ⊤ := hq.1
    rw [e, Subgroup.map_top_of_surjective ρ hρ] at h1
    exact h1.symm
  let σ : K →* K' ⧸ Subgroup.center K' := (QuotientGroup.mk' (Subgroup.center K')).comp ρ
  have hσ : Function.Surjective σ := (QuotientGroup.mk'_surjective _).comp hρ
  have hZN : Subgroup.center K ≤ σ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    show QuotientGroup.mk' (Subgroup.center K') (ρ z) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    intro y
    obtain ⟨k, rfl⟩ := hρ y
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz k).symm]
  rcases on25_normal_le_center_or_top hq σ.ker with hle | htop
  · have hN : σ.ker = Subgroup.center K := le_antisymm hle hZN
    have e : (K ⧸ Subgroup.center K) ≃* (K' ⧸ Subgroup.center K') :=
      (QuotientGroup.quotientMulEquivOfEq hN.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective σ hσ)
    have hsimple : IsSimpleGroup (K' ⧸ Subgroup.center K') := by
      haveI := hq.2
      exact e.symm.isSimpleGroup
    have hcardq : Nat.card (K' ⧸ Subgroup.center K') = Nat.card (K ⧸ Subgroup.center K) :=
      (Nat.card_congr e.toEquiv).symm
    have hKK : Nat.card (K ⧸ Subgroup.center K) * Nat.card (Subgroup.center K) = Nat.card K := by
      rw [← Subgroup.card_eq_card_quotient_mul_card_subgroup]
    have hKK' : Nat.card (K' ⧸ Subgroup.center K') * Nat.card (Subgroup.center K') =
        Nat.card K' := by rw [← Subgroup.card_eq_card_quotient_mul_card_subgroup]
    have hkerK := Subgroup.card_ker_mul_card_of_surjective (f := ρ) hρ
    have hdiv : Nat.card (Subgroup.center K') ∣ Nat.card (Subgroup.center K) := by
      refine ⟨Nat.card ρ.ker, ?_⟩
      have h1 : Nat.card (K ⧸ Subgroup.center K) * Nat.card (Subgroup.center K) =
          Nat.card (K ⧸ Subgroup.center K) *
            (Nat.card (Subgroup.center K') * Nat.card ρ.ker) := by
        rw [hKK, ← hkerK, ← hKK', hcardq]
        ring
      have hpos : 0 < Nat.card (K ⧸ Subgroup.center K) := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_left hpos h1
    obtain ⟨k, hk⟩ := hZ.exists_card_eq
    refine ⟨⟨hperf, hsimple⟩, ?_, ?_⟩
    · obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 (hk ▸ hdiv)
      exact IsPGroup.of_card hi
    · rw [← hKK', hcardq]
      exact Dvd.dvd.mul_right h3 _
  · exfalso
    have hcen : ∀ k : K, ρ k ∈ Subgroup.center K' := by
      intro k
      have : k ∈ σ.ker := by rw [htop]; exact Subgroup.mem_top k
      rw [MonoidHom.mem_ker] at this
      exact (QuotientGroup.eq_one_iff _).1 this
    have hcomm : ∀ x y : K', x * y = y * x := by
      intro x y
      obtain ⟨k, rfl⟩ := hρ x
      exact (Subgroup.mem_center_iff.1 (hcen k) y).symm
    have h1 : (⁅(⊤ : Subgroup K'), ⊤⁆ : Subgroup K') ≤ ⊥ :=
      Subgroup.commutator_le.2 fun x _ y _ => by
        rw [Subgroup.mem_bot]
        exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm x y)
    have h2 : (⊤ : Subgroup K') = ⊥ := by
      rw [← hperf]
      exact le_bot_iff.1 h1
    have htriv : ∀ k : K, ρ k = 1 := by
      intro k
      have : ρ k ∈ (⊤ : Subgroup K') := Subgroup.mem_top _
      rw [h2, Subgroup.mem_bot] at this
      exact this
    have hKz : (⊤ : Subgroup K) ≤ Subgroup.center K := fun k _ => hker (MonoidHom.mem_ker.2 (htriv k))
    haveI := hq.2
    have : Subsingleton (K ⧸ Subgroup.center K) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      rw [QuotientGroup.eq]
      exact (Subgroup.center K).mul_mem ((Subgroup.center K).inv_mem (hKz (Subgroup.mem_top a)))
        (hKz (Subgroup.mem_top b))
    exact not_subsingleton (K ⧸ Subgroup.center K) this

end CFSG.HardMathSupport.Solomon.Coordinator
