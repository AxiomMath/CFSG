module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25G1
public import CFSG.ClassicalInvolution.Asc77.AscFusionR8
public import CFSG.ClassicalInvolution.AschTight.S19COrd
public import CFSG.ClassicalInvolution.Q3.Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516.Four

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Disconnected.AschTight

variable {X : Type} [Group X] [Finite X]

theorem false_of_isClassicalMember3 {t : X} (hEC : OddEC t) {L : Subgroup X}
    (hL : IsClassicalMember3 L t) : False := by
  obtain ⟨N, hNC, hNodd, hNnorm, hNall⟩ := hEC
  have hLC : L ≤ Subgroup.centralizer ({t} : Set X) := isSubnormal_le hL.subnormal
  set S : Subgroup X := N ⊓ L with hS
  have hSL : S ≤ L := inf_le_right
  have hSodd : Odd (Nat.card S) :=
    hNodd.of_dvd_nat (Subgroup.card_dvd_of_le (inf_le_left : S ≤ N))
  have hnorm : L ≤ Subgroup.normalizer (S : Set X) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g ∈ L, ∀ m ∈ S, g * m * g⁻¹ ∈ S := fun g hg m hm =>
      ⟨hNnorm g (hLC hg) m hm.1, L.mul_mem (L.mul_mem hg (hSL hm)) (L.inv_mem hg)⟩
    intro m
    refine ⟨fun hm => key g hg m hm, fun hm => ?_⟩
    have := key g⁻¹ (L.inv_mem hg) _ hm
    simpa [mul_assoc] using this
  have hSO : S ≤ Balance.oddCoreIn L := Balance.le_oddCoreIn_of_normalizes hSL hnorm hSodd
  obtain ⟨e⟩ := hL.nonempty_equiv
  obtain ⟨x, hx3, hx1⟩ : ∃ x : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), x * x * x = 1 ∧ x ≠ 1 := by
    decide +kernel
  obtain ⟨ℓ, hℓ⟩ := QuotientGroup.mk_surjective (e.symm x)
  have hℓ3 : ℓ * ℓ * ℓ ∈ classicalInvolutionOddCore L := by
    rw [← QuotientGroup.eq_one_iff]
    have : e.symm (x * x * x) = 1 := by rw [hx3, map_one]
    rw [map_mul, map_mul, ← hℓ] at this
    simpa using this
  have hOdd : Odd (Nat.card (classicalInvolutionOddCore L)) :=
    CFSG.ComponentClassification.OddCore.odd_card L
  have hpow : ℓ ^ (3 * Nat.card (classicalInvolutionOddCore L)) = 1 := by
    have h1 := pow_card_eq_one' (G := classicalInvolutionOddCore L) (x := ⟨ℓ * ℓ * ℓ, hℓ3⟩)
    have h2 := congrArg (Subtype.val : ↥(classicalInvolutionOddCore L) → ↥L) h1
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h2
    rw [pow_mul, pow_three']
    exact h2
  have hord : Odd (orderOf (ℓ : X)) := by
    have hd : orderOf ℓ ∣ 3 * Nat.card (classicalInvolutionOddCore L) := orderOf_dvd_of_pow_eq_one hpow
    have hodd3 : Odd (3 * Nat.card (classicalInvolutionOddCore L)) := Odd.mul (by decide) hOdd
    rw [Subgroup.orderOf_coe]
    exact hodd3.of_dvd_nat hd
  have hmemC : (ℓ : X) ∈ Subgroup.centralizer ({t} : Set X) := hLC ℓ.2
  have hmemN := hNall _ hmemC hord
  have hmemO : (ℓ : X) ∈ Balance.oddCoreIn L := hSO ⟨hmemN, ℓ.2⟩
  obtain ⟨y, hy, hyℓ⟩ := hmemO
  have : y = ℓ := Subtype.ext hyℓ
  rw [this] at hy
  have h1 : (QuotientGroup.mk ℓ : L ⧸ classicalInvolutionOddCore L) = 1 :=
    (QuotientGroup.eq_one_iff ℓ).mpr hy
  rw [h1] at hℓ
  exact hx1 (by simpa using congrArg e hℓ.symm)

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516.Four
