module

public import CFSG.HardMathSupport.Dickson.Bal207.FCBridge
import CFSG.RankThree.PartOne.KC.UnitaryRegularUnipotentLift

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.HardMathSupport.Dickson.I271 CFSG.LocalAnalysis.GLTheoremB

section Cover

variable {J P : Type} [Group J] [Group P]

theorem ker_eq_center_of_surjective (φ : J →* P) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center J) (hZ : Subgroup.center P = ⊥) :
    φ.ker = Subgroup.center J := by
  refine le_antisymm hker fun z hz => ?_
  have hc : φ z ∈ Subgroup.center P := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨j, rfl⟩ := hφ y
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz) j]
  rw [hZ, Subgroup.mem_bot] at hc
  exact hc

@[expose] noncomputable def centerQuotientEquivOfHom (φ : J →* P) (hφ : Function.Surjective φ)
    (hker : φ.ker = Subgroup.center J) : (J ⧸ Subgroup.center J) ≃* P :=
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)

theorem centerQuotientEquivOfHom_mk (φ : J →* P) (hφ : Function.Surjective φ)
    (hker : φ.ker = Subgroup.center J) (j : J) :
    centerQuotientEquivOfHom φ hφ hker (QuotientGroup.mk j) = φ j :=
  rfl

end Cover

variable {ℓ f : ℕ} {K : Type} [Field K] {n : ℕ} {X : Type} [Group X]

theorem isStronglyLocallyOneBalanced_of_omegaOne_hom [Finite X] {J B : Subgroup X} {a : X}
    (hJ : CFSG.Open.IsQuasisimple ↥J) (h : UnitaryFieldData ℓ f K) (hℓ : ℓ = 2)
    (hf : f = 1 ∨ f = 3) (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (φ : ↥J →* primeFormP h (oneGram K n)) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center ↥J) {D : Subgroup (GL (Fin n) K)} (hD : IsOmegaOneTorus D)
    (hBD : ∀ A : primeFormUnitary h (oneGram K n), (A : GL (Fin n) K) ∈ D →
      ∃ (b : X) (hb : b ∈ Subgroup.normalizer (J : Set X)), b ∈ B ∧
        ∀ j : ↥J, φ (J.normalizerMonoidHom ⟨b, hb⟩ j) = primeFormConjHom h _ A (φ j)) :
    IsStronglyLocallyOneBalanced 3 B a J := by
  have hZ : Subgroup.center (primeFormP h (oneGram K n)) = ⊥ :=
    CFSG.RankThree.PartOne.KCUnitaryRegular.center_primeFormP_eq_bot h (C := 1)
      CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one hn hne
  have hkerZ := ker_eq_center_of_surjective φ hφ hker hZ
  refine isStronglyLocallyOneBalanced_of_omegaOne hJ h hℓ hf hn hne
    (centerQuotientEquivOfHom φ hφ hkerZ) hD fun A hA => ?_
  obtain ⟨b, hb, hbB, hc⟩ := hBD A hA
  refine ⟨b, hb, hbB, MulEquiv.ext fun y => ?_⟩
  obtain ⟨j, rfl⟩ := hφ y
  have he : (centerQuotientEquivOfHom φ hφ hkerZ).symm (φ j) = QuotientGroup.mk j :=
    (MulEquiv.symm_apply_eq _).2 rfl
  show centerQuotientEquivOfHom φ hφ hkerZ
    (actHom J ⟨b, hb⟩ ((centerQuotientEquivOfHom φ hφ hkerZ).symm (φ j))) = _
  rw [he, actHom_mk, centerQuotientEquivOfHom_mk]
  exact hc j

end CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

end
