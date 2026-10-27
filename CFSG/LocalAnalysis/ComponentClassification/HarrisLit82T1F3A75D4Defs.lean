module

public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG.LieType.Universal.Spin
open scoped MatrixGroups

@[expose] def Spin8CentreFixedOutAbelian : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (f : ℕ), Nat.card K = 3 ^ f →
    ∀ α β : MulAut (spinGroup (quadPlus 4 K)),
      (∀ c ∈ Subgroup.center (spinGroup (quadPlus 4 K)), α c = c) →
      (∀ c ∈ Subgroup.center (spinGroup (quadPlus 4 K)), β c = c) →
      α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : spinGroup (quadPlus 4 K) →* MulAut _).range

@[expose] def Harris82Lemma413Three : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (f : ℕ), Nat.card K = 3 ^ f →
    ∀ x : spinGroup (quadPlus 4 K), orderOf x = 2 →
    x ∉ Subgroup.center (spinGroup (quadPlus 4 K)) →
    ∃ J : ↥(Subgroup.center (spinGroup (quadPlus 4 K))) → Subgroup (spinGroup (quadPlus 4 K)),
      (∀ c, J c ≤ Subgroup.centralizer {x}) ∧
      (∀ c, Nonempty (↥(J c) ≃* SL(2, K))) ∧
      (∀ c, x * (c : spinGroup (quadPlus 4 K)) ∈ J c) ∧
      (∀ c d, c ≠ d → ∀ a ∈ J c, ∀ b ∈ J d, a * b = b * a) ∧
      (∀ c, ((J c).subgroupOf (Subgroup.centralizer {x})).IsSubnormal) ∧
      ∀ (β : MulAut (spinGroup (quadPlus 4 K))) (c d : ↥(Subgroup.center _)),
        β (x * (c : spinGroup (quadPlus 4 K))) = x * (d : spinGroup (quadPlus 4 K)) →
          (J c).map β.toMonoidHom = J d

end CFSG.ComponentClassification.HarrisLit.T1
