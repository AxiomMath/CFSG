module

public import CFSG.LocalAnalysis.GLTheoremA.Lemma48
public import CFSG.HardMathSupport.Solomon.Coordinator.AlphaFunctor

public section

namespace CFSG.LocalAnalysis.GLTheoremA.P51

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_le_centModSubgroup_of_coprime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {J D Q : Subgroup G} (hD : IsPGroup p D) (hQ : IsPGroup 2 Q)
    (hDQ : D ≤ Subgroup.normalizer (Q : Set G))
    (hRJ : (⁅D, Q⁆ : Subgroup G) ≤ Subgroup.normalizer (J : Set G))
    (hDJ : D ≤ centModSubgroup p J) :
    (⁅D, Q⁆ : Subgroup G) ≤ centModSubgroup p J := by
  have hcop : Nat.Coprime (Nat.card D) (Nat.card Q) := by
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hD
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hQ
    rw [hm, hn]
    exact Nat.Coprime.pow m n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hR : ⁅⁅D, Q⁆, D⁆ = (⁅D, Q⁆ : Subgroup G) := by
    have h1 := CFSG.HardMathSupport.Solomon.Coordinator.coprime_commutator_commutator_eq' hDQ hcop
    rw [Subgroup.commutator_comm Q D] at h1
    exact h1
  have hRD : ⁅⁅D, Q⁆, D⁆ ≤ centModSubgroup p J := by
    rw [Subgroup.commutator_le]
    intro r hr d hd
    rw [commutatorElement_def]
    have hrN : r ∈ Subgroup.normalizer (centModSubgroup p J : Set G) :=
      normalizer_le_normalizer_centModSubgroup p J (hRJ hr)
    have hdJ : d ∈ centModSubgroup p J := hDJ hd
    have hconj : r * d * r⁻¹ ∈ centModSubgroup p J :=
      (Subgroup.mem_normalizer_iff.mp hrN d).mp hdJ
    exact Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ hdJ)
  exact (le_of_eq hR.symm).trans hRD

end CFSG.LocalAnalysis.GLTheoremA.P51
