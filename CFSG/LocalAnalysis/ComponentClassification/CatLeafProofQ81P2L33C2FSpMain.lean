module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2FSpInner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2FSpField

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {r : ℕ} {K : Type} [Field K]

theorem hasWit_psp {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hr : 3 ≤ r)
    {v : MulAut (StatedProj (StatedSp r K))} (hv : orderOf v = 2) : HasWit v := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : NeZero r := ⟨by omega⟩
  have hvv : v * v = 1 := by rw [← sq, ← hv, pow_orderOf_eq_one]
  have hmem : v ∈ spSemilinearAutGroup r K := by
    rw [(SymplecticHigher.automorphism_generation hr).1]
    exact Subgroup.mem_top v
  obtain ⟨g, φ, hvg⟩ := exists_eq_spInner_mul_fieldAut hmem
  by_cases hφ : φ = 1
  · rw [hφ, map_one, mul_one] at hvg
    subst hvg
    have hgg : g * g = 1 := spInner_injective (by rw [map_mul, hvv, map_one])
    have hg1 : g ≠ 1 := by
      rintro rfl
      rw [map_one, orderOf_one] at hv
      omega
    exact hasWit_inner_sp hr hgg hg1
  · exact hasWit_field_sp hf hK (by omega) hvv g hφ hvg

theorem twoNilpFor_psp_three :
    TwoNilpFor fun Y _ => ∃ n f : ℕ, 3 ≤ n ∧ StatedClassicalModel Y .PSp n 2 f := by
  refine twoNilpFor_of_hasWit fun Y _ _ hY _ a ha => Or.inr ?_
  obtain ⟨n, f, hn, ⟨-, hf, -, -⟩, K, _, _, hK, ⟨θ⟩⟩ := hY
  have hw := (hasWit_psp hf hK hn (v := MulAut.congr θ a)
    (by rw [MulEquiv.orderOf_eq]; exact ha)).congr θ.symm
  have e : MulAut.congr θ.symm (MulAut.congr θ a) = a := by
    ext y
    simp [MulAut.congr_apply]
  rwa [e] at hw

end CFSG.ComponentClassification.HarrisLit.L33.C2
