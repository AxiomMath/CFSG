module

public import CFSG.LieType.Universal.Unitary.BinaryModel.FixedLine

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

open Matrix CFSG.LieType.SpecialLinear.ExteriorModel CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} {k : Type} [Field k] [CharP k 2]

theorem sum_two_pow_mul_bdeg {m : ℕ} (ε : Fin f → Finset (Fin m)) :
    ∑ p : Fin f × Fin m, 2 ^ (p.1 : ℕ) * bdeg ε p =
      ∑ i : Fin f, 2 ^ (i : ℕ) * ∑ j ∈ ε i, (j : ℕ) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ ε i)]
  have h0 : ∑ j ∈ Finset.univ.filter (fun j => j ∉ ε i), 2 ^ (i : ℕ) * bdeg ε (i, j) = 0 :=
    Finset.sum_eq_zero fun j hj => by
      rw [bdeg, if_neg (Finset.mem_filter.mp hj).2, mul_zero]
  rw [h0, add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
  exact Finset.sum_congr rfl fun j hj => by rw [bdeg, if_pos hj]

theorem suRep_scalar_bTop (φ₀ : K →+* k) {m : ℕ} (ε : Fin f → Finset (Fin m)) {c : Kˣ}
    (hc : GeneralLinearGroup.scalar (Fin m) c ∈ SU (unitaryInvolution K 2 f) m) :
    suRep φ₀ m ε ⟨_, hc⟩ (bTop ε) =
      φ₀ (c : K) ^ (∑ i : Fin f, 2 ^ (i : ℕ) * ∑ j ∈ ε i, (j : ℕ)) • bTop ε := by
  have hmat : ∀ r : Fin f,
      (suTwist φ₀ f m ⟨_, hc⟩ r : Matrix (Fin m) (Fin m) k) =
        diagonal fun _ => φ₀ (c : K) ^ 2 ^ (r : ℕ) := by
    intro r
    rw [coe_suTwist_apply, SUExtras.mat_apply]
    change (Matrix.scalar (Fin m) (c : K)).map (suFrob φ₀ f r) = _
    rw [Matrix.scalar_apply, diagonal_map (map_zero _)]
    congr 1
    funext _
    rw [suFrob, RingHom.comp_apply, iterateFrobenius_def, map_pow]
  have hvec : bMat ε (fun r => (suTwist φ₀ f m ⟨_, hc⟩ r : Matrix (Fin m) (Fin m) k)) *ᵥ bvec ε =
      φ₀ (c : K) ^ (∑ i : Fin f, 2 ^ (i : ℕ) * ∑ j ∈ ε i, (j : ℕ)) • bvec ε := by
    simp only [hmat]
    rw [bMat_diagonal_mulVec_bvec, ← sum_two_pow_mul_bdeg, ← Finset.prod_pow_eq_pow_sum]
    congr 1
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [Finset.prod_const, Set.powersetCard.card_eq, ← pow_mul]
  rw [suRep, MonoidHom.comp_apply, bTop, bRep_mk, ← Submodule.Quotient.mk_smul]
  congr 1
  exact Subtype.ext hvec

theorem orderOf_dvd_of_suRep_scalar_eq_one (φ₀ : K →+* k) {m : ℕ} (ε : Fin f → Finset (Fin m))
    {c : Kˣ} (hc : GeneralLinearGroup.scalar (Fin m) c ∈ SU (unitaryInvolution K 2 f) m)
    (h1 : suRep φ₀ m ε ⟨_, hc⟩ = 1) :
    orderOf c ∣ ∑ i : Fin f, 2 ^ (i : ℕ) * ∑ j ∈ ε i, (j : ℕ) := by
  have h := suRep_scalar_bTop φ₀ ε hc
  rw [h1, Module.End.one_apply] at h
  have hpow : φ₀ (c : K) ^ (∑ i : Fin f, 2 ^ (i : ℕ) * ∑ j ∈ ε i, (j : ℕ)) = 1 := by
    have h0 : (φ₀ (c : K) ^ (∑ i : Fin f, 2 ^ (i : ℕ) * ∑ j ∈ ε i, (j : ℕ)) - 1) • bTop (k := k) ε = 0 := by
      rw [sub_smul, one_smul, ← h, sub_self]
    rcases smul_eq_zero.mp h0 with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact absurd h0 (bTop_ne_zero ε)
  rw [← orderOf_units, ← orderOf_injective φ₀.toMonoidHom φ₀.injective]
  exact orderOf_dvd_of_pow_eq_one hpow

end CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
