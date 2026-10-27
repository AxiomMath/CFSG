module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusPerfField
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm

public section

namespace CFSG.AGLEmbedding.O10Cent

open CFSG.LinearAlgebra CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.AGLEmbedding.OmegaMinusPerf Matrix

theorem unitaryFieldData_omega : UnitaryFieldData 2 1 OmegaField :=
  ⟨Nat.prime_two, le_rfl, by rw [natCard_omegaField']; norm_num⟩

@[expose] noncomputable def stdHerm (k : ℕ) :
    (Fin k → OmegaField) →ₛₗ[unitaryFieldData_omega.bar] (Fin k → OmegaField) →ₗ[OmegaField]
      OmegaField :=
  gramForm unitaryFieldData_omega (1 : Matrix (Fin k) (Fin k) OmegaField)

theorem bar_omega (c : OmegaField) : unitaryFieldData_omega.bar c = c ^ 2 := by
  rw [UnitaryFieldData.bar_apply, pow_one]

theorem stdHerm_apply {k : ℕ} (z w : Fin k → OmegaField) :
    stdHerm k z w = ∑ i, z i ^ 2 * w i := by
  simp [stdHerm, gramForm_apply, dotProduct, bar_omega]

theorem stdHerm_isSymm (k : ℕ) : (stdHerm k).IsSymm :=
  gramForm_isSymm unitaryFieldData_omega (by simp [Matrix.map_one])

theorem stdHerm_separatingLeft (k : ℕ) : (stdHerm k).SeparatingLeft :=
  gramForm_separatingLeft unitaryFieldData_omega (by simp)

theorem stdHerm_self {k : ℕ} (z : Fin k → OmegaField) : stdHerm k z z = ∑ i, z i ^ 3 := by
  rw [stdHerm_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem card_unitary_three : Nat.card (sesqUnitaryGroup (stdHerm 3)) = 648 := by
  have h := unitaryFieldData_omega
  have := h.finite
  have := Fintype.ofFinite OmegaField
  have hU := (unitary_full_group_order h (stdHerm_isSymm 3) (stdHerm_separatingLeft 3)
    (Module.finrank_fin_fun OmegaField) (by norm_num)).1
  have hprod : ∏ i ∈ Finset.Icc 1 3, (((2 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) = 81 := by decide
  rw [hprod] at hU
  norm_num at hU
  exact_mod_cast hU

theorem eq_of_trace_eq {a b : OmegaField} (h1 : a + a ^ 2 = b + b ^ 2)
    (h2 : omega * a + (omega * a) ^ 2 = omega * b + (omega * b) ^ 2) : a = b := by
  have hw := omega_sq
  linear_combination omega ^ 2 * h1 - h2 - (a - b) * hw

theorem stdHerm_eq_of_norm {k : ℕ}
    (T : (Fin k → OmegaField) →ₗ[OmegaField] (Fin k → OmegaField))
    (hT : ∀ z, stdHerm k (T z) (T z) = stdHerm k z z) (z w : Fin k → OmegaField) :
    stdHerm k (T z) (T w) = stdHerm k z w := by
  have hs : ∀ u v, (unitaryFieldData_omega.bar) (stdHerm k u v) = stdHerm k v u :=
    fun u v => (stdHerm_isSymm k).eq u v
  have key : ∀ w', stdHerm k (T z) (T w') + (stdHerm k (T z) (T w')) ^ 2 =
      stdHerm k z w' + (stdHerm k z w') ^ 2 := by
    intro w'
    have h1 := hT (z + w')
    rw [map_add] at h1
    simp only [map_add, LinearMap.add_apply, hT] at h1
    have e1 := hs (T z) (T w')
    have e2 := hs z w'
    rw [bar_omega] at e1 e2
    rw [← e1, ← e2] at h1
    have h2 : (2 : OmegaField) = 0 := omegaField_two_eq_zero
    linear_combination h1
  have k1 := key w
  have k2 := key (omega • w)
  simp only [map_smul, smul_eq_mul] at k2
  exact eq_of_trace_eq k1 k2

end CFSG.AGLEmbedding.O10Cent
