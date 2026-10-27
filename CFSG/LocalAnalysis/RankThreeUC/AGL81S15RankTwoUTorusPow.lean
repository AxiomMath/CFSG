module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU5Field
import CFSG.ClassicalInvolution.Asc77.AscC5OM11
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsUnitBorel

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

theorem fieldAut_hypTorus_eq_pow {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    {r ε : ℕ} (τ : K ≃+* K) {N : ℕ} (hτ : ∀ a : K, τ a = a ^ N) {t : hypSU h r ε}
    (ht : t ∈ hypTorus h r ε) : CFSG.Quasithin.H13.Sec53F.Unit.fieldAut h τ t = t ^ N := by
  obtain ⟨a, d, -, -, hm⟩ := ht
  apply CFSG.Quasithin.H13.Sec53F.Unit.hypSU_ext'
  rw [CFSG.Quasithin.H13.Sec53F.Unit.fieldAut_apply,
    CFSG.Quasithin.H13.Sec53F.Unit.mat_fieldHom, hm]
  rw [Matrix.diagonal_map (map_zero τ)]
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hm, Matrix.diagonal_pow]
  congr 1
  funext x
  exact hτ _

private theorem exists_pow_of_involutive {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (τ : K ≃+* K) (hτ : ∀ a, τ (τ a) = a) :
    ∃ N : ℕ, (N = 1 ∨ N = 2 ^ f) ∧ ∀ a : K, τ a = a ^ N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := h.charP
  haveI : Finite K := h.finite
  by_cases hrefl : τ = RingEquiv.refl K
  · refine ⟨1, Or.inl rfl, fun a => ?_⟩
    rw [hrefl]
    simp
  · have hne : ∃ a : K, τ a ≠ a := by
      by_contra hc
      refine hrefl (RingEquiv.ext fun a => ?_)
      by_contra ha
      exact hc ⟨a, ha⟩
    obtain ⟨i, hcard, hpow⟩ :=
      CFSG.ClassicalInvolution.Asc77.C5O.M.exists_ringEquiv_eq_pow_half (p := 2) (F := K) τ
        (fun a => hτ a) hne
    have hcard' : Nat.card K = 2 ^ (i * 2) := by
      rw [hcard, pow_mul]
    have hbase : 2 ^ (2 * f) = 2 ^ (i * 2) := by
      rw [← h.card, hcard']
    have hi : i = f := by
      have h2 := Nat.pow_right_injective (by norm_num : 2 ≤ 2) hbase
      omega
    refine ⟨2 ^ f, Or.inr rfl, fun a => ?_⟩
    rw [hpow a, hi]

theorem fieldAut_hypTorus_eq_self_of_involutive {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {r ε : ℕ} (τ : K ≃+* K) (hτ : ∀ a, τ (τ a) = a)
    {t : hypSU h r ε} (ht : t ∈ hypTorus h r ε) (htq : t ^ (2 ^ f - 1) = 1) :
    CFSG.Quasithin.H13.Sec53F.Unit.fieldAut h τ t = t := by
  obtain ⟨N, hN1, hN⟩ := exists_pow_of_involutive h τ hτ
  rw [fieldAut_hypTorus_eq_pow h τ hN ht]
  rcases hN1 with hN1 | hN1 <;> subst hN1
  · exact pow_one t
  · rw [← Nat.sub_add_cancel (Nat.one_le_two_pow (n := f)), pow_add, htq, one_mul, pow_one]

theorem fieldP_eq_self_of_involutive {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (τ : K ≃+* K) (hτ : ∀ a, τ (τ a) = a) {x : hypPSU h 2 1}
    (hx : x ∈ (hypTorus h 2 1).map (hypProj h 2 1)) (hxq : x ^ (2 ^ f - 1) = 1) :
    CFSG.Quasithin.H13.Sec53F.Unit.fieldP h τ x = x := by
  obtain ⟨t, ht, rfl⟩ := hx
  have hxq' : (hypProj h 2 1 t) ^ (2 ^ f - 1) = 1 := hxq
  obtain ⟨N, hN1, hN⟩ := exists_pow_of_involutive h τ hτ
  have hfield : CFSG.Quasithin.H13.Sec53F.Unit.fieldP h τ (hypProj h 2 1 t) =
      (hypProj h 2 1 t) ^ N := by
    rw [CFSG.Quasithin.H13.Sec53F.Unit.fieldP_apply, fieldAut_hypTorus_eq_pow h τ hN ht,
      map_pow]
  rw [hfield]
  rcases hN1 with hN1 | hN1 <;> subst hN1
  · exact pow_one _
  · rw [← Nat.sub_add_cancel (Nat.one_le_two_pow (n := f)), pow_add, hxq', one_mul, pow_one]

end CFSG.LocalAnalysis.RankThreeUC.S15

end
