module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResOthSU
public import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.Open.StatedAPI CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits
open scoped commutatorElement

set_option linter.unusedSectionVars false

theorem excOth_unit_params {F : Type} [Field F] [Finite F] {Q : ℕ} (hQ : 3 ≤ Q)
    (hF : Nat.card F = Q ^ 2) :
    ∃ l ω : F, l ^ (Q + 1) = 1 ∧ l ^ 3 ≠ 1 ∧ ω ^ Q = ω ∧ ω ≠ 0 ∧ ω ≠ 1 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = Q ^ 2 - 1 := by
    have := Fintype.ofFinite F
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, Fintype.card_units,
      ← Nat.card_eq_fintype_card, hF]
  have hsq : Q ^ 2 - 1 = (Q + 1) * (Q - 1) := sq_sub_one_eq Q (by omega)
  have hg1 : g ^ ((Q + 1) * (Q - 1)) = 1 := by
    rw [← hsq, ← hord, pow_orderOf_eq_one]
  refine ⟨((g ^ (Q - 1) : Fˣ) : F), ((g ^ (Q + 1) : Fˣ) : F), ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, hg1, Units.val_one]
  · intro h
    have h1 : g ^ ((Q - 1) * 3) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, pow_mul, Units.val_one]
      rw [← Units.val_pow_eq_pow_val] at h
      exact h
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hord, hsq, mul_comm (Q + 1) (Q - 1)] at h2
    have h3 : Q + 1 ∣ 3 := Nat.dvd_of_mul_dvd_mul_left (by omega) h2
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  · rw [← Units.val_pow_eq_pow_val, ← pow_mul]
    congr 1
    have : (Q + 1) * Q = (Q + 1) * (Q - 1) + (Q + 1) := by
      zify [show 1 ≤ Q by omega]
      ring
    rw [this, pow_add, hg1, one_mul]
  · exact Units.ne_zero _
  · intro h
    have h1 : g ^ (Q + 1) = 1 := Units.ext (by rw [Units.val_one]; exact h)
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hord, hsq] at h2
    have h3 : Q - 1 ∣ 1 := by
      have : (Q + 1) * (Q - 1) ∣ (Q + 1) * 1 := by rwa [mul_one]
      exact Nat.dvd_of_mul_dvd_mul_left (by omega) this
    have := Nat.le_of_dvd (by norm_num) h3
    omega

theorem excOth_suid_no_psl2 {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]
    [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ} (hn : 3 ≤ n) (hne : (n, p ^ f) ≠ (3, 2))
    {F' : Type} [Field F']
    (φ : (↥(SUid (unitaryInvolution F p f) n) ⧸ Subgroup.center ↥(SUid (unitaryInvolution F p f) n))
      ≃* StatedProj (StatedSL 2 F')) : False := by
  classical
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  have hq := one_lt_pow_of_card hF
  by_cases hQ : 3 ≤ p ^ f
  · obtain ⟨l, ω, hl1, hl3, hω1, hω0, hωne⟩ := excOth_unit_params hQ (F := F)
      hF
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 2 := ⟨n - 3, by omega⟩
    obtain ⟨W⟩ := hσ.nonempty_wittData
    refine excOth_caseA hσ W m (l := l) ?_ hl3 (ω := ω) ?_ hω0 hωne φ
    · rw [unitaryInvolution_apply, ← pow_succ, hl1]
    · rw [unitaryInvolution_apply, hω1]
  · have hQ2 : p ^ f = 2 := by omega
    have hf0 : f ≠ 0 := by
      rintro rfl
      simp at hQ2
    have hp2 : p = 2 := by
      have : p ∣ 2 := by rw [← hQ2]; exact dvd_pow_self p hf0
      exact (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this
    subst hp2
    have h4 : 4 ≤ n := by
      by_contra h
      apply hne
      have : n = 3 := by omega
      rw [this, hQ2]
    have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
    obtain ⟨ω, hω, hω1⟩ := hσ.exists_norm_one_ne_one
    have hne' : ∀ a b : ℕ, (ha : a < n) → (hb : b < n) → a ≠ b →
        (⟨a, ha⟩ : Fin n) ≠ ⟨b, hb⟩ := fun a b ha hb hab h => hab (Fin.mk.inj h)
    exact excOth_caseB hσ h2 hn (i0 := ⟨0, by omega⟩) (i1 := ⟨1, by omega⟩)
      (i2 := ⟨2, by omega⟩) (i3 := ⟨3, by omega⟩) (hne' _ _ _ _ (by omega))
      (hne' _ _ _ _ (by omega)) (hne' _ _ _ _ (by omega)) (hne' _ _ _ _ (by omega))
      (hne' _ _ _ _ (by omega)) (hne' _ _ _ _ (by omega)) hω hω1 φ

end CFSG.HardMathSupport.Dickson.Sec6.I1431
