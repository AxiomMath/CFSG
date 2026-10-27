module

public import CFSG.GH74.GLS.Stage1.Thm4.L96Gen4
public import CFSG.GH74.GLS.Stage1.Thm4.L96C1
public import CFSG.GH74.GLS.Stage1.Thm4.L96Leaf
public import CFSG.GH74.GLS.Stage1.Thm4.L97

public section

namespace CFSG.GH74.GLS.Stage1.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec5
  CFSG.GH74.GLS.Stage1.Thm4.L96
open scoped commutatorElement

theorem card_eq_two_mul_alt {K : Type} [Group K] {n : ℕ} (h : IsDoubleCoverOfAlt K n) :
    Nat.card K = 2 * Nat.card (alternatingGroup (Fin n)) := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K)
  rw [Nat.card_congr e.toEquiv, hc] at h1
  omega

theorem card_alt_two_mul_factorial {n : ℕ} (hn : 2 ≤ n) :
    2 * Nat.card (alternatingGroup (Fin n)) = n.factorial := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  exact Nat.mul_div_cancel' (Nat.dvd_factorial (by norm_num) hn)

theorem isDoubleCoverOfAlt_unique {K : Type} [Group K] {n m : ℕ} (h : IsDoubleCoverOfAlt K n)
    (h' : IsDoubleCoverOfAlt K m) (hm : 8 ≤ m) : n = m := by
  have h1 := card_eq_two_mul_alt h
  have h2 := card_eq_two_mul_alt h'
  have hmf : 2 * Nat.card (alternatingGroup (Fin m)) = m.factorial :=
    card_alt_two_mul_factorial (by omega)
  by_cases hn : 2 ≤ n
  · have hnf : 2 * Nat.card (alternatingGroup (Fin n)) = n.factorial := card_alt_two_mul_factorial hn
    have : n.factorial = m.factorial := by omega
    exact (Nat.factorial_inj (by
      have := Nat.self_le_factorial n
      omega)).1 this
  · exfalso
    have hn1 : n ≤ 1 := by omega
    have hcard : Nat.card (alternatingGroup (Fin n)) ≤ 1 := by
      have h1' : Nat.card (alternatingGroup (Fin n)) ≤ Nat.card (Equiv.Perm (Fin n)) :=
        Nat.card_le_card_of_injective _ Subtype.val_injective
      have h2' : Nat.card (Equiv.Perm (Fin n)) = n.factorial := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      have h3' : n.factorial ≤ 1 := by
        interval_cases n <;> simp [Nat.factorial]
      omega
    have h8 : Nat.factorial 8 ≤ m.factorial := Nat.factorial_le hm
    have h8' : Nat.factorial 8 = 40320 := by decide
    omega

theorem lemma9_6_of_outer3 (hleaf : Lemma9_6Outer3) : Lemma9_6 := by
  intro G _ _ Lh _ z t S K hstd n hcov K' hK'
  have hr1 : RigidSet Lh z = {K} := lemma9_7_thm G Lh z t S K hstd
  obtain rfl : K' = K := by rw [hr1] at hK'; exact hK'
  have hq1 : Qof S K' = zpowers z := Alt51.step9_8_q1_thm G Lh z t S K' hstd hr1
  have h : Ctx98 G Lh z t S K' := ⟨hstd, hr1, hq1⟩
  obtain ⟨n₀, hn8, hn11, hcov₀⟩ := hstd.cover
  obtain rfl : n = n₀ := isDoubleCoverOfAlt_unique hcov hcov₀ hn8
  obtain ⟨A⟩ := L96.Act.exists h hn8 hn11 hcov
  by_cases hsign : Equiv.Perm.sign (A.ρ ⟨t, hstd.t_cen⟩) = 1
  · exact L96.inner_case h hn8 hn11 hcov A hsign
  · exfalso
    by_cases hn10 : 10 ≤ n
    · exact hsign (L96.sign_eq_one_of_ten_eleven hstd.std.gen4 h hn10 hcov A _)
    · have hn : n = 8 ∨ n = 9 := by omega
      have hsq : A.ρ ⟨t, hstd.t_cen⟩ ^ 2 = 1 := by
        rw [← map_pow]
        have : (⟨t, hstd.t_cen⟩ : ↥(Cz z)) ^ 2 = 1 := by
          apply Subtype.ext
          have h2 : t ^ 2 = 1 := by rw [← hstd.t_ord]; exact pow_orderOf_eq_one t
          simpa using h2
        rw [this, map_one]
      have hsm1 : Equiv.Perm.sign (A.ρ ⟨t, hstd.t_cen⟩) = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign (A.ρ ⟨t, hstd.t_cen⟩)) with h1 | h1
        · exact absurd h1 hsign
        · exact h1
      obtain ⟨g, hg⟩ := isConj_iff.1 (h.isConj_z_t hcov)
      rcases L96.oddInvolution_cycleType (by omega) _ hsq hsm1 with hct | hct
      · obtain ⟨a, b, hab, hσ⟩ := L96.exists_swap_of_cycleType_two hct
        exact L96.false_of_transposition A hg hn hab hσ
      · refine hleaf G Lh z t S K' hstd hr1 hq1 n hn hcov
          ((QuotientGroup.quotientMulEquivOfEq (A.ker_eq_center hcov).symm).trans
            (QuotientGroup.quotientKerEquivOfSurjective A.π A.cover.surj))
          (A.ρ ⟨t, hstd.t_cen⟩) hct ?_
        intro k
        have htN : t ∈ normalizer (K' : Set G) := h.mem_normalizer hstd.t_cen
        refine ⟨⟨t * (k : G) * t⁻¹, (Subgroup.mem_normalizer_iff.1 htN k).1 k.2⟩, rfl, ?_⟩
        set k' : ↥K' := ⟨t * (k : G) * t⁻¹, (Subgroup.mem_normalizer_iff.1 htN k).1 k.2⟩ with hk'
        have h1 := A.ρ_K k'
        have h2 := A.ρ_K k
        have e1 : (⟨(k' : G), h.K_le k'.2⟩ : ↥(Cz z)) =
            ⟨t, hstd.t_cen⟩ * ⟨(k : G), h.K_le k.2⟩ * ⟨t, hstd.t_cen⟩⁻¹ := Subtype.ext rfl
        rw [e1, map_mul, map_mul, map_inv, h2] at h1
        exact h1.symm

end CFSG.GH74.GLS.Stage1.Thm4
