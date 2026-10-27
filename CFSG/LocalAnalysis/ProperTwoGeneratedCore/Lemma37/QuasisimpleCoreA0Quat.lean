module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreA0Kernel

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly QuaternionGroup

theorem dvd_sub_one_of_sq {m : ℕ} (hm : 2 ≤ m) {i : ℕ} (hi : 1 ≤ i)
    (h1 : 2 * 2 ^ m ∣ i * i - 1) (h2 : 4 ∣ i - 1) : 2 ^ m ∣ i - 1 := by
  obtain ⟨q, hq⟩ := h2
  obtain rfl : i = 4 * q + 1 := by omega
  have h3 : (4 * q + 1) * (4 * q + 1) - 1 = 8 * q * (2 * q + 1) := by ring_nf; omega
  rw [h3] at h1
  have hcop : Nat.Coprime (2 * 2 ^ m) (2 * q + 1) := by
    rw [← pow_succ']
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (odd_two_mul_add_one q))
  have h4 : 2 * 2 ^ m ∣ 8 * q := hcop.dvd_of_dvd_mul_right h1
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [show 4 * q + 1 - 1 = 4 * q by omega, pow_add, show 2 ^ 2 = 4 by norm_num]
  rw [pow_add, show 2 ^ 2 = 4 by norm_num, show 2 * (4 * 2 ^ k) = 8 * 2 ^ k by ring] at h4
  exact Nat.mul_dvd_mul_left 4 ((Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 8)).mp h4)

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}
  {N : Subgroup J} {M : ℕ}

noncomputable abbrev kerGen (φ : a0Kernel Q B N ≃* QuaternionGroup M) : J :=
  ((φ.symm (a 1) : a0Kernel Q B N) : J)

theorem quaternionGroup_orderOf_a_self' (hm : 1 ≤ M) :
    orderOf (a (M : ZMod (2 * M)) : QuaternionGroup M) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_two, a_mul_a, ← Nat.cast_add, ← two_mul, ZMod.natCast_self, a_zero]
  · rw [Ne, ← a_zero, a.injEq, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega

namespace A0Config

variable (φ : a0Kernel Q B N ≃* QuaternionGroup M)

omit [Finite J] in
theorem kerGen_mem : kerGen φ ∈ a0Kernel Q B N := (φ.symm (a 1)).2

theorem map_centralElt [NeZero M] (hc : A0Config Q B z u N) :
    φ ⟨centralElt J, hc.centralElt_mem_a0Kernel⟩ = a M := by
  have hw : orderOf (φ.symm (a M) : a0Kernel Q B N) = 2 := by
    rw [MulEquiv.orderOf_eq, quaternionGroup_orderOf_a_self' (Nat.one_le_iff_ne_zero.mpr
      (NeZero.ne M))]
  have he : ((φ.symm (a M) : a0Kernel Q B N) : J) = centralElt J :=
    hc.eq_centralElt_of_mem_a0Kernel (φ.symm (a M)).2 (by rw [Subgroup.orderOf_coe]; exact hw)
  rw [show (⟨centralElt J, hc.centralElt_mem_a0Kernel⟩ : a0Kernel Q B N) = φ.symm (a M) from
    Subtype.ext he.symm, MulEquiv.apply_symm_apply]

omit [Finite J] in
theorem kerGen_pow_eq (k : ℕ) :
    kerGen φ ^ k = ((φ.symm (a k) : a0Kernel Q B N) : J) := by
  rw [← a_one_pow, map_pow, Subgroup.coe_pow]

theorem kerGen_pow [NeZero M] (hc : A0Config Q B z u N) : kerGen φ ^ M = centralElt J := by
  rw [kerGen_pow_eq, ← hc.map_centralElt φ, MulEquiv.symm_apply_apply]

omit [Finite J] in
theorem orderOf_kerGen [NeZero M] : orderOf (kerGen φ) = 2 * M := by
  rw [kerGen, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_a_one]

theorem mem_cases [NeZero M] (hc : A0Config Q B z u N) {w : J} (hw : w ∈ a0Kernel Q B N) :
    (∃ k : ℕ, w = kerGen φ ^ k) ∨
      (w * w = centralElt J ∧ w * kerGen φ * w⁻¹ = (kerGen φ)⁻¹) := by
  rcases hφw : φ ⟨w, hw⟩ with k | i
  · left
    refine ⟨k.val, ?_⟩
    rw [kerGen_pow_eq, ZMod.natCast_zmod_val, ← hφw, MulEquiv.symm_apply_apply]
  · right
    constructor
    · have h : (⟨w, hw⟩ : a0Kernel Q B N) * ⟨w, hw⟩ =
          ⟨centralElt J, hc.centralElt_mem_a0Kernel⟩ := by
        apply φ.injective
        rw [map_mul, hφw, xa_mul_xa, hc.map_centralElt φ, add_sub_cancel_right]
      exact congrArg Subtype.val h
    · have h : (⟨w, hw⟩ : a0Kernel Q B N) * φ.symm (a 1) = (φ.symm (a 1))⁻¹ * ⟨w, hw⟩ := by
        apply φ.injective
        rw [map_mul, map_mul, map_inv, hφw, MulEquiv.apply_symm_apply, xa_mul_a]
        change xa (i + 1) = a (-1) * xa i
        rw [a_mul_xa, sub_neg_eq_add]
      have h' : w * kerGen φ = (kerGen φ)⁻¹ * w := congrArg Subtype.val h
      rw [h', mul_inv_cancel_right]

omit [Finite J] in
theorem kerGen_pow_four_ne_one [NeZero M] (hM : 3 ≤ M) : kerGen φ ^ 4 ≠ 1 := fun h4 => by
  have h := orderOf_dvd_of_pow_eq_one h4
  rw [orderOf_kerGen] at h
  have := Nat.le_of_dvd (by norm_num) h
  omega

theorem exists_self_eq_pow [NeZero M] (hc : A0Config Q B z u N) (hM : 3 ≤ M) :
    ∃ k : ℕ, u = kerGen φ ^ k := by
  have h := hc.setting
  rcases hc.mem_cases φ hc.self_mem_a0Kernel with hk | ⟨-, hinv⟩
  · exact hk
  · exfalso
    have haQ : kerGen φ ∈ (Q : Subgroup J) := (kerGen_mem φ).1
    have h1 := h.conj_eq_of_mem_quasiNormalizer hc.sq (hc.mem_quasiNormalizer haQ)
    have h2 : kerGen φ * u * (kerGen φ)⁻¹ = kerGen φ * kerGen φ * u := by
      have h3 : u * (kerGen φ)⁻¹ * u⁻¹ = kerGen φ := by
        rw [show u * (kerGen φ)⁻¹ * u⁻¹ = (u * kerGen φ * u⁻¹)⁻¹ by group, hinv, inv_inv]
      calc kerGen φ * u * (kerGen φ)⁻¹ = kerGen φ * (u * (kerGen φ)⁻¹ * u⁻¹) * u := by group
        _ = kerGen φ * kerGen φ * u := by rw [h3]
    have h4 : kerGen φ * kerGen φ = 1 ∨ kerGen φ * kerGen φ = centralElt J := by
      rcases h1 with h1 | h1 <;> rw [h2] at h1
      · left
        exact mul_eq_right.mp h1
      · right
        exact mul_right_cancel h1
    apply kerGen_pow_four_ne_one φ hM
    rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two]
    rcases h4 with h4 | h4 <;> rw [h4]
    · rw [one_mul]
    · exact h.centralElt_mul_self

section Kernel

variable [NeZero M] (hc : A0Config Q B z u N)

include hc in
theorem exists_pow_mul_of_not_pow {w w' : J} (hw : w ∈ a0Kernel Q B N)
    (hw' : w' ∈ a0Kernel Q B N) (hwa : ¬ ∃ k : ℕ, w = kerGen φ ^ k)
    (hw'a : ¬ ∃ k : ℕ, w' = kerGen φ ^ k) (h8 : 3 ≤ M) :
    ∃ k : ℕ, w = kerGen φ ^ k * w' := by
  have hmem : w * w'⁻¹ ∈ a0Kernel Q B N :=
    (a0Kernel Q B N).mul_mem hw ((a0Kernel Q B N).inv_mem hw')
  rcases hc.mem_cases φ hmem with ⟨k, hk⟩ | ⟨-, hinv⟩
  · exact ⟨k, by rw [← hk]; group⟩
  · exfalso
    rcases hc.mem_cases φ hw with hk | ⟨-, h1⟩
    · exact hwa hk
    rcases hc.mem_cases φ hw' with hk | ⟨-, h2⟩
    · exact hw'a hk
    have h3 : w * kerGen φ * w⁻¹ = kerGen φ := by
      calc w * kerGen φ * w⁻¹ = (w * w'⁻¹) * (w' * kerGen φ * w'⁻¹) * (w * w'⁻¹)⁻¹ := by group
        _ = (w * w'⁻¹) * (kerGen φ)⁻¹ * (w * w'⁻¹)⁻¹ := by rw [h2]
        _ = ((w * w'⁻¹) * kerGen φ * (w * w'⁻¹)⁻¹)⁻¹ := by group
        _ = kerGen φ := by rw [hinv, inv_inv]
    rw [h1] at h3
    have h6 : kerGen φ * kerGen φ = 1 := mul_eq_one_iff_eq_inv.mpr h3.symm
    apply kerGen_pow_four_ne_one φ h8
    rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two, h6, one_mul]

include hc in
theorem pow_comm_self (h3 : 3 ≤ M) (k : ℕ) : kerGen φ ^ k * u = u * kerGen φ ^ k := by
  obtain ⟨j, hj⟩ := hc.exists_self_eq_pow φ h3
  rw [hj, ← pow_add, ← pow_add, add_comm]

include hc in
theorem conj_self_of_not_pow (h3 : 3 ≤ M) {w : J} (hw : w ∈ a0Kernel Q B N)
    (hwa : ¬ ∃ k : ℕ, w = kerGen φ ^ k) : w * u * w⁻¹ = centralElt J * u := by
  rcases hc.mem_cases φ hw with hk | ⟨-, hinv⟩
  · exact absurd hk hwa
  obtain ⟨j, hj⟩ := hc.exists_self_eq_pow φ h3
  have h1 : w * u * w⁻¹ = u⁻¹ := by
    rw [hj, ← conj_pow, hinv, inv_pow]
  rw [h1, hc.setting.inv_eq_central_mul hc.sq]

include hc in
theorem conj_of_not_pow (h3 : 3 ≤ M) {w : J} (hw : w ∈ a0Kernel Q B N)
    (hwa : ¬ ∃ k : ℕ, w = kerGen φ ^ k) : u * w * u⁻¹ = centralElt J * w := by
  have h1 := hc.conj_self_of_not_pow φ h3 hw hwa
  have h2 : w * u = centralElt J * u * w := by rw [← h1]; group
  rw [hc.conj_self_eq_conj_inv w]
  calc u⁻¹ * w * u = u⁻¹ * (w * u) := by group
    _ = u⁻¹ * (centralElt J * u * w) := by rw [h2]
    _ = u⁻¹ * (centralElt J * (u * w)) := by group
    _ = centralElt J * w := by rw [hc.setting.mul_central_left u⁻¹]; group

include hc in
theorem exists_pow_of_comm (h3 : 3 ≤ M) {w : J} (hw : w ∈ a0Kernel Q B N)
    (hwu : w * u = u * w) : ∃ k : ℕ, w = kerGen φ ^ k := by
  by_contra hwa
  have h1 := hc.conj_self_of_not_pow φ h3 hw hwa
  rw [hwu, mul_inv_cancel_right] at h1
  exact hc.setting.centralElt_ne_one (mul_eq_right.mp h1.symm)

include hc in
theorem not_pow_of_conj_self (h3 : 3 ≤ M) {w : J} (hw : w * u * w⁻¹ = centralElt J * u) :
    ¬ ∃ k : ℕ, w = kerGen φ ^ k := fun ⟨k, hk⟩ => by
  rw [hk, hc.pow_comm_self φ h3 k, mul_inv_cancel_right] at hw
  exact hc.setting.centralElt_ne_one (mul_eq_right.mp hw.symm)

include hc in
theorem pow_eq_of_sq_eq_one (i : ℕ) (hi : kerGen φ ^ (2 * i) = 1) :
    kerGen φ ^ i = 1 ∨ kerGen φ ^ i = centralElt J := by
  have h1 := orderOf_dvd_of_pow_eq_one hi
  rw [orderOf_kerGen] at h1
  obtain ⟨l, hl⟩ := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp h1
  rw [hl, pow_mul, hc.kerGen_pow φ]
  rcases Nat.even_or_odd l with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [← two_mul, pow_mul, pow_two, hc.setting.centralElt_mul_self, one_pow]
  · right
    rw [pow_succ, pow_mul, pow_two, hc.setting.centralElt_mul_self, one_pow, one_mul]

include hc in
theorem exists_conj_kerGen_eq_pow (h3 : 3 ≤ M) {s : J} (hs : s ∈ (Q : Subgroup J)) :
    ∃ i : ℕ, s * kerGen φ * s⁻¹ = kerGen φ ^ i := by
  have h := hc.setting
  rcases hc.mem_cases φ (hc.conj_mem_a0Kernel hs (kerGen_mem φ)) with hk | ⟨hsq, -⟩
  · exact hk
  · exfalso
    have h1 : kerGen φ * kerGen φ = centralElt J := by
      have h2 : s * (kerGen φ * kerGen φ) * s⁻¹ = centralElt J := by
        rw [← hsq]; group
      calc kerGen φ * kerGen φ = s⁻¹ * (s * (kerGen φ * kerGen φ) * s⁻¹) * s := by group
        _ = centralElt J := by
            rw [h2, mul_assoc, ← (h.commute_centralElt s).eq, ← mul_assoc, inv_mul_cancel,
              one_mul]
    apply kerGen_pow_four_ne_one φ h3
    rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two, h1, h.centralElt_mul_self]

include hc in
theorem conj_pow_of_not_pow {b : J} (hb : b ∈ a0Kernel Q B N)
    (hba : ¬ ∃ k : ℕ, b = kerGen φ ^ k) (k : ℕ) :
    b * kerGen φ ^ k * b⁻¹ = (kerGen φ ^ k)⁻¹ := by
  rcases hc.mem_cases φ hb with hk | ⟨-, hinv⟩
  · exact absurd hk hba
  · rw [← conj_pow, hinv, inv_pow]

include hc in
theorem mem_cases_b (h3 : 3 ≤ M) {b : J} (hb : b ∈ a0Kernel Q B N)
    (hba : ¬ ∃ k : ℕ, b = kerGen φ ^ k) {w : J} (hw : w ∈ a0Kernel Q B N) :
    ∃ k : ℕ, w = kerGen φ ^ k ∨ w = kerGen φ ^ k * b := by
  by_cases hwa : ∃ k : ℕ, w = kerGen φ ^ k
  · obtain ⟨k, hk⟩ := hwa
    exact ⟨k, Or.inl hk⟩
  · obtain ⟨k, hk⟩ := hc.exists_pow_mul_of_not_pow φ hw hb hwa hba h3
    exact ⟨k, Or.inr hk⟩

include hc in
theorem centralizes_of_comm (h3 : 3 ≤ M) {b : J} (hb : b ∈ a0Kernel Q B N)
    (hba : ¬ ∃ k : ℕ, b = kerGen φ ^ k) {r : J} (hra : r * kerGen φ = kerGen φ * r)
    (hrb : r * b = b * r) : ∀ k ∈ a0Kernel Q B N, r * k = k * r := by
  intro w hw
  have hrak : ∀ k : ℕ, r * kerGen φ ^ k = kerGen φ ^ k * r := fun k =>
    ((Commute.pow_right (show Commute r (kerGen φ) from hra) k)).eq
  obtain ⟨k, rfl | rfl⟩ := hc.mem_cases_b φ h3 hb hba hw
  · exact hrak k
  · rw [← mul_assoc, hrak k, mul_assoc, hrb, mul_assoc]

end Kernel

end A0Config

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
