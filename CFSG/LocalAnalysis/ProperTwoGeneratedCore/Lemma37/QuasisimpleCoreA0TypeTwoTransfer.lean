module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreA0KernelLemma
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreRL2Transfer

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}
  {N : Subgroup J}

namespace A0Config

theorem false_of_cyclic_quotient (hc : A0Config Q B z u N) {s : J} {f : ℕ} (hf : 1 ≤ f)
    (hsQ : s ∈ (Q : Subgroup J))
    (hsz : s ^ 2 ^ (f - 1) = z ∨ s ^ 2 ^ (f - 1) = centralElt J * z)
    (hdec : ∀ x ∈ (Q : Subgroup J), ∃ k ∈ a0Kernel Q B N, ∃ j : ℤ, x = k * s ^ j)
    (hpowK : ∀ j : ℤ, s ^ j ∈ a0Kernel Q B N → (2 ^ f : ℤ) ∣ j) : False := by
  have h := hc.setting
  have hz := hc.fourGen
  set K := a0Kernel Q B N with hKdef
  have hsK : ∀ i : ℤ, ∀ k ∈ K, s ^ i * k * (s ^ i)⁻¹ ∈ K := fun i k hk =>
    hc.conj_mem_a0Kernel ((Q : Subgroup J).zpow_mem hsQ i) hk
  have hs2f : s ^ 2 ^ f = 1 := by
    have : 2 ^ f = 2 ^ (f - 1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel hf]
    rw [this, pow_mul]
    rcases hsz with h1 | h1 <;> rw [h1, pow_two]
    · exact hz.mul_self
    · rw [h.central_mul_central, hz.mul_self]
  have hs2fz : ∀ j : ℤ, (2 ^ f : ℤ) ∣ j → s ^ j = 1 := by
    rintro j ⟨l, rfl⟩
    rw [zpow_mul]
    norm_cast
    rw [hs2f, one_zpow]
  set K' := K ⊔ Subgroup.zpowers (s ^ 2) with hK'
  have hnorm : Subgroup.zpowers (s ^ 2) ≤ Subgroup.normalizer (K : Set J) :=
    Subgroup.zpowers_le.mpr (hc.le_normalizer_a0Kernel ((Q : Subgroup J).pow_mem hsQ 2))
  have hmemK' : ∀ x : J, x ∈ K' ↔ ∃ k ∈ K, ∃ j : ℤ, x = k * s ^ (2 * j) := by
    intro x
    rw [← SetLike.mem_coe, hK', Subgroup.coe_mul_of_right_le_normalizer_left K _ hnorm,
      Set.mem_mul]
    constructor
    · rintro ⟨k, hk, y, hy, rfl⟩
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ⟨k, hk, j, by rw [← zpow_natCast, ← zpow_mul]; norm_num⟩
    · rintro ⟨k, hk, j, rfl⟩
      exact ⟨k, hk, s ^ (2 * j), Subgroup.mem_zpowers_iff.mpr ⟨j, by
        rw [← zpow_natCast, ← zpow_mul]; norm_num⟩, rfl⟩
  have hpar : ∀ k ∈ K, ∀ j : ℤ, k * s ^ j ∈ K' ↔ Even j := by
    intro k hk j
    rw [hmemK']
    constructor
    · rintro ⟨k', hk', i, hi⟩
      have h1 : s ^ (j - 2 * i) ∈ K := by
        have h2 : s ^ (j - 2 * i) = k⁻¹ * k' := by
          rw [zpow_sub, eq_inv_mul_iff_mul_eq, ← mul_assoc, hi]; group
        rw [h2]
        exact K.mul_mem (K.inv_mem hk) hk'
      obtain ⟨l, hl⟩ := hpowK _ h1
      have h3 : (2 : ℤ) ∣ j := by
        have h4 : (2 : ℤ) ∣ 2 ^ f := dvd_pow_self 2 (by omega)
        have h5 : (2 : ℤ) ∣ j - 2 * i := h4.trans ⟨l, hl⟩
        have h6 : (2 : ℤ) ∣ 2 * i := dvd_mul_right 2 i
        have := dvd_add h5 h6
        simpa using this
      exact even_iff_two_dvd.mpr h3
    · rintro ⟨i, rfl⟩
      exact ⟨k, hk, i, by rw [two_mul]⟩
  have hsK' : s ∉ K' := by
    intro hs
    have h1 := (hpar 1 K.one_mem 1).mp (by simpa using hs)
    exact Int.not_even_one h1
  have hK'Q : K' ≤ (Q : Subgroup J) := sup_le a0Kernel_le_sylow
    (Subgroup.zpowers_le.mpr ((Q : Subgroup J).pow_mem hsQ 2))
  have hrel : K'.relIndex (Q : Subgroup J) = 2 := by
    refine relIndex_eq_two_of_mul_mem hsQ hsK' fun t htQ htK' => ?_
    obtain ⟨k, hk, j, rfl⟩ := hdec t htQ
    have hj : ¬ Even j := fun hj => htK' ((hpar k hk j).mpr hj)
    rw [mul_assoc, ← zpow_add_one]
    exact (hpar k hk (j + 1)).mpr (by rw [Int.not_even_iff_odd] at hj; exact hj.add_one)
  have hpow : ∀ k ∈ K, ∀ j : ℤ, ∀ n : ℕ, ∃ k' ∈ K, (k * s ^ j) ^ n = k' * s ^ (j * n) := by
    intro k hk j n
    induction n with
    | zero => exact ⟨1, K.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨k', hk', h1⟩ := ih
      refine ⟨k' * (s ^ (j * n) * k * (s ^ (j * n))⁻¹), K.mul_mem hk' (hsK _ k hk), ?_⟩
      rw [pow_succ, h1, show j * ((n + 1 : ℕ) : ℤ) = j * n + j by push_cast; ring, zpow_add]
      group
  refine false_of_relIndex_eq_two h.perfect Q hK'Q hrel hsQ hsK' fun m a hy => ?_
  obtain ⟨k, hk, j, hj⟩ := hdec _ hy
  have hsm : s ^ m ∈ K' ↔ Even m := by simpa using hpar 1 K.one_mem m
  rw [hsm, hj, hpar k hk j]
  set n₀ := 2 ^ (f - 1) with hn₀
  have h2f : (2 ^ f : ℤ) = 2 * n₀ := by
    rw [hn₀]; push_cast; rw [← pow_succ', Nat.sub_add_cancel hf]
  have hn₀0 : (n₀ : ℤ) ≠ 0 := by positivity
  have hyN : (k * s ^ j) ^ n₀ = a⁻¹ * (s ^ m) ^ n₀ * a := by
    rw [← hj]
    have h0 := conj_pow (i := n₀) (a := a⁻¹) (b := s ^ m)
    rwa [inv_inv] at h0
  obtain ⟨k', hk', hk'eq⟩ := hpow k hk j n₀
  rcases Int.even_or_odd m with hm | hm <;> rcases Int.even_or_odd j with hj' | hj'
  · exact iff_of_true hm hj'
  · exfalso
    obtain ⟨m', rfl⟩ := hm
    have h1 : (s ^ (m' + m')) ^ n₀ = 1 := by
      rw [← zpow_natCast, ← zpow_mul]
      exact hs2fz _ ⟨m', by rw [h2f]; ring⟩
    rw [h1, mul_one, inv_mul_cancel, hk'eq] at hyN
    have h3 : s ^ (j * n₀) ∈ K := by
      rw [eq_inv_of_mul_eq_one_right hyN]; exact K.inv_mem hk'
    obtain ⟨l, hl⟩ := hpowK _ h3
    rw [h2f, mul_comm (2 : ℤ), mul_assoc, mul_comm j] at hl
    have h4 : j = 2 * l := by
      have := mul_left_cancel₀ hn₀0 hl
      linarith
    exact (Int.not_even_iff_odd.mpr hj') ⟨l, by rw [h4]; ring⟩
  · exfalso
    obtain ⟨j', rfl⟩ := hj'
    have h1 : s ^ ((j' + j') * n₀) = 1 := hs2fz _ ⟨j', by rw [h2f]; ring⟩
    rw [h1, mul_one] at hk'eq
    have h2 : (s ^ m) ^ n₀ = s ^ n₀ := by
      obtain ⟨m', rfl⟩ := hm
      rw [← zpow_natCast, ← zpow_mul, show (2 * m' + 1) * (n₀ : ℤ) = 2 ^ f * m' + n₀ by
        rw [h2f]; ring, zpow_add, hs2fz _ (dvd_mul_right _ _), one_mul, zpow_natCast]
    rw [hk'eq, h2] at hyN
    have hsN : s ^ n₀ * s ^ n₀ = 1 := by
      rcases hsz with h3 | h3 <;> rw [h3]
      · exact hz.mul_self
      · rw [h.central_mul_central, hz.mul_self]
    have hsN1 : s ^ n₀ ≠ 1 := by
      rcases hsz with h3 | h3 <;> rw [h3] <;> intro h4
      · exact hz.not_mem_center (h4 ▸ (Subgroup.center J).one_mem)
      · apply hz.not_mem_center
        have : z = centralElt J := by
          have h5 := congrArg (centralElt J * ·) h4
          simp only [mul_one] at h5
          rw [← mul_assoc, h.centralElt_mul_self, one_mul] at h5
          exact h5
        rw [this]; exact h.centralElt_mem_center
    have hord : orderOf (a⁻¹ * s ^ n₀ * a) = 2 := by
      rw [orderOf_inv_mul_mul_eq]
      exact orderOf_eq_prime (by rw [pow_two]; exact hsN) hsN1
    have he := hc.eq_centralElt_of_mem_a0Kernel (hyN ▸ hk') hord
    have h5 : s ^ n₀ = centralElt J := by
      calc s ^ n₀ = a * (a⁻¹ * s ^ n₀ * a) * a⁻¹ := by group
        _ = centralElt J := by rw [he, Setting.conj_eq_of_mem_center h.centralElt_mem_center]
    rcases hsz with h3 | h3 <;> rw [h3] at h5
    · exact hz.ne_centralElt h h5
    · have h6 : z = 1 := by
        calc z = centralElt J * (centralElt J * z) := by
              rw [← mul_assoc, h.centralElt_mul_self, one_mul]
          _ = 1 := by rw [h5, h.centralElt_mul_self]
      have h8 := hz.order
      rw [h6, orderOf_one] at h8
      exact absurd h8 (by decide)
  · exact iff_of_false (Int.not_even_iff_odd.mpr hm) (Int.not_even_iff_odd.mpr hj')

end A0Config

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
