module

public import CFSG.HardMathSupport.Solomon.Proving.UGroupExists

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {G : Type} [Group G]

theorem sq_eq_one_of_zpow_succ_eq_one {h : G} {N : ℕ} (hN : h ^ (2 ^ N) = 1) {k : ℤ}
    (hk : k % 4 = 1) (hh : h ^ (k + 1) = 1) : h ^ 2 = 1 := by
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hN)
  have hk' : ((orderOf h : ℕ) : ℤ) ∣ k + 1 := orderOf_dvd_iff_zpow_eq_one.2 hh
  rw [hi] at hk'
  push_cast at hk'
  have hi1 : i ≤ 1 := by
    by_contra hcon
    have h4 : (2 : ℤ) ^ 2 ∣ (2 : ℤ) ^ i := pow_dvd_pow 2 (by omega)
    have h4' : (4 : ℤ) ∣ k + 1 := by
      have := dvd_trans h4 hk'
      norm_num at this
      exact this
    omega
  apply orderOf_dvd_iff_pow_eq_one.1
  rw [hi]
  simpa using pow_dvd_pow 2 hi1

theorem normal_klein_of_involution_coset [Finite G] {T A : Subgroup G} {a z f : G}
    (hT : IsPGroup 2 T) (hAT : A ≤ T) (hAn : ∀ t ∈ T, ∀ x ∈ A, t * x * t⁻¹ ∈ A)
    (hAgen : ∀ x ∈ A, ∃ j : ℤ, x = a ^ j) (ha : a ∈ A)
    (hcent : ∀ c ∈ T, (∀ x ∈ A, c * x = x * c) → c ∈ A)
    (hz : z ∈ A) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (hzc : ∀ t ∈ T, t * z = z * t)
    (hu : ∀ x ∈ A, x ^ 2 = 1 → x = 1 ∨ x = z)
    (hfT : f ∈ T) (hf2 : f ^ 2 = 1) (hfA : f ∉ A) {k : ℤ} (hk : k % 4 = 1)
    (hfa : f * a * f⁻¹ = a ^ k) :
    ∃ U : Subgroup G, IsPPlane 2 U ∧ U ≤ T ∧ T ≤ Subgroup.normalizer (U : Set G) := by
  have hff : f * f = 1 := by rw [← pow_two]; exact hf2
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  have hfA_pow : ∀ j : ℤ, f * a ^ j * f⁻¹ = a ^ (k * j) := by
    intro j
    rw [← conj_zpow, hfa, ← zpow_mul]
  have F2 : a ^ (k * k) = a := by
    rw [← hfA_pow k, ← hfa]
    calc f * (f * a * f⁻¹) * f⁻¹ = (f * f) * a * (f⁻¹ * f⁻¹) := by group
      _ = a := by rw [hfinv, hff, one_mul, mul_one]
  have hzz : z * z = 1 := by rw [← pow_two]; exact hz2
  have key : ∀ t ∈ T, t * f * t⁻¹ = f ∨ t * f * t⁻¹ = f * z := by
    intro t ht
    obtain ⟨s, hs⟩ := hAgen _ (hAn t ht a ha)
    obtain ⟨s', hs'⟩ := hAgen _ (hAn t⁻¹ (T.inv_mem ht) a ha)
    rw [inv_inv] at hs'
    have e1 : t⁻¹ * a ^ s * t = a := by rw [← hs]; group
    have e2 := conj_zpow (a := t⁻¹) (b := a) (i := s)
    rw [inv_inv, hs', e1, ← zpow_mul] at e2
    have Fb : t * f * t⁻¹ * a * (t * f * t⁻¹)⁻¹ = a ^ k := by
      have e3 : t * f * t⁻¹ * a * (t * f * t⁻¹)⁻¹ = t * (f * (t⁻¹ * a * t) * f⁻¹) * t⁻¹ := by
        group
      rw [e3, hs', hfA_pow s', ← conj_zpow, hs, ← zpow_mul]
      have e4 : s * (k * s') = (s' * s) * k := by ring
      rw [e4, zpow_mul, e2]
    have Fh : t * f * t⁻¹ * f * a * (t * f * t⁻¹ * f)⁻¹ = a := by
      have e5 : t * f * t⁻¹ * f * a * (t * f * t⁻¹ * f)⁻¹ = (t * f * t⁻¹) * (f * a * f⁻¹) * (t * f * t⁻¹)⁻¹ := by
        group
      rw [e5, hfa, ← conj_zpow, Fb, ← zpow_mul, F2]
    have hcomm : ∀ j : ℤ, t * f * t⁻¹ * f * a ^ j = a ^ j * (t * f * t⁻¹ * f) := by
      intro j
      rw [← mul_inv_eq_iff_eq_mul, ← conj_zpow, Fh]
    have hhT : t * f * t⁻¹ * f ∈ T :=
      T.mul_mem (T.mul_mem (T.mul_mem ht hfT) (T.inv_mem ht)) hfT
    have hhA : t * f * t⁻¹ * f ∈ A := hcent _ hhT (fun x hx => by
      obtain ⟨j, rfl⟩ := hAgen x hx
      exact hcomm j)
    obtain ⟨j, hj⟩ := hAgen _ hhA
    have hfh : f * (t * f * t⁻¹ * f) * f⁻¹ = (t * f * t⁻¹ * f) ^ k := by
      rw [hj, hfA_pow j, ← zpow_mul, mul_comm k j]
    have hsq1 : (t * f * t⁻¹ * f) * f * ((t * f * t⁻¹ * f) * f) = 1 := by
      have : (t * f * t⁻¹ * f) * f = t * f * t⁻¹ := by
        rw [mul_assoc, hff, mul_one]
      rw [this]
      calc t * f * t⁻¹ * (t * f * t⁻¹) = t * (f * f) * t⁻¹ := by group
        _ = 1 := by rw [hff, mul_one, mul_inv_cancel]
    have hfhf : f * (t * f * t⁻¹ * f) * f = (t * f * t⁻¹ * f)⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      calc (t * f * t⁻¹ * f) * (f * (t * f * t⁻¹ * f) * f)
          = ((t * f * t⁻¹ * f) * f) * ((t * f * t⁻¹ * f) * f) := by group
        _ = 1 := hsq1
    have hpow : (t * f * t⁻¹ * f) ^ (k + 1) = 1 := by
      have e6 : (t * f * t⁻¹ * f) ^ (k + 1) = f * (t * f * t⁻¹ * f) * f⁻¹ * (t * f * t⁻¹ * f) := by
        rw [zpow_add_one, hfh]
      rw [e6, hfinv, hfhf, inv_mul_cancel]
    obtain ⟨N, hN⟩ := hT ⟨t * f * t⁻¹ * f, hhT⟩
    have hN' : (t * f * t⁻¹ * f) ^ (2 ^ N) = 1 := by
      have := congrArg Subtype.val hN
      simpa using this
    have hsq : (t * f * t⁻¹ * f) ^ 2 = 1 := sq_eq_one_of_zpow_succ_eq_one hN' hk hpow
    rcases hu _ hhA hsq with hcase | hcase
    · left
      have := mul_eq_one_iff_eq_inv.1 hcase
      rw [hfinv] at this
      exact this
    · right
      rw [eq_mul_inv_of_mul_eq hcase, hfinv]
      exact (hzc f hfT).symm
  have hf1 : f ≠ 1 := fun h => hfA (by rw [h]; exact A.one_mem)
  have hfz : f ≠ z := fun h => hfA (by rw [h]; exact hz)
  have hzf : f * z = z * f := hzc f hfT
  refine ⟨kleinOf hf2 hz2 hzf, isPPlane_kleinOf hf1 hz1 hfz, ?_, ?_⟩
  · intro x hx
    rw [mem_kleinOf] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact T.one_mem
    · exact hfT
    · exact hAT hz
    · exact T.mul_mem hfT (hAT hz)
  · have hzc' : ∀ t ∈ T, t * z * t⁻¹ = z := fun t ht => by
      rw [hzc t ht, mul_assoc, mul_inv_cancel, mul_one]
    have key2 : ∀ t ∈ T, ∀ x ∈ kleinOf hf2 hz2 hzf, t * x * t⁻¹ ∈ kleinOf hf2 hz2 hzf := by
      intro t ht x hx
      rw [mem_kleinOf] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl
      · left
        simp
      · rcases key t ht with e | e
        · right; left; exact e
        · right; right; right; exact e
      · right; right; left; exact hzc' t ht
      · have e2 : t * (f * z) * t⁻¹ = (t * f * t⁻¹) * (t * z * t⁻¹) := by group
        rw [e2, hzc' t ht]
        rcases key t ht with e | e
        · rw [e]; right; right; right; rfl
        · rw [e]; right; left; rw [mul_assoc, hzz, mul_one]
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => key2 t ht x hx
    · intro hx
      have h2 := key2 t⁻¹ (T.inv_mem ht) _ hx
      have e : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
      rwa [e] at h2

end CFSG.HardMathSupport.Solomon.Proving

end
