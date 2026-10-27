module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddKernelNormalizerTransferQuotient

public section

namespace CFSG.GroupTheory

open CFSG.ShultStronglyClosedTI.OddKernelNormalizerTransfer

variable {A B : Type*} [Group A] [Group B] [Finite A]

theorem exists_lift_conj_zpow (φ : A →* B) (hφ : Function.Surjective φ)
    (hker : IsPGroup 2 φ.ker) {b : A} {r : ℕ} (hb : orderOf b = r) (hr : r.Prime)
    (hr2 : r ≠ 2) {xbar : B} {m : ℤ}
    (hconj : xbar * φ b * xbar⁻¹ = (φ b) ^ m) :
    ∃ x : A, φ x = xbar ∧ x * b * x⁻¹ = b ^ m := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have : Finite B := Finite.of_surjective φ hφ
  have hcop : Nat.Coprime r (Nat.card φ.ker) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥φ.ker)).mp hker
    rw [hk]
    exact (Nat.coprime_two_left.mpr (hr.odd_of_ne_two hr2)).symm.pow_right k
  have hzp : IsPGroup r (Subgroup.zpowers b) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hb, pow_one]
  have hsem : SemiconjBy xbar (φ b) ((φ b) ^ m) := by
    rw [SemiconjBy]
    calc xbar * φ b = (xbar * φ b * xbar⁻¹) * xbar := by group
      _ = (φ b) ^ m * xbar := by rw [hconj]
  have hordm : orderOf ((φ b) ^ m) = orderOf (φ b) :=
    (SemiconjBy.orderOf_eq xbar hsem).symm
  have hzpows : Subgroup.zpowers ((φ b) ^ m) = Subgroup.zpowers (φ b) := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · exact Subgroup.zpowers_le.mpr (Subgroup.zpow_mem_zpowers (φ b) m)
    · rw [Nat.card_zpowers, Nat.card_zpowers, hordm]
  have hnorm : xbar ∈ Subgroup.normalizer (Subgroup.zpowers (φ b) : Set B) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    have hconj' : (MulAut.conj xbar) (φ b) = (φ b) ^ m := by
      simpa [MulAut.conj_apply] using hconj
    change Subgroup.zpowers ((MulAut.conj xbar) (φ b)) = Subgroup.zpowers (φ b)
    rw [hconj', hzpows]
  have hN := coprime_kernel_full_normalizer_image φ hφ r hr hcop (Subgroup.zpowers b) hzp
  rw [MonoidHom.map_zpowers] at hN
  have hmem : xbar ∈ (Subgroup.normalizer (Subgroup.zpowers b : Set A)).map φ := by
    rw [hN]
    exact hnorm
  obtain ⟨x, hxnorm, hxφ⟩ := Subgroup.mem_map.mp hmem
  have hconjx : x * b * x⁻¹ ∈ Subgroup.zpowers b :=
    (Subgroup.mem_normalizer_iff.mp hxnorm b).mp (Subgroup.mem_zpowers b)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hconjx
  have hφb_ne : φ b ≠ 1 := by
    intro h1
    have hbker : b ∈ φ.ker := h1
    have hdiv : orderOf b ∣ Nat.card φ.ker := Subgroup.orderOf_dvd_natCard _ hbker
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 2) (G := ↥φ.ker)).mp hker
    rw [hj, hb] at hdiv
    have h2 : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
      (hr.dvd_of_dvd_pow hdiv)
    exact hr2 h2
  have hφb_ord : orderOf (φ b) = r := by
    have hdvd : orderOf (φ b) ∣ r := by
      rw [← hb]
      exact orderOf_map_dvd φ b
    rcases (Nat.dvd_prime hr).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hφb_ne
    · exact h1
  have hpow_eq : b ^ k = b ^ m := by
    have h1 : (φ b) ^ k = (φ b) ^ m := by
      calc (φ b) ^ k = φ (b ^ k) := by rw [map_zpow]
        _ = φ (x * b * x⁻¹) := by rw [hk]
        _ = φ x * φ b * (φ x)⁻¹ := by simp
        _ = xbar * φ b * xbar⁻¹ := by rw [hxφ]
        _ = (φ b) ^ m := hconj
    have hmod : k ≡ m [ZMOD (r : ℤ)] := by
      have h2 := (zpow_eq_zpow_iff_modEq (x := φ b)).mp h1
      rwa [hφb_ord] at h2
    rw [zpow_eq_zpow_iff_modEq]
    rwa [hb]
  exact ⟨x, hxφ, by rw [← hpow_eq]; exact hk.symm⟩

end CFSG.GroupTheory
