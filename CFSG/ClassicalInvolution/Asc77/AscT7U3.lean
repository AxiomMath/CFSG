module

public import CFSG.ClassicalInvolution.Asc77.AscP1ThreeTwelve
public import CFSG.ClassicalInvolution.AschTight.Sec7L714A
public import CFSG.ClassicalInvolution.Asc77.AscT7TFAut

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T7U

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G]

theorem exists_sq_mem_zpowers {S R : Subgroup G} {z : G} (hRS : R ≤ S)
    (hidx : Nat.card S = 2 * Nat.card R) (hS2 : IsPGroup 2 ↥S) (hz : IsUniqueInvolution R z)
    (hS : IsQuaternionSub S ∨ IsSemidihedral S) :
    ∃ s ∈ S, s ∉ R ∧ s * s ∈ Subgroup.zpowers z := by
  have hRn : ∀ y ∈ S, conjSub y R = R := fun y hy =>
    ThreeTwelve.conjSub_eq_of_card_eq_two_mul hRS hidx hy
  have hRpos : 0 < Nat.card R := Nat.card_pos
  rcases hS with ⟨a, b, h4, hcard, hbb, hba, hcl⟩ | ⟨a, b, h8, hcard, hbb, hbnot, hba, hcl⟩
  ·
    have haS : a ∈ S := hcl ▸ Subgroup.subset_closure (by simp)
    have hbS : b ∈ S := hcl ▸ Subgroup.subset_closure (by simp)
    have hCS : Subgroup.zpowers a ≤ S := Subgroup.zpowers_le.mpr haS
    have hcardC : Nat.card S = 2 * Nat.card (Subgroup.zpowers a) := by
      rw [Nat.card_zpowers]; exact hcard
    have hbC : b ∉ Subgroup.zpowers a := by
      intro hb
      have hle : S ≤ Subgroup.zpowers a := by
        rw [← hcl, Subgroup.closure_le]
        rintro x (rfl | rfl)
        · exact Subgroup.mem_zpowers _
        · exact hb
      have := Subgroup.card_le_of_le hle
      have hp : 0 < Nat.card (Subgroup.zpowers a) := Nat.card_pos
      omega
    obtain ⟨s, hsS, hsC, hsR⟩ : ∃ s ∈ S, s ∉ Subgroup.zpowers a ∧ s ∉ R := by
      by_contra hcon
      push Not at hcon
      have hbR : b ∈ R := hcon b hbS hbC
      have hSR : S ≤ R := by
        intro y hy
        by_cases hyC : y ∈ Subgroup.zpowers a
        · have hbyC : b * y ∉ Subgroup.zpowers a := by
            intro h
            have h' : b * y * y⁻¹ ∈ Subgroup.zpowers a :=
              (Subgroup.zpowers a).mul_mem h ((Subgroup.zpowers a).inv_mem hyC)
            exact hbC (by simpa using h')
          have h1 := hcon (b * y) (S.mul_mem hbS hy) hbyC
          have h2 : b⁻¹ * (b * y) ∈ R := R.mul_mem (R.inv_mem hbR) h1
          simpa using h2
        · exact hcon y hy hyC
      have := Subgroup.card_le_of_le hSR
      omega
    obtain ⟨m, hm⟩ := AscL62.orderOf_eq_two_pow_of_isPGroup hS2 haS
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by
      have : 2 ^ 2 ≤ 2 ^ m := hm ▸ (by simpa using h4)
      have : 2 ≤ m := (Nat.pow_le_pow_iff_right (by norm_num)).mp this
      omega⟩
    have huI : IsUniqueInvolution (Subgroup.zpowers a) (a ^ 2 ^ k) :=
      CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7.isUniqueInvolution_zpowers hm
    have hz₀ : orderOf a / 2 = 2 ^ k := by rw [hm]; omega
    have hbb' : b * b = a ^ 2 ^ k := by rw [hbb, hz₀]
    have hc : b⁻¹ * s ∈ Subgroup.zpowers a :=
      AscL62.inv_mul_mem_of_index_two hCS hcardC hbS hsS hbC hsC
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hc
    have hsb : s = b * a ^ j := by rw [hj]; group
    have hconj : b * a ^ j * b⁻¹ = (a ^ j)⁻¹ := by
      rw [T7T.conj_zpow hba j, inv_zpow', zpow_neg]
    have hz₀c : a ^ 2 ^ k * a ^ j = a ^ j * a ^ 2 ^ k := by
      rw [← zpow_natCast, ← zpow_add, ← zpow_add, add_comm]
    have hss : s * s = a ^ 2 ^ k := by
      calc s * s = (b * a ^ j * b⁻¹) * (b * b) * a ^ j := by rw [hsb]; group
        _ = (a ^ j)⁻¹ * a ^ 2 ^ k * a ^ j := by rw [hconj, hbb']
        _ = a ^ 2 ^ k := by
          rw [mul_assoc, hz₀c, ← mul_assoc, inv_mul_cancel, one_mul]
    have hzS : z ∈ S := hRS hz.mem
    have hzC : z ∈ Subgroup.zpowers a := by
      by_contra hzC
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp
        (AscL62.inv_mul_mem_of_index_two hCS hcardC hbS hzS hbC hzC)
      have hzb : z = b * a ^ i := by rw [hi]; group
      have hconj' : b * a ^ i * b⁻¹ = (a ^ i)⁻¹ := by
        rw [T7T.conj_zpow hba i, inv_zpow', zpow_neg]
      have hz2 : z * z = a ^ 2 ^ k := by
        calc z * z = (b * a ^ i * b⁻¹) * (b * b) * a ^ i := by rw [hzb]; group
          _ = (a ^ i)⁻¹ * a ^ 2 ^ k * a ^ i := by rw [hconj', hbb']
          _ = a ^ 2 ^ k := by
            have : a ^ 2 ^ k * a ^ i = a ^ i * a ^ 2 ^ k := by
              rw [← zpow_natCast, ← zpow_add, ← zpow_add, add_comm]
            rw [mul_assoc, this, ← mul_assoc, inv_mul_cancel, one_mul]
      exact huI.ne_one (hz2 ▸ hz.sq)
    have hzeq : z = a ^ 2 ^ k := by
      rcases huI.unique z hzC hz.sq with h | h
      · exact absurd h hz.ne_one
      · exact h
    exact ⟨s, hsS, hsR, by rw [hss, ← hzeq]; exact Subgroup.mem_zpowers z⟩
  ·
    have haS : a ∈ S := hcl ▸ Subgroup.subset_closure (by simp)
    have hbS : b ∈ S := hcl ▸ Subgroup.subset_closure (by simp)
    refine ⟨b, hbS, fun hbR => ?_, by rw [hbb]; exact one_mem _⟩
    rcases hz.unique b hbR hbb with h | h
    · exact hbnot (h ▸ one_mem _)
    ·
      have hab : a * b * a⁻¹ = b := by rw [h]; exact hz.conj_eq (hRn a haS)
      have hba' : b * a * b⁻¹ = a := by
        have : a * b = b * a := by
          calc a * b = (a * b * a⁻¹) * a := by group
            _ = b * a := by rw [hab]
        calc b * a * b⁻¹ = (a * b) * b⁻¹ := by rw [this]
          _ = a := by group
      have hexp : a ^ (orderOf a / 2 - 1) = a := by rw [← hba, hba']
      have hge : 2 ≤ orderOf a / 2 := by omega
      have h1 : a ^ (orderOf a / 2 - 2) = 1 := by
        have e : orderOf a / 2 - 1 = (orderOf a / 2 - 2) + 1 := by omega
        rw [e, pow_succ] at hexp
        have : a ^ (orderOf a / 2 - 2) * a = 1 * a := by rw [hexp, one_mul]
        exact mul_right_cancel this
      have h2 := orderOf_dvd_of_pow_eq_one h1
      have h3 := Nat.le_of_dvd (by omega) h2
      omega

end CFSG.ClassicalInvolution.Asc77.T7U
