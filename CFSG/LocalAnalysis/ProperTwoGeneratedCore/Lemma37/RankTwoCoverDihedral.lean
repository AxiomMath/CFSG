module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankTwoCoverCommutator

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open DihedralGroup

variable {P X : Type*} [Group P] [Group X]

theorem index_zpowers_of_ker_le (ψ : P →* X) (hψ : Function.Surjective ψ) {x : P}
    (hker : ∀ z, ψ z = 1 → z ∈ Subgroup.zpowers x) :
    (Subgroup.zpowers x).index = (Subgroup.zpowers (ψ x)).index := by
  have hle : ψ.ker ≤ Subgroup.zpowers x := fun z hz => hker z hz
  rw [← Subgroup.index_comap_of_surjective _ hψ, ← MonoidHom.map_zpowers,
    Subgroup.comap_map_eq, sup_eq_left.mpr hle]

theorem dihedral_index_zpowers_r_one {m : ℕ} [NeZero m] :
    (Subgroup.zpowers (r 1 : DihedralGroup m)).index = 2 := by
  have h := Subgroup.index_mul_card (Subgroup.zpowers (r 1 : DihedralGroup m))
  rw [Nat.card_zpowers, orderOf_r_one, nat_card] at h
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  exact Nat.eq_of_mul_eq_mul_right hm h

theorem dihedral_sr_not_mem_zpowers {m : ℕ} :
    (sr 0 : DihedralGroup m) ∉ Subgroup.zpowers (r 1) := by
  intro h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  rw [r_one_zpow] at hk
  simp at hk

theorem dihedral_map_w {m : ℕ} (ψ : P →* DihedralGroup m) {r₀ s₀ : P} (hr₀ : ψ r₀ = r 1)
    (hs₀ : ψ s₀ = sr 0) : ψ (r₀⁻¹ * (s₀ * r₀ * s₀⁻¹)) = r (-2) := by
  rw [map_mul, map_inv, map_mul, map_mul, map_inv, hr₀, hs₀, inv_r, inv_sr, sr_mul_r, sr_mul_sr,
    r_mul_r]
  congr 1
  ring

theorem exists_cyclic_index_two_of_dihedral_of_two_lt [Finite P] (hP : IsPGroup 2 P) {m : ℕ}
    (hm : 2 < m) (ψ : P →* DihedralGroup m) (hψ : Function.Surjective ψ)
    (hcen : ∀ c, ψ c = 1 → ∀ g, g * c = c * g) (hker : ∀ z, ψ z = 1 → z ∈ commutator P) :
    ∃ x : P, (Subgroup.zpowers x).index = 2 ∧ ∀ z, ψ z = 1 → z ∈ Subgroup.zpowers x := by
  have : NeZero m := ⟨by omega⟩
  obtain ⟨r₀, hr₀⟩ := hψ (r 1)
  obtain ⟨s₀, hs₀⟩ := hψ (sr 0)
  set w := r₀⁻¹ * (s₀ * r₀ * s₀⁻¹) with hw
  have hcomm : commutator P ≤ Subgroup.zpowers w :=
    commutator_le_zpowers_of_index_two ψ hψ hcen (by rw [hr₀]; exact dihedral_index_zpowers_r_one)
      (by rw [hs₀, hr₀]; exact dihedral_sr_not_mem_zpowers)
  have hψw : ψ w = r (-2) := dihedral_map_w ψ hr₀ hs₀
  have hψw1 : ψ w ≠ 1 := by
    rw [hψw, one_def]
    intro h
    have h2 : ((2 : ℕ) : ZMod m) = 0 := by
      have := r.inj h
      rw [neg_eq_zero] at this
      exact_mod_cast this
    rw [ZMod.natCast_eq_zero_iff] at h2
    exact absurd (Nat.le_of_dvd two_pos h2) (by omega)
  have hc₁ : ψ (r₀ ^ 2 * w) = 1 := by
    rw [map_mul, map_pow, hr₀, hψw, pow_two, r_mul_r, r_mul_r, one_def]
    congr 1
    ring
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hcomm (hker _ hc₁))
  have hwr : w ∈ Subgroup.zpowers r₀ := by
    rcases Int.even_or_odd j with hje | hjo
    · have hodd : Odd (j - 1) := hje.sub_odd odd_one
      have hr2 : r₀ ^ 2 = w ^ (j - 1) := by
        rw [zpow_sub_one, hj, mul_inv_cancel_right]
      have hmem := mem_zpowers_zpow_of_odd hP w hodd
      rw [← hr2] at hmem
      exact Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers r₀) 2) hmem
    · exfalso
      have hmem := mem_zpowers_zpow_of_odd hP w hjo
      rw [hj] at hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      apply hψw1
      rw [← hk, map_zpow, hc₁, one_zpow]
  have hkerx : ∀ z, ψ z = 1 → z ∈ Subgroup.zpowers r₀ := fun z hz =>
    Subgroup.zpowers_le.mpr hwr (hcomm (hker z hz))
  refine ⟨r₀, ?_, hkerx⟩
  rw [index_zpowers_of_ker_le ψ hψ hkerx, hr₀]
  exact dihedral_index_zpowers_r_one

theorem exists_cyclic_index_two_of_dihedral_two (ψ : P →* DihedralGroup 2)
    (hψ : Function.Surjective ψ) (hcen : ∀ c, ψ c = 1 → ∀ g, g * c = c * g)
    (hker : ∀ z, ψ z = 1 → z ∈ commutator P) :
    ∃ x : P, (Subgroup.zpowers x).index = 2 ∧ ∀ z, ψ z = 1 → z ∈ Subgroup.zpowers x := by
  obtain ⟨r₀, hr₀⟩ := hψ (r 1)
  obtain ⟨s₀, hs₀⟩ := hψ (sr 0)
  set w := r₀⁻¹ * (s₀ * r₀ * s₀⁻¹) with hw
  have hcomm : commutator P ≤ Subgroup.zpowers w :=
    commutator_le_zpowers_of_index_two ψ hψ hcen (by rw [hr₀]; exact dihedral_index_zpowers_r_one)
      (by rw [hs₀, hr₀]; exact dihedral_sr_not_mem_zpowers)
  have hψw : ψ w = 1 := by rw [dihedral_map_w ψ hr₀ hs₀]; decide
  have hσ : s₀ * r₀ * s₀⁻¹ = r₀ * w := by rw [hw]; group
  have hs2 : ψ (s₀ * s₀) = 1 := by rw [map_mul, hs₀]; decide
  have hr2 : ψ (r₀ * r₀) = 1 := by rw [map_mul, hr₀]; decide
  have hww : w * w = 1 := by
    have h1 : s₀ * (s₀ * r₀ * s₀⁻¹) * s₀⁻¹ = r₀ := by
      calc s₀ * (s₀ * r₀ * s₀⁻¹) * s₀⁻¹ = (s₀ * s₀) * r₀ * (s₀ * s₀)⁻¹ := by group
        _ = r₀ := by rw [← hcen _ hs2 r₀, mul_inv_cancel_right]
    have h2 : s₀ * (s₀ * r₀ * s₀⁻¹) * s₀⁻¹ = r₀ * w * w := by
      calc s₀ * (s₀ * r₀ * s₀⁻¹) * s₀⁻¹ = s₀ * (r₀ * w) * s₀⁻¹ := by rw [hσ]
        _ = (s₀ * r₀ * s₀⁻¹) * (s₀ * w * s₀⁻¹) := by group
        _ = r₀ * w * w := by rw [hσ, hcen w hψw s₀, mul_inv_cancel_right]
    rw [h1] at h2
    have h3 : r₀⁻¹ * r₀ = r₀⁻¹ * (r₀ * w * w) := congrArg (r₀⁻¹ * ·) h2
    rw [inv_mul_cancel, mul_assoc, inv_mul_cancel_left] at h3
    exact h3.symm
  have hker2 : ∀ z, ψ z = 1 → z = 1 ∨ z = w := by
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hcomm (hker z hz))
    have hw2 : w ^ (2 : ℤ) = 1 := by rw [zpow_two, hww]
    rcases Int.even_or_odd' k with ⟨l, rfl | rfl⟩
    · left
      rw [zpow_mul, hw2, one_zpow]
    · right
      rw [zpow_add, zpow_mul, hw2, one_zpow, one_mul, zpow_one]
  have hrs : (r₀ * s₀) * (r₀ * s₀) = (r₀ * r₀) * w * (s₀ * s₀) := by
    calc (r₀ * s₀) * (r₀ * s₀) = r₀ * (s₀ * r₀ * s₀⁻¹) * (s₀ * s₀) := by group
      _ = (r₀ * r₀) * w * (s₀ * s₀) := by rw [hσ]; group
  obtain ⟨x, hxw, hψx⟩ : ∃ x, x * x = w ∧ ψ x ≠ 1 := by
    rcases hker2 _ hr2 with h | h
    · rcases hker2 _ hs2 with h' | h'
      · exact ⟨r₀ * s₀, by rw [hrs, h, h', one_mul, mul_one], by
          rw [map_mul, hr₀, hs₀]; decide⟩
      · exact ⟨s₀, h', by rw [hs₀]; decide⟩
    · exact ⟨r₀, h, by rw [hr₀]; decide⟩
  have hkerx : ∀ z, ψ z = 1 → z ∈ Subgroup.zpowers x := by
    intro z hz
    rcases hker2 z hz with rfl | rfl
    · exact Subgroup.one_mem _
    · rw [← hxw]
      exact Subgroup.mul_mem _ (Subgroup.mem_zpowers x) (Subgroup.mem_zpowers x)
  refine ⟨x, ?_, hkerx⟩
  rw [index_zpowers_of_ker_le ψ hψ hkerx]
  have hsq : ∀ g : DihedralGroup 2, g ^ 2 = 1 := by decide
  have hord : orderOf (ψ x) = 2 := orderOf_eq_prime (hsq _) hψx
  have h := Subgroup.index_mul_card (Subgroup.zpowers (ψ x))
  rw [Nat.card_zpowers, hord, nat_card] at h
  omega

theorem exists_cyclic_index_two_of_dihedral [Finite P] (hP : IsPGroup 2 P) {m : ℕ} (hm : 2 ≤ m)
    (ψ : P →* DihedralGroup m) (hψ : Function.Surjective ψ)
    (hcen : ∀ c, ψ c = 1 → ∀ g, g * c = c * g) (hker : ∀ z, ψ z = 1 → z ∈ commutator P) :
    ∃ x : P, (Subgroup.zpowers x).index = 2 ∧ ∀ z, ψ z = 1 → z ∈ Subgroup.zpowers x := by
  rcases hm.lt_or_eq with hm | rfl
  · exact exists_cyclic_index_two_of_dihedral_of_two_lt hP hm ψ hψ hcen hker
  · exact exists_cyclic_index_two_of_dihedral_two ψ hψ hcen hker

end CFSG.ProperTwoGeneratedCore.Lemma37
