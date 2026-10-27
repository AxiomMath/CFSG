module

public import CFSG.GF2Type.Smith1980Orth.S3CaseB
public import CFSG.GF2Type.Smith1980Orth.S3Count

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S14 CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G}

private theorem ρ_mul_pow_eq_one_iff {x y : G} (hxM : x ∈ S.M) (hyM : y ∈ S.M) (n : ℕ) :
    (S.ρ ⟨x, hxM⟩ * S.ρ ⟨y, hyM⟩) ^ n = 1 ↔ (x * y) ^ n ∈ S.QG := by
  rw [← map_mul, ← map_pow, S.ρ_eq_one_iff]
  rfl

private theorem eq_one_of_sq_of_cube {M : Type*} [Group M] {x : M} (h2 : x * x = 1)
    (h3 : x ^ 3 = 1) : x = 1 := by
  calc x = x ^ 3 * (x * x)⁻¹ := by group
    _ = 1 := by rw [h3, h2, inv_one, mul_one]

private theorem mul_mul_eq_one_of_comm {M : Type*} [Group M] {a b : M} (haa : a * a = 1)
    (hbb : b * b = 1) (hc : a * b = b * a) : (a * b) * (a * b) = 1 := by
  calc a * b * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [hc]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [haa, hbb, mul_one]

private theorem ne_one_left {M : Type*} [Group M] {x y : M} (hyy : y * y = 1)
    (h3 : (x * y) ^ 3 = 1) (h1 : x * y ≠ 1) : x ≠ 1 := by
  rintro rfl
  rw [one_mul] at h3 h1
  exact h1 (eq_one_of_sq_of_cube hyy h3)

private theorem ne_one_right {M : Type*} [Group M] {x y : M} (hxx : x * x = 1)
    (h3 : (x * y) ^ 3 = 1) (h1 : x * y ≠ 1) : y ≠ 1 := by
  rintro rfl
  rw [mul_one] at h3 h1
  exact h1 (eq_one_of_sq_of_cube hxx h3)

private theorem ρ_mul_self_of_isConj {a : G} (ha : IsConj S.z a) (haM : a ∈ S.M) :
    S.ρ ⟨a, haM⟩ * S.ρ ⟨a, haM⟩ = 1 := by
  rw [← map_mul]
  have h : (⟨a, haM⟩ : S.M) * ⟨a, haM⟩ = 1 :=
    Subtype.ext (SmithQ.mul_self_eq_one_of_isConj S ha)
  rw [h, map_one]

namespace S2Data

variable (D : S2Data S)

theorem types_of_orderOf_eq_three (hT : D.OTypes) {a b : G} (ha : IsConj S.z a)
    (hb : IsConj S.z b) (haM : a ∈ S.M) (hbM : b ∈ S.M) (h3 : orderOf (a * b) = 3) :
    a ∉ S.QG ∧ b ∉ S.QG ∧
      ((D.IsTInv (S.ρ ⟨a, haM⟩) ∧ D.IsTInv (S.ρ ⟨b, hbM⟩)) ∨
        (D.IsUInv (S.ρ ⟨a, haM⟩) ∧ D.IsUInv (S.ρ ⟨b, hbM⟩))) := by
  have habQ : a * b ∉ S.QG := fun h => by
    have h4 := orderOf_dvd_of_pow_eq_one (S.pow_four_eq_one h)
    rw [h3] at h4
    omega
  have hab1 : S.ρ ⟨a, haM⟩ * S.ρ ⟨b, hbM⟩ ≠ 1 := fun h => habQ (by
    simpa using (ρ_mul_pow_eq_one_iff haM hbM 1).mp (by rw [pow_one]; exact h))
  have hab3 : (S.ρ ⟨a, haM⟩ * S.ρ ⟨b, hbM⟩) ^ 3 = 1 :=
    (ρ_mul_pow_eq_one_iff haM hbM 3).mpr (by rw [← h3]; simp)
  have haa := ρ_mul_self_of_isConj ha haM
  have hbb := ρ_mul_self_of_isConj hb hbM
  have haQ : a ∉ S.QG := fun h =>
    ne_one_left hbb hab3 hab1 ((S.ρ_eq_one_iff ⟨a, haM⟩).mpr h)
  have hbQ : b ∉ S.QG := fun h =>
    ne_one_right haa hab3 hab1 ((S.ρ_eq_one_iff ⟨b, hbM⟩).mpr h)
  refine ⟨haQ, hbQ, ?_⟩
  rcases hT a ha haM haQ with haT | haU <;> rcases hT b hb hbM hbQ with hbT | hbU
  · exact Or.inl ⟨haT, hbT⟩
  · obtain ⟨hs, -⟩ := hbU
    exact absurd (eq_one_of_sq_of_cube
      (mul_mul_eq_one_of_comm haa hbb (D.comm_of_isTInv_of_mem_Cbar haT hs)) hab3) hab1
  · obtain ⟨hs, -⟩ := haU
    exact absurd (eq_one_of_sq_of_cube
      (mul_mul_eq_one_of_comm haa hbb (D.comm_of_isTInv_of_mem_Cbar hbT hs).symm) hab3) hab1
  · exact Or.inr ⟨haU, hbU⟩

theorem eq_one_or_z_of_commute_of_isTInv {a b : G} (haM : a ∈ S.M) (hbM : b ∈ S.M)
    (haT : D.IsTInv (S.ρ ⟨a, haM⟩)) (hbT : D.IsTInv (S.ρ ⟨b, hbM⟩))
    (hab : S.ρ ⟨a, haM⟩ ≠ S.ρ ⟨b, hbM⟩) {q : G} (hq : q ∈ S.QG)
    (hqθ : (a * b) * q = q * (a * b)) : q = 1 ∨ q = S.z := by
  have hθM : a * b ∈ S.M := S.M.mul_mem haM hbM
  have hρθ : S.ρ ⟨a * b, hθM⟩ = S.ρ ⟨a, haM⟩ * S.ρ ⟨b, hbM⟩ := by
    rw [← map_mul]
    rfl
  have hfix : ((S.ρ ⟨a * b, hθM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl q) = S.cl q := by
    rw [S.ρ_cl ⟨a * b, hθM⟩ hq]
    congr 1
    calc a * b * q * (a * b)⁻¹ = q * (a * b) * (a * b)⁻¹ := by rw [hqθ]
      _ = q := by group
  rw [← S.cl_eq_zero_iff hq]
  rw [hρθ] at hfix
  rcases D.mul_eq_of_isTInv haT hbT with h | h | h
  · exact absurd (mul_left_cancel (h.trans (D.mul_self_of_isTInv haT).symm)).symm hab
  · rw [h] at hfix
    exact D.k_fix_eq_zero _ hfix
  · rw [h, coe_mul_apply] at hfix
    apply D.k_fix_eq_zero
    calc (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl q)
        = (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt)
          ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl q))) := by rw [hfix]
      _ = S.cl q := D.k_apply_cube _

theorem finrank_commSpace_eq_width_of_isTInv {a : S.O} (ha : D.IsTInv a) :
    finrank (ZMod 2) (commSpace (a : S.Qt ≃ₗ[ZMod 2] S.Qt)) = S.width := by
  rcases ha with rfl | rfl | rfl
  · rw [D.commSpace_eq, D.finrank_Vt]
  · rw [D.commSpace_kt_eq, D.finrank_Wkt]
  · rw [D.commSpace_kkt_eq, D.finrank_Wk]

theorem finrank_commSpace_eq_four_of_isUInv {a : S.O} (ha : D.IsUInv a) :
    finrank (ZMod 2) (commSpace (a : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 4 := by
  obtain ⟨hs, hA⟩ := ha
  have h := D.finrank_commSpace_Cbar ⟨a, hs⟩
  rw [hA.2.2.2.1] at h
  exact h

private theorem card_Dl_eq_pow_finrank {k : G} (hxM : k * S.z * k⁻¹ ∈ S.M)
    (hT : D.IsTInv (S.ρ ⟨_, hxM⟩) ∨ D.IsUInv (S.ρ ⟨_, hxM⟩)) (hxQ : k * S.z * k⁻¹ ∉ S.QG)
    (hxz : ¬ IsConj S.z (k * S.z * k⁻¹ * S.z)) (hΔ : S.QG ⊓ S.Qa k ≠ ⊥) :
    Nat.card (S.QG ⊓ S.Qa k : Subgroup G) =
      2 ^ finrank (ZMod 2) (commSpace (S.ρ ⟨_, hxM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  rw [← SMK.card_clSub_Dl S hxQ, S.card_submodule,
    D.clSub_Dl_eq_commSpace_of_types hxM hT hxQ hxz hΔ, S.commQt_of_mem hxM]

theorem card_Dl_of_isTInv {k : G} (hxM : k * S.z * k⁻¹ ∈ S.M) (hxQ : k * S.z * k⁻¹ ∉ S.QG)
    (hxz : ¬ IsConj S.z (k * S.z * k⁻¹ * S.z)) (hΔ : S.QG ⊓ S.Qa k ≠ ⊥)
    (h : D.IsTInv (S.ρ ⟨_, hxM⟩)) : Nat.card (S.QG ⊓ S.Qa k : Subgroup G) = 2 ^ S.width := by
  rw [D.card_Dl_eq_pow_finrank hxM (Or.inl h) hxQ hxz hΔ, D.finrank_commSpace_eq_width_of_isTInv h]

theorem card_Dl_of_isUInv {k : G} (hxM : k * S.z * k⁻¹ ∈ S.M) (hxQ : k * S.z * k⁻¹ ∉ S.QG)
    (hxz : ¬ IsConj S.z (k * S.z * k⁻¹ * S.z)) (hΔ : S.QG ⊓ S.Qa k ≠ ⊥)
    (h : D.IsUInv (S.ρ ⟨_, hxM⟩)) : Nat.card (S.QG ⊓ S.Qa k : Subgroup G) = 2 ^ 4 := by
  rw [D.card_Dl_eq_pow_finrank hxM (Or.inr h) hxQ hxz hΔ, D.finrank_commSpace_eq_four_of_isUInv h]

end S2Data

end CFSG.GF2Type.Smith1980Orth
