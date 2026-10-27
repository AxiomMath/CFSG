module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64F

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

section Dihedral

variable {Q : Type*} [Group Q] {a b : Q}

theorem dihedral_conj (ha : a * a = 1) (hb : b * b = 1) : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  rw [mul_inv_rev, ha', hb', ← mul_assoc, ha, one_mul]

theorem dihedral_conj_zpow (ha : a * a = 1) (hb : b * b = 1) (i : ℤ) :
    a * (a * b) ^ i * a⁻¹ = ((a * b) ^ i)⁻¹ := by
  have h := dihedral_conj ha hb
  have : a * (a * b) ^ i * a⁻¹ = (a * (a * b) * a⁻¹) ^ i := by
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
  rw [this, h, inv_zpow]

theorem dihedral_zpow_mul (ha : a * a = 1) (hb : b * b = 1) (i : ℤ) :
    (a * b) ^ i * a = a * (a * b) ^ (-i) := by
  have h := dihedral_conj_zpow ha hb (-i)
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  rw [zpow_neg, inv_inv] at h
  calc (a * b) ^ i * a = (a * ((a * b) ^ i)⁻¹ * a⁻¹) * a := by rw [h]
    _ = a * (a * b) ^ (-i) := by rw [zpow_neg]; group

theorem dihedral_normal_form (ha : a * a = 1) (hb : b * b = 1)
    (hgen : ∀ q : Q, q ∈ Subgroup.closure ({a, b} : Set Q)) (q : Q) :
    ∃ i : ℤ, q = (a * b) ^ i ∨ q = a * (a * b) ^ i := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  let S : Subgroup Q :=
    { carrier := {q | ∃ i : ℤ, q = (a * b) ^ i ∨ q = a * (a * b) ^ i}
      mul_mem' := by
        rintro _ _ ⟨i, rfl | rfl⟩ ⟨k, rfl | rfl⟩
        · exact ⟨i + k, Or.inl (zpow_add _ _ _).symm⟩
        · refine ⟨-i + k, Or.inr ?_⟩
          rw [← mul_assoc, dihedral_zpow_mul ha hb, mul_assoc, ← zpow_add]
        · exact ⟨i + k, Or.inr (by rw [mul_assoc, ← zpow_add])⟩
        · refine ⟨-i + k, Or.inl ?_⟩
          rw [mul_assoc, ← mul_assoc ((a * b) ^ i), dihedral_zpow_mul ha hb, ← mul_assoc,
            ← mul_assoc, ha, one_mul, ← zpow_add]
      one_mem' := ⟨0, Or.inl (zpow_zero _).symm⟩
      inv_mem' := by
        rintro _ ⟨i, rfl | rfl⟩
        · exact ⟨-i, Or.inl (zpow_neg _ _).symm⟩
        · refine ⟨i, Or.inr ?_⟩
          rw [mul_inv_rev, ha', ← zpow_neg, dihedral_zpow_mul ha hb, neg_neg] }
  have hle : Subgroup.closure ({a, b} : Set Q) ≤ S := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ⟨0, Or.inr (by rw [zpow_zero, mul_one])⟩
    · exact ⟨1, Or.inr (by rw [zpow_one, ← mul_assoc, ha, one_mul])⟩
  exact hle (hgen q)

end Dihedral

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J R T : Subgroup G}
  {z j u v : G}

namespace Cfg64

variable (c : Cfg64 Ω K J z j u v R T)
include c

theorem conj_t_z {t : G} (ht : t ∈ T) (htv : t ∉ Subgroup.zpowers v) : t * z * t⁻¹ = z * j := by
  rw [c.symm.conj_j_of_not_mem ht htv, c.zj_comm]

omit [Finite G] in
theorem conj_t_j {t : G} (ht : t ∈ T) : t * j * t⁻¹ = j := c.symm.conj_z ht

theorem conj_rho_z {r t : G} (hr : r ∈ R) (hru : r ∉ Subgroup.zpowers u) (ht : t ∈ T)
    (htv : t ∉ Subgroup.zpowers v) : (r * t) * z * (r * t)⁻¹ = j := by
  calc (r * t) * z * (r * t)⁻¹ = r * (t * z * t⁻¹) * r⁻¹ := by group
    _ = (r * z * r⁻¹) * (r * j * r⁻¹) := by rw [c.conj_t_z ht htv]; group
    _ = z * (z * j) := by rw [c.conj_z hr, c.conj_j_of_not_mem hr hru]
    _ = j := by rw [← mul_assoc, c.hz.sq, one_mul]

theorem conj_rho_j {r t : G} (hr : r ∈ R) (hru : r ∉ Subgroup.zpowers u) (ht : t ∈ T) :
    (r * t) * j * (r * t)⁻¹ = z * j := by
  calc (r * t) * j * (r * t)⁻¹ = r * (t * j * t⁻¹) * r⁻¹ := by group
    _ = z * j := by rw [c.conj_t_j ht, c.conj_j_of_not_mem hr hru]

theorem conj_rho3_z {r t : G} (hr : r ∈ R) (hru : r ∉ Subgroup.zpowers u) (ht : t ∈ T)
    (htv : t ∉ Subgroup.zpowers v) : (r * t) ^ 3 * z * ((r * t) ^ 3)⁻¹ = z := by
  have h1 := c.conj_rho_z hr hru ht htv
  have h2 := c.conj_rho_j hr hru ht
  have h3 : (r * t) * (z * j) * (r * t)⁻¹ = z := by
    calc (r * t) * (z * j) * (r * t)⁻¹ =
          ((r * t) * z * (r * t)⁻¹) * ((r * t) * j * (r * t)⁻¹) := by group
      _ = j * (z * j) := by rw [h1, h2]
      _ = z := by
        rw [← mul_assoc, ← c.zj_comm, mul_assoc, c.hj.sq, mul_one]
  rw [pow_three]
  calc (r * t) * ((r * t) * (r * t)) * z * ((r * t) * ((r * t) * (r * t)))⁻¹ =
        (r * t) * ((r * t) * ((r * t) * z * (r * t)⁻¹) * (r * t)⁻¹) * (r * t)⁻¹ := by group
    _ = z := by rw [h1, h2, h3]

theorem conj_rho3_j {r t : G} (hr : r ∈ R) (hru : r ∉ Subgroup.zpowers u) (ht : t ∈ T)
    (htv : t ∉ Subgroup.zpowers v) : (r * t) ^ 3 * j * ((r * t) ^ 3)⁻¹ = j := by
  have h1 := c.conj_rho_z hr hru ht htv
  have h2 := c.conj_rho_j hr hru ht
  have h3 : (r * t) * (z * j) * (r * t)⁻¹ = z := by
    calc (r * t) * (z * j) * (r * t)⁻¹ =
          ((r * t) * z * (r * t)⁻¹) * ((r * t) * j * (r * t)⁻¹) := by group
      _ = j * (z * j) := by rw [h1, h2]
      _ = z := by
        rw [← mul_assoc, ← c.zj_comm, mul_assoc, c.hj.sq, mul_one]
  rw [pow_three]
  calc (r * t) * ((r * t) * (r * t)) * j * ((r * t) * ((r * t) * (r * t)))⁻¹ =
        (r * t) * ((r * t) * ((r * t) * j * (r * t)⁻¹) * (r * t)⁻¹) * (r * t)⁻¹ := by group
    _ = j := by rw [h2, h3, h1]

theorem conj_rho_zpow_z_eq_iff {r t : G} (hr : r ∈ R) (hru : r ∉ Subgroup.zpowers u)
    (ht : t ∈ T) (htv : t ∉ Subgroup.zpowers v) (i : ℤ) :
    (r * t) ^ i * z * ((r * t) ^ i)⁻¹ = z ↔ (3 : ℤ) ∣ i := by
  set ρ := r * t with hρ
  have h1 := c.conj_rho_z hr hru ht htv
  have h2 := c.conj_rho_j hr hru ht
  have hc3 : Commute (ρ ^ 3) z := by
    have := c.conj_rho3_z hr hru ht htv
    show ρ ^ 3 * z = z * ρ ^ 3
    calc ρ ^ 3 * z = ρ ^ 3 * z * (ρ ^ 3)⁻¹ * ρ ^ 3 := by group
      _ = z * ρ ^ 3 := by rw [this]
  have hdec : ρ ^ i = ρ ^ (i % 3) * (ρ ^ 3) ^ (i / 3) := by
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add]
    congr 1
    push_cast
    omega
  have hq : (ρ ^ 3) ^ (i / 3) * z * ((ρ ^ 3) ^ (i / 3))⁻¹ = z := by
    rw [(hc3.zpow_left (i / 3)).eq]
    group
  have hred : ρ ^ i * z * (ρ ^ i)⁻¹ = ρ ^ (i % 3) * z * (ρ ^ (i % 3))⁻¹ := by
    have e : ρ ^ (i % 3) * (ρ ^ 3) ^ (i / 3) * z * (ρ ^ (i % 3) * (ρ ^ 3) ^ (i / 3))⁻¹ =
        ρ ^ (i % 3) * ((ρ ^ 3) ^ (i / 3) * z * ((ρ ^ 3) ^ (i / 3))⁻¹) * (ρ ^ (i % 3))⁻¹ := by
      group
    rw [hdec, e, hq]
  rw [hred]
  have hr0 : 0 ≤ i % 3 := Int.emod_nonneg i (by norm_num)
  have hr3 : i % 3 < 3 := Int.emod_lt_of_pos i (by norm_num)
  have hcases : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases hcases with h | h | h
  · rw [h, zpow_zero]
    simp only [one_mul, inv_one, mul_one, true_iff]
    omega
  · rw [h, zpow_one, h1]
    constructor
    · intro hjz
      exact absurd hjz.symm c.z_ne_j
    · intro hd
      omega
  · rw [h]
    have e : ρ ^ (2 : ℤ) * z * (ρ ^ (2 : ℤ))⁻¹ = z * j := by
      rw [zpow_two]
      calc ρ * ρ * z * (ρ * ρ)⁻¹ = ρ * (ρ * z * ρ⁻¹) * ρ⁻¹ := by group
        _ = z * j := by rw [h1, h2]
    rw [e]
    constructor
    · intro hzj
      exact absurd hzj c.zj_ne_z
    · intro hd
      omega

end Cfg64

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
