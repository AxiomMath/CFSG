module

public import CFSG.GH74.GLS.LU.Local.FiveWCfg
public import CFSG.GH74.GLS.LU.Local.FiveL88f

public section

open Subgroup CFSG CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

section L83b

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ : G} {X₁ : Subgroup G}

def invSub (A : Subgroup G) (g : G) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : Subgroup G where
  carrier := {a | a ∈ A ∧ g * a * g⁻¹ = a⁻¹}
  one_mem' := ⟨A.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨A.mul_mem ha hb, ?_⟩
    have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e, ha', hb', mul_inv_rev]
    have := hcomm a ha b hb
    have h2 : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := by
      have := congrArg (·⁻¹) this
      simpa [mul_inv_rev] using this.symm
    rw [h2]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨A.inv_mem ha, ?_⟩
    have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [e, ha']

omit [Finite G] in
theorem mem_invSub {A : Subgroup G} {g : G} {hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a} {a : G} :
    a ∈ invSub A g hcomm ↔ a ∈ A ∧ g * a * g⁻¹ = a⁻¹ := Iff.rfl

theorem comm_of_card_five {A : Subgroup G} (h : Nat.card ↥A = 5) :
    ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
  obtain ⟨g, rfl⟩ := exists_zpowers_of_card_five A h
  intro a ha b hb
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact (Commute.zpow_zpow_self g i j).eq

theorem exists_ne_one_of_card_gt_one {A : Subgroup G} (h : 1 < Nat.card ↥A) :
    ∃ a ∈ A, a ≠ 1 := by
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := A)).mp
    ((Subgroup.one_lt_card_iff_ne_bot A).mp h)
  exact ⟨a, a.2, fun h1 => ha (Subtype.ext h1)⟩

theorem Cfg2W.tz_comm (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : t * z = z * t :=
  c.hs.comm_z c.hs.t_mem

theorem Cfg2W.t_ne_one (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : t ≠ 1 := by
  intro h
  have h1 := c.hs.t_conj
  rw [h] at h1
  have : z = 1 := isConj_one_left.mp h1
  exact c.z_ne_one this

theorem Cfg2W.t_ne_z (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : t ≠ z := by
  intro h
  have h1 : cjL t K₁ = K₂ := c.hs.t_swap
  have h2 : cjL t K₁ = K₁ := by
    rw [h]
    apply cjL_eq_of_comm
    intro a ha
    exact (c.hc.cz₁ ha).symm
  exact c.hc.ne (h2.symm.trans h1)

theorem Cfg2W.card_TT (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : Nat.card ↥(TT z t) = 4 := by
  have hz2 : z * z = 1 := c.hs.z_sq
  have ht2 : t * t = 1 := c.t_sq
  have hcomm : ∀ a ∈ zpowers z, ∀ b ∈ zpowers t, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((Commute.zpow_right (Commute.zpow_left (c.tz_comm.symm : Commute z t) i) j)).eq
  have hdisj : zpowers z ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    rcases mem_zpowers_of_sq_eq_one hz2 hx1 with h1 | h1
    · rw [h1]; exact Subgroup.one_mem _
    · rcases mem_zpowers_of_sq_eq_one ht2 hx2 with h2 | h2
      · rw [h2]; exact Subgroup.one_mem _
      · exact absurd (h2.symm.trans h1) c.t_ne_z
  rw [TT, card_sup_of_commute_disjoint hcomm hdisj]
  have hz : Nat.card ↥(zpowers z) = 2 := by rw [Nat.card_zpowers]; exact c.hs.z_inv
  have ht : Nat.card ↥(zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact ht2) c.t_ne_one
  rw [hz, ht]

theorem Cfg2W.TT_comm (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) :
    ∀ a ∈ TT z t, ∀ b ∈ TT z t, a * b = b * a := by
  have hz : ∀ a ∈ zpowers z, ∀ b ∈ zpowers z, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow_self z i j).eq
  have ht : ∀ a ∈ zpowers t, ∀ b ∈ zpowers t, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow_self t i j).eq
  have hzt : ∀ a ∈ zpowers z, ∀ b ∈ zpowers t, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((Commute.zpow_right (Commute.zpow_left (c.tz_comm.symm : Commute z t) i) j)).eq
  exact commute_sup hz ht hzt

theorem Cfg2W.TT_sq (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : ∀ a ∈ TT z t, a * a = 1 := by
  have hzt : ∀ a ∈ zpowers z, ∀ b ∈ zpowers t, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((Commute.zpow_right (Commute.zpow_left (c.tz_comm.symm : Commute z t) i) j)).eq
  intro a ha
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_sup_of_commute hzt).mp ha
  have hx2 : x * x = 1 := by
    rcases mem_zpowers_of_sq_eq_one c.hs.z_sq hx with h | h
    · rw [h, one_mul]
    · rw [h]; exact c.hs.z_sq
  have hy2 : y * y = 1 := by
    rcases mem_zpowers_of_sq_eq_one c.t_sq hy with h | h
    · rw [h, one_mul]
    · rw [h]; exact c.t_sq
  have hxy := hzt x hx y hy
  calc x * y * (x * y) = x * (y * x) * y := by group
    _ = x * (x * y) * y := by rw [← hxy]
    _ = (x * x) * (y * y) := by group
    _ = 1 := by rw [hx2, hy2, one_mul]

end L83b

end CFSG.GH74.GLS.LU.Local.Five
