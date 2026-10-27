module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7F0
public import CFSG.ClassicalInvolution.AschTight.Sec71Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

section Group

variable {G : Type} [Group G]

theorem isElemAbelian_closure_triple {a b c : G} (ha : a * a = 1) (hb : b * b = 1)
    (hc : c * c = 1) (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) :
    IsElemAbelian 2 (Subgroup.closure ({a, b, c} : Set G)) :=
  CFSG.ClassicalInvolution.ConnectedA2.isElemAbelian_closure_triple ha hb hc hab hac hbc

variable [Finite G]

theorem natCard_closure_triple_eight {z x y : G} (hz : z * z = 1) (hx : x * x = 1)
    (hy : y * y = 1) (hz1 : z ≠ 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxz : x ≠ z)
    (hzx : z * x = x * z) (hzy : z * y = y * z) (hxy : x * y = y * x)
    (hnot : y ∉ Subgroup.closure ({x, z} : Set G)) :
    Nat.card ↥(Subgroup.closure ({z, x, y} : Set G)) = 8 := by
  have hD := T7A.isElemAbelian2_closure_pair hx hz hx1 hz1 hxz hzx.symm
  have hy2 : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy) hy1
  have hcl : Subgroup.closure ({z, x, y} : Set G) =
      Subgroup.closure ({x, z} : Set G) ⊔ Subgroup.zpowers y := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro w hw
      rcases hw with rfl | rfl | rfl
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · refine sup_le ?_ (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
      rw [Subgroup.closure_le]
      intro w hw
      rcases hw with rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
  have hcomm : Commutes (Subgroup.closure ({x, z} : Set G)) (Subgroup.zpowers y) := by
    have hle : Subgroup.closure ({x, z} : Set G) ≤ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.closure_le]
      intro w hw
      rcases hw with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hxy
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hzy
    intro w hw v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    have : Commute w y := Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
    exact (this.zpow_right i).eq
  have hinf : Subgroup.closure ({x, z} : Set G) ⊓ Subgroup.zpowers y = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    rcases T7A.eq_one_or_eq_of_mem_zpowers hy2 he.2 with h1 | h1
    · rw [h1]
      exact Subgroup.one_mem _
    · exfalso
      apply hnot
      rw [← h1]
      exact he.1
  have hN := T7A.card_sup_mul_card_inf (T7A.le_normalizer_of_commutes hcomm)
  rw [hinf, Subgroup.card_bot, Nat.card_zpowers, hy2, hD.1, mul_one] at hN
  rw [hcl, sup_comm, hN]
  norm_num

end Group

section Frame3

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

structure Frame3 (Ω : Set (Subgroup G)) (z : G) (K₁ K₂ K₃ R₁ R₂ R₃ : Subgroup G)
    (u₁ u₂ u₃ : G) : Prop where
  mem₁ : K₁ ∈ Ω
  mem₂ : K₂ ∈ Ω
  mem₃ : K₃ ∈ Ω
  hz₁ : IsUniqueInvolution K₁ z
  hz₂ : IsUniqueInvolution K₂ z
  hz₃ : IsUniqueInvolution K₃ z
  ne₁₂ : K₂ ≠ K₁
  ne₁₃ : K₃ ≠ K₁
  ne₂₃ : K₃ ≠ K₂
  syl₁ : IsSylow2In R₁ K₁
  syl₂ : IsSylow2In R₂ K₂
  syl₃ : IsSylow2In R₃ K₃
  comm₁₂ : Commutes R₁ R₂
  comm₁₃ : Commutes R₁ R₃
  comm₂₃ : Commutes R₂ R₃
  mem_u₁ : u₁ ∈ R₁
  mem_u₂ : u₂ ∈ R₂
  mem_u₃ : u₃ ∈ R₃
  ord₁ : orderOf u₁ = 4
  ord₂ : orderOf u₂ = 4
  ord₃ : orderOf u₃ = 4

namespace Frame3

variable {z : G} {K₁ K₂ K₃ R₁ R₂ R₃ : Subgroup G} {u₁ u₂ u₃ : G}
  (F : Frame3 Ω z K₁ K₂ K₃ R₁ R₂ R₃ u₁ u₂ u₃)
include F

theorem sq₁ : u₁ * u₁ = z := T7A.sq_eq_of_orderOf_four F.hz₁ (F.syl₁.1 F.mem_u₁) F.ord₁

theorem sq₂ : u₂ * u₂ = z := T7A.sq_eq_of_orderOf_four F.hz₂ (F.syl₂.1 F.mem_u₂) F.ord₂

theorem sq₃ : u₃ * u₃ = z := T7A.sq_eq_of_orderOf_four F.hz₃ (F.syl₃.1 F.mem_u₃) F.ord₃

theorem comm₁₂' : u₁ * u₂ = u₂ * u₁ := F.comm₁₂ u₁ F.mem_u₁ u₂ F.mem_u₂

theorem comm₁₃' : u₁ * u₃ = u₃ * u₁ := F.comm₁₃ u₁ F.mem_u₁ u₃ F.mem_u₃

theorem comm₂₃' : u₂ * u₃ = u₃ * u₂ := F.comm₂₃ u₂ F.mem_u₂ u₃ F.mem_u₃

theorem z_comm₁ : z * u₁ = u₁ * z := by
  rw [← F.sq₁]
  group

theorem z_comm₂ : z * u₂ = u₂ * z := by
  rw [← F.sq₂]
  group

theorem z_comm₃ : z * u₃ = u₃ * z := by
  rw [← F.sq₃]
  group

theorem z_mem_R₁ : z ∈ R₁ := F.sq₁ ▸ R₁.mul_mem F.mem_u₁ F.mem_u₁

theorem z_mem_R₂ : z ∈ R₂ := F.sq₂ ▸ R₂.mul_mem F.mem_u₂ F.mem_u₂

theorem z_ne_one : z ≠ 1 := F.hz₁.ne_one

theorem z_sq : z * z = 1 := F.hz₁.sq

theorem swap₁₂ : Frame3 Ω z K₂ K₁ K₃ R₂ R₁ R₃ u₂ u₁ u₃ where
  mem₁ := F.mem₂
  mem₂ := F.mem₁
  mem₃ := F.mem₃
  hz₁ := F.hz₂
  hz₂ := F.hz₁
  hz₃ := F.hz₃
  ne₁₂ := F.ne₁₂.symm
  ne₁₃ := F.ne₂₃
  ne₂₃ := F.ne₁₃
  syl₁ := F.syl₂
  syl₂ := F.syl₁
  syl₃ := F.syl₃
  comm₁₂ := F.comm₁₂.symm
  comm₁₃ := F.comm₂₃
  comm₂₃ := F.comm₁₃
  mem_u₁ := F.mem_u₂
  mem_u₂ := F.mem_u₁
  mem_u₃ := F.mem_u₃
  ord₁ := F.ord₂
  ord₂ := F.ord₁
  ord₃ := F.ord₃

theorem swap₂₃ : Frame3 Ω z K₁ K₃ K₂ R₁ R₃ R₂ u₁ u₃ u₂ where
  mem₁ := F.mem₁
  mem₂ := F.mem₃
  mem₃ := F.mem₂
  hz₁ := F.hz₁
  hz₂ := F.hz₃
  hz₃ := F.hz₂
  ne₁₂ := F.ne₁₃
  ne₁₃ := F.ne₁₂
  ne₂₃ := F.ne₂₃.symm
  syl₁ := F.syl₁
  syl₂ := F.syl₃
  syl₃ := F.syl₂
  comm₁₂ := F.comm₁₃
  comm₁₃ := F.comm₁₂
  comm₂₃ := F.comm₂₃.symm
  mem_u₁ := F.mem_u₁
  mem_u₂ := F.mem_u₃
  mem_u₃ := F.mem_u₂
  ord₁ := F.ord₁
  ord₂ := F.ord₃
  ord₃ := F.ord₂

section NotMem

variable [Finite G] (hΩ : HypOmegaGen Ω)
include hΩ

theorem u₁_not_mem₂ : u₁ ∉ K₂ := fun h =>
  T7X.not_mem_inf_of_orderOf_four hΩ F.mem₁ F.mem₂ F.ne₁₂ F.ord₁ (F.syl₁.1 F.mem_u₁) h

theorem u₁_not_mem₃ : u₁ ∉ K₃ := fun h =>
  T7X.not_mem_inf_of_orderOf_four hΩ F.mem₁ F.mem₃ F.ne₁₃ F.ord₁ (F.syl₁.1 F.mem_u₁) h

theorem u₂_not_mem₃ : u₂ ∉ K₃ := fun h =>
  T7X.not_mem_inf_of_orderOf_four hΩ F.mem₂ F.mem₃ F.ne₂₃ F.ord₂ (F.syl₂.1 F.mem_u₂) h

theorem u₃_not_mem₁ : u₃ ∉ K₁ := fun h =>
  T7X.not_mem_inf_of_orderOf_four hΩ F.mem₁ F.mem₃ F.ne₁₃ F.ord₃ h (F.syl₃.1 F.mem_u₃)

end NotMem

section Alg

theorem x_sq : (u₁ * u₂) * (u₁ * u₂) = 1 := by
  calc (u₁ * u₂) * (u₁ * u₂) = u₁ * (u₂ * u₁) * u₂ := by group
    _ = u₁ * (u₁ * u₂) * u₂ := by rw [← F.comm₁₂']
    _ = (u₁ * u₁) * (u₂ * u₂) := by group
    _ = 1 := by rw [F.sq₁, F.sq₂]; exact F.z_sq

theorem y_sq : (u₂ * u₃) * (u₂ * u₃) = 1 := by
  calc (u₂ * u₃) * (u₂ * u₃) = u₂ * (u₃ * u₂) * u₃ := by group
    _ = u₂ * (u₂ * u₃) * u₃ := by rw [← F.comm₂₃']
    _ = (u₂ * u₂) * (u₃ * u₃) := by group
    _ = 1 := by rw [F.sq₂, F.sq₃]; exact F.z_sq

theorem x_comm_y : (u₁ * u₂) * (u₂ * u₃) = (u₂ * u₃) * (u₁ * u₂) := by
  have h12 : Commute u₁ u₂ := F.comm₁₂'
  have h13 : Commute u₁ u₃ := F.comm₁₃'
  have h23 : Commute u₂ u₃ := F.comm₂₃'
  exact ((h12.mul_right h13).mul_left ((Commute.refl u₂).mul_right h23)).eq

theorem z_comm_x : z * (u₁ * u₂) = (u₁ * u₂) * z :=
  ((show Commute z u₁ from F.z_comm₁).mul_right (show Commute z u₂ from F.z_comm₂)).eq

theorem z_comm_y : z * (u₂ * u₃) = (u₂ * u₃) * z :=
  ((show Commute z u₂ from F.z_comm₂).mul_right (show Commute z u₃ from F.z_comm₃)).eq

theorem x_mul_y : (u₁ * u₂) * (u₂ * u₃) = (u₁ * z) * u₃ := by
  calc (u₁ * u₂) * (u₂ * u₃) = u₁ * (u₂ * u₂) * u₃ := by group
    _ = (u₁ * z) * u₃ := by rw [F.sq₂]

theorem x_mul_z_mul_y : (u₁ * u₂) * z * (u₂ * u₃) = u₁ * u₃ := by
  have e : u₂ * z = z * u₂ := F.z_comm₂.symm
  calc (u₁ * u₂) * z * (u₂ * u₃) = u₁ * (u₂ * z) * u₂ * u₃ := by group
    _ = u₁ * (z * u₂) * u₂ * u₃ := by rw [e]
    _ = u₁ * (z * (u₂ * u₂)) * u₃ := by group
    _ = u₁ * u₃ := by rw [F.sq₂, F.z_sq]; group

theorem mem_K₁ : u₁ ∈ K₁ := F.syl₁.1 F.mem_u₁

theorem mem_K₂ : u₂ ∈ K₂ := F.syl₂.1 F.mem_u₂

theorem mem_K₃ : u₃ ∈ K₃ := F.syl₃.1 F.mem_u₃

end Alg

section BGroup

variable [Finite G] (hΩ : HypOmegaGen Ω)
include hΩ

theorem x_ne_one : u₁ * u₂ ≠ 1 := fun h =>
  F.u₁_not_mem₂ hΩ (by rw [eq_inv_of_mul_eq_one_left h]; exact K₂.inv_mem F.mem_K₂)

theorem x_ne_z : u₁ * u₂ ≠ z := fun h =>
  F.u₁_not_mem₂ hΩ (by
    have : u₁ = u₂ := mul_right_cancel (h.trans F.sq₂.symm)
    rw [this]
    exact F.mem_K₂)

theorem y_ne_one : u₂ * u₃ ≠ 1 := fun h =>
  F.u₂_not_mem₃ hΩ (by rw [eq_inv_of_mul_eq_one_left h]; exact K₃.inv_mem F.mem_K₃)

theorem y_ne_z : u₂ * u₃ ≠ z := fun h =>
  F.u₂_not_mem₃ hΩ (by
    have : u₂ = u₃ := mul_right_cancel (h.trans F.sq₃.symm)
    rw [this]
    exact F.mem_K₃)

theorem x_ne_y : u₁ * u₂ ≠ u₂ * u₃ := fun h =>
  F.u₁_not_mem₃ hΩ (by
    have h' : u₂ * u₁ = u₂ * u₃ := by rw [← F.comm₁₂']; exact h
    have : u₁ = u₃ := mul_left_cancel h'
    rw [this]
    exact F.mem_K₃)

theorem y_ne_zx : u₂ * u₃ ≠ z * (u₁ * u₂) := fun h =>
  F.u₃_not_mem₁ hΩ (by
    have h12 : Commute u₁ u₂ := F.comm₁₂'
    have hc : Commute u₂ (u₁ * u₁ * u₁) := ((h12.symm.mul_right h12.symm).mul_right h12.symm)
    have e : z * (u₁ * u₂) = u₂ * (u₁ * u₁ * u₁) := by
      calc z * (u₁ * u₂) = (u₁ * u₁) * (u₁ * u₂) := by rw [F.sq₁]
        _ = (u₁ * u₁ * u₁) * u₂ := by group
        _ = u₂ * (u₁ * u₁ * u₁) := hc.eq.symm
    have : u₃ = u₁ * u₁ * u₁ := mul_left_cancel (h.trans e)
    rw [this]
    exact K₁.mul_mem (K₁.mul_mem F.mem_K₁ F.mem_K₁) F.mem_K₁)

theorem y_not_mem_closure : u₂ * u₃ ∉ Subgroup.closure ({u₁ * u₂, z} : Set G) := by
  intro h
  rcases Sec71.mem_closure_pair_iff F.x_sq F.z_sq F.z_comm_x.symm |>.mp h with h1 | h1 | h1 | h1
  · exact F.y_ne_one hΩ h1
  · exact F.x_ne_y hΩ h1.symm
  · exact F.y_ne_z hΩ h1
  · exact F.y_ne_zx hΩ (h1.trans (by
      have : (u₁ * u₂) * z = z * (u₁ * u₂) := F.z_comm_x.symm
      exact this))

theorem isElemAbelian_B :
    IsElemAbelian 2 (Subgroup.closure ({z, u₁ * u₂, u₂ * u₃} : Set G)) :=
  isElemAbelian_closure_triple F.z_sq F.x_sq F.y_sq F.z_comm_x F.z_comm_y F.x_comm_y

theorem natCard_B : Nat.card ↥(Subgroup.closure ({z, u₁ * u₂, u₂ * u₃} : Set G)) = 8 :=
  natCard_closure_triple_eight F.z_sq F.x_sq F.y_sq F.z_ne_one (F.x_ne_one hΩ) (F.y_ne_one hΩ)
    (F.x_ne_z hΩ) F.z_comm_x F.z_comm_y F.x_comm_y (F.y_not_mem_closure hΩ)

theorem mem_B_cases {c : G} (hc : c ∈ Subgroup.closure ({z, u₁ * u₂, u₂ * u₃} : Set G)) :
    c = 1 ∨ c = z ∨ (∃ a ∈ R₁, ∃ b ∈ R₂, c = a * b) ∨ (∃ a ∈ R₂, ∃ b ∈ R₃, c = a * b) ∨
      (∃ a ∈ R₁, ∃ b ∈ R₃, c = a * b) := by
  have hy2 : orderOf (u₂ * u₃) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact F.y_sq) (F.y_ne_one hΩ)
  have hcl : Subgroup.closure ({z, u₁ * u₂, u₂ * u₃} : Set G) =
      Subgroup.closure ({u₁ * u₂, z} : Set G) ⊔ Subgroup.zpowers (u₂ * u₃) := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro w hw
      rcases hw with rfl | rfl | rfl
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · refine sup_le ?_ (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
      rw [Subgroup.closure_le]
      intro w hw
      rcases hw with rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
  have hcomm : Commutes (Subgroup.closure ({u₁ * u₂, z} : Set G)) (Subgroup.zpowers (u₂ * u₃)) := by
    have hle : Subgroup.closure ({u₁ * u₂, z} : Set G) ≤
        Subgroup.centralizer ({u₂ * u₃} : Set G) := by
      rw [Subgroup.closure_le]
      intro w hw
      rcases hw with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr F.x_comm_y
      · exact Subgroup.mem_centralizer_singleton_iff.mpr F.z_comm_y
    intro w hw v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    have : Commute w (u₂ * u₃) := Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
    exact (this.zpow_right i).eq
  rw [hcl] at hc
  obtain ⟨a, ha, b, hb, rfl⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hcomm hc
  have hz1 : z ∈ R₁ := F.z_mem_R₁
  have hz2 : z ∈ R₂ := F.z_mem_R₂
  have hu1 : u₁ ∈ R₁ := F.mem_u₁
  have hu2 : u₂ ∈ R₂ := F.mem_u₂
  have hu3 : u₃ ∈ R₃ := F.mem_u₃
  rcases (Sec71.mem_closure_pair_iff F.x_sq F.z_sq F.z_comm_x.symm).mp ha with
    ha1 | ha1 | ha1 | ha1 <;>
  rcases T7A.eq_one_or_eq_of_mem_zpowers hy2 hb with hb1 | hb1 <;> rw [ha1, hb1]
  · left
    simp
  · right; right; right; left
    exact ⟨u₂, hu2, u₃, hu3, by simp⟩
  · right; right; left
    exact ⟨u₁, hu1, u₂, hu2, by simp⟩
  · right; right; right; right
    refine ⟨u₁ * z, R₁.mul_mem hu1 hz1, u₃, hu3, ?_⟩
    rw [F.x_mul_y]
  · right; left
    simp
  · right; right; right; left
    exact ⟨z * u₂, R₂.mul_mem hz2 hu2, u₃, hu3, by group⟩
  · right; right; left
    refine ⟨z * u₁, R₁.mul_mem hz1 hu1, u₂, hu2, ?_⟩
    have : (u₁ * u₂) * z = z * (u₁ * u₂) := F.z_comm_x.symm
    rw [this]
    group
  · right; right; right; right
    refine ⟨u₁, hu1, u₃, hu3, ?_⟩
    exact F.x_mul_z_mul_y

end BGroup

end Frame3

end Frame3

end CFSG.ClassicalInvolution.Hat2A7S
