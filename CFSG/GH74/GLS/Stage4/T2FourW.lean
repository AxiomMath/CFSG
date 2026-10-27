module

public import CFSG.GH74.GLS.Stage4.T2FourWey
public import CFSG.GH74.GLS.Stage4.T2HDih

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup

section Act

variable {G : Type} [Group G] {z u : G} {K₁ K₂ H : Subgroup G} {w₁ w₂ a : G}

theorem T2Weyl.a_zu (h : T2Weyl z u K₁ K₂ H w₁ w₂ a) : a⁻¹ * (z * u) * a = z := by
  have e : a⁻¹ * (z * u) * a = (a⁻¹ * z * a) * (a⁻¹ * u * a) := by group
  rw [e, h.a_z, h.a_u]
  calc u * (z * u) = (u * z) * u := by group
    _ = (z * u) * u := by rw [← h.four.zu_comm]
    _ = z * (u * u) := by group
    _ = z := by rw [h.four.uu, mul_one]

theorem T2Weyl.a_ne_one (h : T2Weyl z u K₁ K₂ H w₁ w₂ a) : a ≠ 1 := by
  intro h1
  apply h.four.zu_ne
  have := h.a_z
  rw [h1] at this
  simpa using this

theorem T2Weyl.cent_U (h : T2Weyl z u K₁ K₂ H w₁ w₂ a) {v : G} (hv : v ∈ t2U z u)
    (hc : a⁻¹ * v * a = v) : v = 1 := by
  rcases (t2U_mem h.four.zz h.four.uu h.four.zu_comm).1 hv with hv1 | hv1 | hv1 | hv1
  · exact hv1
  · exfalso
    rw [hv1, h.a_z] at hc
    exact h.four.zu_ne hc.symm
  · exfalso
    rw [hv1, h.a_u] at hc
    apply h.four.z_ne
    have : z * u = 1 * u := by rw [hc, one_mul]
    exact mul_right_cancel this
  · exfalso
    rw [hv1, h.a_zu] at hc
    apply h.four.u_ne
    have : z * 1 = z * u := by rw [mul_one]; exact hc
    exact (mul_left_cancel this).symm

end Act

section ActF

variable {G : Type} [Group G] [Finite G] {z u : G} {K₁ K₂ H : Subgroup G} {w₁ w₂ a : G}

theorem T2Weyl.a_normU (h : T2Weyl z u K₁ K₂ H w₁ w₂ a) :
    a ∈ normalizer (t2U z u : Set G) := by
  have : a⁻¹ ∈ normalizer (t2U z u : Set G) := by
    refine t2U_norm (z := z) (u := u) ?_ ?_
    · rw [inv_inv, h.a_z]; exact Subgroup.subset_closure (by simp)
    · rw [inv_inv, h.a_u]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  simpa using Subgroup.inv_mem _ this

end ActF
section Y

variable {G : Type} [Group G] [Finite G] {z u : G} {K₁ K₂ H : Subgroup G} {w₁ w₂ a : G}

theorem T2Four.w₁_normU (h : T2Four z u K₁ K₂ H w₁ w₂) : w₁ ∈ normalizer (t2U z u : Set G) := by
  apply t2U_norm
  · rw [h.w₁_z']; exact Subgroup.subset_closure (by simp)
  · rw [h.w₁_u]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

theorem T2Weyl.exists_y (h : T2Weyl z u K₁ K₂ H w₁ w₂ a) (hr : CFSG.pRank 2 G = 3) :
    ∃ v ∈ t2U z u, (w₁ * v) * (w₁ * v) = 1 ∧ (w₁ * v) * a * (w₁ * v)⁻¹ = a⁻¹ := by
  have hF := h.four
  obtain ⟨x', hx', hw⟩ := h.w₁_a
  have hz : z ∈ t2U z u := Subgroup.subset_closure (by simp)
  have hu : u ∈ t2U z u := Subgroup.subset_closure (by simp)
  have c1 : Commute (w₁ * w₂) w₁ := hF.w₁_w₀.symm
  have c2 : Commute (w₁ * w₂) a := h.a_cent.symm
  have hcomm : (w₁ * a * w₁⁻¹) * (w₁ * w₂) = (w₁ * w₂) * (w₁ * a * w₁⁻¹) :=
    ((c1.mul_right c2).mul_right c1.inv_right).eq.symm
  rw [hw] at hcomm
  have hw₀a : a⁻¹ * (w₁ * w₂) = (w₁ * w₂) * a⁻¹ := c2.inv_right.eq.symm
  have hx'w : x' * (w₁ * w₂) = (w₁ * w₂) * x' := by
    have : a⁻¹ * (x' * (w₁ * w₂)) = a⁻¹ * ((w₁ * w₂) * x') := by
      calc a⁻¹ * (x' * (w₁ * w₂)) = (a⁻¹ * x') * (w₁ * w₂) := by group
        _ = (w₁ * w₂) * (a⁻¹ * x') := hcomm
        _ = ((w₁ * w₂) * a⁻¹) * x' := by group
        _ = (a⁻¹ * (w₁ * w₂)) * x' := by rw [hw₀a]
        _ = a⁻¹ * ((w₁ * w₂) * x') := by group
    exact mul_left_cancel this
  have hx'sq : x' * x' = 1 := by
    have h1 := hF.w₀_inv x' hx'
    rw [hF.w₀_inv_self] at h1
    have h2 : (w₁ * w₂) * x' * (w₁ * w₂) = x' := by
      calc (w₁ * w₂) * x' * (w₁ * w₂) = x' * (w₁ * w₂) * (w₁ * w₂) := by rw [← hx'w]
        _ = x' := by rw [mul_assoc, hF.w₀_sq, mul_one]
    rw [h2] at h1
    calc x' * x' = x' * x'⁻¹ := by rw [← h1]
      _ = 1 := by group
  have hwz : w₁ * z * w₁⁻¹ = z := hF.w₁_z'
  have hwu : w₁ * u * w₁⁻¹ = u * z := hF.w₁_u
  have hzu : z * u = u * z := hF.zu_comm
  have hwzu : w₁ * (z * u) * w₁⁻¹ = u := by
    calc w₁ * (z * u) * w₁⁻¹ = (w₁ * z * w₁⁻¹) * (w₁ * u * w₁⁻¹) := by group
      _ = z * (u * z) := by rw [hwz, hwu]
      _ = (z * u) * z := by group
      _ = (u * z) * z := by rw [hzu]
      _ = u * (z * z) := by group
      _ = u := by rw [hF.zz, mul_one]
  have hkey : ∀ v : G, (w₁ * v) * a * (w₁ * v)⁻¹ =
      a⁻¹ * (x' * (w₁ * ((a⁻¹ * v * a) * v⁻¹) * w₁⁻¹)) := by
    intro v
    calc (w₁ * v) * a * (w₁ * v)⁻¹
        = (w₁ * a * w₁⁻¹) * (w₁ * ((a⁻¹ * v * a) * v⁻¹) * w₁⁻¹) := by group
      _ = (a⁻¹ * x') * (w₁ * ((a⁻¹ * v * a) * v⁻¹) * w₁⁻¹) := by rw [hw]
      _ = a⁻¹ * (x' * (w₁ * ((a⁻¹ * v * a) * v⁻¹) * w₁⁻¹)) := by group
  have hzuu : z * u * u = z := by
    calc z * u * u = z * (u * u) := by group
      _ = z := by rw [hF.uu, mul_one]
  have hs : ∃ v ∈ t2U z u, x' * (w₁ * ((a⁻¹ * v * a) * v⁻¹) * w₁⁻¹) = 1 := by
    rcases hF.omega1 hr x' hx' hx'sq with h1 | h1 | h1 | h1
    · exact ⟨1, one_mem _, by simp [h1]⟩
    ·
      refine ⟨u, hu, ?_⟩
      have : (a⁻¹ * u * a) * u⁻¹ = z := by
        rw [h.a_u, hF.u_inv]
        exact hzuu
      rw [this, h1, hwz, hF.zz]
    ·
      refine ⟨z, hz, ?_⟩
      have : (a⁻¹ * z * a) * z⁻¹ = u * z := by rw [h.a_z, hF.z_inv]
      have hwuz : w₁ * (u * z) * w₁⁻¹ = u := by
        calc w₁ * (u * z) * w₁⁻¹ = (w₁ * u * w₁⁻¹) * (w₁ * z * w₁⁻¹) := by group
          _ = (u * z) * z := by rw [hwu, hwz]
          _ = u * (z * z) := by group
          _ = u := by rw [hF.zz, mul_one]
      rw [this, h1, hwuz, hF.uu]
    ·
      refine ⟨z * u, Subgroup.mul_mem _ hz hu, ?_⟩
      have hzuinv : (z * u)⁻¹ = z * u := by
        calc (z * u)⁻¹ = u⁻¹ * z⁻¹ := by group
          _ = u * z := by rw [hF.u_inv, hF.z_inv]
          _ = z * u := hzu.symm
      have : (a⁻¹ * (z * u) * a) * (z * u)⁻¹ = u := by
        rw [h.a_zu, hzuinv]
        calc z * (z * u) = (z * z) * u := by group
          _ = u := by rw [hF.zz, one_mul]
      rw [this, h1, hwu]
      calc z * u * (u * z) = z * (u * u) * z := by group
        _ = 1 := by rw [hF.uu, mul_one, hF.zz]
  obtain ⟨v, hvU, hv⟩ := hs
  refine ⟨v, hvU, ?_, ?_⟩
  ·
    have hya : (w₁ * v) * a * (w₁ * v)⁻¹ = a⁻¹ := by rw [hkey v, hv, mul_one]
    have hy2U : (w₁ * v) * (w₁ * v) ∈ t2U z u := by
      have e : (w₁ * v) * (w₁ * v) = (w₁ * v * w₁⁻¹) * z * v := by
        calc (w₁ * v) * (w₁ * v) = (w₁ * v * w₁⁻¹) * (w₁ * w₁) * v := by group
          _ = (w₁ * v * w₁⁻¹) * z * v := by rw [hF.w₁_sq]
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _
        ((Subgroup.mem_normalizer_iff.1 hF.w₁_normU v).1 hvU) hz) hvU
    apply h.cent_U hy2U
    have hy' : (w₁ * v) * a⁻¹ = a * (w₁ * v) := by
      have := congrArg (·⁻¹) hya
      simp only [mul_inv_rev, inv_inv] at this
      calc (w₁ * v) * a⁻¹ = (w₁ * v) * a⁻¹ * (w₁ * v)⁻¹ * (w₁ * v) := by group
        _ = a * (w₁ * v) := by
            rw [show (w₁ * v) * a⁻¹ * (w₁ * v)⁻¹ = a by simpa [mul_assoc] using this]
    calc a⁻¹ * ((w₁ * v) * (w₁ * v)) * a = a⁻¹ * (w₁ * v) * ((w₁ * v) * a) := by group
      _ = a⁻¹ * (w₁ * v) * (a⁻¹ * (w₁ * v)) := by
          rw [show (w₁ * v) * a = a⁻¹ * (w₁ * v) from by
            calc (w₁ * v) * a = ((w₁ * v) * a * (w₁ * v)⁻¹) * (w₁ * v) := by group
              _ = a⁻¹ * (w₁ * v) := by rw [hya]]
      _ = (a⁻¹ * (w₁ * v)) * (a⁻¹ * (w₁ * v)) := rfl
      _ = a⁻¹ * ((w₁ * v) * a⁻¹) * (w₁ * v) := by group
      _ = a⁻¹ * (a * (w₁ * v)) * (w₁ * v) := by rw [hy']
      _ = (w₁ * v) * (w₁ * v) := by group
  · rw [hkey v, hv, mul_one]

end Y

section Conj

variable {G : Type} [Group G] {z u : G} {K₁ K₂ H : Subgroup G} {w₁ w₂ a : G}

theorem T2Weyl.a_conj_z (h : T2Weyl z u K₁ K₂ H w₁ w₂ a) : a * z * a⁻¹ = z * u := by
  calc a * z * a⁻¹ = a * (a⁻¹ * (z * u) * a) * a⁻¹ := by rw [h.a_zu]
    _ = z * u := by group

theorem T2Weyl.a_conj_u (h : T2Weyl z u K₁ K₂ H w₁ w₂ a) : a * u * a⁻¹ = z := by
  calc a * u * a⁻¹ = a * (a⁻¹ * z * a) * a⁻¹ := by rw [h.a_z]
    _ = z := by group

theorem T2Weyl.a_conj_zu (h : T2Weyl z u K₁ K₂ H w₁ w₂ a) : a * (z * u) * a⁻¹ = u := by
  calc a * (z * u) * a⁻¹ = (a * z * a⁻¹) * (a * u * a⁻¹) := by group
    _ = (z * u) * z := by rw [h.a_conj_z, h.a_conj_u]
    _ = (u * z) * z := by rw [h.four.zu_comm]
    _ = u * (z * z) := by group
    _ = u := by rw [h.four.zz, mul_one]

end Conj

section Trans

variable {G : Type} [Group G] [Finite G] {z u : G} {K₁ K₂ H : Subgroup G} {w₁ w₂ a : G}

omit [Finite G] in
theorem t2U_comm (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z) :
    ∀ x ∈ t2U z u, ∀ y ∈ t2U z u, x * y = y * x := by
  intro x hx y hy
  have hx' := (t2U_mem hz2 hu2 hzu).1 hx
  have hxz : x * z = z * x := by
    rcases hx' with rfl | rfl | rfl | rfl
    · simp
    · rfl
    · exact hzu.symm
    · calc z * u * z = z * (u * z) := by group
        _ = z * (z * u) := by rw [hzu]
        _ = z * (z * u) := rfl
  have hxu : x * u = u * x := by
    rcases hx' with rfl | rfl | rfl | rfl
    · simp
    · exact hzu
    · rfl
    · calc z * u * u = z * (u * u) := by group
        _ = z := by rw [hu2, mul_one]
        _ = u * u * z := by rw [hu2, one_mul]
        _ = u * (u * z) := by group
        _ = u * (z * u) := by rw [hzu]
  exact t2U_comm_all hz2 hu2 hzu hxz hxu y hy

theorem T2Weyl.U_trans (h : T2Weyl z u K₁ K₂ H w₁ w₂ a) :
    ∀ x ∈ t2U z u, ∀ y ∈ t2U z u, x ≠ 1 → y ≠ 1 →
      ∃ g ∈ normalizer (t2U z u : Set G), g * x * g⁻¹ = y := by
  intro x hx y hy hx1 hy1
  have hF := h.four
  have haN := h.a_normU
  have haN' : a⁻¹ ∈ normalizer (t2U z u : Set G) := Subgroup.inv_mem _ haN
  rcases (t2U_mem hF.zz hF.uu hF.zu_comm).1 hx with hx' | hx' | hx' | hx' <;>
    rcases (t2U_mem hF.zz hF.uu hF.zu_comm).1 hy with hy' | hy' | hy' | hy'
  · exact absurd hx' hx1
  · exact absurd hx' hx1
  · exact absurd hx' hx1
  · exact absurd hx' hx1
  · exact absurd hy' hy1
  · exact ⟨1, Subgroup.one_mem _, by rw [hx', hy']; group⟩
  · exact ⟨a⁻¹, haN', by rw [hx', hy', inv_inv]; exact h.a_z⟩
  · exact ⟨a, haN, by rw [hx', hy']; exact h.a_conj_z⟩
  · exact absurd hy' hy1
  · exact ⟨a, haN, by rw [hx', hy']; exact h.a_conj_u⟩
  · exact ⟨1, Subgroup.one_mem _, by rw [hx', hy']; group⟩
  · exact ⟨a⁻¹, haN', by rw [hx', hy', inv_inv]; exact h.a_u⟩
  · exact absurd hy' hy1
  · exact ⟨a⁻¹, haN', by rw [hx', hy', inv_inv]; exact h.a_zu⟩
  · exact ⟨a, haN, by rw [hx', hy']; exact h.a_conj_zu⟩
  · exact ⟨1, Subgroup.one_mem _, by rw [hx', hy']; group⟩

end Trans

section W

variable {G : Type} [Group G] [Finite G] {z u : G} {K₁ K₂ H : Subgroup G} {w₁ w₂ a : G}

omit [Finite G] in
theorem T2Four.y_z (h : T2Four z u K₁ K₂ H w₁ w₂) {v : G} (hv : v ∈ t2U z u) :
    (w₁ * v) * z * (w₁ * v)⁻¹ = z := by
  have hvz : v * z = z * v := t2U_comm h.zz h.uu h.zu_comm v hv z
    (Subgroup.subset_closure (by simp))
  calc (w₁ * v) * z * (w₁ * v)⁻¹ = w₁ * (v * z * v⁻¹) * w₁⁻¹ := by group
    _ = w₁ * z * w₁⁻¹ := by rw [hvz]; group
    _ = z := h.w₁_z'

omit [Finite G] in
theorem T2Four.y_u (h : T2Four z u K₁ K₂ H w₁ w₂) {v : G} (hv : v ∈ t2U z u) :
    (w₁ * v) * u * (w₁ * v)⁻¹ = u * z := by
  have hvu : v * u = u * v := t2U_comm h.zz h.uu h.zu_comm v hv u
    (Subgroup.subset_closure (by simp))
  calc (w₁ * v) * u * (w₁ * v)⁻¹ = w₁ * (v * u * v⁻¹) * w₁⁻¹ := by group
    _ = w₁ * u * w₁⁻¹ := by rw [hvu]; group
    _ = u * z := h.w₁_u

theorem T2Four.y_normU (h : T2Four z u K₁ K₂ H w₁ w₂) {v : G} (hv : v ∈ t2U z u) :
    w₁ * v ∈ normalizer (t2U z u : Set G) :=
  Subgroup.mul_mem _ h.w₁_normU (Subgroup.le_normalizer hv)

omit [Finite G] in
theorem T2Four.y_w₀ (h : T2Four z u K₁ K₂ H w₁ w₂) {v : G} (hv : v ∈ t2U z u) :
    (w₁ * v) * (w₁ * w₂) = (w₁ * w₂) * (w₁ * v) := by
  have hv0 : v * (w₁ * w₂) = (w₁ * w₂) * v :=
    (t2U_comm_all h.zz h.uu h.zu_comm h.w₀_z h.w₀_u v hv).symm
  calc (w₁ * v) * (w₁ * w₂) = w₁ * (v * (w₁ * w₂)) := by group
    _ = w₁ * ((w₁ * w₂) * v) := by rw [hv0]
    _ = (w₁ * (w₁ * w₂)) * v := by group
    _ = ((w₁ * w₂) * w₁) * v := by rw [h.w₁_w₀]
    _ = (w₁ * w₂) * (w₁ * v) := by group

end W

section Dih

variable {G : Type} [Group G] [Finite G] {z u : G} {K₁ K₂ H : Subgroup G} {w₁ w₂ a : G}

omit [Finite G] in
theorem T2Weyl.dihedral (h : T2Weyl z u K₁ K₂ H w₁ w₂ a) {v : G} (hv : v ∈ t2U z u)
    (hy2 : (w₁ * v) * (w₁ * v) = 1) (hya : (w₁ * v) * a * (w₁ * v)⁻¹ = a⁻¹) :
    ∃ f : DihedralGroup 6 →* G, Function.Injective f ∧
      f.range = Subgroup.closure ({a, w₁ * v, w₁ * w₂} : Set G) ∧
      f (DihedralGroup.r 1) = a * (w₁ * w₂) ∧ f (DihedralGroup.sr 0) = w₁ * v := by
  have hF := h.four
  have hw₁ : w₁ * w₂ ≠ 1 := fun h1 => hF.w₀_not_mem (h1 ▸ H.one_mem)
  have hnc : (w₁ * v) ∉ Subgroup.closure ({a, w₁ * w₂} : Set G) := by
    intro hmem
    have hle : Subgroup.closure ({a, w₁ * w₂} : Set G) ≤ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.2 rfl
      · exact Subgroup.mem_centralizer_singleton_iff.2 h.a_cent.symm
    have hc := Subgroup.mem_centralizer_singleton_iff.1 (hle hmem)
    apply h.a_ne_one
    have h1 : a = a⁻¹ := by
      calc a = ((w₁ * v) * a * (w₁ * v)⁻¹) := by rw [hc]; group
        _ = a⁻¹ := hya
    have h2 : a * a = 1 := by
      calc a * a = a * a⁻¹ := by rw [← h1]
        _ = 1 := by group
    have h3 : a * (a * a) = 1 := (pow_three a).symm.trans h.a_cube
    calc a = a * (a * a) * (a * a)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; group
  exact t2H_dihedral_six a (w₁ * v) (w₁ * w₂) h.a_cube h.a_ne_one (by rw [pow_two]; exact hy2)
    (by rw [pow_two]; exact hF.w₀_sq) hw₁ hya h.a_cent.symm (hF.y_w₀ hv).symm hnc

end Dih

section Dec

variable {G : Type} [Group G] [Finite G] {z u : G} {K₁ K₂ H : Subgroup G} {w₁ w₂ a : G}

theorem T2Weyl.W_le_normU (h : T2Weyl z u K₁ K₂ H w₁ w₂ a) {v : G} (hv : v ∈ t2U z u) :
    Subgroup.closure ({a, w₁ * v, w₁ * w₂} : Set G) ≤ normalizer (t2U z u : Set G) := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl | rfl)
  · exact h.a_normU
  · exact h.four.y_normU hv
  ·
    apply t2U_norm
    · rw [show (w₁ * w₂) * z * (w₁ * w₂)⁻¹ = z by
        calc (w₁ * w₂) * z * (w₁ * w₂)⁻¹ = z * (w₁ * w₂) * (w₁ * w₂)⁻¹ := by rw [h.four.w₀_z]
          _ = z := by group]
      exact Subgroup.subset_closure (by simp)
    · rw [show (w₁ * w₂) * u * (w₁ * w₂)⁻¹ = u by
        calc (w₁ * w₂) * u * (w₁ * w₂)⁻¹ = u * (w₁ * w₂) * (w₁ * w₂)⁻¹ := by rw [h.four.w₀_u]
          _ = u := by group]
      exact Subgroup.subset_closure (by simp)

theorem T2Weyl.decomp (h : T2Weyl z u K₁ K₂ H w₁ w₂ a) {v : G} (hv : v ∈ t2U z u)
    (hy2 : (w₁ * v) * (w₁ * v) = 1) :
    ∀ g ∈ normalizer (t2U z u : Set G),
      ∃ w ∈ Subgroup.closure ({a, w₁ * v, w₁ * w₂} : Set G), ∃ c : G, c * z = z * c ∧
        c * u = u * c ∧ g = w * c := by
  intro g hg
  have hF := h.four
  set W : Subgroup G := Subgroup.closure ({a, w₁ * v, w₁ * w₂} : Set G) with hW
  have haW : a ∈ W := Subgroup.subset_closure (by simp)
  have hyW : w₁ * v ∈ W := Subgroup.subset_closure (by simp)
  have hWN : W ≤ normalizer (t2U z u : Set G) := h.W_le_normU hv
  have hzU : z ∈ t2U z u := Subgroup.subset_closure (by simp)
  have huU : u ∈ t2U z u := Subgroup.subset_closure (by simp)
  have hyinv : (w₁ * v)⁻¹ = w₁ * v := inv_eq_of_mul_eq_one_right hy2
  have hyz := hF.y_z hv
  have hyu := hF.y_u hv
  rw [hyinv] at hyz hyu
  have hz' : g * z * g⁻¹ ∈ t2U z u := (Subgroup.mem_normalizer_iff.1 hg z).1 hzU
  have hz'1 : g * z * g⁻¹ ≠ 1 := by
    intro h1
    apply hF.z_ne
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨r, hrW, hr⟩ : ∃ r ∈ W, r * z * r⁻¹ = g * z * g⁻¹ := by
    rcases (t2U_mem hF.zz hF.uu hF.zu_comm).1 hz' with h1 | h1 | h1 | h1
    · exact absurd h1 hz'1
    · exact ⟨1, W.one_mem, by rw [h1]; group⟩
    · exact ⟨a⁻¹, W.inv_mem haW, by rw [h1, inv_inv]; exact h.a_z⟩
    · exact ⟨a, haW, by rw [h1]; exact h.a_conj_z⟩
  set g₁ : G := r⁻¹ * g with hg₁
  have hg₁N : g₁ ∈ normalizer (t2U z u : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hWN hrW)) hg
  have hg₁z : g₁ * z * g₁⁻¹ = z := by
    calc g₁ * z * g₁⁻¹ = r⁻¹ * (g * z * g⁻¹) * r := by rw [hg₁]; group
      _ = r⁻¹ * (r * z * r⁻¹) * r := by rw [hr]
      _ = z := by group
  have hu' : g₁ * u * g₁⁻¹ ∈ t2U z u := (Subgroup.mem_normalizer_iff.1 hg₁N u).1 huU
  have hu'1 : g₁ * u * g₁⁻¹ ≠ 1 := by
    intro h1
    apply hF.u_ne
    calc u = g₁⁻¹ * (g₁ * u * g₁⁻¹) * g₁ := by group
      _ = 1 := by rw [h1]; group
  have hu'z : g₁ * u * g₁⁻¹ ≠ z := by
    intro h1
    apply hF.zu_ne
    have : g₁ * z * g₁⁻¹ = g₁ * u * g₁⁻¹ := by rw [hg₁z, h1]
    have h2 := mul_right_cancel this
    exact (mul_left_cancel h2)
  have hgr : g = r * g₁ := by rw [hg₁]; group
  rcases (t2U_mem hF.zz hF.uu hF.zu_comm).1 hu' with h1 | h1 | h1 | h1
  · exact absurd h1 hu'1
  · exact absurd h1 hu'z
  ·
    refine ⟨r, hrW, g₁, ?_, ?_, hgr⟩
    · calc g₁ * z = (g₁ * z * g₁⁻¹) * g₁ := by group
        _ = z * g₁ := by rw [hg₁z]
    · calc g₁ * u = (g₁ * u * g₁⁻¹) * g₁ := by group
        _ = u * g₁ := by rw [h1]
  ·
    refine ⟨r * (w₁ * v), W.mul_mem hrW hyW, (w₁ * v) * g₁, ?_, ?_, ?_⟩
    · have e : ((w₁ * v) * g₁) * z * ((w₁ * v) * g₁)⁻¹ = z := by
        calc ((w₁ * v) * g₁) * z * ((w₁ * v) * g₁)⁻¹
            = (w₁ * v) * (g₁ * z * g₁⁻¹) * (w₁ * v)⁻¹ := by group
          _ = (w₁ * v) * z * (w₁ * v)⁻¹ := by rw [hg₁z]
          _ = z := by rw [hyinv]; exact hyz
      calc ((w₁ * v) * g₁) * z = (((w₁ * v) * g₁) * z * ((w₁ * v) * g₁)⁻¹) * ((w₁ * v) * g₁) := by
            group
        _ = z * ((w₁ * v) * g₁) := by rw [e]
    · have e : ((w₁ * v) * g₁) * u * ((w₁ * v) * g₁)⁻¹ = u := by
        calc ((w₁ * v) * g₁) * u * ((w₁ * v) * g₁)⁻¹
            = (w₁ * v) * (g₁ * u * g₁⁻¹) * (w₁ * v)⁻¹ := by group
          _ = (w₁ * v) * (z * u) * (w₁ * v)⁻¹ := by rw [h1]
          _ = ((w₁ * v) * z * (w₁ * v)⁻¹) * ((w₁ * v) * u * (w₁ * v)⁻¹) := by group
          _ = z * (u * z) := by rw [hyinv, hyz, hyu]
          _ = (z * u) * z := by group
          _ = (u * z) * z := by rw [hF.zu_comm]
          _ = u * (z * z) := by group
          _ = u := by rw [hF.zz, mul_one]
      calc ((w₁ * v) * g₁) * u = (((w₁ * v) * g₁) * u * ((w₁ * v) * g₁)⁻¹) * ((w₁ * v) * g₁) := by
            group
        _ = u * ((w₁ * v) * g₁) := by rw [e]
    · calc g = r * g₁ := hgr
        _ = r * ((w₁ * v) * (w₁ * v)) * g₁ := by rw [hy2, mul_one]
        _ = (r * (w₁ * v)) * ((w₁ * v) * g₁) := by group

end Dec

section Inv

variable {G : Type} [Group G] [Finite G] {z u : G} {K₁ K₂ H : Subgroup G} {w₁ w₂ a : G}

omit [Finite G] in
theorem t2_y_pow_conj {y a : G} (ha3 : a ^ 3 = 1) (hya : y * a * y⁻¹ = a⁻¹) (m : ℕ) :
    y * a ^ m = a ^ m * y * (a ^ m)⁻¹ := by
  have h1 : y * a ^ m * y⁻¹ = (a ^ m)⁻¹ := by
    rw [← conj_pow, hya, inv_pow]
  have hb3 : a ^ m * (a ^ m * a ^ m) = 1 := by
    have : (a ^ m) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, ha3, one_pow]
    rw [← pow_three]; exact this
  have hbinv : (a ^ m)⁻¹ = a ^ m * a ^ m := inv_eq_of_mul_eq_one_right hb3
  have h2 : y * (a ^ m)⁻¹ * y⁻¹ = a ^ m := by
    calc y * (a ^ m)⁻¹ * y⁻¹ = (y * a ^ m * y⁻¹)⁻¹ := by group
      _ = ((a ^ m)⁻¹)⁻¹ := by rw [h1]
      _ = a ^ m := inv_inv _
  calc y * a ^ m = (y * a ^ m * y⁻¹) * y := by group
    _ = (a ^ m)⁻¹ * y := by rw [h1]
    _ = (a ^ m * a ^ m) * y := by rw [hbinv]
    _ = a ^ m * (y * (a ^ m)⁻¹ * y⁻¹) * y := by rw [h2]
    _ = a ^ m * y * (a ^ m)⁻¹ := by group

omit [Finite G] in
theorem T2Weyl.involutions (h : T2Weyl z u K₁ K₂ H w₁ w₂ a) {v : G} (hv : v ∈ t2U z u)
    (hy2 : (w₁ * v) * (w₁ * v) = 1) (hya : (w₁ * v) * a * (w₁ * v)⁻¹ = a⁻¹) {y' : G}
    (hy' : y' ∈ Subgroup.closure ({a, w₁ * v, w₁ * w₂} : Set G)) (hord : orderOf y' = 2)
    (hne : y' ≠ w₁ * w₂) :
    ∃ m l : ℕ, l ≤ 1 ∧ y' = a ^ m * ((w₁ * v) * (w₁ * w₂) ^ l) * (a ^ m)⁻¹ := by
  obtain ⟨f, hf, hrange, hfr, hfs⟩ := h.dihedral hv hy2 hya
  rw [← hrange] at hy'
  obtain ⟨d, rfl⟩ := hy'
  have hw₀2 : (w₁ * w₂) * (w₁ * w₂) = 1 := h.four.w₀_sq
  have hcomm : Commute a (w₁ * w₂) := h.a_cent
  rcases d with i | i
  ·
    exfalso
    have hord' : orderOf (DihedralGroup.r i) = 2 := by
      rw [← orderOf_injective f hf]; exact hord
    have hi : i = 3 := by
      rw [DihedralGroup.orderOf_r] at hord'
      have hlt : i.val < 6 := ZMod.val_lt i
      have h3 : i.val = 3 := by
        revert hord'
        generalize i.val = k at hlt ⊢
        interval_cases k <;> decide
      apply ZMod.val_injective 6
      rw [h3]
      rfl
    apply hne
    rw [hi]
    have e : DihedralGroup.r (3 : ZMod 6) = (DihedralGroup.r (1 : ZMod 6)) ^ 3 := by
      rw [DihedralGroup.r_one_pow]; rfl
    rw [e, map_pow, hfr, hcomm.mul_pow, h.a_cube, one_mul]
    calc (w₁ * w₂) ^ 3 = (w₁ * w₂) * ((w₁ * w₂) * (w₁ * w₂)) := pow_three _
      _ = w₁ * w₂ := by rw [hw₀2, mul_one]
  ·
    have e : DihedralGroup.sr i = DihedralGroup.sr (0 : ZMod 6) * (DihedralGroup.r (1 : ZMod 6)) ^ i.val := by
      rw [DihedralGroup.r_one_pow]; simp
    rw [e, map_mul, map_pow, hfs, hfr, hcomm.mul_pow]
    refine ⟨i.val, i.val % 2, by omega, ?_⟩
    have hw₀pow : (w₁ * w₂) ^ i.val = (w₁ * w₂) ^ (i.val % 2) := by
      conv_lhs => rw [← Nat.mod_add_div i.val 2, pow_add, pow_mul, sq, hw₀2, one_pow, mul_one]
    rw [hw₀pow]
    have hcm : Commute (a ^ i.val) ((w₁ * w₂) ^ (i.val % 2)) :=
      (hcomm.pow_left _).pow_right _
    calc w₁ * v * (a ^ i.val * (w₁ * w₂) ^ (i.val % 2))
        = (w₁ * v * a ^ i.val) * (w₁ * w₂) ^ (i.val % 2) := by group
      _ = (a ^ i.val * (w₁ * v) * (a ^ i.val)⁻¹) * (w₁ * w₂) ^ (i.val % 2) := by
          rw [t2_y_pow_conj h.a_cube hya]
      _ = a ^ i.val * ((w₁ * v) * (w₁ * w₂) ^ (i.val % 2)) * (a ^ i.val)⁻¹ := by
          have := hcm.eq
          calc a ^ i.val * (w₁ * v) * (a ^ i.val)⁻¹ * (w₁ * w₂) ^ (i.val % 2)
              = a ^ i.val * (w₁ * v) * ((a ^ i.val)⁻¹ * (w₁ * w₂) ^ (i.val % 2)) := by group
            _ = a ^ i.val * (w₁ * v) * ((w₁ * w₂) ^ (i.val % 2) * (a ^ i.val)⁻¹) := by
                rw [hcm.inv_left.eq]
            _ = a ^ i.val * ((w₁ * v) * (w₁ * w₂) ^ (i.val % 2)) * (a ^ i.val)⁻¹ := by group

theorem T2Weyl.N_eq (h : T2Weyl z u K₁ K₂ H w₁ w₂ a) (hr : CFSG.pRank 2 G = 3) {v : G}
    (hv : v ∈ t2U z u) (hy2 : (w₁ * v) * (w₁ * v) = 1) :
    ∀ g ∈ normalizer (t2U z u : Set G),
      ∃ x ∈ H, ∃ w ∈ Subgroup.closure ({a, w₁ * v, w₁ * w₂} : Set G), g = x * w := by
  intro g hg
  obtain ⟨w, hwW, c, hcz, hcu, hgc⟩ := h.decomp hv hy2 g hg
  have hwN : w ∈ normalizer (t2U z u : Set G) := h.W_le_normU hv hwW
  have hcC : c ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hcz
  have hw₀W : w₁ * w₂ ∈ Subgroup.closure ({a, w₁ * v, w₁ * w₂} : Set G) :=
    Subgroup.subset_closure (by simp)
  rcases h.four.Y1 c hcC hcu with hcH | ⟨x, hx, hcx⟩
  · refine ⟨w * c * w⁻¹, h.four.normH hr hwN c hcH, w, hwW, ?_⟩
    rw [hgc]; group
  · refine ⟨w * x * w⁻¹, h.four.normH hr hwN x hx, w * (w₁ * w₂),
      Subgroup.mul_mem _ hwW hw₀W, ?_⟩
    rw [hgc, hcx]; group

end Inv

end CFSG.GH74.GLS.Stage4.Rest
