module

public import CFSG.CGT.Foote81L6.TStruct.Transvect

public section

namespace CFSG.CGT.Foote81L6.Fusion3

open Subgroup

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)

private theorem mem_zpowers_of_mul_self {z x : G} (hz : z * z = 1) :
    x ∈ zpowers z ↔ x = 1 ∨ x = z := by
  constructor
  · intro hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hx
    rw [zpow_eq_zpow_emod' j (show z ^ 2 = 1 by rw [sq]; exact hz)]
    rcases Int.emod_two_eq_zero_or_one j with h0 | h1
    · left; rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h0, zpow_zero]
    · right; rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h1, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

theorem comm_of_conj_eq {v z : G} (h : v * z * v⁻¹ = z) : z * v = v * z := by
  calc z * v = v * z * v⁻¹ * v := by rw [h]
    _ = v * z := by group

theorem Zab_eq : D.Zab = zpowers D.a ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁) := by
  apply le_antisymm
  · rw [FooteCore.Zab, closure_le]
    rintro x (rfl | rfl | rfl)
    · exact mem_sup_left (mem_zpowers _)
    · exact mem_sup_right (mem_sup_left (mem_zpowers _))
    · exact mem_sup_right (mem_sup_right (mem_zpowers _))
  · exact sup_le (zpowers_le.2 (subset_closure (Set.mem_insert _ _)))
      (sup_le (zpowers_le.2 (subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
        (zpowers_le.2 (subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)))))

theorem mem_Zab_iff {x : G} : x ∈ D.Zab ↔ ∃ α w : G, (α = 1 ∨ α = D.a) ∧
    (w = 1 ∨ w = D.b₀ ∨ w = D.b₁ ∨ w = D.b) ∧ x = α * w := by
  have hBle : zpowers D.b₀ ⊔ zpowers D.b₁ ≤ D.B :=
    sup_le (zpowers_le.2 D.b₀_mem_B) (zpowers_le.2 D.b₁_mem_B)
  rw [Zab_eq]
  constructor
  · intro hx
    obtain ⟨α, hα, w, hw, rfl⟩ := (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm
      fun x hx y hy => D.A_comm_B x (zpowers_le.2 D.a_mem hx) y (hBle hy))).1 hx
    obtain ⟨w₀, hw₀, w₁, hw₁, rfl⟩ := (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm
      fun x hx y hy => D.B₀_comm_B₁ x (zpowers_le.2 D.b₀_mem hx) y
        (zpowers_le.2 D.b₁_mem hy))).1 hw
    refine ⟨α, w₀ * w₁, (mem_zpowers_of_mul_self D.a_mul_a).1 hα, ?_, rfl⟩
    rcases (mem_zpowers_of_mul_self D.b₀_mul_b₀).1 hw₀ with rfl | rfl <;>
      rcases (mem_zpowers_of_mul_self D.b₁_mul_b₁).1 hw₁ with rfl | rfl
    · left; group
    · right; right; left; group
    · right; left; group
    · right; right; right; rfl
  · rintro ⟨α, w, hα, hw, rfl⟩
    refine mul_mem ?_ ?_
    · rcases hα with rfl | rfl
      · exact one_mem _
      · exact mem_sup_left (mem_zpowers _)
    · rcases hw with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact mem_sup_right (mem_sup_left (mem_zpowers _))
      · exact mem_sup_right (mem_sup_right (mem_zpowers _))
      · exact mem_sup_right (mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _)))

theorem Zab_le_T₁ : D.Zab ≤ D.T₁ := by
  rw [FooteCore.Zab, closure_le]
  rintro x (rfl | rfl | rfl)
  · exact D.A_le_T₁ D.a_mem
  · exact D.B₀_le_T₁ D.b₀_mem
  · exact D.B₁_le_T₁ D.b₁_mem

theorem comm_of_mem_Zab {z : G} (hz : z ∈ D.Zab) {w : G} (hw : w ∈ D.T₁) : w * z = z * w := by
  have hle : D.Zab ≤ centralizer (D.T₁ : Set G) := by
    rw [FooteCore.Zab, closure_le]
    rintro y (rfl | rfl | rfl) <;> rw [SetLike.mem_coe, mem_centralizer_iff] <;> intro v hv
    · obtain ⟨α, hα, u, hu, rfl⟩ := D.mem_T₁_iff.1 hv
      have h1 : α * D.a = D.a * α := D.a_comm α (mem_sup_left hα)
      have h2 : u * D.a = D.a * u := (D.A_comm_B D.a D.a_mem u (D.B₀B₁_le_B hu)).symm
      calc α * u * D.a = α * (u * D.a) := mul_assoc _ _ _
        _ = α * (D.a * u) := by rw [h2]
        _ = (α * D.a) * u := (mul_assoc _ _ _).symm
        _ = (D.a * α) * u := by rw [h1]
        _ = D.a * (α * u) := mul_assoc _ _ _
    · exact D.comm_b₀_of_mem_T₁ hv
    · exact D.comm_b₁_of_mem_T₁ hv
  exact mem_centralizer_iff.1 (hle hz) w hw

theorem conj_eq_of_fix {v : G} (ha : v * D.a * v⁻¹ = D.a) (hb₀ : v * D.b₀ * v⁻¹ = D.b₀)
    (hb₁ : v * D.b₁ * v⁻¹ = D.b₁) {z : G} (hz : z ∈ D.Zab) : v * z * v⁻¹ = z := by
  have hle : D.Zab ≤ centralizer ({v} : Set G) := by
    rw [FooteCore.Zab, closure_le]
    rintro y (rfl | rfl | rfl) <;> rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    · exact comm_of_conj_eq ha
    · exact comm_of_conj_eq hb₀
    · exact comm_of_conj_eq hb₁
  have h := mem_centralizer_singleton_iff.1 (hle hz)
  rw [← h, mul_inv_cancel_right]

theorem conj_mem_Zab_of_gen {v : G} (ha : v * D.a * v⁻¹ ∈ D.Zab) (hb₀ : v * D.b₀ * v⁻¹ ∈ D.Zab)
    (hb₁ : v * D.b₁ * v⁻¹ ∈ D.Zab) {z : G} (hz : z ∈ D.Zab) : v * z * v⁻¹ ∈ D.Zab := by
  have hle : D.Zab ≤ D.Zab.comap (MulAut.conj v).toMonoidHom := by
    conv_lhs => rw [FooteCore.Zab]
    rw [closure_le]
    rintro y (rfl | rfl | rfl) <;>
      simp only [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    · exact ha
    · exact hb₀
    · exact hb₁
  have h := hle hz
  simpa only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h

theorem conj_b₀_cases {u : G} (hu : u ∈ T) :
    (u * D.b₀ * u⁻¹ = D.b₀ ∧ u * D.b₁ * u⁻¹ = D.b₁) ∨
      (u * D.b₀ * u⁻¹ = D.b₁ ∧ u * D.b₁ * u⁻¹ = D.b₀) := by
  have hmem : u * D.b₀ * u⁻¹ ∈ D.B₀ ⊔ D.B₁ := D.conj_mem_B₀B₁ hu (mem_sup_left D.b₀_mem)
  have hcomm : ∀ w ∈ D.B₀ ⊔ D.B₁, w * (u * D.b₀ * u⁻¹) = (u * D.b₀ * u⁻¹) * w := by
    intro w hw
    have hw' : u⁻¹ * w * u ∈ D.B₀ ⊔ D.B₁ := by
      have := D.conj_mem_B₀B₁ (inv_mem hu) hw
      rwa [inv_inv] at this
    have h := D.b₀_comm_B₀B₁ hw'
    calc w * (u * D.b₀ * u⁻¹) = u * ((u⁻¹ * w * u) * D.b₀) * u⁻¹ := by group
      _ = u * (D.b₀ * (u⁻¹ * w * u)) * u⁻¹ := by rw [h]
      _ = (u * D.b₀ * u⁻¹) * w := by group
  have hub : u * D.b * u⁻¹ = D.b := by rw [D.b_comm_T hu, mul_inv_cancel_right]
  have hconj₁ : u * D.b₁ * u⁻¹ = (u * D.b₀ * u⁻¹) * D.b := by
    calc u * D.b₁ * u⁻¹ = u * (D.b₀ * D.b) * u⁻¹ := by rw [D.b₀_mul_b]
      _ = (u * D.b₀ * u⁻¹) * (u * D.b * u⁻¹) := by group
      _ = (u * D.b₀ * u⁻¹) * D.b := by rw [hub]
  rcases D.eq_of_comm_B₀B₁ hmem hcomm with h | h | h | h
  · exact absurd (conj_eq_one_iff.1 h) D.b₀_ne_one
  · left
    exact ⟨h, by rw [hconj₁, h, D.b₀_mul_b]⟩
  · right
    refine ⟨h, ?_⟩
    rw [hconj₁, h]
    show D.b₁ * (D.b₀ * D.b₁) = D.b₀
    rw [← mul_assoc, ← D.B₀_comm_B₁ D.b₀ D.b₀_mem D.b₁ D.b₁_mem, mul_assoc, D.b₁_mul_b₁,
      mul_one]
  · exfalso
    have h' : D.b₀ = D.b := by
      have h'' : u * D.b₀ * u⁻¹ = u * D.b * u⁻¹ := by rw [h, hub]
      exact mul_left_cancel (mul_right_cancel h'')
    apply D.b₁_ne_one
    have h2 : D.b₀ * D.b₁ = D.b₀ * 1 := by rw [mul_one]; exact h'.symm
    exact mul_left_cancel h2

theorem conj_s_a : D.s * D.a * D.s⁻¹ = D.a := by
  rw [← D.A_comm_B D.a D.a_mem D.s D.s_mem_B, mul_inv_cancel_right]

theorem conj_Zab_cases {u : G} (hu : u ∈ T) {x : G} (hx : x ∈ D.Zab) :
    u * x * u⁻¹ = x ∨ u * x * u⁻¹ = D.s * x * D.s⁻¹ := by
  have hua : u * D.a * u⁻¹ = D.a := by rw [D.a_comm_T hu, mul_inv_cancel_right]
  rcases conj_b₀_cases D hu with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
  · exact Or.inl (conj_eq_of_fix D hua h₀ h₁ hx)
  · right
    have ha' : (D.s⁻¹ * u) * D.a * (D.s⁻¹ * u)⁻¹ = D.a := by
      calc (D.s⁻¹ * u) * D.a * (D.s⁻¹ * u)⁻¹ = D.s⁻¹ * (u * D.a * u⁻¹) * D.s := by group
        _ = D.s * D.a * D.s⁻¹ := by rw [hua, D.s_inv]
        _ = D.a := conj_s_a D
    have hb₀' : (D.s⁻¹ * u) * D.b₀ * (D.s⁻¹ * u)⁻¹ = D.b₀ := by
      calc (D.s⁻¹ * u) * D.b₀ * (D.s⁻¹ * u)⁻¹ = D.s⁻¹ * (u * D.b₀ * u⁻¹) * D.s := by group
        _ = D.s * D.b₁ * D.s⁻¹ := by rw [h₀, D.s_inv]
        _ = D.b₀ := D.conj_s_b₁
    have hb₁' : (D.s⁻¹ * u) * D.b₁ * (D.s⁻¹ * u)⁻¹ = D.b₁ := by
      calc (D.s⁻¹ * u) * D.b₁ * (D.s⁻¹ * u)⁻¹ = D.s⁻¹ * (u * D.b₁ * u⁻¹) * D.s := by group
        _ = D.s * D.b₀ * D.s⁻¹ := by rw [h₁, D.s_inv]
        _ = D.b₁ := D.conj_s_b₀
    have key := conj_eq_of_fix D ha' hb₀' hb₁' hx
    calc u * x * u⁻¹ = D.s * ((D.s⁻¹ * u) * x * (D.s⁻¹ * u)⁻¹) * D.s⁻¹ := by group
      _ = D.s * x * D.s⁻¹ := by rw [key]

theorem conj_mem_Zab_of_mem_T {u : G} (hu : u ∈ T) {x : G} (hx : x ∈ D.Zab) :
    u * x * u⁻¹ ∈ D.Zab := by
  have hb₀ : D.b₀ ∈ D.Zab := subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hb₁ : D.b₁ ∈ D.Zab :=
    subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  refine conj_mem_Zab_of_gen D ?_ ?_ ?_ hx
  · rw [D.a_comm_T hu, mul_inv_cancel_right]
    exact subset_closure (Set.mem_insert _ _)
  · rcases conj_b₀_cases D hu with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    · exact hb₀
    · exact hb₁
  · rcases conj_b₀_cases D hu with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h]
    · exact hb₁
    · exact hb₀

include D in
theorem mem_Zab_of_comm_T {z : G} (hz : z ∈ T) (hc : ∀ u ∈ T, u * z = z * u) : z ∈ D.Zab := by
  have hE := D.isE64_Frep 0 0
  have hzE : z ∈ D.Frep 0 0 := by
    rw [← D.centralizer_E64 hE]
    exact mem_inf.2 ⟨hz, mem_centralizer_iff.2 fun v hv => hc v (hE.1 hv)⟩
  obtain ⟨α, hα, w, hw, rfl⟩ := D.mem_T₁_iff.1 (D.le_T₁_of_isE64 hE hzE)
  have hwc : ∀ w' ∈ D.B₀ ⊔ D.B₁, w' * w = w * w' := by
    intro w' hw'
    have h1 := hc w' (D.T₁_le_T (D.B₀B₁_le_T₁ hw'))
    have h2 : α * w' = w' * α := D.A_comm_B₀B₁ α hα w' hw'
    have : α * (w' * w) = α * (w * w') := by
      calc α * (w' * w) = (w' * α) * w := by rw [← mul_assoc, h2]
        _ = w' * (α * w) := mul_assoc _ _ _
        _ = α * w * w' := h1
        _ = α * (w * w') := mul_assoc _ _ _
    exact mul_left_cancel this
  have hαt : α * D.t = D.t * α := by
    have h1 := hc D.t D.t_mem_T
    have hwB : w ∈ D.B := D.B₀B₁_le_B hw
    have e : (D.t * α * D.t⁻¹) * (D.t * w * D.t⁻¹) = α * w := by
      calc (D.t * α * D.t⁻¹) * (D.t * w * D.t⁻¹) = D.t * (α * w) * D.t⁻¹ := by group
        _ = α * w := by rw [h1, mul_inv_cancel_right]
    obtain ⟨hα', -⟩ := D.eq_of_mul_eq_mul_T₀ (D.conj_t_A α hα) hα (D.conj_t_B w hwB) hwB e
    calc α * D.t = (D.t * α * D.t⁻¹) * D.t := by rw [hα']
      _ = D.t * α := by group
  exact (mem_Zab_iff D).2 ⟨α, w, D.eq_one_or_a_of_comm_t hα hαt, D.eq_of_comm_B₀B₁ hw hwc, rfl⟩

end CFSG.CGT.Foote81L6.Fusion3
