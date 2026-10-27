module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.ZTwo.Setup

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin Subgroup ZTwoAux

namespace ZTwoConfig

variable {G : Type} [Group G] [Finite G] {T S U R : Subgroup G} {y x c : G}
  (h : ZTwoConfig T S U R y x c)

include h

theorem y_sq : y ^ 2 = 1 := h.y_order ▸ pow_orderOf_eq_one y

theorem y_ne_one : y ≠ 1 := by
  intro e
  have := h.y_order
  rw [e, orderOf_one] at this
  omega

theorem R_le_S : R ≤ S := h.R_le

theorem R_le_normalizer_zpowers_y : R ≤ normalizer ((zpowers y : Subgroup G) : Set G) :=
  fun r hr => mem_normalizer_zpowers_of_comm (h.y_comm r (h.R_le hr))

theorem mem_S_iff {s : G} : s ∈ S ↔ ∃ r ∈ R, s = r ∨ s = r * y := by
  rw [h.S_eq, A3Dich.mem_sup_iff_of_le_normalizer h.R_le_normalizer_zpowers_y]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rcases (mem_zpowers_iff_of_sq_eq_one h.y_sq).mp hb with rfl | rfl
    · exact ⟨a, ha, Or.inl (by simp)⟩
    · exact ⟨a, ha, Or.inr rfl⟩
  · rintro ⟨r, hr, h1 | h1⟩ <;> rw [h1]
    · exact ⟨r, hr, 1, one_mem _, by simp⟩
    · exact ⟨r, hr, y, mem_zpowers y, rfl⟩

theorem sq_of_mem_S {r : G} (hr : r ∈ R) : (r * y) ^ 2 = r ^ 2 := by
  have hc : y * r = r * y := (h.y_comm r (h.R_le hr)).symm
  have hy : y * y = 1 := by simpa [pow_two] using h.y_sq
  rw [pow_two, pow_two]
  calc r * y * (r * y) = r * (y * r) * y := by group
    _ = r * (r * y) * y := by rw [hc]
    _ = r * r * (y * y) := by group
    _ = r * r := by rw [hy, mul_one]

theorem conjU_e {s₀ : G} (hs₀ : s₀ ∈ S) : conjSubgroup U (x * s₀) = conjSubgroup U x := by
  rw [← conjSubgroup_conjSubgroup]
  exact conjSubgroup_eq_iff_mem_normalizer.mpr (h.S_norm_U' hs₀)

theorem conjU'_e {s₀ : G} (hs₀ : s₀ ∈ S) : conjSubgroup (conjSubgroup U x) (x * s₀) = U := by
  rw [← conjSubgroup_conjSubgroup, h.U'_conj]
  exact conjSubgroup_eq_iff_mem_normalizer.mpr (h.S_normalizes_U hs₀)

theorem U_conj_e {s₀ u : G} (hs₀ : s₀ ∈ S) (hu : u ∈ U) :
    (x * s₀)⁻¹ * u * (x * s₀) ∈ conjSubgroup U x := by
  have := mem_conj_self (g := x * s₀) hu
  rwa [h.conjU_e hs₀] at this

theorem U'_conj_e {s₀ v : G} (hs₀ : s₀ ∈ S) (hv : v ∈ conjSubgroup U x) :
    (x * s₀)⁻¹ * v * (x * s₀) ∈ U := by
  have := mem_conj_self (g := x * s₀) hv
  rwa [h.conjU'_e hs₀] at this

variable {z : G} (hd : D8Data R U (conjSubgroup U x) z)

include hd

theorem z_mem_S : z ∈ S := h.U_le hd.z_mem_U

theorem comm_z_S {s : G} (hs : s ∈ S) : s * z = z * s := by
  obtain ⟨r, hr, rfl | rfl⟩ := (h.mem_S_iff).mp hs
  · exact hd.z_central hr
  · have h1 : z * y = y * z := h.y_comm z (h.z_mem_S hd)
    calc r * y * z = r * (y * z) := by rw [mul_assoc]
      _ = r * (z * y) := by rw [← h1]
      _ = (r * z) * y := by rw [mul_assoc]
      _ = (z * r) * y := by rw [hd.z_central hr]
      _ = z * (r * y) := by rw [mul_assoc]

theorem central_S {s : G} (hs : s ∈ S) (hc : ∀ t ∈ S, s * t = t * s) :
    s = 1 ∨ s = z ∨ s = y ∨ s = z * y := by
  obtain ⟨r, hr, rfl | rfl⟩ := (h.mem_S_iff).mp hs
  · rcases (mem_zpowers_iff_of_sq_eq_one hd.z_sq).mp
      (hd.mem_zpowers_of_central hr fun t ht => hc t (h.R_le ht)) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · have hr' : r ∈ zpowers z := by
      refine hd.mem_zpowers_of_central hr fun t ht => ?_
      have h1 := hc t (h.R_le ht)
      have hyt : y * t = t * y := (h.y_comm t (h.R_le ht)).symm
      have h2 : r * t * y = t * r * y := by
        calc r * t * y = r * (t * y) := by rw [mul_assoc]
          _ = r * (y * t) := by rw [hyt]
          _ = r * y * t := by rw [mul_assoc]
          _ = t * (r * y) := h1
          _ = t * r * y := by rw [mul_assoc]
      exact mul_right_cancel h2
    rcases (mem_zpowers_iff_of_sq_eq_one hd.z_sq).mp hr' with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl (by simp)))
    · exact Or.inr (Or.inr (Or.inr rfl))

theorem x_inv_z : x⁻¹ * z * x = z := by
  have e0 : x * (x⁻¹ * z * x) * x⁻¹ = z := by group
  have h1 : x⁻¹ * z * x ∈ conjSubgroup U x := by
    rw [mem_conjSubgroup_iff, e0]
    exact hd.z_mem_U
  have h2 : x⁻¹ * z * x ∈ U := by
    have : x⁻¹ * z * x ∈ conjSubgroup (conjSubgroup U x) x := by
      rw [mem_conjSubgroup_iff, e0]
      exact hd.z_mem_V
    rwa [h.U'_conj] at this
  rcases (mem_zpowers_iff_of_sq_eq_one hd.z_sq).mp (hd.inter _ h2 h1) with e | e
  · exfalso
    apply hd.z_ne_one
    calc z = x * (x⁻¹ * z * x) * x⁻¹ := by group
      _ = 1 := by rw [e]; group
  · exact e

theorem x_comm_z : x * z = z * x := by
  have := h.x_inv_z hd
  calc x * z = x * (x⁻¹ * z * x) := by rw [this]
    _ = z * x := by group

theorem y_not_conj_z (g : G) : g⁻¹ * y * g ≠ z := by
  intro hg
  have hcent : centralizer ({z} : Set G) = conjSubgroup (centralizer ({y} : Set G)) g := by
    ext a
    rw [mem_conjSubgroup_iff, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
      ← hg]
    constructor
    · intro e
      calc g * a * g⁻¹ * y = g * (a * (g⁻¹ * y * g)) * g⁻¹ := by group
        _ = g * (g⁻¹ * y * g * a) * g⁻¹ := by rw [e]
        _ = y * (g * a * g⁻¹) := by group
    · intro e
      calc a * (g⁻¹ * y * g) = g⁻¹ * (g * a * g⁻¹ * y) * g := by group
        _ = g⁻¹ * (y * (g * a * g⁻¹)) * g := by rw [e]
        _ = g⁻¹ * y * g * a := by group
  have htwo : twoPart (centralizer ({z} : Set G)) = Nat.card S := by
    rw [hcent]
    have h1 := twoPart_map_equiv (MulAut.conj g⁻¹) (centralizer ({y} : Set G))
    have h2 : twoPart (conjSubgroup (centralizer ({y} : Set G)) g) =
        twoPart (centralizer ({y} : Set G)) := h1
    rw [h2]
    exact (isSylowTwoOf_iff.mp h.sylow_Cy).2.2.symm
  have hle : S ⊔ zpowers x ≤ centralizer ({z} : Set G) := by
    refine sup_le (fun s hs => mem_centralizer_singleton_iff.mpr (h.comm_z_S hd hs))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (h.x_comm_z hd)))
  have hp : IsPGroup 2 ↥(S ⊔ zpowers x) :=
    h.isPGroup_T.to_le (sup_le h.S_le (zpowers_le.mpr h.x_mem))
  have hcard := card_le_twoPart hle hp
  rw [htwo] at hcard
  have heq : S = S ⊔ zpowers x := Subgroup.eq_of_le_of_card_ge le_sup_left hcard
  exact h.x_not_mem (heq ▸ (le_sup_right : zpowers x ≤ S ⊔ zpowers x) (mem_zpowers x))

theorem y_conj : x⁻¹ * y * x = z * y := by
  have hYS : x⁻¹ * y * x ∈ S := h.conj_inv_mem h.y_mem
  have hc : ∀ t ∈ S, x⁻¹ * y * x * t = t * (x⁻¹ * y * x) := by
    intro t ht
    have ht' : x * t * x⁻¹ ∈ S := h.conj_mem ht
    have hy := h.y_comm _ ht'
    calc x⁻¹ * y * x * t = x⁻¹ * (y * (x * t * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * t * x⁻¹) * y) * x := by rw [← hy]
      _ = t * (x⁻¹ * y * x) := by group
  rcases h.central_S hd hYS (fun t ht => hc t ht) with e | e | e | e
  · exfalso
    apply h.y_ne_one
    calc y = x * (x⁻¹ * y * x) * x⁻¹ := by group
      _ = 1 := by rw [e]; group
  · exact absurd e (h.y_not_conj_z hd x)
  · exfalso
    apply h.x_not_mem
    refine h.N_y x h.x_mem (mem_normalizer_zpowers_of_comm ?_)
    calc x * y = x * (x⁻¹ * y * x) := by rw [e]
      _ = y * x := by group
  · exact e

theorem comm_zy_S {s : G} (hs : s ∈ S) : s * (z * y) = (z * y) * s := by
  calc s * (z * y) = (s * z) * y := by rw [mul_assoc]
    _ = (z * s) * y := by rw [h.comm_z_S hd hs]
    _ = z * (s * y) := by rw [mul_assoc]
    _ = z * (y * s) := by rw [h.y_comm s hs]
    _ = (z * y) * s := by rw [mul_assoc]

theorem conj_y_e {s₀ : G} (hs₀ : s₀ ∈ S) : (x * s₀)⁻¹ * y * (x * s₀) = z * y := by
  have h1 := h.y_conj hd
  have h2 := h.comm_zy_S hd hs₀
  calc (x * s₀)⁻¹ * y * (x * s₀) = s₀⁻¹ * (x⁻¹ * y * x) * s₀ := by group
    _ = s₀⁻¹ * (z * y) * s₀ := by rw [h1]
    _ = s₀⁻¹ * (s₀ * (z * y)) := by rw [mul_assoc, h2]
    _ = z * y := by group

theorem conj_z_e {s₀ : G} (hs₀ : s₀ ∈ S) : (x * s₀)⁻¹ * z * (x * s₀) = z := by
  have h1 := h.x_inv_z hd
  have h2 := h.comm_z_S hd hs₀
  calc (x * s₀)⁻¹ * z * (x * s₀) = s₀⁻¹ * (x⁻¹ * z * x) * s₀ := by group
    _ = s₀⁻¹ * z * s₀ := by rw [h1]
    _ = s₀⁻¹ * (s₀ * z) := by rw [mul_assoc, ← h2]
    _ = z := by group

end ZTwoConfig

end CFSG.QuasithinUnique
