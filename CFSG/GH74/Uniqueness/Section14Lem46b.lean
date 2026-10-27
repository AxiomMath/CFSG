module

public import CFSG.GH74.Uniqueness.Section14Lem46a
public import CFSG.GH74.Uniqueness.Section14Defs
public import CFSG.GH74.Uniqueness.Section14Lem43

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] {Z : Set X} {M : Subgroup X} {t : X} {n r : ℕ}
  {L K J Mo P U T S2 : Subgroup X}

namespace Sec146

variable (F : Facts14 Z M t n r L K J Mo P U T S2)
include F

theorem comm_P_U : ∀ x ∈ P, ∀ u ∈ U, x * u = u * x := by
  intro x hx u hu
  have hu' := F.U_le_J hu
  rw [F.J_eq] at hu'
  exact (mem_centralizer_iff.mp hu') x (F.P_le_L hx)

theorem comm_L_J : ∀ x ∈ L, ∀ j ∈ J, x * j = j * x := by
  intro x hx j hj
  rw [F.J_eq] at hj
  exact (mem_centralizer_iff.mp hj) x hx

theorem U_le_normalizer_P : U ≤ normalizer (P : Set X) := by
  intro u hu
  apply centralizer_le_normalizer
  rw [mem_centralizer_iff]
  intro x hx
  exact comm_P_U F x hx u hu

theorem mem_T_iff {x : X} : x ∈ T ↔ ∃ p ∈ P, ∃ u ∈ U, x = p * u := by
  rw [F.T_eq, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ (U_le_normalizer_P F)]
  constructor
  · rintro ⟨p, hp, u, hu, rfl⟩
    exact ⟨p, hp, u, hu, rfl⟩
  · rintro ⟨p, hp, u, hu, rfl⟩
    exact ⟨p, hp, u, hu, rfl⟩

theorem P_le_T : P ≤ T := by rw [F.T_eq]; exact le_sup_left
theorem U_le_T : U ≤ T := by rw [F.T_eq]; exact le_sup_right
theorem Mo_le_T : Mo ≤ T := F.Mo_le_P.trans (P_le_T F)
theorem T_le_S2 : T ≤ S2 := F.T_le_S2

theorem P_inf_U : P ⊓ U = ⊥ := by
  rw [eq_bot_iff, ← F.L_inf_J]
  exact inf_le_inf F.P_le_L F.U_le_J

theorem Mo_inf_U : Mo ⊓ U = ⊥ := by
  rw [eq_bot_iff, ← P_inf_U F]
  exact inf_le_inf_right _ F.Mo_le_P

theorem decomp_unique {p p' u u' : X} (hp : p ∈ P) (hp' : p' ∈ P) (hu : u ∈ U) (hu' : u' ∈ U)
    (h : p * u = p' * u') : p = p' ∧ u = u' := by
  have h1 : p'⁻¹ * p = u' * u⁻¹ := by
    calc p'⁻¹ * p = p'⁻¹ * (p * u) * u⁻¹ := by group
      _ = p'⁻¹ * (p' * u') * u⁻¹ := by rw [h]
      _ = u' * u⁻¹ := by group
  have h2 : p'⁻¹ * p ∈ P ⊓ U :=
    mem_inf.mpr ⟨mul_mem (inv_mem hp') hp, h1 ▸ mul_mem hu' (inv_mem hu)⟩
  rw [P_inf_U F, mem_bot] at h2
  have hpp : p = p' := by
    have := congrArg (p' * ·) h2
    simpa using this
  refine ⟨hpp, ?_⟩
  rw [h2] at h1
  have := congrArg (· * u) h1
  simpa using this

theorem U_comm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := comm_of_sq_eq_one F.U_sq

theorem Mo_comm : ∀ a ∈ Mo, ∀ b ∈ Mo, a * b = b * a := comm_of_sq_eq_one F.Mo_sq

theorem comm_Mo_U : ∀ m ∈ Mo, ∀ u ∈ U, m * u = u * m := fun m hm u hu =>
  comm_P_U F m (F.Mo_le_P hm) u hu

theorem U_le_normalizer_Mo : U ≤ normalizer (Mo : Set X) := by
  intro u hu
  apply centralizer_le_normalizer
  rw [mem_centralizer_iff]
  intro m hm
  exact comm_Mo_U F m hm u hu

theorem mem_MoU_iff {x : X} : x ∈ Mo ⊔ U ↔ ∃ m ∈ Mo, ∃ u ∈ U, x = m * u := by
  rw [← SetLike.mem_coe,
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ (U_le_normalizer_Mo F)]
  constructor
  · rintro ⟨m, hm, u, hu, rfl⟩
    exact ⟨m, hm, u, hu, rfl⟩
  · rintro ⟨m, hm, u, hu, rfl⟩
    exact ⟨m, hm, u, hu, rfl⟩

theorem MoU_le_T : Mo ⊔ U ≤ T := sup_le (Mo_le_T F) (U_le_T F)

theorem MoU_sq : ∀ x ∈ Mo ⊔ U, x * x = 1 := by
  intro x hx
  obtain ⟨m, hm, u, hu, rfl⟩ := (mem_MoU_iff F).mp hx
  calc m * u * (m * u) = m * (u * m) * u := by group
    _ = m * (m * u) * u := by rw [comm_Mo_U F m hm u hu]
    _ = (m * m) * (u * u) := by group
    _ = 1 := by rw [F.Mo_sq m hm, F.U_sq u hu, one_mul]

theorem MoU_comm : ∀ a ∈ Mo ⊔ U, ∀ b ∈ Mo ⊔ U, a * b = b * a := comm_of_sq_eq_one (MoU_sq F)

theorem MoU_central : ∀ w ∈ Mo ⊔ U, ∀ x ∈ T, w * x = x * w := by
  intro w hw x hx
  obtain ⟨m, hm, u, hu, rfl⟩ := (mem_MoU_iff F).mp hw
  obtain ⟨p, hp, u', hu', rfl⟩ := (mem_T_iff F).mp hx
  have h1 : m * p = p * m := (F.Mo_central p hp m hm).symm
  have h2 : u * p = p * u := (comm_P_U F p hp u hu).symm
  have h3 : u * u' = u' * u := U_comm F u hu u' hu'
  have h4 : m * u' = u' * m := comm_Mo_U F m hm u' hu'
  calc m * u * (p * u') = m * (u * p) * u' := by group
    _ = m * p * (u * u') := by rw [h2]; group
    _ = p * m * (u' * u) := by rw [h1, h3]
    _ = p * (m * u') * u := by group
    _ = p * u' * (m * u) := by rw [h4]; group

theorem center_T : ∀ x ∈ T, (∀ y ∈ T, x * y = y * x) → x ∈ Mo ⊔ U := by
  intro x hx hc
  obtain ⟨p, hp, u, hu, rfl⟩ := (mem_T_iff F).mp hx
  have hpc : ∀ y ∈ P, p * y = y * p := by
    intro y hy
    have h1 := hc y (P_le_T F hy)
    have h2 : u * y = y * u := (comm_P_U F y hy u hu).symm
    have : p * y * u = y * p * u := by
      calc p * y * u = p * (u * y) := by rw [h2, mul_assoc]
        _ = p * u * y := by group
        _ = y * (p * u) := h1
        _ = y * p * u := by group
    exact mul_right_cancel this
  exact mul_mem (mem_sup_left (F.center_P p hp hpc)) (mem_sup_right hu)

theorem T_inf_L : ∀ x ∈ T, x ∈ L → x ∈ P := by
  intro x hx hxL
  obtain ⟨p, hp, u, hu, rfl⟩ := (mem_T_iff F).mp hx
  have huL : u ∈ L := by
    have := L.mul_mem (L.inv_mem (F.P_le_L hp)) hxL
    simpa using this
  have : u ∈ L ⊓ J := mem_inf.mpr ⟨huL, F.U_le_J hu⟩
  rw [F.L_inf_J, mem_bot] at this
  rw [this, mul_one]
  exact hp

theorem T_inf_J : ∀ x ∈ T, x ∈ J → x ∈ U := by
  intro x hx hxJ
  obtain ⟨p, hp, u, hu, rfl⟩ := (mem_T_iff F).mp hx
  have hpJ : p ∈ J := by
    have := J.mul_mem hxJ (J.inv_mem (F.U_le_J hu))
    simpa using this
  have : p ∈ L ⊓ J := mem_inf.mpr ⟨F.P_le_L hp, hpJ⟩
  rw [F.L_inf_J, mem_bot] at this
  rw [this, one_mul]
  exact hu

theorem NT_le_M : normalizer (T : Set X) ≤ M := by
  intro g hg
  have := mem_normalizer_commutator hg
  rw [F.comm_T] at this
  exact F.normalizer_Mo_le this

theorem NT_norm_Mo : normalizer (T : Set X) ≤ normalizer (Mo : Set X) := by
  intro g hg
  have := mem_normalizer_commutator hg
  rwa [F.comm_T] at this

theorem NT_norm_MoU {g : X} (hg : g ∈ normalizer (T : Set X)) :
    ∀ w ∈ Mo ⊔ U, g * w * g⁻¹ ∈ Mo ⊔ U := by
  intro w hw
  apply center_T F
  · exact (mem_normalizer_iff.mp hg w).mp (MoU_le_T F hw)
  · intro y hy
    have hy' : g⁻¹ * y * g ∈ T := by
      have := (mem_normalizer_iff.mp (inv_mem hg) y).mp hy
      simpa using this
    have h1 := MoU_central F w hw _ hy'
    calc g * w * g⁻¹ * y = g * (w * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * w) * g⁻¹ := by rw [h1]
      _ = y * (g * w * g⁻¹) := by group

theorem S2_le_NT : S2 ≤ normalizer (T : Set X) := F.S2_sylow.le

theorem S2_le_M : S2 ≤ M := (S2_le_NT F).trans (NT_le_M F)

theorem S2_le_C0 : S2 ≤ centralizer (Mo : Set X) := by
  intro x hx
  apply F.two_C0 x (S2_le_M F hx)
  exact F.S2_sylow.isPGroup.to_le (zpowers_le.mpr hx)

theorem J_le_NL : J ≤ normalizer (L : Set X) := by
  rw [F.J_eq]
  exact centralizer_le_normalizer _

theorem S2_inf_NL [Finite X] {x : X} (hx : x ∈ S2) (hxN : x ∈ normalizer (L : Set X)) :
    x ∈ T := by
  have hW : T ⊔ zpowers x ≤ normalizer (L : Set X) :=
    sup_le F.T_sylow.le (zpowers_le.mpr hxN)
  have hWS : T ⊔ zpowers x ≤ S2 := sup_le F.T_le_S2 (zpowers_le.mpr hx)
  have heq := F.T_sylow.eq_of_le le_sup_left hW (F.S2_sylow.isPGroup.to_le hWS)
  rw [← heq]
  exact mem_sup_right (mem_zpowers x)

theorem cent_le_NL {v : X} (hv : v ∈ J) (hv1 : v ≠ 1) :
    centralizer ({v} : Set X) ≤ normalizer (L : Set X) := by
  have hY1 : zpowers v ≠ ⊥ := by
    intro h0
    apply hv1
    have := mem_zpowers v
    rw [h0, mem_bot] at this
    exact this
  refine le_trans ?_ (F.NY_le (zpowers v) (zpowers_le.mpr hv) hY1)
  intro x hx
  apply centralizer_le_normalizer
  rw [mem_centralizer_iff]
  intro y hy
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  have hc : Commute v x := (mem_centralizer_singleton_iff.mp hx).symm
  exact (hc.zpow_left k).eq

theorem T_le_cent_u {u : X} (hu : u ∈ U) : T ≤ centralizer ({u} : Set X) := by
  intro x hx
  rw [mem_centralizer_singleton_iff]
  exact (MoU_central F u (mem_sup_right hu) x hx).symm

theorem cent_S2_u [Finite X] {u : X} (hu : u ∈ U) (hu1 : u ≠ 1) :
    centralizer ({u} : Set X) ⊓ S2 = T := by
  apply le_antisymm
  · intro x hx
    exact S2_inf_NL F (mem_inf.mp hx).2 (cent_le_NL F (F.U_le_J hu) hu1 (mem_inf.mp hx).1)
  · exact le_inf (T_le_cent_u F hu) F.T_le_S2

theorem cent_out [Finite X] {x : X} (hx : x ∈ S2) (hxT : x ∉ T) {w : X} (hw : w ∈ Mo ⊔ U)
    (hxw : x * w = w * x) : w ∈ Mo := by
  obtain ⟨m, hm, u, hu, rfl⟩ := (mem_MoU_iff F).mp hw
  by_cases hu1 : u = 1
  · rw [hu1, mul_one]
    exact hm
  exfalso
  have hxm : x * m = m * x := ((mem_centralizer_iff.mp (S2_le_C0 F hx)) m hm).symm
  have hxu : x * u = u * x := by
    have : m * (x * u) = m * (u * x) := by
      calc m * (x * u) = (x * m) * u := by rw [hxm]; group
        _ = x * (m * u) := by group
        _ = m * u * x := hxw
        _ = m * (u * x) := by group
    exact mul_left_cancel this
  have : x ∈ centralizer ({u} : Set X) ⊓ S2 :=
    mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hxu, hx⟩
  rw [cent_S2_u F hu hu1] at this
  exact hxT this

theorem exists_S2_not_T [Finite X] : ∃ y ∈ S2, y ∉ T := by
  have hT2 : IsPGroup 2 T := F.T_sylow.isPGroup
  apply exists_mem_not_mem_of_lt_two_part hT2 F.S2_sylow
  rw [F.two_part]
  have h1 : 1 < 2 ^ n := Nat.one_lt_two_pow (by have := F.three_le; omega)
  have hT0 : 0 < Nat.card T := Nat.card_pos
  nlinarith

theorem K_le_M : K ≤ M := by
  rw [F.K_eq]
  exact inf_le_left.trans inf_le_left

theorem K_le_L : K ≤ L := by
  rw [F.K_eq]
  exact inf_le_right

theorem K_le_D : K ≤ dGrp M t := by
  rw [F.K_eq]
  exact inf_le_left

theorem K_comm_U : ∀ k ∈ K, ∀ u ∈ U, k * u = u * k := fun k hk u hu =>
  comm_L_J F k (K_le_L F hk) u (F.U_le_J hu)

theorem K_norm_Mo : ∀ k ∈ K, ∀ m ∈ Mo, k * m * k⁻¹ ∈ Mo := fun k hk m hm =>
  F.Mo_normal k (K_le_M F hk) m hm

theorem K_le_NT : K ≤ normalizer (T : Set X) := by
  intro k hk
  rw [mem_normalizer_iff]
  intro x
  have key : ∀ k ∈ K, ∀ x ∈ T, k * x * k⁻¹ ∈ T := by
    intro k hk x hx
    obtain ⟨p, hp, u, hu, rfl⟩ := (mem_T_iff F).mp hx
    have hkP := F.D_norm_P (K_le_D F hk)
    have h1 : k * p * k⁻¹ ∈ P := (mem_normalizer_iff.mp hkP p).mp hp
    have h2 : k * u * k⁻¹ = u := by rw [K_comm_U F k hk u hu, mul_inv_cancel_right]
    have e : k * (p * u) * k⁻¹ = (k * p * k⁻¹) * (k * u * k⁻¹) := by group
    rw [e, h2]
    exact mul_mem (P_le_T F h1) (U_le_T F hu)
  constructor
  · exact key k hk x
  · intro hx
    have := key k⁻¹ (inv_mem hk) _ hx
    simpa [mul_assoc] using this

theorem cent_MoU_le {g : X} (hg : ∀ w ∈ Mo ⊔ U, g * w = w * g) : g ∈ T := by
  obtain ⟨u, hu, hu1⟩ : ∃ u ∈ U, u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact F.U_ne_bot (eq_bot_iff.mpr fun x hx => mem_bot.mpr (hcon x hx))
  rw [← F.cent_Mo_u u hu hu1]
  refine mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_centralizer_iff]
    intro m hm
    exact (hg m (mem_sup_left hm)).symm
  · exact mem_centralizer_singleton_iff.mpr (hg u (mem_sup_right hu))

theorem exists_u [Finite X] : ∃ u ∈ U, u ≠ 1 ∧ ∀ s ∈ S2, s * u * s⁻¹ * u⁻¹ ∈ Mo := by
  obtain ⟨u₀, hu₀, hu₀1⟩ : ∃ u ∈ U, u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact F.U_ne_bot (eq_bot_iff.mpr fun x hx => mem_bot.mpr (hcon x hx))
  have hu₀Mo : u₀ ∉ Mo := by
    intro h
    have : u₀ ∈ Mo ⊓ U := mem_inf.mpr ⟨h, hu₀⟩
    rw [Mo_inf_U F, mem_bot] at this
    exact hu₀1 this
  have hSW : S2 ≤ normalizer ((Mo ⊔ U : Subgroup X) : Set X) := by
    intro s hs
    have hsN := S2_le_NT F hs
    rw [mem_normalizer_iff]
    intro w
    constructor
    · exact NT_norm_MoU F hsN w
    · intro hw
      have := NT_norm_MoU F (inv_mem hsN) _ hw
      simpa [mul_assoc] using this
  obtain ⟨w, hw, hwMo, hwS⟩ := exists_mem_central_mod F.S2_sylow.isPGroup
    ((MoU_le_T F).trans F.T_le_S2) (S2_le_C0 F) hSW (mem_sup_right hu₀) hu₀Mo
  obtain ⟨m, hm, u, hu, rfl⟩ := (mem_MoU_iff F).mp hw
  refine ⟨u, hu, fun h1 => hwMo (by rw [h1, mul_one]; exact hm), fun s hs => ?_⟩
  have hsm : s * m = m * s := ((mem_centralizer_iff.mp (S2_le_C0 F hs)) m hm).symm
  have h1 := hwS s hs
  have e : s * u * s⁻¹ * u⁻¹ = m⁻¹ * (s * (m * u) * s⁻¹ * (m * u)⁻¹) * m := by
    have : s * m * s⁻¹ = m := by rw [hsm, mul_inv_cancel_right]
    calc s * u * s⁻¹ * u⁻¹ = m⁻¹ * (s * m * s⁻¹) * (s * u * s⁻¹) * u⁻¹ := by
          rw [this]; group
      _ = m⁻¹ * (s * (m * u) * s⁻¹ * (m * u)⁻¹) * m := by group
  rw [e]
  have h2 : m⁻¹ * (s * (m * u) * s⁻¹ * (m * u)⁻¹) * m = s * (m * u) * s⁻¹ * (m * u)⁻¹ := by
    have hcm := Mo_comm F _ h1 m hm
    calc m⁻¹ * (s * (m * u) * s⁻¹ * (m * u)⁻¹) * m
        = m⁻¹ * ((s * (m * u) * s⁻¹ * (m * u)⁻¹) * m) := by group
      _ = m⁻¹ * (m * (s * (m * u) * s⁻¹ * (m * u)⁻¹)) := by rw [hcm]
      _ = s * (m * u) * s⁻¹ * (m * u)⁻¹ := by group
  rw [h2]
  exact h1

end Sec146

end CFSG.GH74.Uniqueness
