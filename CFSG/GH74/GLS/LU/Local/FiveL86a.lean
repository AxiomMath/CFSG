module

public import CFSG.GH74.GLS.LU.Local.FiveCfg2

public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

theorem braid_of_cube {N : Type*} [Group N] (Hn : Subgroup N) [Hn.Normal] {a b : N}
    (ha : a * a ∈ Hn) (hb : b * b ∈ Hn) (hab : (a * b) ^ 3 ∈ Hn) :
    a⁻¹ * b⁻¹ * a⁻¹ * b * a * b ∈ Hn := by
  rw [← QuotientGroup.eq_one_iff]
  have ha' : (a : N ⧸ Hn) * a = 1 := by
    rw [← QuotientGroup.mk_mul]; exact (QuotientGroup.eq_one_iff _).mpr ha
  have hb' : (b : N ⧸ Hn) * b = 1 := by
    rw [← QuotientGroup.mk_mul]; exact (QuotientGroup.eq_one_iff _).mpr hb
  have hab' : ((a : N ⧸ Hn) * b) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).mpr hab
  have hai : (a : N ⧸ Hn)⁻¹ = a := inv_eq_of_mul_eq_one_right ha'
  have hbi : (b : N ⧸ Hn)⁻¹ = b := inv_eq_of_mul_eq_one_right hb'
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hai, hbi]
  calc (a : N ⧸ Hn) * b * a * b * a * b = ((a : N ⧸ Hn) * b) ^ 3 := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := hab'

theorem perm4_pow : ∀ σ : Equiv.Perm (Fin 4), σ ^ 3 = 1 ∨ σ ^ 4 = 1 := by decide

section Braid

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ v : G} {X₁ Y : Subgroup G}

theorem mem_NN_of_comm {x : G} (hz : x * z = z * x) (hu : x * u = u * x) : x ∈ NN z u := by
  apply CFSG.Walter.J1.mem_normalizer_of_conj_mem
  intro y hy
  have hle : UU z u ≤ centralizer ({x} : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hz.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hu.symm
  have h1 : x * y = y * x := (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm
  have : x * y * x⁻¹ = y := by rw [h1]; group
  rw [this]; exact hy

theorem Cfg2.H_le_NN (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) : H ≤ NN z u := fun x hx =>
  mem_NN_of_comm (c.b66.H_cent x hx).1 (c.b66.H_cent x hx).2

theorem Cfg2.zu_comm (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) : z * u = u * z := c.hs.zu_comm

theorem Cfg2.u_sq (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) : u * u = 1 := c.hs.u_sq

theorem Cfg2.z_sq (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) : z * z = 1 := c.hs.z_sq

theorem Cfg2.w₁_z (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) : w₁ * z * w₁⁻¹ = z := by
  have := c.hc.cz₁ c.b66.w₁_mem
  calc w₁ * z * w₁⁻¹ = (z * w₁) * w₁⁻¹ := by rw [this]
    _ = z := by group

theorem Cfg4.g_z (c : Cfg4 G p f z S K₁ K₂ t u H w₁ X₁ Y v) : (w₁ * v) * z * (w₁ * v)⁻¹ = u := by
  have h1 : (w₁ * v) * z * (w₁ * v)⁻¹ = w₁ * (v * z * v⁻¹) * w₁⁻¹ := by group
  rw [h1, c.b84.v_z]
  have e : w₁ * (z * u) * w₁⁻¹ = (w₁ * z * w₁⁻¹) * (w₁ * u * w₁⁻¹) := by group
  rw [e, c.w₁_z, c.b66.w₁_u]
  calc z * (u * z) = (z * u) * z := by group
    _ = (u * z) * z := by rw [c.zu_comm]
    _ = u * (z * z) := by group
    _ = u := by rw [c.z_sq, mul_one]

theorem Cfg4.v_u (c : Cfg4 G p f z S K₁ K₂ t u H w₁ X₁ Y v) : v * u * v⁻¹ = u := by
  have hu : u = z * (z * u) := by rw [← mul_assoc, c.z_sq, one_mul]
  have e : v * u * v⁻¹ = (v * z * v⁻¹) * (v * (z * u) * v⁻¹) := by
    conv_lhs => rw [hu]
    group
  rw [e, c.b84.v_z, c.b84.v_zu]
  calc z * u * z = (u * z) * z := by rw [c.zu_comm]
    _ = u * (z * z) := by group
    _ = u := by rw [c.z_sq, mul_one]

theorem Cfg4.g_u (c : Cfg4 G p f z S K₁ K₂ t u H w₁ X₁ Y v) : (w₁ * v) * u * (w₁ * v)⁻¹ = u * z := by
  have h1 : (w₁ * v) * u * (w₁ * v)⁻¹ = w₁ * (v * u * v⁻¹) * w₁⁻¹ := by group
  rw [h1, c.v_u, c.b66.w₁_u]

theorem Cfg4.g_uz (c : Cfg4 G p f z S K₁ K₂ t u H w₁ X₁ Y v) : (w₁ * v) * (u * z) * (w₁ * v)⁻¹ = z := by
  have e : (w₁ * v) * (u * z) * (w₁ * v)⁻¹ =
      ((w₁ * v) * u * (w₁ * v)⁻¹) * ((w₁ * v) * z * (w₁ * v)⁻¹) := by group
  rw [e, c.g_u, c.g_z]
  calc u * z * u = u * (z * u) := by group
    _ = u * (u * z) := by rw [c.zu_comm]
    _ = (u * u) * z := by group
    _ = z := by rw [c.u_sq, one_mul]

theorem Cfg4.cube_mem (c : Cfg4 G p f z S K₁ K₂ t u H w₁ X₁ Y v) : (w₁ * v) ^ 3 ∈ H := by
  obtain ⟨hn, ⟨φ⟩⟩ := c.b66.N_quot
  have hHN := c.H_le_NN
  set N := NN z u with hN
  let a : ↥N := ⟨w₁, c.w₁_NN⟩
  let b : ↥N := ⟨v, c.b84.v_N⟩
  let g : ↥N := a * b
  have h4 : g ^ 4 ∉ H.subgroupOf N := by
    intro h
    have hH : ((g ^ 4 : ↥N) : G) ∈ H := h
    have hcent := (c.b66.H_cent _ hH).1
    have hg : (g : G) = w₁ * v := rfl
    have hpow : ((g ^ 4 : ↥N) : G) = (w₁ * v) ^ 4 := by simp [hg]
    rw [hpow] at hcent
    set q : G := w₁ * v with hq
    have e1 : q * z * q⁻¹ = u := c.g_z
    have e2 : q * u * q⁻¹ = u * z := c.g_u
    have e3 : q * (u * z) * q⁻¹ = z := c.g_uz
    have hq4 : q ^ 4 = q * q * q * q := by simp only [pow_succ, pow_zero, one_mul]
    rw [hq4] at hcent
    have e4 : (q * q * q * q) * z * (q * q * q * q)⁻¹ = u := by
      have : (q * q * q * q) * z * (q * q * q * q)⁻¹ =
          q * (q * (q * (q * z * q⁻¹) * q⁻¹) * q⁻¹) * q⁻¹ := by group
      rw [this, e1, e2, e3, e1]
    have : (q * q * q * q) * z * (q * q * q * q)⁻¹ = z := by
      calc (q * q * q * q) * z * (q * q * q * q)⁻¹ = (z * (q * q * q * q)) * (q * q * q * q)⁻¹ := by
            rw [hcent]
        _ = z := by group
    exact c.hs.u_ne (e4.symm.trans this)
  have hφ := perm4_pow (φ (QuotientGroup.mk g))
  have h4' : (φ (QuotientGroup.mk g)) ^ 4 ≠ 1 := by
    intro h
    apply h4
    have : (QuotientGroup.mk (g ^ 4) : ↥N ⧸ H.subgroupOf N) = 1 := by
      apply φ.injective
      rw [map_one, QuotientGroup.mk_pow, map_pow]; exact h
    exact (QuotientGroup.eq_one_iff _).mp this
  have h3 : (φ (QuotientGroup.mk g)) ^ 3 = 1 := hφ.resolve_right h4'
  have : g ^ 3 ∈ H.subgroupOf N := by
    rw [← QuotientGroup.eq_one_iff]
    apply φ.injective
    rw [map_one, QuotientGroup.mk_pow, map_pow]; exact h3
  exact this

theorem Cfg4.braid (c : Cfg4 G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    ∃ h ∈ H, v * w₁ * v = w₁ * v * w₁ * h := by
  obtain ⟨hn, ⟨φ⟩⟩ := c.b66.N_quot
  have hHN := c.H_le_NN
  set N := NN z u with hN
  let a : ↥N := ⟨w₁, c.w₁_NN⟩
  let b : ↥N := ⟨v, c.b84.v_N⟩
  have ha : a * a ∈ H.subgroupOf N := by
    show w₁ * w₁ ∈ H
    rw [← pow_two, c.b66.w₁_sq]; exact c.b66.z_mem
  have hb : b * b ∈ H.subgroupOf N := by
    show v * v ∈ H
    exact c.v_sq'
  have hab : (a * b) ^ 3 ∈ H.subgroupOf N := by
    show (w₁ * v) ^ 3 ∈ H
    exact c.cube_mem
  have key := braid_of_cube (H.subgroupOf N) ha hb hab
  have hmem : w₁⁻¹ * v⁻¹ * w₁⁻¹ * v * w₁ * v ∈ H := key
  refine ⟨w₁⁻¹ * v⁻¹ * w₁⁻¹ * v * w₁ * v, hmem, ?_⟩
  group

theorem Cfg2.w₁_comm_X2 (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) :
    ∀ a ∈ XB t X₁, w₁ * a = a * w₁ := fun a ha =>
  c.hc.comm w₁ c.b66.w₁_mem a (c.X2_le_K2 ha)

theorem Cfg4.X6_v (c : Cfg4 G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    cjL v (X6 v t w₁ X₁) = X6 v t w₁ X₁ := by
  obtain ⟨h, hh, hbr⟩ := c.braid
  have hw₂ : cjL w₁ (XB t X₁) = XB t X₁ := by
    apply cjL_eq_of_comm
    intro a ha
    exact c.w₁_comm_X2 a ha
  have hX6 : X6 v t w₁ X₁ = cjL (w₁ * v) (XB t X₁) := by
    show cjL w₁ (cjL v (XB t X₁)) = _
    rw [cjL_cjL]
  rw [hX6, cjL_cjL]
  have e : v * (w₁ * v) = w₁ * v * w₁ * h := by rw [← mul_assoc]; exact hbr
  calc cjL (v * (w₁ * v)) (XB t X₁) = cjL (w₁ * v * w₁ * h) (XB t X₁) := by rw [e]
    _ = cjL (w₁ * v * w₁) (cjL h (XB t X₁)) := (cjL_cjL _ _ _).symm
    _ = cjL (w₁ * v * w₁) (XB t X₁) := by rw [c.hinv_X2 h hh]
    _ = cjL (w₁ * v) (cjL w₁ (XB t X₁)) := (cjL_cjL _ _ _).symm
    _ = cjL (w₁ * v) (XB t X₁) := by rw [hw₂]

end Braid

end CFSG.GH74.GLS.LU.Local.Five
