module

public import CFSG.GH74.GLS.LU.Local.FiveL84j
public import CFSG.GH74.GLS.LU.Local.FiveL84e
public import CFSG.GH74.GLS.LU.Local.FiveL84a

public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

section Asm

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ v : G} {X₁ Y : Subgroup G}

theorem leaf84''_aux (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y)
    (bw : Five84w z t u H X₁ Y v) : v ^ 2 ∈ H := by
  by_contra hv2
  have ht2 : t * t = 1 := c.t_sq
  have hHt : ∀ l ∈ zpowers t, ∀ e ∈ H, l * e * l⁻¹ ∈ H := by
    intro l hl e he
    have : t ∈ normalizer (H : Set G) := by
      apply CFSG.Walter.J1.mem_normalizer_of_conj_mem
      intro x hx
      have h1 : t * x * t⁻¹ ∈ cjL t H := mem_cjL_self hx
      rw [c.b66.t_normH] at h1
      exact h1
    have hle : zpowers t ≤ normalizer (H : Set G) := (Subgroup.zpowers_le).2 this
    have hl' := hle hl
    rw [Subgroup.mem_normalizer_iff] at hl'
    exact (hl' e).1 he
  obtain ⟨h0, hh0, l, hl, hvl⟩ := mem_sup_of_normalizes hHt bw.v_sq
  rcases mem_zpowers_of_sq_eq_one ht2 hl with hl1 | hlt
  · exact hv2 (by rw [hvl, hl1, mul_one]; exact hh0)
  rw [hlt] at hvl
  obtain ⟨a, ha, ha1⟩ : ∃ a ∈ X₁, a ≠ 1 := by
    have hne : X₁ ≠ ⊥ := by
      intro hb
      have := c.card_X1
      rw [hb, Subgroup.card_bot] at this
      omega
    obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    exact ⟨a, ha, fun h => ha1 (Subtype.ext h)⟩
  have ha5 : orderOf a = 5 := orderOf_eq_five_of_card c.card_X1 ha ha1
  have hH : ∀ h ∈ H, ∃ k : ℕ, h * a * h⁻¹ = a ^ k :=
    fun h hh => exists_exp_of_hinv c.card_X1 ha ha1 c.hinv_X1 hh
  have hvH : cjL v H = H := c.cjL_H bw.v_N
  have hwH : cjL w₁ H = H := c.cjL_H c.w₁_NN
  obtain ⟨e⟩ := c.b66.H_iso
  let _ : CommGroup ↥H := { (inferInstance : Group ↥H) with
    mul_comm := fun a b => Subtype.ext (c.H_comm a.1 a.2 b.1 b.2) }
  let σ : ↥H ≃* ↥H := conjEquiv H w₁ hwH
  let τ : ↥H ≃* ↥H := conjEquiv H v hvH
  let χ : ↥H →* (ZMod 5)ˣ := chiHom H ha5 hH
  have hσ : ∀ h : ↥H, σ (σ h) = h := by
    intro h
    apply Subtype.ext
    show w₁ * (w₁ * (h : G) * w₁⁻¹) * w₁⁻¹ = h
    have hz : z * (h : G) = (h : G) * z := c.H_comm z c.b66.z_mem h h.2
    have hw1sq : w₁ * w₁ = z := by rw [← pow_two]; exact c.b66.w₁_sq
    calc w₁ * (w₁ * (h : G) * w₁⁻¹) * w₁⁻¹ = (w₁ * w₁) * (h : G) * (w₁ * w₁)⁻¹ := by group
      _ = z * (h : G) * z⁻¹ := by rw [hw1sq]
      _ = h := by rw [hz]; group
  have hc3 : (w₁ * v) ^ 3 = 1 := c.cube_aux bw.v_N bw.v_z bw.v_zu
  have h3 : ∀ h : ↥H, σ (τ (σ (τ (σ (τ h))))) = h := by
    intro h
    apply Subtype.ext
    show w₁ * (v * (w₁ * (v * (w₁ * (v * (h : G) * v⁻¹) * w₁⁻¹) * v⁻¹) * w₁⁻¹) * v⁻¹) * w₁⁻¹ = h
    have : w₁ * (v * (w₁ * (v * (w₁ * (v * (h : G) * v⁻¹) * w₁⁻¹) * v⁻¹) * w₁⁻¹) * v⁻¹) * w₁⁻¹
        = (w₁ * v) ^ 3 * (h : G) * ((w₁ * v) ^ 3)⁻¹ := by
      rw [show (w₁ * v) ^ 3 = (w₁ * v) * (w₁ * v) * (w₁ * v) by rw [pow_succ, pow_succ, pow_one]]
      group
    rw [this, hc3]; group
  have hK : ∀ h : ↥H, χ (τ.symm h) = χ h * χ (τ.symm (σ.symm h)) := by
    intro h
    apply Units.ext
    have hhm : (h : G) ∈ H := h.2
    have hwm : w₁⁻¹ * (h : G) * w₁ ∈ H := by
      have : (h : G) ∈ cjL w₁ H := by rw [hwH]; exact hhm
      exact mem_cjL.mp this
    show wt a (v⁻¹ * (h : G) * v) = wt a h * wt a (v⁻¹ * (w₁⁻¹ * (h : G) * w₁) * v)
    have hK0 := c.K_rel bw.v_N bw.v_X ha ha1 h hhm
    have h3a : wt (v * a * v⁻¹) h = wt a (v⁻¹ * h * v) := wt_conj_H ha5 hvH hH hhm
    have hord3 : orderOf (v * a * v⁻¹) = 5 := orderOf_conj_eq ha5
    have hexp3 := exists_exp_conj hvH hH
    have h5a : wt (w₁ * (v * a * v⁻¹) * w₁⁻¹) h = wt (v * a * v⁻¹) (w₁⁻¹ * h * w₁) :=
      wt_conj_H hord3 hwH hexp3 hhm
    have h5b : wt (v * a * v⁻¹) (w₁⁻¹ * h * w₁) = wt a (v⁻¹ * (w₁⁻¹ * h * w₁) * v) :=
      wt_conj_H ha5 hvH hH hwm
    rw [← h3a, hK0, h5a, h5b]
  have key := weights_core e σ τ χ hσ h3 hK
  obtain ⟨h1, hh1, hne⟩ := c.exists_wt_ne ha ha1
  have e1 : wt a (v⁻¹ * (v⁻¹ * h1 * v) * v) = wt a h1 := congrArg Units.val (key ⟨h1, hh1⟩)
  have hvv : v * v = h0 * t := by rw [← pow_two]; exact hvl
  have hcomm : h0⁻¹ * h1 * h0 = h1 := by
    have := c.H_comm h1 hh1 h0 hh0
    calc h0⁻¹ * h1 * h0 = h0⁻¹ * (h1 * h0) := by group
      _ = h0⁻¹ * (h0 * h1) := by rw [this]
      _ = h1 := by group
  have e2 : v⁻¹ * (v⁻¹ * h1 * v) * v = t⁻¹ * h1 * t := by
    calc v⁻¹ * (v⁻¹ * h1 * v) * v = (v * v)⁻¹ * h1 * (v * v) := by group
      _ = (h0 * t)⁻¹ * h1 * (h0 * t) := by rw [hvv]
      _ = t⁻¹ * (h0⁻¹ * h1 * h0) * t := by group
      _ = t⁻¹ * h1 * t := by rw [hcomm]
  rw [e2] at e1
  have e3 : wt (t * a * t⁻¹) h1 = wt a (t⁻¹ * h1 * t) := wt_conj_H ha5 c.b66.t_normH hH hh1
  exact hne (by rw [e3, e1])

end Asm

theorem leaf84'' : Leaf84'' := by
  intro G _ _ p f z S K₁ K₂ t u ctx H w₁ b66 X₁ b82 Y b83 v bw
  exact leaf84''_aux ⟨⟨ctx, b66, b82⟩, b83⟩ bw

end CFSG.GH74.GLS.LU.Local.Five
