module

public import CFSG.GH74.GLS.Stage4.RestZFDef
public import CFSG.GH74.GLS.Stage4.RestZFGen
public import CFSG.GH74.GLS.Stage4.RestX2A

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4
  CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage4.Rest

variable {G : Type} [Group G] {D : Ch6Notation G}

theorem Ch6Basics.sl2Pair₂ (h : Ch6Basics D) : SL2Pair D.H D.w₂ D.X₂ D.X₂' := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := h.iso₂
  obtain ⟨n, hn⟩ := h.q₂_pow
  refine ⟨F, hF, hFin, D.p, n, h.prime, by rw [hcard, hn], ?_, ?_, ?_, ?_, D.H ⊓ D.K₂, inf_le_left,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.card_X₂, hcard]
  · rw [h.card_X₂', hcard]
  · exact h.X₂_ne
  · rw [← h.K₂_eq]
    exact ⟨e⟩
  · rw [← h.K₂_eq]
    exact inf_le_right
  · rw [h.card_H_K₂, hcard]
  · rw [← h.K₂_eq]
    exact h.w₂_mem
  · rw [h.w₂_sq]
    exact ⟨h.z_mem_H, h.z_mem_K₂⟩
  · exact h.w₂_swap

theorem Ch6Basics.sl2Phi₂ (h : Ch6Basics D) : SL2Phi D.H D.w₂ D.X₂ D.X₂' :=
  SL2Pair.toSL2Phi (fun x hx y hy => h.H_norm_X₂ x hx y hy) (fun x hx y hy => h.H_norm_X₂' x hx y hy)
    h.sl2Pair₂

theorem Ch6Basics.u_mem_H (h : Ch6Basics D) : D.u ∈ D.H := by
  have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ h.a_normH) D.z).1 h.z_mem_H
  simpa [Ch6Notation.u] using this

theorem Ch6Core.u_not_cent (hc : Ch6Core D) (hs : D.ShapeStd) :
    (∀ x ∈ D.X₁, x ≠ 1 → D.u * x * D.u⁻¹ ≠ x) ∧ (∀ x ∈ D.X₂, x ≠ 1 → D.u * x * D.u⁻¹ ≠ x) := by
  have hd := hc.l92Data hs
  have hcent := hd.cent_inf
  have hX₁P : D.X₁ ≤ D.P := by
    have := hc.root_le_P (i := 1) (by norm_num) (by norm_num)
    rwa [root_p1] at this
  have hX₂P : D.X₂ ≤ D.P := by
    have := hc.root_le_P (i := 4) (by norm_num) (by norm_num)
    rwa [root_p4] at this
  have key : ∀ x ∈ D.P, x ∈ D.root 1 ⊔ D.root 4 → D.u * x * D.u⁻¹ = x → x = 1 := by
    intro x hxP hx1 hxu
    have hxc : x ∈ D.P ⊓ centralizer ({D.u} : Set G) :=
      ⟨hxP, Subgroup.mem_centralizer_iff.2 (fun g hg => by
        rw [Set.mem_singleton_iff] at hg
        rw [hg]
        exact mul_inv_eq_iff_eq_mul.1 hxu)⟩
    rw [hd.cent_u] at hxc
    have : x ∈ (D.root 1 ⊔ D.root 4) ⊓ (D.root 3 ⊔ D.root 6) := ⟨hx1, hxc⟩
    rw [hcent] at this
    exact this
  refine ⟨fun x hx hx1 hxu => hx1 (key x (hX₁P hx) ?_ hxu), fun x hx hx1 hxu => hx1 (key x (hX₂P hx) ?_ hxu)⟩
  · exact Subgroup.mem_sup_left (by rw [root_p1]; exact hx)
  · exact Subgroup.mem_sup_right (by rw [root_p4]; exact hx)


theorem Ch6Core.kit₁ (hc : Ch6Core D) (hs : D.ShapeStd) :
    ∃ W k : G, W ∈ D.K₁ ∧ k ∈ D.K₁ ∧ W * W = D.z ∧ (∃ g ∈ D.H, W = D.w₁ * g) ∧
      D.u * k * D.u⁻¹ = W * k ∧ D.u * W * D.u⁻¹ = D.z * W := by
  have hb := hc.toCh6Basics
  obtain ⟨W, k, hW, hk, h1, h2, h3, h4⟩ := ZF.kit_of_phi (z := D.z) (u := D.u) hb.sl2Phi₁
    (by rw [hb.card_X₁]; exact hb.q₁_odd) hb.H_comm hb.u_mem_H hb.u_mul_u hb.H_norm_X₁
    hb.H_norm_X₁' (hc.u_not_cent hs).1 (by rw [← hb.K₁_eq]; exact hb.sl2Facts₁.inv)
  rw [← hb.K₁_eq] at hW hk
  exact ⟨W, k, hW, hk, h1, h2, h3, h4⟩

theorem Ch6Core.kit₂ (hc : Ch6Core D) (hs : D.ShapeStd) :
    ∃ W k : G, W ∈ D.K₂ ∧ k ∈ D.K₂ ∧ W * W = D.z ∧ (∃ g ∈ D.H, W = D.w₂ * g) ∧
      D.u * k * D.u⁻¹ = W * k ∧ D.u * W * D.u⁻¹ = D.z * W := by
  have hb := hc.toCh6Basics
  obtain ⟨W, k, hW, hk, h1, h2, h3, h4⟩ := ZF.kit_of_phi (z := D.z) (u := D.u) hb.sl2Phi₂
    (by rw [hb.card_X₂]; exact hb.q₂_odd) hb.H_comm hb.u_mem_H hb.u_mul_u hb.H_norm_X₂
    hb.H_norm_X₂' (hc.u_not_cent hs).2 (by rw [← hb.K₂_eq]; exact hb.sl2Facts₂.inv)
  rw [← hb.K₂_eq] at hW hk
  exact ⟨W, k, hW, hk, h1, h2, h3, h4⟩


theorem Ch6Core.zfusion_of_not_mem (hc : Ch6Core D) (hs : D.ShapeStd) (hH : D.HIdx)
    (hu : D.u ∉ D.K₁ ⊔ D.K₂) : D.ZFusion := by
  have hb := hc.toCh6Basics
  have huH : D.u ∈ D.H := hb.u_mem_H
  have hzH : D.z ∈ D.H := hb.z_mem_H
  have hzz : D.z * D.z = 1 := hb.z_mul_z
  have hz1 : D.z ≠ 1 := hb.z_ne_one
  have huu : D.u * D.u = 1 := hb.u_mul_u
  have hzu : D.z * D.u = D.u * D.z := hb.H_comm _ hzH _ huH
  have hui : D.u⁻¹ = D.u := inv_eq_of_mul_eq_one_right huu
  have hzi : D.z⁻¹ = D.z := inv_eq_of_mul_eq_one_right hzz
  have hu_def : D.u = D.a⁻¹ * D.z * D.a := rfl
  have hau : D.a * D.u * D.a⁻¹ = D.z := by rw [hu_def]; group
  have hza : D.a * D.z * D.a⁻¹ = D.z * D.u := by
    have h1 : D.a⁻¹ * (D.z * D.u) * D.a = D.z := by
      calc D.a⁻¹ * (D.z * D.u) * D.a = (D.a⁻¹ * D.z * D.a) * (D.a⁻¹ * D.u * D.a) := by group
        _ = D.u * (D.z * D.u) := by rw [hs.a_cycle, ← hu_def]
        _ = D.z := by
          calc D.u * (D.z * D.u) = (D.u * D.z) * D.u := by group
            _ = (D.z * D.u) * D.u := by rw [hzu]
            _ = D.z * (D.u * D.u) := by group
            _ = D.z := by rw [huu, mul_one]
    calc D.a * D.z * D.a⁻¹ = D.a * (D.a⁻¹ * (D.z * D.u) * D.a) * D.a⁻¹ := by rw [h1]
      _ = D.z * D.u := by group
  obtain ⟨W₁, k₁, hW₁K, hk₁K, hW₁sq, ⟨g₁, hg₁, hW₁g⟩, hk₁u, hW₁u⟩ := hc.kit₁ hs
  obtain ⟨W₂, k₂, hW₂K, hk₂K, hW₂sq, ⟨g₂, hg₂, hW₂g⟩, hk₂u, hW₂u⟩ := hc.kit₂ hs
  have c12 := hb.K_comm
  have hW₂W₁ : W₂ * W₁ = W₁ * W₂ := (c12 _ hW₁K _ hW₂K).symm
  have hk₁W₂ : k₁ * W₂ = W₂ * k₁ := c12 _ hk₁K _ hW₂K
  have hzW₁ : D.z * W₁ = W₁ * D.z := by
    calc D.z * W₁ = (W₁ * W₁) * W₁ := by rw [hW₁sq]
      _ = W₁ * (W₁ * W₁) := by group
      _ = W₁ * D.z := by rw [hW₁sq]
  have hW₁W : W₁ * (W₁ * W₂) = (W₁ * W₂) * W₁ := by
    calc W₁ * (W₁ * W₂) = W₁ * (W₂ * W₁) := by rw [hW₂W₁]
      _ = (W₁ * W₂) * W₁ := by group
  have hkW : D.u * (k₁ * k₂) * D.u⁻¹ = (W₁ * W₂) * (k₁ * k₂) := by
    calc D.u * (k₁ * k₂) * D.u⁻¹ = (D.u * k₁ * D.u⁻¹) * (D.u * k₂ * D.u⁻¹) := by group
      _ = (W₁ * k₁) * (W₂ * k₂) := by rw [hk₁u, hk₂u]
      _ = W₁ * (k₁ * W₂) * k₂ := by group
      _ = W₁ * (W₂ * k₁) * k₂ := by rw [hk₁W₂]
      _ = (W₁ * W₂) * (k₁ * k₂) := by group
  have huW : D.u * (W₁ * W₂) * D.u⁻¹ = W₁ * W₂ := by
    calc D.u * (W₁ * W₂) * D.u⁻¹ = (D.u * W₁ * D.u⁻¹) * (D.u * W₂ * D.u⁻¹) := by group
      _ = (D.z * W₁) * (D.z * W₂) := by rw [hW₁u, hW₂u]
      _ = D.z * (W₁ * D.z) * W₂ := by group
      _ = D.z * (D.z * W₁) * W₂ := by rw [hzW₁]
      _ = (D.z * D.z) * (W₁ * W₂) := by group
      _ = W₁ * W₂ := by rw [hzz, one_mul]
  have hWu : D.u * (W₁ * W₂) = (W₁ * W₂) * D.u := mul_inv_eq_iff_eq_mul.1 huW
  have hW₁u' : W₁ * D.u = D.z * D.u * W₁ := by
    have h1 : D.u * W₁ * D.u = D.z * W₁ := by have := hW₁u; rwa [hui] at this
    calc W₁ * D.u = D.u * (D.u * W₁ * D.u) := by
          calc W₁ * D.u = (D.u * D.u) * W₁ * D.u := by rw [huu, one_mul]
            _ = D.u * (D.u * W₁ * D.u) := by group
      _ = D.u * (D.z * W₁) := by rw [h1]
      _ = (D.u * D.z) * W₁ := by group
      _ = D.z * D.u * W₁ := by rw [← hzu]
  have hkuk : (k₁ * k₂) * D.u * (k₁ * k₂)⁻¹ = D.u * (W₁ * W₂) := by
    have h1 : D.u * (k₁ * k₂) * D.u = (W₁ * W₂) * (k₁ * k₂) := by have := hkW; rwa [hui] at this
    calc (k₁ * k₂) * D.u * (k₁ * k₂)⁻¹ = D.u * (D.u * (k₁ * k₂) * D.u) * (k₁ * k₂)⁻¹ := by
          calc (k₁ * k₂) * D.u * (k₁ * k₂)⁻¹ = (D.u * D.u) * (k₁ * k₂) * D.u * (k₁ * k₂)⁻¹ := by
                rw [huu, one_mul]
            _ = D.u * (D.u * (k₁ * k₂) * D.u) * (k₁ * k₂)⁻¹ := by group
      _ = D.u * ((W₁ * W₂) * (k₁ * k₂)) * (k₁ * k₂)⁻¹ := by rw [h1]
      _ = D.u * (W₁ * W₂) := by group
  have haG : D.a ∈ (D.H ⊔ D.P) ⊔ D.N := Subgroup.mem_sup_right hb.a_mem_N
  have hkG : k₁ * k₂ ∈ (D.H ⊔ D.P) ⊔ D.N := mul_mem (hc.K₁_le_G₀ hk₁K) (hc.K₂_le_G₀ hk₂K)
  have hW₁G : W₁ ∈ (D.H ⊔ D.P) ⊔ D.N := hc.K₁_le_G₀ hW₁K
  have hgG₁ : D.a * (k₁ * k₂) * D.a⁻¹ ∈ (D.H ⊔ D.P) ⊔ D.N := mul_mem (mul_mem haG hkG) (inv_mem haG)
  have hgG₂ : D.a * (W₁ * (k₁ * k₂)) * D.a⁻¹ ∈ (D.H ⊔ D.P) ⊔ D.N :=
    mul_mem (mul_mem haG (mul_mem hW₁G hkG)) (inv_mem haG)
  have hg₁z : (D.a * (k₁ * k₂) * D.a⁻¹) * D.z * (D.a * (k₁ * k₂) * D.a⁻¹)⁻¹ =
      D.a * (D.u * (W₁ * W₂)) * D.a⁻¹ := by
    calc (D.a * (k₁ * k₂) * D.a⁻¹) * D.z * (D.a * (k₁ * k₂) * D.a⁻¹)⁻¹
        = D.a * ((k₁ * k₂) * (D.a⁻¹ * D.z * D.a) * (k₁ * k₂)⁻¹) * D.a⁻¹ := by group
      _ = D.a * ((k₁ * k₂) * D.u * (k₁ * k₂)⁻¹) * D.a⁻¹ := by rw [← hu_def]
      _ = D.a * (D.u * (W₁ * W₂)) * D.a⁻¹ := by rw [hkuk]
  have hg₂z : (D.a * (W₁ * (k₁ * k₂)) * D.a⁻¹) * D.z * (D.a * (W₁ * (k₁ * k₂)) * D.a⁻¹)⁻¹ =
      D.a * (D.z * D.u * (W₁ * W₂)) * D.a⁻¹ := by
    calc (D.a * (W₁ * (k₁ * k₂)) * D.a⁻¹) * D.z * (D.a * (W₁ * (k₁ * k₂)) * D.a⁻¹)⁻¹
        = D.a * (W₁ * ((k₁ * k₂) * (D.a⁻¹ * D.z * D.a) * (k₁ * k₂)⁻¹) * W₁⁻¹) * D.a⁻¹ := by group
      _ = D.a * (W₁ * ((k₁ * k₂) * D.u * (k₁ * k₂)⁻¹) * W₁⁻¹) * D.a⁻¹ := by rw [← hu_def]
      _ = D.a * (W₁ * (D.u * (W₁ * W₂)) * W₁⁻¹) * D.a⁻¹ := by rw [hkuk]
      _ = D.a * (D.z * D.u * (W₁ * W₂)) * D.a⁻¹ := by
          congr 2
          calc W₁ * (D.u * (W₁ * W₂)) * W₁⁻¹ = (W₁ * D.u) * (W₁ * W₂) * W₁⁻¹ := by group
            _ = (D.z * D.u * W₁) * (W₁ * W₂) * W₁⁻¹ := by rw [hW₁u']
            _ = D.z * D.u * ((W₁ * (W₁ * W₂)) * W₁⁻¹) := by group
            _ = D.z * D.u * (((W₁ * W₂) * W₁) * W₁⁻¹) := by rw [hW₁W]
            _ = D.z * D.u * (W₁ * W₂) := by group
  obtain ⟨h, hhH, hWh⟩ := ZF.aW_mem (H := D.H) (a := D.a) (w₁ := D.w₁) (w₂ := D.w₂) (W₁ := W₁)
    (W₂ := W₂) hb.a_normH hb.w₁_normH hb.w₂_normH hb.w₁_a hb.w₂_a ⟨g₁, hg₁, hW₁g⟩ ⟨g₂, hg₂, hW₂g⟩
  have hW₁K₂ : W₁ ∉ D.K₂ := by
    intro hmem
    have hcent : ∀ k ∈ D.K₁, W₁ * k = k * W₁ := fun k hk => (hb.K_comm k hk W₁ hmem).symm
    rcases hb.sl2Facts₁.center W₁ hW₁K hcent with h1 | h1
    · apply hz1
      rw [← hW₁sq, h1, mul_one]
    · apply hz1
      rw [h1, hzz] at hW₁sq
      exact hW₁sq.symm
  have hW1 : W₁ * W₂ ≠ 1 := by
    intro h1
    apply hW₁K₂
    have : W₁ = W₂⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact D.K₂.inv_mem hW₂K
  have hWz : W₁ * W₂ ≠ D.z := by
    intro h1
    apply hW₁K₂
    have : W₁ = D.z * W₂⁻¹ := eq_mul_inv_of_mul_eq h1
    rw [this]
    exact D.K₂.mul_mem hb.z_mem_K₂ (D.K₂.inv_mem hW₂K)
  have hordz : ∀ g v : G, g * D.z * g⁻¹ = v → orderOf v = 2 := by
    intro g v hv
    have hsc : SemiconjBy g D.z v := by
      rw [SemiconjBy, ← hv]
      group
    exact (SemiconjBy.orderOf_eq g hsc).symm.trans hb.z_ord
  have hz₁K : D.z ∈ D.K₁ ⊔ D.K₂ := Subgroup.mem_sup_left hb.z_mem_K₁
  have hWK : W₁ * W₂ ∈ D.K₁ ⊔ D.K₂ :=
    mul_mem (Subgroup.mem_sup_left hW₁K) (Subgroup.mem_sup_right hW₂K)
  have hLK : (D.H ⊓ D.K₁) ⊔ (D.H ⊓ D.K₂) ≤ D.K₁ ⊔ D.K₂ := sup_le_sup inf_le_right inf_le_right
  have huL : D.u ∉ (D.H ⊓ D.K₁) ⊔ (D.H ⊓ D.K₂) := fun h => hu (hLK h)
  have hdich : h ∈ (D.H ⊓ D.K₁) ⊔ (D.H ⊓ D.K₂) ∨ D.u * h ∈ (D.H ⊓ D.K₁) ⊔ (D.H ⊓ D.K₂) := by
    have hidx : (((D.H ⊓ D.K₁) ⊔ (D.H ⊓ D.K₂)).subgroupOf D.H).index = 2 := hH
    have hmul := Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨D.u, huH⟩ : D.H))
      (b := (⟨h, hhH⟩ : D.H))
    by_cases hb' : h ∈ (D.H ⊓ D.K₁) ⊔ (D.H ⊓ D.K₂)
    · exact Or.inl hb'
    · refine Or.inr ?_
      have hbn : (⟨h, hhH⟩ : D.H) ∉ ((D.H ⊓ D.K₁) ⊔ (D.H ⊓ D.K₂)).subgroupOf D.H := hb'
      have han : (⟨D.u, huH⟩ : D.H) ∉ ((D.H ⊓ D.K₁) ⊔ (D.H ⊓ D.K₂)).subgroupOf D.H := huL
      have : (⟨D.u, huH⟩ : D.H) * ⟨h, hhH⟩ ∈ ((D.H ⊓ D.K₁) ⊔ (D.H ⊓ D.K₂)).subgroupOf D.H :=
        hmul.2 (iff_of_false han hbn)
      exact this
  have hc1 : D.a * (D.u * (W₁ * W₂)) * D.a⁻¹ = D.z * ((W₁ * W₂) * h) := by
    calc D.a * (D.u * (W₁ * W₂)) * D.a⁻¹
        = (D.a * D.u * D.a⁻¹) * (D.a * (W₁ * W₂) * D.a⁻¹) := by group
      _ = D.z * ((W₁ * W₂) * h) := by rw [hau, hWh]
  have hc2 : D.a * (D.z * D.u * (W₁ * W₂)) * D.a⁻¹ = (W₁ * W₂) * (D.u * h) := by
    calc D.a * (D.z * D.u * (W₁ * W₂)) * D.a⁻¹
        = (D.a * D.z * D.a⁻¹) * (D.a * D.u * D.a⁻¹) * (D.a * (W₁ * W₂) * D.a⁻¹) := by group
      _ = (D.z * D.u) * D.z * ((W₁ * W₂) * h) := by rw [hza, hau, hWh]
      _ = D.u * ((W₁ * W₂) * h) := by
          have : (D.z * D.u) * D.z = D.u := by
            calc (D.z * D.u) * D.z = D.z * (D.u * D.z) := by group
              _ = D.z * (D.z * D.u) := by rw [hzu]
              _ = (D.z * D.z) * D.u := by group
              _ = D.u := by rw [hzz, one_mul]
          rw [this]
      _ = (D.u * (W₁ * W₂)) * h := by group
      _ = ((W₁ * W₂) * D.u) * h := by rw [hWu]
      _ = (W₁ * W₂) * (D.u * h) := by group
  rcases hdich with hL | hL
  ·
    refine ⟨D.z * ((W₁ * W₂) * h), ?_, hordz _ _ (hg₁z.trans hc1), ?_, D.a * (k₁ * k₂) * D.a⁻¹, hgG₁,
      hg₁z.trans hc1⟩
    · exact mul_mem hz₁K (mul_mem hWK (hLK hL))
    · intro hv
      apply hW1
      have h1 : D.a * (D.u * (W₁ * W₂)) * D.a⁻¹ = D.a * D.u * D.a⁻¹ := hc1.trans (hv.trans hau.symm)
      have h2 : D.a * (D.u * (W₁ * W₂)) = D.a * D.u := mul_right_cancel h1
      have h3 : D.u * (W₁ * W₂) = D.u := mul_left_cancel h2
      have h4 : D.u * (W₁ * W₂) = D.u * 1 := by rw [h3, mul_one]
      exact mul_left_cancel h4
  ·
    refine ⟨(W₁ * W₂) * (D.u * h), mul_mem hWK (hLK hL), hordz _ _ (hg₂z.trans hc2), ?_,
      D.a * (W₁ * (k₁ * k₂)) * D.a⁻¹, hgG₂, hg₂z.trans hc2⟩
    intro hv
    apply hWz
    have h1 : D.a * (D.z * D.u * (W₁ * W₂)) * D.a⁻¹ = D.a * D.u * D.a⁻¹ := hc2.trans (hv.trans hau.symm)
    have h2 : D.a * (D.z * D.u * (W₁ * W₂)) = D.a * D.u := mul_right_cancel h1
    have h3 : D.z * D.u * (W₁ * W₂) = D.u := mul_left_cancel h2
    have h4 : D.u * (D.z * (W₁ * W₂)) = D.u * 1 := by
      calc D.u * (D.z * (W₁ * W₂)) = (D.u * D.z) * (W₁ * W₂) := by group
        _ = (D.z * D.u) * (W₁ * W₂) := by rw [hzu]
        _ = D.u := h3
        _ = D.u * 1 := by rw [mul_one]
    have h5 : D.z * (W₁ * W₂) = 1 := mul_left_cancel h4
    have h6 : W₁ * W₂ = D.z⁻¹ := eq_inv_of_mul_eq_one_right h5
    rw [h6, hzi]


theorem Ch6Core.zfusion_of_shapeStd (hc : Ch6Core D) (hs : D.ShapeStd) (hH : D.HIdx) : D.ZFusion := by
  by_cases hu : D.u ∈ D.K₁ ⊔ D.K₂
  · exact hc.zfusion_of_u_mem (hc.toCh6Basics.u_ne_z hs.a_cycle) hu
  · exact hc.zfusion_of_not_mem hs hH hu

theorem ch6ZFusionAll_proved : Ch6ZFusionAll := fun _ _ _ hc hs hH => hc.zfusion_of_shapeStd hs hH

end CFSG.GH74.GLS.Stage4.Rest
