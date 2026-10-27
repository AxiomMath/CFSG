module

public import CFSG.GH74.GLS.Stage4.T2FourEx

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG.GH74.GLS.Stage4.Hex

section U

variable {G : Type} [Group G] {z u : G}

theorem t2U_comm_all (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z) {y : G}
    (hyz : y * z = z * y) (hyu : y * u = u * y) : ∀ v ∈ t2U z u, y * v = v * y := by
  intro v hv
  rcases (t2U_mem hz2 hu2 hzu).1 hv with rfl | rfl | rfl | rfl
  · simp
  · exact hyz
  · exact hyu
  · calc y * (z * u) = (y * z) * u := by group
      _ = z * (y * u) := by rw [hyz]; group
      _ = z * (u * y) := by rw [hyu]
      _ = (z * u) * y := by group

theorem t2U_cent_conj {g y : G}
    (hg : g ∈ normalizer (t2U z u : Set G)) (hy : ∀ v ∈ t2U z u, y * v = v * y) :
    ∀ v ∈ t2U z u, (g⁻¹ * y * g) * v = v * (g⁻¹ * y * g) := by
  intro v hv
  have hv' : g * v * g⁻¹ ∈ t2U z u := (Subgroup.mem_normalizer_iff.1 hg v).1 hv
  have h1 := hy _ hv'
  calc (g⁻¹ * y * g) * v = g⁻¹ * (y * (g * v * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * v * g⁻¹) * y) * g := by rw [h1]
    _ = v * (g⁻¹ * y * g) := by group

theorem t2U_le_of_mem {H : Subgroup G} (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z)
    (hz : z ∈ H) (hu : u ∈ H) : t2U z u ≤ H := by
  intro x hx
  rcases (t2U_mem hz2 hu2 hzu).1 hx with rfl | rfl | rfl | rfl
  · exact H.one_mem
  · exact hz
  · exact hu
  · exact H.mul_mem hz hu

end U

section Exact

variable {G : Type} [Group G] [Finite G] {z u : G} {K₁ K₂ H : Subgroup G} {w₁ w₂ : G}

theorem T2Four.exists_exact (h : T2Four z u K₁ K₂ H w₁ w₂) (hr : CFSG.pRank 2 G = 3)
    {F₁ : Type} [Field F₁] [Finite F₁] (hodd : Odd (Nat.card F₁)) (h3 : 3 < Nat.card F₁)
    (e₁ : ↥K₁ ≃* SL2 F₁) (hK₁inv : ∀ x ∈ K₁, x * x = 1 → x = 1 ∨ x = z)
    (hnc : ∀ y : G, y * y = 1 → y * z = z * y → y ≠ 1 → y ≠ z → ∃ x ∈ K₁, y * x * y⁻¹ ≠ x)
    (hconj : ∃ g : G, g⁻¹ * z * g = u) (hH3 : ¬ 3 ∣ Nat.card H) :
    ∃ a : G, a ^ 3 = 1 ∧ a ∈ normalizer (H : Set G) ∧ a⁻¹ * z * a = u ∧ a⁻¹ * u * a = z * u ∧
      ∃ x ∈ H, w₁ * a * w₁⁻¹ = a⁻¹ * x := by
  obtain ⟨a₀, d1, d2, haN, ha3, ⟨x₀, hx₀, hw₁a⟩, -⟩ :=
    h.exists_a hr hodd h3 e₁ hK₁inv hnc hconj
  obtain ⟨k, hNk, hk3⟩ : ∃ k : ℕ, Nat.card H ∣ k ∧ k % 3 = 1 := by
    have : Nat.card H % 3 = 1 ∨ Nat.card H % 3 = 2 := by omega
    rcases this with h1 | h2
    · exact ⟨Nat.card H, dvd_rfl, h1⟩
    · exact ⟨2 * Nat.card H, dvd_mul_left _ 2, by omega⟩
  have hk : k = 3 * (k / 3) + 1 := by omega
  set y : G := (a₀ ^ 3) ^ (k / 3) with hy
  have hyH : y ∈ H := H.pow_mem ha3 _
  have hay : a₀ ^ k = a₀ * y := by
    rw [hy, ← pow_mul, ← pow_succ']
    congr 1
  refine ⟨a₀ ^ k, ?_, ?_, ?_, ?_, ?_⟩
  ·
    obtain ⟨m, hm⟩ := hNk
    have h1 : (a₀ ^ 3) ^ Nat.card H = 1 :=
      congrArg Subtype.val (pow_card_eq_one' (G := ↥H) (x := (⟨a₀ ^ 3, ha3⟩ : ↥H)))
    calc (a₀ ^ k) ^ 3 = (a₀ ^ 3) ^ k := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = ((a₀ ^ 3) ^ Nat.card H) ^ m := by rw [← pow_mul (a₀ ^ 3) (Nat.card H) m, ← hm]
      _ = 1 := by rw [h1, one_pow]
  · rw [hay]
    exact Subgroup.mul_mem _ haN (Subgroup.le_normalizer hyH)
  · rw [hay]
    calc (a₀ * y)⁻¹ * z * (a₀ * y) = y⁻¹ * (a₀⁻¹ * z * a₀) * y := by group
      _ = y⁻¹ * u * y := by rw [d1]
      _ = y⁻¹ * (u * y) := by group
      _ = y⁻¹ * (y * u) := by rw [h.H_comm u h.u_mem_H y hyH]
      _ = u := by group
  · rw [hay]
    have hzuH : z * u ∈ H := H.mul_mem h.z_mem_H h.u_mem_H
    calc (a₀ * y)⁻¹ * u * (a₀ * y) = y⁻¹ * (a₀⁻¹ * u * a₀) * y := by group
      _ = y⁻¹ * (z * u) * y := by rw [d2]
      _ = y⁻¹ * ((z * u) * y) := by group
      _ = y⁻¹ * (y * (z * u)) := by rw [h.H_comm (z * u) hzuH y hyH]
      _ = z * u := by group
  · rw [hay]
    have hy₁ : w₁ * y * w₁⁻¹ ∈ H := h.w₁_normH y hyH
    have ha₀y : a₀ * y * a₀⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 haN y).1 hyH
    refine ⟨(a₀ * y * a₀⁻¹) * x₀ * (w₁ * y * w₁⁻¹),
      H.mul_mem (H.mul_mem ha₀y hx₀) hy₁, ?_⟩
    calc w₁ * (a₀ * y) * w₁⁻¹ = (w₁ * a₀ * w₁⁻¹) * (w₁ * y * w₁⁻¹) := by group
      _ = (a₀⁻¹ * x₀) * (w₁ * y * w₁⁻¹) := by rw [hw₁a]
      _ = (a₀ * y)⁻¹ * ((a₀ * y * a₀⁻¹) * x₀ * (w₁ * y * w₁⁻¹)) := by group

end Exact

section Fixed

variable {G : Type} [Group G] [Finite G] {z u : G} {K₁ K₂ H : Subgroup G} {w₁ w₂ : G}

theorem T2Four.exists_fixed (h : T2Four z u K₁ K₂ H w₁ w₂) (hr : CFSG.pRank 2 G = 3) {a : G}
    (ha3 : a ^ 3 = 1) (haU : a ∈ normalizer (t2U z u : Set G)) (hH3 : ¬ 3 ∣ Nat.card H) :
    ∃ x ∈ H, a * (x * (w₁ * w₂)) * a⁻¹ = x * (w₁ * w₂) := by
  set w₀ : G := w₁ * w₂ with hw₀
  let X : Set G := {y | ∃ x ∈ H, y = x * w₀}
  have hcent : ∀ x ∈ H, ∀ v ∈ t2U z u, (x * w₀) * v = v * (x * w₀) := by
    intro x hx
    have hxz : x * z = z * x := h.H_comm x hx z h.z_mem_H
    have hxu : x * u = u * x := h.H_comm x hx u h.u_mem_H
    have hyz : (x * w₀) * z = z * (x * w₀) := by
      calc (x * w₀) * z = x * (w₀ * z) := by group
        _ = x * (z * w₀) := by rw [h.w₀_z]
        _ = (x * z) * w₀ := by group
        _ = (z * x) * w₀ := by rw [hxz]
        _ = z * (x * w₀) := by group
    have hyu : (x * w₀) * u = u * (x * w₀) := by
      calc (x * w₀) * u = x * (w₀ * u) := by group
        _ = x * (u * w₀) := by rw [h.w₀_u]
        _ = (x * u) * w₀ := by group
        _ = (u * x) * w₀ := by rw [hxu]
        _ = u * (x * w₀) := by group
    exact t2U_comm_all h.zz h.uu h.zu_comm hyz hyu
  have hXconj : ∀ g ∈ normalizer (t2U z u : Set G), ∀ y ∈ X, g * y * g⁻¹ ∈ X := by
    intro g hg y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hg' : g⁻¹ ∈ normalizer (t2U z u : Set G) := Subgroup.inv_mem _ hg
    have hc := t2U_cent_conj hg' (hcent x hx)
    have hz' := hc z (Subgroup.subset_closure (by simp))
    have hu' := hc u (Subgroup.subset_closure (by simp))
    simp only [inv_inv] at hz' hu'
    have hy2 : (g * (x * w₀) * g⁻¹) * (g * (x * w₀) * g⁻¹) = 1 := by
      calc (g * (x * w₀) * g⁻¹) * (g * (x * w₀) * g⁻¹)
          = g * ((x * w₀) * (x * w₀)) * g⁻¹ := by group
        _ = 1 := by rw [h.Hw_sq hx]; group
    have hyU : ¬ (g * (x * w₀) * g⁻¹ = 1 ∨ g * (x * w₀) * g⁻¹ = z ∨ g * (x * w₀) * g⁻¹ = u ∨
        g * (x * w₀) * g⁻¹ = z * u) := by
      intro hU
      have hU' : g * (x * w₀) * g⁻¹ ∈ t2U z u := (t2U_mem h.zz h.uu h.zu_comm).2 hU
      have hback : x * w₀ ∈ t2U z u := by
        have := (Subgroup.mem_normalizer_iff.1 hg' _).1 hU'
        simpa [mul_assoc] using this
      have hbackH : x * w₀ ∈ H := t2U_le_of_mem h.zz h.uu h.zu_comm h.z_mem_H h.u_mem_H hback
      apply h.w₀_not_mem
      show w₀ ∈ H
      have : w₀ = x⁻¹ * (x * w₀) := by group
      rw [this]
      exact H.mul_mem (H.inv_mem hx) hbackH
    obtain ⟨x', hx', hx'e⟩ := h.inv_mem_Hw hr hz' hu' hy2 hyU
    exact ⟨x', hx', hx'e⟩
  have hcard : Nat.card H = Nat.card X := by
    refine Nat.card_congr (Equiv.ofBijective (fun x : ↥H => (⟨x * w₀, x, x.2, rfl⟩ : X)) ⟨?_, ?_⟩)
    · intro x x' hxx
      have := congrArg Subtype.val hxx
      exact Subtype.ext (mul_right_cancel this)
    · rintro ⟨y, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨y, ⟨x, hx, rfl⟩, hfix⟩ := t2_exists_fixed_conj ha3 X (fun y hy => hXconj a haU y hy)
    (fun y hy => by simpa using hXconj a⁻¹ (Subgroup.inv_mem _ haU) y hy)
    (by rw [← hcard]; exact hH3)
  exact ⟨x, hx, hfix⟩

end Fixed

section Parity

theorem t2_zmod2_aux (p0 px p1 p2 d : ZMod 2) (h1 : p0 = px) (h2 : p0 = p1 + d)
    (h3 : p0 = p2 + d) (h4 : px + p1 + p2 = 0) : p0 = 0 := by
  revert p0 px p1 p2 d
  decide

variable {G : Type} [Group G] [Finite G] {z u : G} {K₁ K₂ H : Subgroup G} {w₁ w₂ : G}

omit [Finite G] in
theorem T2Four.fixed_mem_K (h : T2Four z u K₁ K₂ H w₁ w₂) {a : G} (ha3 : a ^ 3 = 1)
    (haN : a ∈ normalizer (H : Set G)) (haU : a ∈ normalizer (t2U z u : Set G))
    (hw₁a : ∃ x ∈ H, w₁ * a * w₁⁻¹ = a⁻¹ * x)
    (hCH : ∀ x ∈ H, a * x * a⁻¹ = x → x = 1) {x : G} (hx : x ∈ H)
    (hfix : a * (x * (w₁ * w₂)) * a⁻¹ = x * (w₁ * w₂)) : x * (w₁ * w₂) ∈ K₁ ⊔ K₂ := by
  set M : Subgroup G := K₁ ⊔ K₂ with hM
  set C : Subgroup G := centralizer ({z} : Set G) with hC
  have hidx : M.relIndex C = 2 := h.C_idx
  set w₀ : G := w₁ * w₂ with hw₀
  have ha2 : a * a = a⁻¹ := by
    have : a * (a * a) = 1 := (pow_three a).symm.trans ha3
    exact (inv_eq_of_mul_eq_one_right this).symm
  have haH : ∀ y ∈ H, a * y * a⁻¹ ∈ H := fun y hy => (Subgroup.mem_normalizer_iff.1 haN y).1 hy
  have haH' : ∀ y ∈ H, a⁻¹ * y * a ∈ H := by
    intro y hy
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ haN) y).1 hy
    simpa using this
  have hHC : ∀ y ∈ H, y ∈ C := fun y hy => h.H_le_C hy
  have hw₀M : w₀ ∈ M := h.w₀_mem_K
  have hw₀U : ∀ v ∈ t2U z u, w₀ * v = v * w₀ := t2U_comm_all h.zz h.uu h.zu_comm h.w₀_z h.w₀_u
  have haU' : a⁻¹ ∈ normalizer (t2U z u : Set G) := Subgroup.inv_mem _ haU
  have hzU : z ∈ t2U z u := Subgroup.subset_closure (by simp)
  have huU : u ∈ t2U z u := Subgroup.subset_closure (by simp)
  have hCU : ∀ y : G, (∀ v ∈ t2U z u, y * v = v * y) → y ∈ C := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.2 (hy z hzU)
  have hA₁ : a⁻¹ * w₀ * a ∈ C := hCU _ (t2U_cent_conj haU hw₀U)
  have hA₂ : a * w₀ * a⁻¹ ∈ C := by
    have := hCU _ (t2U_cent_conj haU' hw₀U)
    simpa using this
  have hw₁C : w₁ ∈ C := h.K_le_C (Subgroup.mem_sup_left h.w₁_mem)
  obtain ⟨x', hx', hw₁a'⟩ := hw₁a
  have hδ : t2Par M (a⁻¹ * w₀ * a) = t2Par M (a * w₀ * a⁻¹) := by
    have h1 := t2Par_conj hidx hw₁C hA₁
    have e : w₁ * (a⁻¹ * w₀ * a) * w₁⁻¹ = x'⁻¹ * (a * w₀ * a⁻¹) * x' := by
      calc w₁ * (a⁻¹ * w₀ * a) * w₁⁻¹
          = (w₁ * a * w₁⁻¹)⁻¹ * (w₁ * w₀ * w₁⁻¹) * (w₁ * a * w₁⁻¹) := by group
        _ = (a⁻¹ * x')⁻¹ * w₀ * (a⁻¹ * x') := by
            rw [hw₁a']
            have : w₁ * w₀ * w₁⁻¹ = w₀ := by
              calc w₁ * w₀ * w₁⁻¹ = (w₀ * w₁) * w₁⁻¹ := by rw [← h.w₁_w₀]
                _ = w₀ := by group
            rw [this]
        _ = x'⁻¹ * (a * w₀ * a⁻¹) * x' := by group
    rw [e] at h1
    have := t2Par_conj hidx (C.inv_mem (hHC x' hx')) hA₂
    rw [inv_inv] at this
    exact h1.symm.trans this
  have hN : x * (a⁻¹ * x * a) * (a * x * a⁻¹) = 1 := by
    apply hCH
    · exact H.mul_mem (H.mul_mem hx (haH' x hx)) (haH x hx)
    · have e1 : a * (a⁻¹ * x * a) * a⁻¹ = x := by group
      have e2 : a * (a * x * a⁻¹) * a⁻¹ = a⁻¹ * x * a := by
        calc a * (a * x * a⁻¹) * a⁻¹ = (a * a) * x * (a * a)⁻¹ := by group
          _ = a⁻¹ * x * a := by rw [ha2]; group
      calc a * (x * (a⁻¹ * x * a) * (a * x * a⁻¹)) * a⁻¹
          = (a * x * a⁻¹) * (a * (a⁻¹ * x * a) * a⁻¹) * (a * (a * x * a⁻¹) * a⁻¹) := by group
        _ = (a * x * a⁻¹) * x * (a⁻¹ * x * a) := by rw [e1, e2]
        _ = x * (a⁻¹ * x * a) * (a * x * a⁻¹) := by
            have c1 := h.H_comm (a * x * a⁻¹) (haH x hx) x hx
            have c2 := h.H_comm (a * x * a⁻¹) (haH x hx) (a⁻¹ * x * a) (haH' x hx)
            have c3 := h.H_comm x hx (a⁻¹ * x * a) (haH' x hx)
            calc (a * x * a⁻¹) * x * (a⁻¹ * x * a) = x * (a * x * a⁻¹) * (a⁻¹ * x * a) := by
                  rw [c1]
              _ = x * ((a * x * a⁻¹) * (a⁻¹ * x * a)) := by group
              _ = x * ((a⁻¹ * x * a) * (a * x * a⁻¹)) := by rw [c2]
              _ = x * (a⁻¹ * x * a) * (a * x * a⁻¹) := by group
  have hpN : t2Par M x + t2Par M (a⁻¹ * x * a) + t2Par M (a * x * a⁻¹) = 0 := by
    have h1 := t2Par_mul hidx (C.mul_mem (hHC x hx) (hHC _ (haH' x hx))) (hHC _ (haH x hx))
    have h2 := t2Par_mul hidx (hHC x hx) (hHC _ (haH' x hx))
    rw [hN, h2] at h1
    have h0 : t2Par M (1 : G) = 0 := t2Par_of_mem M.one_mem
    rw [h0] at h1
    exact h1.symm
  have hx₀fix' : a⁻¹ * (x * w₀) * a = x * w₀ := by
    calc a⁻¹ * (x * w₀) * a = a⁻¹ * (a * (x * w₀) * a⁻¹) * a := by rw [hfix]
      _ = x * w₀ := by group
  have hxC := hHC x hx
  have hx₁C := hHC _ (haH' x hx)
  have hx₂C := hHC _ (haH x hx)
  have hp0 : t2Par M (x * w₀) = t2Par M x := by
    rw [t2Par_mul hidx hxC (h.w₀_mem_C), t2Par_of_mem hw₀M, add_zero]
  have hp1 : t2Par M (x * w₀) = t2Par M (a⁻¹ * x * a) + t2Par M (a⁻¹ * w₀ * a) := by
    have e : x * w₀ = (a⁻¹ * x * a) * (a⁻¹ * w₀ * a) := by
      calc x * w₀ = a⁻¹ * (x * w₀) * a := hx₀fix'.symm
        _ = (a⁻¹ * x * a) * (a⁻¹ * w₀ * a) := by group
    rw [e, t2Par_mul hidx hx₁C hA₁]
  have hp2 : t2Par M (x * w₀) = t2Par M (a * x * a⁻¹) + t2Par M (a * w₀ * a⁻¹) := by
    have e : x * w₀ = (a * x * a⁻¹) * (a * w₀ * a⁻¹) := by
      calc x * w₀ = a * (x * w₀) * a⁻¹ := hfix.symm
        _ = (a * x * a⁻¹) * (a * w₀ * a⁻¹) := by group
    conv_lhs => rw [e]
    rw [t2Par_mul hidx hx₂C hA₂]
  have hfin : t2Par M (x * w₀) = 0 := by
    rw [hδ] at hp1
    exact t2_zmod2_aux _ _ _ _ _ hp0 hp1 hp2 hpN
  exact t2Par_eq_zero_iff.1 hfin

end Parity

section Weyl

variable {G : Type} [Group G] [Finite G] {z u : G} {K₁ K₂ H : Subgroup G} {w₁ w₂ : G}

structure T2Weyl (z u : G) (K₁ K₂ H : Subgroup G) (w₁ w₂ a : G) : Prop where
  four : T2Four z u K₁ K₂ H w₁ w₂
  a_cube : a ^ 3 = 1
  a_normH : a ∈ normalizer (H : Set G)
  a_z : a⁻¹ * z * a = u
  a_u : a⁻¹ * u * a = z * u
  a_cent : a * (w₁ * w₂) = (w₁ * w₂) * a
  w₁_a : ∃ x ∈ H, w₁ * a * w₁⁻¹ = a⁻¹ * x

theorem T2Four.exists_weyl (h : T2Four z u K₁ K₂ H w₁ w₂) (hr : CFSG.pRank 2 G = 3)
    {F₁ : Type} [Field F₁] [Finite F₁] (hodd : Odd (Nat.card F₁)) (h3 : 3 < Nat.card F₁)
    (e₁ : ↥K₁ ≃* SL2 F₁) (hK₁inv : ∀ x ∈ K₁, x * x = 1 → x = 1 ∨ x = z)
    (hnc : ∀ y : G, y * y = 1 → y * z = z * y → y ≠ 1 → y ≠ z → ∃ x ∈ K₁, y * x * y⁻¹ ≠ x)
    (hconj : ∃ g : G, g⁻¹ * z * g = u) (hH3 : ¬ 3 ∣ Nat.card H)
    (hCH : ∀ a : G, a ∈ normalizer (H : Set G) → a ^ 3 = 1 → a⁻¹ * z * a = u →
      a⁻¹ * u * a = z * u → ∀ x ∈ H, a * x * a⁻¹ = x → x = 1) :
    ∃ w₁' w₂' a : G, T2Weyl z u K₁ K₂ H w₁' w₂' a := by
  obtain ⟨a, ha3, haN, d1, d2, hw₁a⟩ := h.exists_exact hr hodd h3 e₁ hK₁inv hnc hconj hH3
  have haU : a ∈ normalizer (t2U z u : Set G) := by
    have : a⁻¹ ∈ normalizer (t2U z u : Set G) := by
      refine t2U_norm (z := z) (u := u) ?_ ?_
      · rw [inv_inv, d1]; exact Subgroup.subset_closure (by simp)
      · rw [inv_inv, d2]; exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
    simpa using Subgroup.inv_mem _ this
  have ha1 : a ≠ 1 := by
    intro h1
    apply h.zu_ne
    rw [h1] at d1
    simpa using d1
  have hCH' := hCH a haN ha3 d1 d2
  obtain ⟨x, hx, hfix⟩ := h.exists_fixed hr ha3 haU hH3
  have hxK := h.fixed_mem_K ha3 haN haU hw₁a (fun y hy => hCH' y hy) hx hfix
  have hxM : x ∈ K₁ ⊔ K₂ := by
    have : x = (x * (w₁ * w₂)) * (w₁ * w₂)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ hxK (Subgroup.inv_mem _ h.w₀_mem_K)
  obtain ⟨x₁, hx₁, hx₁K, x₂, hx₂, hx₂K, hxx⟩ := h.H_inf_K hx hxM
  have h' := h.rechoose hx₁ hx₁K hx₂ hx₂K
  have hww : (x₁ * w₁) * (x₂ * w₂) = x * (w₁ * w₂) := by
    have hc : w₁ * x₂ = x₂ * w₁ := h.K_comm w₁ h.w₁_mem x₂ hx₂K
    calc (x₁ * w₁) * (x₂ * w₂) = x₁ * (w₁ * x₂) * w₂ := by group
      _ = x₁ * (x₂ * w₁) * w₂ := by rw [hc]
      _ = (x₁ * x₂) * (w₁ * w₂) := by group
      _ = x * (w₁ * w₂) := by rw [hxx]
  refine ⟨x₁ * w₁, x₂ * w₂, a, h', ha3, haN, d1, d2, ?_, ?_⟩
  · rw [hww]
    calc a * (x * (w₁ * w₂)) = (a * (x * (w₁ * w₂)) * a⁻¹) * a := by group
      _ = (x * (w₁ * w₂)) * a := by rw [hfix]
  · obtain ⟨x', hx', hw⟩ := hw₁a
    have ha₁ : a * x₁ * a⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 haN x₁).1 hx₁
    refine ⟨(a * x₁ * a⁻¹) * x' * x₁⁻¹, H.mul_mem (H.mul_mem ha₁ hx') (H.inv_mem hx₁), ?_⟩
    calc (x₁ * w₁) * a * (x₁ * w₁)⁻¹ = x₁ * (w₁ * a * w₁⁻¹) * x₁⁻¹ := by group
      _ = x₁ * (a⁻¹ * x') * x₁⁻¹ := by rw [hw]
      _ = a⁻¹ * ((a * x₁ * a⁻¹) * x' * x₁⁻¹) := by group

end Weyl

end CFSG.GH74.GLS.Stage4.Rest
