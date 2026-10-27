module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec5EEmbed
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec5EFacts

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec5E

open Sec7 Sec8 T2M

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

namespace Ctx

variable (C : Ctx S F T₁)

theorem T₂_le_T₁ : C.D.T₂ ≤ T₁ := by rw [C.D.T₂_eq]; exact inf_le_left

include C in
theorem T_le_T₁ : S.data.T ≤ T₁ := C.h4.le

include C in
theorem card_T₁ : Nat.card T₁ = 128 := by rw [C.h4.card, S.card_T]

theorem T₂_normal : (C.D.T₂.subgroupOf T₁).Normal := by
  refine Subgroup.normal_of_index_eq_two ?_
  have h := Subgroup.card_mul_index (C.D.T₂.subgroupOf T₁)
  rw [Nat.card_congr (subgroupOfEquivOfLe C.T₂_le_T₁).toEquiv, C.D.card_T₂, C.card_T₁] at h
  omega

theorem conj_mem_T₂ {n : X} (hn : n ∈ T₁) {a : X} (ha : a ∈ C.D.T₂) : n * a * n⁻¹ ∈ C.D.T₂ :=
  Subgroup.mem_subgroupOf.1
    (C.T₂_normal.conj_mem ⟨a, C.T₂_le_T₁ ha⟩ (Subgroup.mem_subgroupOf.2 ha) ⟨n, hn⟩)

theorem g_mem_N_T : C.D.g ∈ normalizer (S.data.T : Set X) := C.h4.le_normalizer C.D.g_mem

include C in
theorem z_comm_T₁ {n : X} (hn : n ∈ T₁) : S.z * n = n * S.z :=
  (C.D.center_T₁ S.z (C.T_le_T₁ z_mem_T)).mpr (mem_zpowers _) n hn

theorem g_z : C.D.g * S.z * C.D.g⁻¹ = S.z := conj_eq (C.z_comm_T₁ C.D.g_mem).symm

noncomputable def σ₀ (a : T2M) : T2M := C.ιinv (C.D.g * C.ι a * C.D.g⁻¹)

noncomputable def σ₀inv (a : T2M) : T2M := C.ιinv (C.D.g⁻¹ * C.ι a * C.D.g)

theorem ι_σ₀ (a : T2M) : C.ι (C.σ₀ a) = C.D.g * C.ι a * C.D.g⁻¹ :=
  C.ι_ιinv (C.conj_mem_T₂ C.D.g_mem (C.ι_mem_T₂ a))

theorem ι_σ₀inv (a : T2M) : C.ι (C.σ₀inv a) = C.D.g⁻¹ * C.ι a * C.D.g := by
  have := C.ι_ιinv (C.conj_mem_T₂ (inv_mem C.D.g_mem) (C.ι_mem_T₂ a))
  rwa [inv_inv] at this

theorem ι_inj {a b : T2M} (h : C.ι a = C.ι b) : a = b := C.ι_injective h

theorem σ₀_eq (a : T2M) : C.σ₀ a = homOf (C.σ₀ T2M.x) (C.σ₀ T2M.y) (C.σ₀ T2M.w)
    (T2M.t * T2M.k) (T2M.z * T2M.k) a := by
  apply C.ι_inj
  have h := T2M.map_eq_homOf ((MulAut.conj C.D.g).toMonoidHom.comp C.ι) C.ι
    (ix := C.σ₀ T2M.x) (iy := C.σ₀ T2M.y) (iw := C.σ₀ T2M.w) (it := T2M.t * T2M.k)
    (ik := T2M.z * T2M.k) (by simp [C.ι_σ₀]) (by simp [C.ι_σ₀]) (by simp [C.ι_σ₀])
    (by simp [C.ι_t, C.ι_k, C.D.g_t]) (by simp [C.ι_k, C.ι_z, C.D.g_k]) a
  rw [C.ι_σ₀]
  simpa using h

theorem σ₀_mul (a b : T2M) : C.σ₀ (a * b) = C.σ₀ a * C.σ₀ b := by
  apply C.ι_inj
  rw [map_mul, C.ι_σ₀, C.ι_σ₀, C.ι_σ₀, map_mul]; group

theorem σ₀_inv (a : T2M) : C.σ₀ a⁻¹ = (C.σ₀ a)⁻¹ := by
  apply C.ι_inj
  rw [map_inv, C.ι_σ₀, C.ι_σ₀, map_inv]; group

theorem σ₀_one : C.σ₀ 1 = 1 := by
  apply C.ι_inj; rw [C.ι_σ₀, map_one]; group

theorem σ₀_t : C.σ₀ T2M.t = T2M.t * T2M.k := by
  apply C.ι_inj; rw [C.ι_σ₀, map_mul, C.ι_t, C.ι_k, C.D.g_t]

theorem σ₀_k : C.σ₀ T2M.k = T2M.z * T2M.k := by
  apply C.ι_inj; rw [C.ι_σ₀, map_mul, C.ι_k, C.ι_z, C.D.g_k]

theorem σ₀_z : C.σ₀ T2M.z = T2M.z := by
  apply C.ι_inj; rw [C.ι_σ₀, C.ι_z, C.g_z]

theorem σ₀_injective {a b : T2M} (h : C.σ₀ a = C.σ₀ b) : a = b := by
  apply C.ι_inj
  have := congrArg C.ι h
  rw [C.ι_σ₀, C.ι_σ₀] at this
  simpa using this

theorem σ₀_σ₀inv (a : T2M) : C.σ₀ (C.σ₀inv a) = a := by
  apply C.ι_inj; rw [C.ι_σ₀, C.ι_σ₀inv]; group

theorem σ₀_σ₀ (a : T2M) : C.σ₀ (C.σ₀ a) = a ∨ C.σ₀ (C.σ₀ a) = a * T2M.z := by
  have hg2 : C.D.g * C.D.g ∈ C.D.T₂ := by rw [← pow_two]; exact C.D.g_sq_mem
  obtain ⟨c, hc⟩ := C.exists_ι hg2
  have h : C.σ₀ (C.σ₀ a) = c * a * c⁻¹ := by
    apply C.ι_inj
    rw [C.ι_σ₀, C.ι_σ₀, map_mul, map_mul, map_inv, hc]; group
  rw [h]
  rcases T2M.comm_cases c a with h1 | h1
  · left
    calc c * a * c⁻¹ = c * a * c⁻¹ * a⁻¹ * a := by group
      _ = a := by rw [h1, one_mul]
  · right
    calc c * a * c⁻¹ = c * a * c⁻¹ * a⁻¹ * a := by group
      _ = T2M.z * a := by rw [h1]
      _ = a * T2M.z := (T2M.central_of_mem_Zl _ (by decide) a)

theorem ι_mem_T_of_σ₀ {a : T2M} (ha : C.ι a ∈ S.data.T) : T2M.InT (C.σ₀ a) := by
  rw [← C.ι_mem_T_iff, C.ι_σ₀]
  exact conj_mem_of_mem_normalizer C.g_mem_N_T ha

theorem σ₀_y_mem_E2 : C.σ₀ T2M.y ∈ T2M.E2l := by
  rw [← C.ι_mem_E₂_iff, C.ι_σ₀, ← C.D.g_E, C.ι_y]
  exact ⟨F.yF, by rw [E₁_eq C]; exact subset_closure (by simp), rfl⟩

end Ctx

structure GD (C : Ctx S F T₁) where
  p : SigD
  hp : p ∈ T2M.repList
  g : X
  g_mem : g ∈ T₁
  hσ : ∀ a, g * C.ι a * g⁻¹ = C.ι (p.sig a)
  hσinv : ∀ a, g⁻¹ * C.ι a * g = C.ι (p.sigInv a)
  g_sq_mem : g * g ∈ C.D.T₂
  g_sq_not : g * g ∉ S.data.T

namespace Ctx

variable (C : Ctx S F T₁)

theorem tk_comm_T : ∀ τ : T2M, T2M.InT τ → τ * T2M.t = T2M.t * τ := by decide +kernel

theorem k_comm_all : ∀ τ : T2M, τ * T2M.k = T2M.k * τ := by decide +kernel

theorem tkz_comm_T : ∀ τ : T2M, T2M.InT τ →
    τ⁻¹ * (T2M.t * T2M.k * T2M.z) * τ = T2M.t * T2M.k * T2M.z := by decide +kernel

theorem zk_comm_all : ∀ τ : T2M, τ⁻¹ * (T2M.z * T2M.k) * τ = T2M.z * T2M.k := by decide +kernel

theorem model_x_t : T2M.x * T2M.t = T2M.t * T2M.x := by decide +kernel
theorem model_x_k : T2M.x * T2M.k = T2M.k * T2M.x := by decide +kernel
theorem model_x_z : T2M.x * T2M.x = T2M.z := by decide +kernel
theorem model_y_y : T2M.y * T2M.y = 1 := by decide +kernel
theorem model_y_x : T2M.y * T2M.x * T2M.y⁻¹ = T2M.x⁻¹ := by decide +kernel
theorem model_y_t : T2M.y * T2M.t = T2M.t * T2M.y := by decide +kernel
theorem model_y_k : T2M.y * T2M.k = T2M.k * T2M.y := by decide +kernel
theorem model_w_w : T2M.w * T2M.w = 1 := by decide +kernel
theorem model_w_x : T2M.w * T2M.x = T2M.x * T2M.w := by decide +kernel
theorem model_w_y : T2M.w * T2M.y = T2M.y * T2M.w := by decide +kernel
theorem model_w_k : T2M.w * T2M.k = T2M.k * T2M.w := by decide +kernel
theorem model_w_t : T2M.w * T2M.t * T2M.w⁻¹ = T2M.t * T2M.z := by decide +kernel

theorem σ₀_comm {a b : T2M} (h : a * b = b * a) : C.σ₀ a * C.σ₀ b = C.σ₀ b * C.σ₀ a := by
  rw [← C.σ₀_mul, h, C.σ₀_mul]

theorem exists_gD : Nonempty (GD C) := by
  have hx := C.ι_mem_T_of_σ₀ (a := T2M.x) (by rw [C.ι_x]; exact xF_mem_T F)
  have hy := C.ι_mem_T_of_σ₀ (a := T2M.y) (by rw [C.ι_y]; exact yF_mem_T F)
  have hσσ : ∀ g ∈ [T2M.x, T2M.y, T2M.w, T2M.t, T2M.k],
      homOf (C.σ₀ T2M.x) (C.σ₀ T2M.y) (C.σ₀ T2M.w) (T2M.t * T2M.k) (T2M.z * T2M.k)
        (homOf (C.σ₀ T2M.x) (C.σ₀ T2M.y) (C.σ₀ T2M.w) (T2M.t * T2M.k) (T2M.z * T2M.k) g) = g ∨
      homOf (C.σ₀ T2M.x) (C.σ₀ T2M.y) (C.σ₀ T2M.w) (T2M.t * T2M.k) (T2M.z * T2M.k)
        (homOf (C.σ₀ T2M.x) (C.σ₀ T2M.y) (C.σ₀ T2M.w) (T2M.t * T2M.k) (T2M.z * T2M.k) g) =
          g * T2M.z := by
    intro g _
    rw [← C.σ₀_eq, ← C.σ₀_eq]
    exact C.σ₀_σ₀ g
  have hB : ∀ a, homOf (C.σ₀ T2M.x) (C.σ₀ T2M.y) (C.σ₀ T2M.w) (T2M.t * T2M.k) (T2M.z * T2M.k)
      (C.σ₀inv a) = a := fun a => by rw [← C.σ₀_eq, C.σ₀_σ₀inv]
  obtain ⟨τ, hτ, hmem⟩ := T2M.classify (C.σ₀ T2M.x) hx
    (by rw [← C.σ₀_mul, model_x_z, C.σ₀_z])
    (by rw [← C.σ₀_t, C.σ₀_comm model_x_t])
    (by rw [← C.σ₀_k, C.σ₀_comm model_x_k])
    (C.σ₀ T2M.y) hy C.σ₀_y_mem_E2 (by rw [← C.σ₀_mul, model_y_y, C.σ₀_one])
    (by rw [← C.σ₀_inv, ← C.σ₀_mul, ← C.σ₀_mul, model_y_x, C.σ₀_inv])
    (by rw [← C.σ₀_t, C.σ₀_comm model_y_t])
    (by rw [← C.σ₀_k, C.σ₀_comm model_y_k])
    (C.σ₀ T2M.w) (by rw [← C.σ₀_mul, model_w_w, C.σ₀_one])
    (C.σ₀_comm model_w_x) (C.σ₀_comm model_w_y)
    (by rw [← C.σ₀_k, C.σ₀_comm model_w_k])
    (by rw [← C.σ₀_t, ← C.σ₀_z, ← C.σ₀_inv, ← C.σ₀_mul, ← C.σ₀_mul, model_w_t, C.σ₀_mul])
    hσσ (C.σ₀inv T2M.x) (hB _) (C.σ₀inv T2M.y) (hB _) (C.σ₀inv T2M.w) (hB _)
  set p := T2M.normD (C.σ₀ T2M.x) (C.σ₀ T2M.y) (C.σ₀ T2M.w) (C.σ₀inv T2M.x) (C.σ₀inv T2M.y)
    (C.σ₀inv T2M.w) τ with hp
  set g' := C.D.g * C.ι τ with hg'
  have hτT : C.ι τ ∈ S.data.T := (C.ι_mem_T_iff τ).mpr hτ
  have key : ∀ b : T2M, g' * C.ι b * g'⁻¹ = C.ι (C.σ₀ (τ * b * τ⁻¹)) := by
    intro b; rw [C.ι_σ₀, map_mul, map_mul, map_inv, hg']; group
  have key' : ∀ b : T2M, g'⁻¹ * C.ι b * g' = C.ι (τ⁻¹ * C.σ₀inv b * τ) := by
    intro b; rw [map_mul, map_mul, map_inv, C.ι_σ₀inv, hg']; group
  have hconj : ∀ b : T2M, ((MulAut.conj g').toMonoidHom.comp C.ι) b = g' * C.ι b * g'⁻¹ :=
    fun b => rfl
  have hconj' : ∀ b : T2M, ((MulAut.conj g'⁻¹).toMonoidHom.comp C.ι) b = g'⁻¹ * C.ι b * g' :=
    fun b => by simp
  have hσ : ∀ a, g' * C.ι a * g'⁻¹ = C.ι (p.sig a) := by
    intro a
    have h := T2M.map_eq_homOf ((MulAut.conj g').toMonoidHom.comp C.ι) C.ι
      (ix := p.ax) (iy := p.ay) (iw := p.aw) (it := T2M.t * T2M.k) (ik := T2M.z * T2M.k)
      (by rw [hconj, key, C.σ₀_eq]; rfl) (by rw [hconj, key, C.σ₀_eq]; rfl)
      (by rw [hconj, key, C.σ₀_eq]; rfl)
      (by rw [hconj, key, tk_comm_T τ hτ, mul_inv_cancel_right, C.σ₀_t])
      (by rw [hconj, key, k_comm_all τ, mul_inv_cancel_right, C.σ₀_k]) a
    rw [← hconj, h]; rfl
  have hσinv : ∀ a, g'⁻¹ * C.ι a * g' = C.ι (p.sigInv a) := by
    intro a
    have hg_t : C.σ₀inv T2M.t = T2M.t * T2M.k * T2M.z := by
      apply C.σ₀_injective
      rw [C.σ₀_σ₀inv, C.σ₀_mul, C.σ₀_mul, C.σ₀_t, C.σ₀_k, C.σ₀_z]
      decide +kernel
    have hg_k : C.σ₀inv T2M.k = T2M.z * T2M.k := by
      apply C.σ₀_injective
      rw [C.σ₀_σ₀inv, C.σ₀_mul, C.σ₀_k, C.σ₀_z]
      decide +kernel
    have h := T2M.map_eq_homOf ((MulAut.conj g'⁻¹).toMonoidHom.comp C.ι) C.ι
      (ix := p.bx) (iy := p.by_) (iw := p.bw) (it := T2M.t * T2M.k * T2M.z)
      (ik := T2M.z * T2M.k) (by rw [hconj', key']; rfl) (by rw [hconj', key']; rfl)
      (by rw [hconj', key']; rfl)
      (by rw [hconj', key', hg_t, tkz_comm_T τ hτ])
      (by rw [hconj', key', hg_k, zk_comm_all τ]) a
    rw [← hconj', h]; rfl
  have hgT : C.D.g⁻¹ * C.ι τ * C.D.g ∈ S.data.T := by
    have := conj_mem_of_mem_normalizer (inv_mem C.g_mem_N_T) hτT
    rwa [inv_inv] at this
  have hsq : g' * g' = (C.D.g * C.D.g) * ((C.D.g⁻¹ * C.ι τ * C.D.g) * C.ι τ) := by
    rw [hg']; group
  have hg2 : C.D.g * C.D.g ∈ C.D.T₂ := by rw [← pow_two]; exact C.D.g_sq_mem
  refine ⟨⟨p, hmem, g', mul_mem C.D.g_mem (C.T_le_T₁ hτT), hσ, hσinv, ?_, ?_⟩⟩
  · rw [hsq]; exact mul_mem hg2 (C.T_le_T₂ (mul_mem hgT hτT))
  · rw [hsq]
    intro h
    apply C.D.g_sq_not_mem
    have := mul_mem h (inv_mem (mul_mem hgT hτT))
    rwa [mul_inv_cancel_right, ← pow_two] at this

end Ctx

end Sec5E

end CFSG.ComponentClassification.HSFLit
