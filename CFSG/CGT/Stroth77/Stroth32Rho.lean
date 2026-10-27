module

public import CFSG.CGT.Stroth77.Stroth32Par
public import CFSG.CGT.Stroth77.Stroth32Nat
public import CFSG.CGT.Stroth77.Stroth32V0

public section

namespace CFSG.CGT.Stroth77

open Stroth42Core Stroth32H1 Stroth32Par

namespace StrothWeakTypeData

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {τ : StrothTypeIndex}
  (dD : StrothWeakTypeData D τ)

theorem thetaT_proj_rho {S : Subgroup G} (hS : Local.Setting S D) {f : G} (hf : f ∈ hS.R)
    (x : Torus τ.k) :
    dD.thetaT (hS.R_le_normalizer (hS.proj_mem dD.ρ_mem hf)) x =
      τ.action.φρ (dD.thetaT (hS.R_le_normalizer hf) (τ.action.φρ (τ.action.φρ x))) := by
  rw [dD.thetaT_proj hS dD.ρ_mem hf, dD.thetaT_conj (hS.R_le_normalizer hf) dD.ρ_mem,
    dD.thetaT_ρ, dD.thetaT_ρ_inv]

end StrothWeakTypeData

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
  {dD : StrothWeakTypeData D (.t100 m)}

theorem t100Par_ne_one (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) (hm : 2 ≤ m)
    (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) {e : G}
    (he : e ∈ hS.R1 dD.uv dD.t) : dD.t100Par e ≠ (1, 1, 1) := by
  intro hP
  have hm1 : 1 ≤ m := by omega
  have hDR1 : ∀ {d : G}, d ∈ D → d ∈ hS.R1 dD.uv dD.t := fun {d} hd =>
    ⟨hS.D_le_R hd, (dD.crdT_cocycle_of_mem_uv hd).1, (dD.crdT_cocycle_of_mem_t hd).1⟩
  have hue : dD.u⁻¹ * e * dD.u * e⁻¹ ∈ D := by
    rw [h.t100Par_mul_inv_mem_iff hS hm1 (h.conj_u_mem_R1 hS he) he,
      t100Par_conj_u hS hm1 he, hP]
    decide
  obtain ⟨d, hd, hcomm⟩ := dD.t100_exists_u_comm hm1 hfus (hS.R_le_normalizer he.1) hue
  set f := e * d with hf
  have hfR1 : f ∈ hS.R1 dD.uv dD.t := mul_mem he (hDR1 hd)
  have hPf : dD.t100Par f = (1, 1, 1) := by
    rw [hf, t100Par_mul hS hm1 he (hDR1 hd), hP, (h.t100Par_eq_zero_iff hS hm1 (hDR1 hd)).2 hd,
      add_zero]
  clear_value f
  obtain ⟨hfR, hfuv, hft⟩ := hfR1
  have hfN := hS.R_le_normalizer hfR
  obtain ⟨x, hx⟩ := Torus.exists_ofInt (crdT dD.e (f⁻¹ * dD.uv * f * dD.uv⁻¹))
  obtain ⟨y, hy⟩ := Torus.exists_ofInt (crdT dD.e (f⁻¹ * dD.t * f * dD.t⁻¹))
  obtain ⟨c1, c2, c3⟩ := cocycle_uv_t dD.e dD.uv_sq dD.t_sq dD.uv_comm_t dD.uv_mem dD.t_mem
    dD.uv_conj dD.t_conj hfuv hft
  rw [← hx] at c1
  rw [← hy] at c2
  rw [← hx, ← hy] at c3
  obtain ⟨κ₁, κ₂, κ₃, e1, e2, e3⟩ := t100_cocycle_ints x y c1 c2 c3
  have hPxy := dD.t100Par_eq hm1 hx.symm hy.symm
  rw [hPf, Prod.mk.injEq, Prod.mk.injEq] at hPxy
  obtain ⟨hx1, hx2, hy0⟩ := hPxy
  have ox1 : Odd (x 1) := ZMod.intCast_eq_one_iff_odd.1 hx1.symm
  have ox2 : Odd (x 2) := ZMod.intCast_eq_one_iff_odd.1 hx2.symm
  have oy0 : Odd (y 0) := ZMod.intCast_eq_one_iff_odd.1 hy0.symm
  set θ := dD.thetaT hfN with hθdef
  have huv : ∀ v, θ ((StrothTypeIndex.t100 m).action.φuv v) =
      (StrothTypeIndex.t100 m).action.φuv (θ v) := fun v => by
    have := dD.thetaT_comm_of_conj_mem hfN dD.uv_mem hfuv v
    rwa [dD.thetaT_uv, dD.thetaT_uv] at this
  have ht : ∀ v, θ ((StrothTypeIndex.t100 m).action.φt v) =
      (StrothTypeIndex.t100 m).action.φt (θ v) := fun v => by
    have := dD.thetaT_comm_of_conj_mem hfN dD.t_mem hft v
    rwa [dD.thetaT_t, dD.thetaT_t] at this
  have hfu : f⁻¹ * dD.u * f * dD.u⁻¹ ∈ D := by
    rw [show f⁻¹ * dD.u * f * dD.u⁻¹ = 1 by
      rw [mul_assoc f⁻¹, hcomm]; group]
    exact one_mem D
  have hu : ∀ v, θ ((StrothTypeIndex.t100 m).action.φu v) =
      (StrothTypeIndex.t100 m).action.φu (θ v) := fun v => by
    have := dD.thetaT_comm_of_conj_mem hfN dD.u_mem hfu v
    rwa [dD.thetaT_u, dD.thetaT_u] at this
  have hΩ : ∀ v, v + v = 0 → θ v = v := fun v hv =>
    dD.thetaT_of_two hfN (hS.R_le_centralizer_omega hfR) hv
  have hff : f * f ∈ D := by
    rw [← h.t100Par_eq_zero_iff hS hm1 (mul_mem ⟨hfR, hfuv, hft⟩ ⟨hfR, hfuv, hft⟩),
      t100Par_mul hS hm1 ⟨hfR, hfuv, hft⟩ ⟨hfR, hfuv, hft⟩, hPf]
    decide
  have hsq : ∀ v, θ (θ v) = v := dD.thetaT_thetaT_of_sq hfN hff
  have hf₂ := h.proj_rho_mem_R1 hS ⟨hfR, hfuv, hft⟩
  have hf₃ := h.proj_rho_mem_R1 hS hf₂
  have hP₂ : dD.t100Par (hS.proj dD.ρ f) = (0, 1, 0) := by
    rw [h.t100Par_proj_rho hS hm1 ⟨hfR, hfuv, hft⟩, hPf]; decide
  have hP₃ : dD.t100Par (hS.proj dD.ρ (hS.proj dD.ρ f)) = (1, 0, 1) := by
    rw [h.t100Par_proj_rho hS hm1 hf₂, hP₂]; decide
  have hnorm : f * hS.proj dD.ρ f * hS.proj dD.ρ (hS.proj dD.ρ f) ∈ D := by
    rw [← h.t100Par_eq_zero_iff hS hm1 (mul_mem (mul_mem ⟨hfR, hfuv, hft⟩ hf₂) hf₃),
      t100Par_mul hS hm1 (mul_mem ⟨hfR, hfuv, hft⟩ hf₂) hf₃,
      t100Par_mul hS hm1 ⟨hfR, hfuv, hft⟩ hf₂, hPf, hP₂, hP₃]
    decide
  have hθ₂ : ∀ v, dD.thetaT (hS.R_le_normalizer hf₂.1) v =
      (StrothTypeIndex.t100 m).action.φρ (θ ((StrothTypeIndex.t100 m).action.φρ
        ((StrothTypeIndex.t100 m).action.φρ v))) := fun v =>
    dD.thetaT_proj_rho hS hfR v
  have hθ₃ : ∀ v, dD.thetaT (hS.R_le_normalizer hf₃.1) v =
      (StrothTypeIndex.t100 m).action.φρ (dD.thetaT (hS.R_le_normalizer hf₂.1)
        ((StrothTypeIndex.t100 m).action.φρ ((StrothTypeIndex.t100 m).action.φρ v))) := fun v =>
    dD.thetaT_proj_rho hS hf₂.1 v
  have hcube : ∀ v : Torus (StrothTypeIndex.t100 m).k, (StrothTypeIndex.t100 m).action.φρ
      ((StrothTypeIndex.t100 m).action.φρ ((StrothTypeIndex.t100 m).action.φρ v)) = v :=
    fun v => StrothWeakTypeData.φρ_cube v
  have hN : ∀ v, θ ((StrothTypeIndex.t100 m).action.φρ ((StrothTypeIndex.t100 m).action.φρ
      (θ ((StrothTypeIndex.t100 m).action.φρ ((StrothTypeIndex.t100 m).action.φρ
        (θ ((StrothTypeIndex.t100 m).action.φρ ((StrothTypeIndex.t100 m).action.φρ v)))))))) = v := by
    intro v
    have key := dD.thetaT_of_mem (hS.R_le_normalizer (mul_mem (mul_mem hfR hf₂.1) hf₃.1)) hnorm
      ((StrothTypeIndex.t100 m).action.φρ ((StrothTypeIndex.t100 m).action.φρ v))
    rw [dD.thetaT_mul (hS.R_le_normalizer (mul_mem hfR hf₂.1)) (hS.R_le_normalizer hf₃.1),
      dD.thetaT_mul hfN (hS.R_le_normalizer hf₂.1)] at key
    simp only [hθ₃, hθ₂, hcube] at key
    have := congrArg (StrothTypeIndex.t100 m).action.φρ key
    simp only [hcube] at this
    exact this
  obtain ⟨ε₁, ε₃, hθ⟩ := Stroth32V0.t100_V0 hm θ huv ht hu hΩ hsq hN
  obtain ⟨w, hw⟩ := Torus.exists_ofInt (crdT dD.e (f * f))
  have hwθ : θ (Torus.ofInt _ w) = Torus.ofInt _ w := by
    rw [hw, hθdef, dD.thetaT_crdT hfN hff]
    congr 1
    group
  have hsq1 : θ (Torus.ofInt _ x) + Torus.ofInt _ x =
      (StrothTypeIndex.t100 m).action.φuv (Torus.ofInt _ w) - Torus.ofInt _ w := by
    rw [hx, hw, hθdef, ← (dD.crdT_cocycle_mul hfN hfuv hfuv).2,
      (dD.crdT_cocycle_of_mem_uv hff).2]
  have hsq2 : θ (Torus.ofInt _ y) + Torus.ofInt _ y =
      (StrothTypeIndex.t100 m).action.φt (Torus.ofInt _ w) - Torus.ofInt _ w := by
    rw [hy, hw, hθdef, ← (dD.crdT_cocycle_mul hfN hft hft).2,
      (dD.crdT_cocycle_of_mem_t hff).2]
  have hε₃ := Stroth32Nat.t100_sq_par hm θ ε₁ ε₃ hθ x y w hwθ hsq1 hsq2 ox1 oy0
  set f₂ := hS.proj dD.ρ f with hf₂def
  have hf₂u := h.conj_u_mem_R1 hS hf₂
  have hz : (f * f₂)⁻¹ * (dD.u⁻¹ * f₂ * dD.u) ∈ D := by
    have h1 : dD.u⁻¹ * f₂ * dD.u * (f * f₂)⁻¹ ∈ D := by
      rw [h.t100Par_mul_inv_mem_iff hS hm1 hf₂u (mul_mem ⟨hfR, hfuv, hft⟩ hf₂),
        t100Par_conj_u hS hm1 hf₂, t100Par_mul hS hm1 ⟨hfR, hfuv, hft⟩ hf₂, hP₂, hPf]
      decide
    have := (Subgroup.mem_normalizer_iff''.mp
      (hS.R_le_normalizer (mul_mem hfR hf₂.1)) _).mp h1
    convert this using 1
    group
  set z := (f * f₂)⁻¹ * (dD.u⁻¹ * f₂ * dD.u) with hzdef
  have hfz : dD.u⁻¹ * f₂ * dD.u = f * f₂ * z := by rw [hzdef]; group
  have hθ₂v : ∀ v : Fin 3 → ℤ, dD.thetaT (hS.R_le_normalizer hf₂.1) (Torus.ofInt _ v) =
      Torus.ofInt _ ![v 0, v 1 + 2 ^ m * (ε₁ * v 0 + ε₃ * v 1 + ε₃ * v 2),
        v 2 + 2 ^ m * (ε₃ * v 2)] := fun v => by
    rw [hθ₂]
    exact Stroth32Nat.t100_theta_rho_form θ ε₁ ε₃ hθ v
  have hf₂N := hS.R_le_normalizer hf₂.1
  have hzN : z ∈ Subgroup.normalizer (D : Set G) := Subgroup.le_normalizer hz
  obtain ⟨-, -, q1, q2⟩ := cocycle_conj_u hS hf₂.2.1 hf₂.2.2
  rw [hfz] at q1 q2
  obtain ⟨m12uv, r12uv⟩ := dD.crdT_cocycle_mul hf₂N hfuv hf₂.2.1
  obtain ⟨m12t, r12t⟩ := dD.crdT_cocycle_mul hf₂N hft hf₂.2.2
  obtain ⟨-, r3uv⟩ := dD.crdT_cocycle_mul hzN m12uv (dD.crdT_cocycle_of_mem_uv hz).1
  obtain ⟨-, r3t⟩ := dD.crdT_cocycle_mul hzN m12t (dD.crdT_cocycle_of_mem_t hz).1
  rw [dD.thetaT_of_mem hzN hz, r12uv, (dD.crdT_cocycle_of_mem_uv hz).2] at r3uv
  rw [dD.thetaT_of_mem hzN hz, r12t, (dD.crdT_cocycle_of_mem_t hz).2] at r3t
  obtain ⟨-, -, -, hu1⟩ := cocycle_conj_u hS hfuv hft
  have hufu : dD.u⁻¹ * f * dD.u = f := by
    calc dD.u⁻¹ * f * dD.u = dD.u⁻¹ * (f * dD.u) := by group
      _ = dD.u⁻¹ * (dD.u * f) := by rw [hcomm]
      _ = f := by group
  rw [hufu, ← hx, ← hy] at hu1
  have hε := Stroth32Nat.t100_urel_par hm1 _ ε₁ ε₃ hθ₂v x y e2 e3 hu1.symm
    (crdT dD.e (f₂⁻¹ * dD.uv * f₂ * dD.uv⁻¹)) (crdT dD.e (f₂⁻¹ * dD.t * f₂ * dD.t⁻¹))
    (crdT dD.e z) (by rw [← q1, r3uv, ← hx]) (by rw [← q2, r3t, ← hy]) ox2 oy0
  have hid : ∀ v, θ v = v := fun v => by
    obtain ⟨v₀, rfl⟩ := Torus.exists_ofInt v
    obtain ⟨a, ha⟩ := hε₃
    obtain ⟨b, hb⟩ := hε
    rw [hθ, t100_ofInt_eq_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    refine ⟨⟨0, by ring⟩, ⟨-((b - a) * v₀ 0 + a * v₀ 2), ?_⟩,
      ⟨-((b - a) * v₀ 0 + a * v₀ 1), ?_⟩⟩
    · linear_combination (-(2 ^ m * v₀ 0)) * hb + (2 ^ m * v₀ 0 - 2 ^ m * v₀ 2) * ha
    · linear_combination (-(2 ^ m * v₀ 0)) * hb + (2 ^ m * v₀ 0 - 2 ^ m * v₀ 1) * ha
  have hfD : f ∈ D := h.mem_of_mem_centralizer (hS.R_le_S hfR) (dD.mem_centralizer_of_thetaT hfN hid)
  have := (h.t100Par_eq_zero_iff hS hm1 ⟨hfR, hfuv, hft⟩).2 hfD
  rw [hPf] at this
  exact absurd this (by decide)

theorem t100_proj_rho_mul_inv_mem (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    (hm : 2 ≤ m) (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) {e : G}
    (he : e ∈ hS.R1 dD.uv dD.t) : hS.proj dD.ρ e * e⁻¹ ∈ D := by
  have hm1 : 1 ≤ m := by omega
  have he₂ := h.proj_rho_mem_R1 hS he
  have he₃ := h.proj_rho_mem_R1 hS he₂
  have hP₂ := h.t100Par_proj_rho hS hm1 he
  have hP₃ := h.t100Par_proj_rho hS hm1 he₂
  rw [hP₂] at hP₃
  have hne := fun {g : G} (hg : g ∈ hS.R1 dD.uv dD.t) => h.t100Par_ne_one hS hm hfus hg
  have key : ∀ p : ZMod 2 × ZMod 2 × ZMod 2, p ≠ (1, 1, 1) → t100RhoPar p ≠ (1, 1, 1) →
      t100RhoPar (t100RhoPar p) ≠ (1, 1, 1) → p + t100RhoPar p ≠ (1, 1, 1) →
      t100RhoPar p + t100RhoPar (t100RhoPar p) ≠ (1, 1, 1) →
      t100RhoPar (t100RhoPar p) + p ≠ (1, 1, 1) → t100RhoPar p = p := by decide
  have hfix := key (dD.t100Par e) (hne he) (by rw [← hP₂]; exact hne he₂)
    (by rw [← hP₃]; exact hne he₃)
    (by rw [← hP₂, ← t100Par_mul hS hm1 he he₂]; exact hne (mul_mem he he₂))
    (by rw [← hP₃, ← hP₂, ← t100Par_mul hS hm1 he₂ he₃]; exact hne (mul_mem he₂ he₃))
    (by rw [← hP₃, ← t100Par_mul hS hm1 he₃ he]; exact hne (mul_mem he₃ he))
  exact (h.t100Par_mul_inv_mem_iff hS hm1 he₂ he).2 (hP₂.trans hfix)

end StrothFrame.IsD

end CFSG.CGT.Stroth77
