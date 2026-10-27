module

public import CFSG.CGT.Stroth77.Stroth32Cent
public import CFSG.CGT.Stroth77.Stroth32H1

public section

namespace CFSG.CGT.Stroth77

open Stroth42Core Stroth32H1

namespace Stroth32Par

variable {m : ℕ}

theorem t100_cent_mod_two (hm : 1 ≤ m)
    (θ : Torus (StrothTypeIndex.t100 m).k →+ Torus (StrothTypeIndex.t100 m).k)
    (huv : ∀ x, θ ((StrothTypeIndex.t100 m).action.φuv x) =
      (StrothTypeIndex.t100 m).action.φuv (θ x))
    (ht : ∀ x, θ ((StrothTypeIndex.t100 m).action.φt x) =
      (StrothTypeIndex.t100 m).action.φt (θ x))
    (hΩ : ∀ x, x + x = 0 → θ x = x) (x : Torus (StrothTypeIndex.t100 m).k) :
    ∃ y, θ x = x + (y + y) := by
  obtain ⟨⟨α₁, s₁, r₁, ⟨k₁, hk₁⟩, e₁⟩, ⟨α₂, s₂, r₂, ⟨k₂, hk₂⟩, e₂⟩, ⟨α₃, s₃, r₃, ⟨k₃, hk₃⟩, e₃⟩⟩ :=
    Stroth32Cent.images hm θ huv ht hΩ
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hA : Torus.ofInt (StrothTypeIndex.t100 (n + 1)).k ![0, 2 ^ (n + 1), 0] =
      Torus.ofInt _ ![0, 2 ^ n, 0] + Torus.ofInt _ ![0, 2 ^ n, 0] := by
    rw [t100_add_vec, t100_vec_eq_iff]
    exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩
  have hB : Torus.ofInt (StrothTypeIndex.t100 (n + 1)).k ![0, 0, 2 ^ (n + 1)] =
      Torus.ofInt _ ![0, 0, 2 ^ n] + Torus.ofInt _ ![0, 0, 2 ^ n] := by
    rw [t100_add_vec, t100_vec_eq_iff]
    exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩
  obtain ⟨v, rfl⟩ := Torus.exists_ofInt x
  have hx : Torus.ofInt (StrothTypeIndex.t100 (n + 1)).k v =
      (v 1 + v 2 - v 0) • Torus.ofInt _ ![1, 1, 1] + (v 0 - v 2) • Torus.ofInt _ ![1, 1, 0] +
        (v 0 - v 1) • Torus.ofInt _ ![1, 0, 1] := by
    rw [← Torus.ofInt_zsmul, ← Torus.ofInt_zsmul, ← Torus.ofInt_zsmul, ← Torus.ofInt_add,
      ← Torus.ofInt_add]
    congr 1; funext i; fin_cases i <;> simp
  refine ⟨(v 1 + v 2 - v 0) • (k₁ • Torus.ofInt _ ![1, 1, 1] + s₁ • Torus.ofInt _ ![0, 2 ^ n, 0] +
      r₁ • Torus.ofInt _ ![0, 0, 2 ^ n]) +
    (v 0 - v 2) • (k₂ • Torus.ofInt _ ![1, 1, 0] + s₂ • Torus.ofInt _ ![0, 2 ^ n, 0] +
      r₂ • Torus.ofInt _ ![0, 0, 2 ^ n]) +
    (v 0 - v 1) • (k₃ • Torus.ofInt _ ![1, 0, 1] + s₃ • Torus.ofInt _ ![0, 2 ^ n, 0] +
      r₃ • Torus.ofInt _ ![0, 0, 2 ^ n]), ?_⟩
  rw [hx, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, e₁, e₂, e₃, hk₁, hk₂, hk₃, hA, hB]
  module

theorem t100_cent_par (hm : 1 ≤ m)
    (θ : Torus (StrothTypeIndex.t100 m).k →+ Torus (StrothTypeIndex.t100 m).k)
    (huv : ∀ x, θ ((StrothTypeIndex.t100 m).action.φuv x) =
      (StrothTypeIndex.t100 m).action.φuv (θ x))
    (ht : ∀ x, θ ((StrothTypeIndex.t100 m).action.φt x) =
      (StrothTypeIndex.t100 m).action.φt (θ x))
    (hΩ : ∀ x, x + x = 0 → θ x = x) (v w : Fin 3 → ℤ)
    (h : θ (Torus.ofInt (StrothTypeIndex.t100 m).k v) = Torus.ofInt _ w) (i : Fin 3) :
    ((w i : ℤ) : ZMod 2) = ((v i : ℤ) : ZMod 2) := by
  obtain ⟨y, hy⟩ := t100_cent_mod_two hm θ huv ht hΩ (Torus.ofInt _ v)
  obtain ⟨u, rfl⟩ := Torus.exists_ofInt y
  rw [hy, ← Torus.ofInt_add, ← Torus.ofInt_add, t100_ofInt_eq_iff] at h
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  have h2 : ∀ j : ℕ, 1 ≤ j → (2 : ℤ) ∣ 2 ^ j := fun j hj => dvd_pow_self 2 (by omega)
  obtain ⟨h0, h1, h2'⟩ := h
  simp only [Pi.add_apply] at h0 h1 h2'
  fin_cases i
  · obtain ⟨c, hc⟩ := dvd_trans (h2 m hm) h0
    exact ⟨-c - u 0, by push_cast; linear_combination -hc⟩
  · obtain ⟨c, hc⟩ := dvd_trans (h2 (m + 1) (by omega)) h1
    exact ⟨-c - u 1, by push_cast; linear_combination -hc⟩
  · obtain ⟨c, hc⟩ := dvd_trans (h2 (m + 1) (by omega)) h2'
    exact ⟨-c - u 2, by push_cast; linear_combination -hc⟩

@[expose] def t100RhoPar (p : ZMod 2 × ZMod 2 × ZMod 2) : ZMod 2 × ZMod 2 × ZMod 2 :=
  (p.2.1 + p.2.2, p.1, p.1 + p.2.1)

@[expose] def t100UPar (p : ZMod 2 × ZMod 2 × ZMod 2) : ZMod 2 × ZMod 2 × ZMod 2 :=
  (p.2.1, p.1, p.1 + p.2.1 + p.2.2)

theorem cast_eq_of_eq_add_two_mul {a b : ℤ} (k : ℤ) (h : b = a + 2 * k) :
    ((a : ℤ) : ZMod 2) = ((b : ℤ) : ZMod 2) :=
  (ZMod.intCast_eq_intCast_iff_dvd_sub a b 2).2 ⟨k, by push_cast; linear_combination h⟩

end Stroth32Par

open Stroth32Par

namespace StrothWeakTypeData

section Def

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t100 m))

@[expose] noncomputable def t100Par (e : G) : ZMod 2 × ZMod 2 × ZMod 2 :=
  (ZMod.cast (crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹) 1),
    ZMod.cast (crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹) 2),
    ZMod.cast (crdT dD.e (e⁻¹ * dD.t * e * dD.t⁻¹) 0))

theorem t100Par_eq (hm : 1 ≤ m) {e : G} {x y : Fin 3 → ℤ}
    (hx : crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹) = Torus.ofInt _ x)
    (hy : crdT dD.e (e⁻¹ * dD.t * e * dD.t⁻¹) = Torus.ofInt _ y) :
    dD.t100Par e = (((x 1 : ℤ) : ZMod 2), ((x 2 : ℤ) : ZMod 2), ((y 0 : ℤ) : ZMod 2)) := by
  have hd : ∀ i : Fin 3, 2 ∣ 2 ^ (StrothTypeIndex.t100 m).k i := fun i =>
    dvd_pow_self 2 (by have := t100_one_le_k hm i; omega)
  rw [t100Par, hx, hy, Torus.ofInt_apply, Torus.ofInt_apply, Torus.ofInt_apply,
    ZMod.cast_intCast (hd 1), ZMod.cast_intCast (hd 2), ZMod.cast_intCast (hd 0)]

theorem t100Par_one : dD.t100Par (1 : G) = 0 := by
  rw [t100Par, show (1 : G)⁻¹ * dD.uv * 1 * dD.uv⁻¹ = 1 by group,
    show (1 : G)⁻¹ * dD.t * 1 * dD.t⁻¹ = 1 by group, crdT_one]
  simp

end Def

end StrothWeakTypeData

namespace StrothFrame.IsD

section Generic

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
  {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem proj_rho_mem_R1 (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) {e : G}
    (he : e ∈ hS.R1 dD.uv dD.t) : hS.proj dD.ρ e ∈ hS.R1 dD.uv dD.t :=
  ⟨hS.proj_mem dD.ρ_mem he.1, (h.cocycle_proj_rho hS he.1 he.2.1 he.2.2).1,
    (h.cocycle_proj_rho hS he.1 he.2.1 he.2.2).2.1⟩

theorem conj_u_mem_R1 (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) {e : G}
    (he : e ∈ hS.R1 dD.uv dD.t) : dD.u⁻¹ * e * dD.u ∈ hS.R1 dD.uv dD.t :=
  ⟨h.conj_u_mem_R hS he.1, (cocycle_conj_u hS he.2.1 he.2.2).1,
    (cocycle_conj_u hS he.2.1 he.2.2).2.1⟩

end Generic

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
  {dD : StrothWeakTypeData D (.t100 m)}

theorem t100Par_mul (hS : Local.Setting (F.S : Subgroup G) D) (hm : 1 ≤ m) {e f : G}
    (he : e ∈ hS.R1 dD.uv dD.t) (hf : f ∈ hS.R1 dD.uv dD.t) :
    dD.t100Par (e * f) = dD.t100Par e + dD.t100Par f := by
  obtain ⟨-, heuv, het⟩ := he
  obtain ⟨hfR, hfuv, hft⟩ := hf
  have hfN := hS.R_le_normalizer hfR
  have cuv : ∀ x, dD.thetaT hfN ((StrothTypeIndex.t100 m).action.φuv x) =
      (StrothTypeIndex.t100 m).action.φuv (dD.thetaT hfN x) := fun x => by
    have := dD.thetaT_comm_of_conj_mem hfN dD.uv_mem hfuv x
    rwa [dD.thetaT_uv, dD.thetaT_uv] at this
  have ct : ∀ x, dD.thetaT hfN ((StrothTypeIndex.t100 m).action.φt x) =
      (StrothTypeIndex.t100 m).action.φt (dD.thetaT hfN x) := fun x => by
    have := dD.thetaT_comm_of_conj_mem hfN dD.t_mem hft x
    rwa [dD.thetaT_t, dD.thetaT_t] at this
  have cΩ : ∀ x, x + x = 0 → dD.thetaT hfN x = x := fun x hx =>
    dD.thetaT_of_two hfN (hS.R_le_centralizer_omega hfR) hx
  obtain ⟨-, muv⟩ := dD.crdT_cocycle_mul hfN heuv hfuv
  obtain ⟨-, mt⟩ := dD.crdT_cocycle_mul hfN het hft
  obtain ⟨x, hx⟩ := Torus.exists_ofInt (crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹))
  obtain ⟨y, hy⟩ := Torus.exists_ofInt (crdT dD.e (e⁻¹ * dD.t * e * dD.t⁻¹))
  obtain ⟨x', hx'⟩ := Torus.exists_ofInt (crdT dD.e (f⁻¹ * dD.uv * f * dD.uv⁻¹))
  obtain ⟨y', hy'⟩ := Torus.exists_ofInt (crdT dD.e (f⁻¹ * dD.t * f * dD.t⁻¹))
  obtain ⟨xθ, hxθ⟩ := Torus.exists_ofInt (dD.thetaT hfN (Torus.ofInt _ x))
  obtain ⟨yθ, hyθ⟩ := Torus.exists_ofInt (dD.thetaT hfN (Torus.ofInt _ y))
  have px := t100_cent_par hm _ cuv ct cΩ x xθ hxθ.symm
  have py := t100_cent_par hm _ cuv ct cΩ y yθ hyθ.symm
  rw [← hx, ← hxθ, ← hx', ← Torus.ofInt_add] at muv
  rw [← hy, ← hyθ, ← hy', ← Torus.ofInt_add] at mt
  rw [dD.t100Par_eq hm muv mt, dD.t100Par_eq hm hx.symm hy.symm,
    dD.t100Par_eq hm hx'.symm hy'.symm]
  simp only [Pi.add_apply, Int.cast_add, px, py, Prod.mk_add_mk]

theorem t100Par_inv (hS : Local.Setting (F.S : Subgroup G) D) (hm : 1 ≤ m) {e : G}
    (he : e ∈ hS.R1 dD.uv dD.t) : dD.t100Par e⁻¹ = dD.t100Par e := by
  have h := t100Par_mul hS hm he (inv_mem he)
  rw [mul_inv_cancel, dD.t100Par_one] at h
  have h2 : ∀ p : ZMod 2 × ZMod 2 × ZMod 2, -p = p := by decide
  rw [← h2 (dD.t100Par e)]
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem t100Par_eq_zero_iff (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    (hm : 1 ≤ m) {e : G} (he : e ∈ hS.R1 dD.uv dD.t) : dD.t100Par e = 0 ↔ e ∈ D := by
  obtain ⟨x, hx⟩ := Torus.exists_ofInt (crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹))
  obtain ⟨y, hy⟩ := Torus.exists_ofInt (crdT dD.e (e⁻¹ * dD.t * e * dD.t⁻¹))
  rw [dD.t100Par_eq hm hx.symm hy.symm]
  have hev : ∀ z : ℤ, ((z : ℤ) : ZMod 2) = 0 ↔ Even z := fun z => by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, even_iff_two_dvd]
    norm_num
  constructor
  · intro h0
    simp only [Prod.mk_eq_zero, hev] at h0
    exact h.t100_mem_of_even hS hm he x y hx.symm hy.symm h0.1 h0.2.1 h0.2.2
  · intro hD
    obtain ⟨-, huv, ht⟩ := he
    obtain ⟨c1, c2, c3⟩ := cocycle_uv_t dD.e dD.uv_sq dD.t_sq dD.uv_comm_t dD.uv_mem dD.t_mem
      dD.uv_conj dD.t_conj huv ht
    rw [← hx] at c1
    rw [← hy] at c2
    rw [← hx, ← hy] at c3
    obtain ⟨-, κ₂, κ₃, -, e2, e3⟩ := t100_cocycle_ints x y c1 c2 c3
    obtain ⟨p1, p2, p0, -⟩ := dD.t100_even_of_mem hm hD x y hx.symm hy.symm e2 e3
    simp only [Prod.mk_eq_zero, hev]
    exact ⟨p1, p2, p0⟩

theorem t100Par_mul_inv_mem_iff (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    (hm : 1 ≤ m) {e f : G} (he : e ∈ hS.R1 dD.uv dD.t) (hf : f ∈ hS.R1 dD.uv dD.t) :
    e * f⁻¹ ∈ D ↔ dD.t100Par e = dD.t100Par f := by
  rw [← h.t100Par_eq_zero_iff hS hm (mul_mem he (inv_mem hf)), t100Par_mul hS hm he (inv_mem hf),
    t100Par_inv hS hm hf]
  constructor
  · intro h0
    have h2 : ∀ p q : ZMod 2 × ZMod 2 × ZMod 2, p + q = 0 → p = q := by decide
    exact h2 _ _ h0
  · intro h0
    rw [h0]
    have h2 : ∀ p : ZMod 2 × ZMod 2 × ZMod 2, p + p = 0 := by decide
    exact h2 _

theorem t100Par_proj_rho (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    (hm : 1 ≤ m) {e : G} (he : e ∈ hS.R1 dD.uv dD.t) :
    dD.t100Par (hS.proj dD.ρ e) = t100RhoPar (dD.t100Par e) := by
  obtain ⟨heR, huv, ht⟩ := he
  obtain ⟨-, -, p1, p2⟩ := h.cocycle_proj_rho hS heR huv ht
  obtain ⟨c1, c2, c3⟩ := cocycle_uv_t dD.e dD.uv_sq dD.t_sq dD.uv_comm_t dD.uv_mem dD.t_mem
    dD.uv_conj dD.t_conj huv ht
  obtain ⟨x, hx⟩ := Torus.exists_ofInt (crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹))
  obtain ⟨y, hy⟩ := Torus.exists_ofInt (crdT dD.e (e⁻¹ * dD.t * e * dD.t⁻¹))
  rw [← hx] at c1 p2
  rw [← hy] at c2
  rw [← hx, ← hy] at c3 p1
  obtain ⟨κ₁, κ₂, κ₃, e1, e2, e3⟩ := t100_cocycle_ints x y c1 c2 c3
  rw [t100_φuv, ← Torus.ofInt_add, t100_φρ] at p1
  rw [t100_φρ] at p2
  rw [dD.t100Par_eq hm p1 p2, dD.t100Par_eq hm hx.symm hy.symm, t100RhoPar]
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · rw [← Int.cast_add]
    exact cast_eq_of_eq_add_two_mul (x 2 + y 1 + 2 ^ n * κ₂) (by linear_combination e2)
  · exact cast_eq_of_eq_add_two_mul (-2 ^ n * (κ₂ + κ₃)) (by linear_combination -e2 - e3)
  · rw [← Int.cast_add]
    exact cast_eq_of_eq_add_two_mul (x 2 + 2 ^ n * κ₁) (by linear_combination e1)

theorem t100Par_conj_u (hS : Local.Setting (F.S : Subgroup G) D) (hm : 1 ≤ m) {e : G}
    (he : e ∈ hS.R1 dD.uv dD.t) :
    dD.t100Par (dD.u⁻¹ * e * dD.u) = t100UPar (dD.t100Par e) := by
  obtain ⟨-, huv, ht⟩ := he
  obtain ⟨-, -, p1, p2⟩ := cocycle_conj_u hS huv ht
  obtain ⟨c1, c2, c3⟩ := cocycle_uv_t dD.e dD.uv_sq dD.t_sq dD.uv_comm_t dD.uv_mem dD.t_mem
    dD.uv_conj dD.t_conj huv ht
  obtain ⟨x, hx⟩ := Torus.exists_ofInt (crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹))
  obtain ⟨y, hy⟩ := Torus.exists_ofInt (crdT dD.e (e⁻¹ * dD.t * e * dD.t⁻¹))
  rw [← hx] at c1 p1
  rw [← hy] at c2
  rw [← hx, ← hy] at c3 p2
  obtain ⟨κ₁, κ₂, κ₃, e1, e2, e3⟩ := t100_cocycle_ints x y c1 c2 c3
  rw [t100_φu] at p1
  rw [t100_φuv, ← Torus.ofInt_add, t100_φu] at p2
  rw [dD.t100Par_eq hm p1 p2, dD.t100Par_eq hm hx.symm hy.symm, t100UPar]
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  refine Prod.ext rfl (Prod.ext rfl ?_)
  simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [← Int.cast_add, ← Int.cast_add]
  exact cast_eq_of_eq_add_two_mul (2 ^ n * κ₁ + 2 * y 0 - y 1 - y 2) (by linear_combination e1)

end StrothFrame.IsD

end CFSG.CGT.Stroth77
