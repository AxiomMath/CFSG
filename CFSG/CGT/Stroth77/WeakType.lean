module

public import Mathlib.Tactic.Group
public import CFSG.CGT.Stroth77.TypePredicates

public section

namespace CFSG.CGT.Stroth77

section Group

variable {S : Type*} [Group S]

structure StrothWeakTypeData (B : Subgroup S) (τ : StrothTypeIndex) where
  e : Additive B ≃+ Torus τ.k
  uv : S
  t : S
  u : S
  ρ : S
  uv_sq : uv * uv = 1
  t_sq : t * t = 1
  uv_comm_t : uv * t = t * uv
  rho_odd : Odd (orderOf ρ)
  u_sq : u * u = 1
  u_rho : u * ρ * u * ρ = 1
  uv_rho : uv * ρ = ρ * t
  t_rho : t * ρ = ρ * uv * t
  uv_comm_u : uv * u = u * uv
  t_u : t * u = u * uv * t
  uv_mem : uv ∈ Subgroup.normalizer B
  t_mem : t ∈ Subgroup.normalizer B
  u_mem : u ∈ Subgroup.normalizer B
  ρ_mem : ρ ∈ Subgroup.normalizer B
  uv_conj : ∀ x : B,
    e (Additive.ofMul (conjBy uv_mem x)) = τ.action.φuv (e (Additive.ofMul x))
  t_conj : ∀ x : B,
    e (Additive.ofMul (conjBy t_mem x)) = τ.action.φt (e (Additive.ofMul x))
  u_conj : ∀ x : B,
    e (Additive.ofMul (conjBy u_mem x)) = τ.action.φu (e (Additive.ofMul x))
  ρ_conj : ∀ x : B,
    e (Additive.ofMul (conjBy ρ_mem x)) = τ.action.φρ (e (Additive.ofMul x))

@[expose] def HasStrothWeakType (B : Subgroup S) (τ : StrothTypeIndex) : Prop :=
  Nonempty (StrothWeakTypeData B τ)

variable {B : Subgroup S} {τ : StrothTypeIndex}

@[expose] def StrothTypeData.toWeak (D : StrothTypeData B τ) : StrothWeakTypeData B τ where
  e := D.e
  uv := D.uv
  t := D.t
  u := D.u
  ρ := D.ρ
  uv_sq := D.uv_sq
  t_sq := D.t_sq
  uv_comm_t := D.uv_comm_t
  rho_odd := Odd.of_dvd_nat (by decide) D.orderOf_ρ_dvd_three
  u_sq := D.u_sq
  u_rho := D.u_rho
  uv_rho := D.uv_rho
  t_rho := D.t_rho
  uv_comm_u := D.uv_comm_u
  t_u := D.t_u
  uv_mem := D.uv_mem
  t_mem := D.t_mem
  u_mem := D.u_mem
  ρ_mem := D.ρ_mem
  uv_conj := D.uv_conj
  t_conj := D.t_conj
  u_conj := D.u_conj
  ρ_conj := D.ρ_conj

namespace StrothWeakTypeData

@[expose] def c (D : StrothWeakTypeData B τ) : B := Additive.toMul (D.e.symm Torus.c)

@[expose] def a (D : StrothWeakTypeData B τ) : B := Additive.toMul (D.e.symm Torus.a)

@[expose] def b (D : StrothWeakTypeData B τ) : B := Additive.toMul (D.e.symm Torus.b)

@[expose] def cab (D : StrothWeakTypeData B τ) : S := (D.c : S) * D.a * D.b

@[expose] def L (D : StrothWeakTypeData B τ) : Subgroup S :=
  Subgroup.closure ({D.uv, D.t, D.u, D.ρ} : Set S)

@[expose] def IsMinimalLModule (D : StrothWeakTypeData B τ) (C : Subgroup S) : Prop :=
  B < C ∧ D.L ≤ Subgroup.normalizer C ∧
    ∀ E : Subgroup S, B < E → E < C → D.L ≤ Subgroup.normalizer E → False

theorem uv_mem_L (D : StrothWeakTypeData B τ) : D.uv ∈ D.L :=
  Subgroup.subset_closure (by simp)

theorem t_mem_L (D : StrothWeakTypeData B τ) : D.t ∈ D.L :=
  Subgroup.subset_closure (by simp)

theorem u_mem_L (D : StrothWeakTypeData B τ) : D.u ∈ D.L :=
  Subgroup.subset_closure (by simp)

theorem ρ_mem_L (D : StrothWeakTypeData B τ) : D.ρ ∈ D.L :=
  Subgroup.subset_closure (by simp)

theorem L_le_normalizer (D : StrothWeakTypeData B τ) : D.L ≤ Subgroup.normalizer B := by
  rw [L, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  exacts [D.uv_mem, D.t_mem, D.u_mem, D.ρ_mem]

theorem isMulCommutative (D : StrothWeakTypeData B τ) : IsMulCommutative B := by
  refine IsMulCommutative.of_comm fun x y => ?_
  apply Additive.ofMul.injective
  apply D.e.injective
  simp only [ofMul_mul, map_add]
  exact add_comm _ _

theorem card (D : StrothWeakTypeData B τ) : Nat.card B = 2 ^ (τ.k 0 + τ.k 1 + τ.k 2) := by
  calc Nat.card B = Nat.card (Additive B) := Nat.card_congr Additive.ofMul
    _ = Nat.card (Torus τ.k) := Nat.card_congr D.e.toEquiv
    _ = 2 ^ (τ.k 0 + τ.k 1 + τ.k 2) := natCard_torus τ.k

theorem conj_apply (D : StrothWeakTypeData B τ) {g : S} (hg : g ∈ Subgroup.normalizer B)
    {φ : Torus τ.k →+ Torus τ.k}
    (hconj : ∀ x : B, D.e (Additive.ofMul (conjBy hg x)) = φ (D.e (Additive.ofMul x)))
    (y : Torus τ.k) :
    D.e (Additive.ofMul (conjBy hg (Additive.toMul (D.e.symm y)))) = φ y := by
  rw [hconj, ofMul_toMul, AddEquiv.apply_symm_apply]

theorem rho_cube_mem (D : StrothWeakTypeData B τ) :
    D.ρ ^ 3 ∈ Subgroup.centralizer (B : Set S) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h3 := τ.action.rels.rho_cube
  have key : D.e (Additive.ofMul (conjBy D.ρ_mem (conjBy D.ρ_mem (conjBy D.ρ_mem ⟨x, hx⟩)))) =
      D.e (Additive.ofMul ⟨x, hx⟩) := by
    rw [D.ρ_conj, D.ρ_conj, D.ρ_conj]
    exact DFunLike.congr_fun h3 _
  have key' := congrArg (fun y : B => (y : S)) (Additive.ofMul.injective (D.e.injective key))
  simp only [conjBy] at key'
  rw [pow_three]
  calc x * (D.ρ * (D.ρ * D.ρ))
      = D.ρ * (D.ρ * D.ρ) * (D.ρ⁻¹ * (D.ρ⁻¹ * (D.ρ⁻¹ * x * D.ρ) * D.ρ) * D.ρ) := by group
    _ = D.ρ * (D.ρ * D.ρ) * x := by rw [key']

end StrothWeakTypeData

end Group

end CFSG.CGT.Stroth77
