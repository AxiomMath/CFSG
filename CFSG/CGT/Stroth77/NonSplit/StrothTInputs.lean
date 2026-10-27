module

public import CFSG.CGT.Stroth77.NonSplit.Model
public import CFSG.CGT.Stroth77.NonSplit.Closure

public section

namespace CFSG.CGT.Stroth77

open Equiv Equiv.Perm

@[expose] def mnsElt (v : Vec6) (σ : Perm (Fin 6)) (h : par v = sg σ) : Mns := (Mns.mk v σ h)⁻¹

@[expose] def mnsX1 : Mns := mnsElt ![0, 0, 1, 0, 1, 0] 1 (by decide)
@[expose] def mnsY1 : Mns := mnsElt ![1, 1, 1, 0, 1, 0] 1 (by decide)
@[expose] def mnsUV : Mns := mnsElt ![1, 1, 1, 1, 0, 0] 1 (by decide)
@[expose] def mnsT : Mns := mnsElt ![1, 0, 0, 1, 0, 0] 1 (by decide)
@[expose] def mnsX : Mns := mnsElt ![1, 0, 1, 0, 1, 1] (swap 0 1 * swap 3 5) (by decide)
@[expose] def mnsY : Mns := mnsElt ![0, 1, 1, 0, 0, 0] (swap 0 1 * swap 2 4) (by decide)
@[expose] def mnsU : Mns :=
  mnsElt ![0, 1, 0, 1, 0, 1] (swap 0 1 * swap 2 3 * swap 4 5) (by decide)
@[expose] def mnsW : Mns :=
  mnsElt ![1, 0, 0, 0, 1, 1] (swap 0 1 * swap 2 4 * swap 3 5) (by decide)
@[expose] def mnsRho : Mns :=
  mnsElt ![0, 0, 0, 1, 1, 0] (swap 0 2 * swap 2 5 * (swap 1 4 * swap 4 3)) (by decide)

structure StrothRel {G : Type*} [Group G] (x1 y1 uv t x y u w : G) : Prop where
  u_sq : u * u = 1
  w_sq : w * w = 1
  x_w : Commute x w
  y_w : Commute y w
  u_w : Commute u w
  x_x1 : Commute x x1
  x_y1 : Commute x y1
  x_y : Commute x y
  y_x1 : Commute y x1
  y_y1 : Commute y y1
  w_x1 : Commute w x1
  w_y1 : Commute w y1
  uv_u : Commute uv u
  x_u : u⁻¹ * x * u = y
  x1_u : u⁻¹ * x1 * u = y1
  uv_x : x⁻¹ * uv * x = y1 * uv
  uv_y : y⁻¹ * uv * y = x1 * uv
  uv_w : w⁻¹ * uv * w = x1 * y1 * uv
  t_x : x⁻¹ * t * x = x1 * t
  t_y : y⁻¹ * t * y = x1 * y1 * t
  t_w : w⁻¹ * t * w = x1 * t
  t_u : u⁻¹ * t * u = uv * t
  x_sq : x * x = x1
  y_sq : y * y = y1

structure StrothRhoRel {G : Type*} [Group G] (x1 y1 uv t x y w u ρ : G) : Prop where
  rho_cube : ρ * ρ * ρ = 1
  x1_rho : ρ⁻¹ * x1 * ρ = y1
  y1_rho : ρ⁻¹ * y1 * ρ = x1 * y1
  x_rho : ρ⁻¹ * x * ρ = y
  y_rho : ρ⁻¹ * y * ρ = (x * y)⁻¹
  w_rho : ρ⁻¹ * w * ρ = w
  uv_rho : ρ⁻¹ * uv * ρ = t
  t_rho : ρ⁻¹ * t * ρ = uv * t
  rho_u : u⁻¹ * ρ * u = ρ⁻¹

structure Stroth21Rel {G : Type*} [Group G] (c a b uv t u ρ : G) : Prop where
  c_uv : uv⁻¹ * c * uv = c⁻¹ ^ 3 * a⁻¹ ^ 2 * b⁻¹ ^ 2
  c_t : t⁻¹ * c * t = c * a ^ 2
  c_u : u⁻¹ * c * u = c
  a_uv : uv⁻¹ * a * uv = c ^ 2 * a * b ^ 2
  a_t : t⁻¹ * a * t = a⁻¹
  a_u : u⁻¹ * a * u = b
  a_rho : ρ⁻¹ * a * ρ = b
  b_rho : ρ⁻¹ * b * ρ = c⁻¹ ^ 2 * a⁻¹ * b⁻¹
  c_rho : ρ⁻¹ * c * ρ = c

@[expose] def gensE : List Mns := [mnsX1, mnsY1, mnsUV, mnsT]
@[expose] def gensT : List Mns := [mnsX1, mnsY1, mnsUV, mnsT, mnsX, mnsY, mnsU, mnsW]
@[expose] def gensA : List Mns := [mnsX1, mnsY1, mnsX, mnsY, mnsW]
@[expose] def gensL : List Mns := [mnsUV, mnsT, mnsU, mnsRho]

@[expose] def Eg : Subgroup Mns := Subgroup.closure {g | g ∈ gensE}
@[expose] def Tg : Subgroup Mns := Subgroup.closure {g | g ∈ gensT}
@[expose] def Ag : Subgroup Mns := Subgroup.closure {g | g ∈ gensA}
@[expose] def Lg : Subgroup Mns := Subgroup.closure {g | g ∈ gensL}

@[expose] def NAg : Subgroup Mns := Subgroup.normalizer (Ag : Set Mns)

@[expose] def normB (g : Mns) : Bool :=
  gensA.all fun a => decide (g * a * g⁻¹ ∈ bfsList gensA 60)

end CFSG.CGT.Stroth77
