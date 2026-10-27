module

public import CFSG.CGT.Stroth77.TorusMat

public section

namespace CFSG.CGT.Stroth77

open Matrix

structure SigmaFourRels {A : Type*} [AddCommGroup A] (uv t u ρ : A →+ A) : Prop where
  uv_sq : uv.comp uv = AddMonoidHom.id A
  t_sq : t.comp t = AddMonoidHom.id A
  uv_comm_t : t.comp uv = uv.comp t
  rho_cube : ρ.comp (ρ.comp ρ) = AddMonoidHom.id A
  u_sq : u.comp u = AddMonoidHom.id A
  u_rho : ρ.comp (u.comp (ρ.comp u)) = AddMonoidHom.id A
  uv_rho : ρ.comp uv = t.comp ρ
  t_rho : ρ.comp t = t.comp (uv.comp ρ)
  uv_comm_u : u.comp uv = uv.comp u
  t_u : u.comp t = t.comp (uv.comp u)

structure SigmaFourAction (k : Fin 3 → ℕ) where
  uv : IntMat
  t : IntMat
  u : IntMat
  ρ : IntMat
  compat_uv : Compat k uv
  compat_t : Compat k t
  compat_u : Compat k u
  compat_ρ : Compat k ρ
  rels : SigmaFourRels (matAct k uv compat_uv) (matAct k t compat_t) (matAct k u compat_u)
    (matAct k ρ compat_ρ)

namespace SigmaFourAction

variable {k : Fin 3 → ℕ} (S : SigmaFourAction k)

abbrev φuv : Torus k →+ Torus k := matAct k S.uv S.compat_uv
abbrev φt : Torus k →+ Torus k := matAct k S.t S.compat_t
abbrev φu : Torus k →+ Torus k := matAct k S.u S.compat_u
abbrev φρ : Torus k →+ Torus k := matAct k S.ρ S.compat_ρ

theorem relsOfMatEq {uv t u ρ : IntMat} (hUv : Compat k uv) (hT : Compat k t)
    (hU : Compat k u) (hR : Compat k ρ)
    (h1 : MatEq k (uv * uv) 1) (h2 : MatEq k (t * t) 1) (h3 : MatEq k (t * uv) (uv * t))
    (h4 : MatEq k (ρ * (ρ * ρ)) 1) (h5 : MatEq k (u * u) 1)
    (h6 : MatEq k (ρ * (u * (ρ * u))) 1) (h7 : MatEq k (ρ * uv) (t * ρ))
    (h8 : MatEq k (ρ * t) (t * (uv * ρ))) (h9 : MatEq k (u * uv) (uv * u))
    (h10 : MatEq k (u * t) (t * (uv * u))) :
    SigmaFourRels (matAct k uv hUv) (matAct k t hT) (matAct k u hU) (matAct k ρ hR) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← matAct_mul _ _ hUv hUv, ← matAct_one]; exact matAct_congr _ _ h1
  · rw [← matAct_mul _ _ hT hT, ← matAct_one]; exact matAct_congr _ _ h2
  · rw [← matAct_mul _ _ hT hUv, ← matAct_mul _ _ hUv hT]; exact matAct_congr _ _ h3
  · rw [← matAct_mul _ _ hR hR, ← matAct_mul _ _ hR (hR.mul hR), ← matAct_one]
    exact matAct_congr _ _ h4
  · rw [← matAct_mul _ _ hU hU, ← matAct_one]; exact matAct_congr _ _ h5
  · rw [← matAct_mul _ _ hR hU, ← matAct_mul _ _ hU (hR.mul hU),
      ← matAct_mul _ _ hR (hU.mul (hR.mul hU)), ← matAct_one]
    exact matAct_congr _ _ h6
  · rw [← matAct_mul _ _ hR hUv, ← matAct_mul _ _ hT hR]; exact matAct_congr _ _ h7
  · rw [← matAct_mul _ _ hR hT, ← matAct_mul _ _ hUv hR, ← matAct_mul _ _ hT (hUv.mul hR)]
    exact matAct_congr _ _ h8
  · rw [← matAct_mul _ _ hU hUv, ← matAct_mul _ _ hUv hU]; exact matAct_congr _ _ h9
  · rw [← matAct_mul _ _ hU hT, ← matAct_mul _ _ hUv hU, ← matAct_mul _ _ hT (hUv.mul hU)]
    exact matAct_congr _ _ h10

@[expose] def ofMatEq (uv t u ρ : IntMat) (hUv : Compat k uv) (hT : Compat k t)
    (hU : Compat k u) (hR : Compat k ρ)
    (h1 : MatEq k (uv * uv) 1) (h2 : MatEq k (t * t) 1) (h3 : MatEq k (t * uv) (uv * t))
    (h4 : MatEq k (ρ * (ρ * ρ)) 1) (h5 : MatEq k (u * u) 1)
    (h6 : MatEq k (ρ * (u * (ρ * u))) 1) (h7 : MatEq k (ρ * uv) (t * ρ))
    (h8 : MatEq k (ρ * t) (t * (uv * ρ))) (h9 : MatEq k (u * uv) (uv * u))
    (h10 : MatEq k (u * t) (t * (uv * u))) : SigmaFourAction k :=
  ⟨uv, t, u, ρ, hUv, hT, hU, hR, relsOfMatEq hUv hT hU hR h1 h2 h3 h4 h5 h6 h7 h8 h9 h10⟩

end SigmaFourAction

end CFSG.CGT.Stroth77
