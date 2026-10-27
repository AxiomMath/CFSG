module

public import CFSG.ClassicalInvolution.Phan.PhanS4Std
public import Mathlib

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.T

@[ext] structure Co (K : Type) where
  xa : K
  xb : K
  xA : K
  xB : K
  xf : K
  xz : K
  xr : K

variable {K : Type} [Field K] {M : Model K}

@[expose] def nrm (M : Model K) (x : K) : K := x * M.τ x

structure Gd (M : Model K) where
  na : K
  nb : K
  h : K
  ζ : K
  hna : M.τ na = na
  hnb : M.τ nb = nb
  hζ : M.τ ζ = ζ

@[expose] def Co.cj (M : Model K) (x : Co K) : Co K :=
  ⟨M.τ x.xA, M.τ x.xB, M.τ x.xa, M.τ x.xb, M.τ x.xf, M.τ x.xz, M.τ x.xr⟩

@[expose] def va : Co K := ⟨1, 0, 0, 0, 0, 0, 0⟩

@[expose] def vb : Co K := ⟨0, 1, 0, 0, 0, 0, 0⟩

@[expose] def vc (α β : K) : Co K := ⟨α, β, 0, 0, 0, 0, 1⟩

namespace Gd

variable (g : Gd M)

@[expose] def D : K := g.na * g.nb - g.h * M.τ g.h

@[expose] def nf (w : K) : K := -(2 * g.ζ * (w - M.τ w) ^ 2)

@[expose] def nc (α β : K) : K :=
  α * M.τ α * g.na + α * M.τ β * g.h + M.τ α * β * M.τ g.h + β * M.τ β * g.nb

@[expose] def bfc (x y : Co K) : K :=
  g.na * (x.xa * y.xA + x.xA * y.xa) + g.h * (x.xa * y.xB + x.xB * y.xa) +
    M.τ g.h * (x.xb * y.xA + x.xA * y.xb) + g.nb * (x.xb * y.xB + x.xB * y.xb) +
    (x.xf * y.xr + x.xr * y.xf) + g.ζ * (x.xz * y.xz)

@[expose] def herc (x y : Co K) : K := g.bfc x (Co.cj M y)

@[expose] def gramc (x y : Co K) : K := g.herc x x * g.herc y y - g.herc x y * g.herc y x

@[expose] def det3c (x y z : Co K) : K :=
  g.herc x x * (g.herc y y * g.herc z z - g.herc y z * g.herc z y) -
    g.herc x y * (g.herc y x * g.herc z z - g.herc y z * g.herc z x) +
    g.herc x z * (g.herc y x * g.herc z y - g.herc y y * g.herc z x)

@[expose] def vp3 (w : K) : Co K := ⟨0, 0, 0, 0, 1, 2 * w, -(2 * g.ζ * w ^ 2)⟩

@[expose] def vp1 (α w u : K) : Co K :=
  ⟨0, u, g.nb, -(M.τ g.h), -(α * g.D), -(α * g.D * (2 * w)), α * g.D * (2 * g.ζ * w ^ 2)⟩

@[expose] def vp2 (β w u : K) : Co K :=
  ⟨u, 0, g.h, -g.na, β * g.D, β * g.D * (2 * w), -(β * g.D * (2 * g.ζ * w ^ 2))⟩

theorem bfc_comm (x y : Co K) : g.bfc x y = g.bfc y x := by
  simp only [bfc]
  ring

theorem gramc_comm (x y : Co K) : g.gramc x y = g.gramc y x := by
  simp only [gramc]
  ring

end Gd

macro "co_simp" : tactic =>
  `(tactic| simp only [Gd.bfc, Gd.herc, Gd.gramc, Gd.det3c, Co.cj, va, vb, vc, Gd.vp1, Gd.vp2,
    Gd.vp3, Gd.D, Gd.nf, Gd.nc, nrm, map_neg, map_mul, map_add, map_sub, map_pow, map_ofNat,
    map_one, map_zero, Model.tau_tau, Gd.hna, Gd.hnb, Gd.hζ])

namespace Gd

variable (g : Gd M) (α β w u : K)
theorem bfc_ab :
    g.bfc va vb = 0 := by
  co_simp
  ring

theorem bfc_ac :
    g.bfc va (vc α β) = 0 := by
  co_simp
  ring

theorem bfc_bc :
    g.bfc vb (vc α β) = 0 := by
  co_simp
  ring

theorem bfc_cc :
    g.bfc (vc α β) (vc α β) = 0 := by
  co_simp
  ring

theorem bfc_ap2 :
    g.bfc va (g.vp2 β w u) = 0 := by
  co_simp
  ring

theorem bfc_ap3 :
    g.bfc va (g.vp3 w) = 0 := by
  co_simp
  ring

theorem bfc_bp1 :
    g.bfc vb (g.vp1 α w u) = 0 := by
  co_simp
  ring

theorem bfc_bp3 :
    g.bfc vb (g.vp3 w) = 0 := by
  co_simp
  ring

theorem bfc_cp1 :
    g.bfc (vc α β) (g.vp1 α w u) = 0 := by
  co_simp
  ring

theorem bfc_cp2 :
    g.bfc (vc α β) (g.vp2 β w u) = 0 := by
  co_simp
  ring

theorem bfc_p1p2 :
    g.bfc (g.vp1 α w u) (g.vp2 β w u) = 0 := by
  co_simp
  ring

theorem bfc_p1p3 :
    g.bfc (g.vp1 α w u) (g.vp3 w) = 0 := by
  co_simp
  ring

theorem bfc_p2p3 :
    g.bfc (g.vp2 β w u) (g.vp3 w) = 0 := by
  co_simp
  ring

theorem bfc_p1p1 :
    g.bfc (g.vp1 α w u) (g.vp1 α w u) = 0 := by
  co_simp
  ring

theorem bfc_p2p2 :
    g.bfc (g.vp2 β w u) (g.vp2 β w u) = 0 := by
  co_simp
  ring

theorem bfc_p3p3 :
    g.bfc (g.vp3 w) (g.vp3 w) = 0 := by
  co_simp
  ring

theorem herc_cc :
    g.herc (vc α β) (vc α β) = g.nc α β := by
  co_simp
  ring

theorem herc_p3 :
    g.herc (g.vp3 w) (g.vp3 w) = g.nf w := by
  co_simp
  ring

theorem herc_p1 :
    g.herc (g.vp1 α w u) (g.vp1 α w u) =
      g.nb * (u * M.τ u) + g.D * (nrm M α * g.D * g.nf w + g.nb) := by
  co_simp
  ring

theorem herc_p2 :
    g.herc (g.vp2 β w u) (g.vp2 β w u) =
      g.na * (u * M.τ u) + g.D * (nrm M β * g.D * g.nf w + g.na) := by
  co_simp
  ring

theorem gramc_ab :
    g.gramc va vb =
      g.D := by
  co_simp
  ring

theorem gramc_ac :
    g.gramc va (vc α β) =
      nrm M β * g.D := by
  co_simp
  ring

theorem gramc_bc :
    g.gramc vb (vc α β) =
      nrm M α * g.D := by
  co_simp
  ring

theorem gramc_ap2 :
    g.gramc va (g.vp2 β w u) =
      g.na * g.D * (nrm M β * g.D * g.nf w + g.na) := by
  co_simp
  ring

theorem gramc_ap3 :
    g.gramc va (g.vp3 w) =
      g.na * g.nf w := by
  co_simp
  ring

theorem gramc_bp1 :
    g.gramc vb (g.vp1 α w u) =
      g.nb * g.D * (nrm M α * g.D * g.nf w + g.nb) := by
  co_simp
  ring

theorem gramc_bp3 :
    g.gramc vb (g.vp3 w) =
      g.nb * g.nf w := by
  co_simp
  ring

theorem gramc_cp1 :
    g.gramc (vc α β) (g.vp1 α w u) =
      g.D * (nrm M (M.τ α * u + (α * g.h + β * g.nb)) +
        nrm M α * g.D * g.nf w * g.nc α β) := by
  co_simp
  ring

theorem gramc_cp2 :
    g.gramc (vc α β) (g.vp2 β w u) =
      g.D * (nrm M (M.τ β * u - (α * g.na + β * M.τ g.h)) +
        nrm M β * g.D * g.nf w * g.nc α β) := by
  co_simp
  ring

theorem gramc_p1p2 :
    g.gramc (g.vp1 α w u) (g.vp2 β w u) =
      g.D * (u * M.τ u + g.D) * (g.D * g.nf w * g.nc α β + g.D + u * M.τ u) := by
  co_simp
  ring

theorem gramc_p1p3 :
    g.gramc (g.vp1 α w u) (g.vp3 w) =
      g.nb * g.nf w * (u * M.τ u + g.D) := by
  co_simp
  ring

theorem gramc_p2p3 :
    g.gramc (g.vp2 β w u) (g.vp3 w) =
      g.na * g.nf w * (u * M.τ u + g.D) := by
  co_simp
  ring

theorem det3c_bp3p1 :
    g.det3c vb (g.vp3 w) (g.vp1 α w u) =
      g.nb ^ 2 * g.nf w * g.D := by
  co_simp
  ring

theorem det3c_p3p2p1 :
    g.det3c (g.vp3 w) (g.vp2 β w u) (g.vp1 α w u) =
      g.nf w * g.D * (u * M.τ u + g.D) ^ 2 := by
  co_simp
  ring

theorem det3c_p2cp1 :
    g.det3c (g.vp2 β w u) (vc α β) (g.vp1 α w u) =
      g.nf w * g.D ^ 3 * g.nc α β ^ 2 := by
  co_simp
  ring

theorem det3c_bcp1 :
    g.det3c vb (vc α β) (g.vp1 α w u) =
      nrm M α ^ 2 * g.nf w * g.D ^ 3 := by
  co_simp
  ring

theorem det3c_bp3a :
    g.det3c vb (g.vp3 w) va =
      g.nf w * g.D := by
  co_simp
  ring

theorem det3c_p3p2a :
    g.det3c (g.vp3 w) (g.vp2 β w u) va =
      g.na ^ 2 * g.nf w * g.D := by
  co_simp
  ring

theorem det3c_p2ca :
    g.det3c (g.vp2 β w u) (vc α β) va =
      nrm M β ^ 2 * g.nf w * g.D ^ 3 := by
  co_simp
  ring

end Gd

end CFSG.ClassicalInvolution.PhanB3.S.Std.T
