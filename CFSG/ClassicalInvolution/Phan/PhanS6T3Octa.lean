module

public import CFSG.ClassicalInvolution.Phan.PhanS6T2Co

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.T

variable {K : Type} [Field K] {M : Model K}

namespace Gd

variable (g : Gd M)

@[expose] def Ffc (x : Co K) : Prop := g.bfc x x = 0 ∧ g.herc x x ≠ 0

@[expose] def Colc (x y : Co K) : Prop := g.bfc x y = 0 ∧ g.gramc x y ≠ 0

@[expose] def Geomc (x y z : Co K) : Prop :=
  g.Colc x y ∧ g.Colc y z ∧ g.Colc z x ∧ g.det3c x y z ≠ 0

theorem Colc.symm {g : Gd M} {x y : Co K} (h : g.Colc x y) : g.Colc y x :=
  ⟨by rw [bfc_comm]; exact h.1, by rw [gramc_comm]; exact h.2⟩

structure Hyp (g : Gd M) (α β w u : K) : Prop where
  na_ne : g.na ≠ 0
  nb_ne : g.nb ≠ 0
  D_ne : g.D ≠ 0
  α_ne : α ≠ 0
  β_ne : β ≠ 0
  nc_ne : g.nc α β ≠ 0
  ζ_ne : g.ζ ≠ 0
  w_ne : M.τ w ≠ w
  F1 : nrm M β * g.D * g.nf w + g.na ≠ 0
  F2 : nrm M α * g.D * g.nf w + g.nb ≠ 0
  U1 : g.nb * (u * M.τ u) + g.D * (nrm M α * g.D * g.nf w + g.nb) ≠ 0
  U2 : g.na * (u * M.τ u) + g.D * (nrm M β * g.D * g.nf w + g.na) ≠ 0
  U3 : u * M.τ u + g.D ≠ 0
  U4 : g.D * g.nf w * g.nc α β + g.D + u * M.τ u ≠ 0
  U5 : nrm M (M.τ α * u + (α * g.h + β * g.nb)) + nrm M α * g.D * g.nf w * g.nc α β ≠ 0
  U6 : nrm M (M.τ β * u - (α * g.na + β * M.τ g.h)) + nrm M β * g.D * g.nf w * g.nc α β ≠ 0

variable {g : Gd M} {α β w u : K}

theorem Hyp.nf_ne (H : Hyp g α β w u) : g.nf w ≠ 0 := by
  have h2 : (w - M.τ w) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (sub_ne_zero.2 fun h => H.w_ne h.symm)
  simp only [nf]
  exact neg_ne_zero.2 (mul_ne_zero (mul_ne_zero M.two_ne H.ζ_ne) h2)

theorem Hyp.nα (H : Hyp g α β w u) : nrm M α ≠ 0 := norm_ne_zero M H.α_ne

theorem Hyp.nβ (H : Hyp g α β w u) : nrm M β ≠ 0 := norm_ne_zero M H.β_ne

structure Octa (g : Gd M) (α β w u : K) : Prop where
  ff1 : g.Ffc (g.vp1 α w u)
  ff2 : g.Ffc (g.vp2 β w u)
  ff3 : g.Ffc (g.vp3 w)
  t1 : g.Geomc vb (g.vp3 w) (g.vp1 α w u)
  t2 : g.Geomc (g.vp3 w) (g.vp2 β w u) (g.vp1 α w u)
  t3 : g.Geomc (g.vp2 β w u) (vc α β) (g.vp1 α w u)
  t4 : g.Geomc vb (vc α β) (g.vp1 α w u)
  t5 : g.Geomc vb (g.vp3 w) va
  t6 : g.Geomc (g.vp3 w) (g.vp2 β w u) va
  t7 : g.Geomc (g.vp2 β w u) (vc α β) va

theorem Hyp.col_ab (H : Hyp g α β w u) : g.Colc va vb :=
  ⟨bfc_ab g, by rw [gramc_ab]; exact H.D_ne⟩

theorem Hyp.col_ac (H : Hyp g α β w u) : g.Colc va (vc α β) :=
  ⟨bfc_ac g α β, by rw [gramc_ac]; exact mul_ne_zero H.nβ H.D_ne⟩

theorem Hyp.col_bc (H : Hyp g α β w u) : g.Colc vb (vc α β) :=
  ⟨bfc_bc g α β, by rw [gramc_bc]; exact mul_ne_zero H.nα H.D_ne⟩

theorem Hyp.col_ap2 (H : Hyp g α β w u) : g.Colc va (g.vp2 β w u) :=
  ⟨bfc_ap2 g β w u, by
    rw [gramc_ap2]; exact mul_ne_zero (mul_ne_zero H.na_ne H.D_ne) H.F1⟩

theorem Hyp.col_ap3 (H : Hyp g α β w u) : g.Colc va (g.vp3 w) :=
  ⟨bfc_ap3 g w, by rw [gramc_ap3]; exact mul_ne_zero H.na_ne H.nf_ne⟩

theorem Hyp.col_bp1 (H : Hyp g α β w u) : g.Colc vb (g.vp1 α w u) :=
  ⟨bfc_bp1 g α w u, by
    rw [gramc_bp1]; exact mul_ne_zero (mul_ne_zero H.nb_ne H.D_ne) H.F2⟩

theorem Hyp.col_bp3 (H : Hyp g α β w u) : g.Colc vb (g.vp3 w) :=
  ⟨bfc_bp3 g w, by rw [gramc_bp3]; exact mul_ne_zero H.nb_ne H.nf_ne⟩

theorem Hyp.col_cp1 (H : Hyp g α β w u) : g.Colc (vc α β) (g.vp1 α w u) :=
  ⟨bfc_cp1 g α β w u, by rw [gramc_cp1]; exact mul_ne_zero H.D_ne H.U5⟩

theorem Hyp.col_cp2 (H : Hyp g α β w u) : g.Colc (vc α β) (g.vp2 β w u) :=
  ⟨bfc_cp2 g α β w u, by rw [gramc_cp2]; exact mul_ne_zero H.D_ne H.U6⟩

theorem Hyp.col_p1p2 (H : Hyp g α β w u) : g.Colc (g.vp1 α w u) (g.vp2 β w u) :=
  ⟨bfc_p1p2 g α β w u, by
    rw [gramc_p1p2]; exact mul_ne_zero (mul_ne_zero H.D_ne H.U3) H.U4⟩

theorem Hyp.col_p1p3 (H : Hyp g α β w u) : g.Colc (g.vp1 α w u) (g.vp3 w) :=
  ⟨bfc_p1p3 g α w u, by
    rw [gramc_p1p3]; exact mul_ne_zero (mul_ne_zero H.nb_ne H.nf_ne) H.U3⟩

theorem Hyp.col_p2p3 (H : Hyp g α β w u) : g.Colc (g.vp2 β w u) (g.vp3 w) :=
  ⟨bfc_p2p3 g β w u, by
    rw [gramc_p2p3]; exact mul_ne_zero (mul_ne_zero H.na_ne H.nf_ne) H.U3⟩

theorem octa_co (H : Hyp g α β w u) : Octa g α β w u where
  ff1 := ⟨bfc_p1p1 g α w u, by rw [herc_p1]; exact H.U1⟩
  ff2 := ⟨bfc_p2p2 g β w u, by rw [herc_p2]; exact H.U2⟩
  ff3 := ⟨bfc_p3p3 g w, by rw [herc_p3]; exact H.nf_ne⟩
  t1 := ⟨H.col_bp3, H.col_p1p3.symm, H.col_bp1.symm, by
    rw [det3c_bp3p1]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 H.nb_ne) H.nf_ne) H.D_ne⟩
  t2 := ⟨H.col_p2p3.symm, H.col_p1p2.symm, H.col_p1p3, by
    rw [det3c_p3p2p1]
    exact mul_ne_zero (mul_ne_zero H.nf_ne H.D_ne) (pow_ne_zero 2 H.U3)⟩
  t3 := ⟨H.col_cp2.symm, H.col_cp1, H.col_p1p2, by
    rw [det3c_p2cp1]
    exact mul_ne_zero (mul_ne_zero H.nf_ne (pow_ne_zero 3 H.D_ne))
      (pow_ne_zero 2 H.nc_ne)⟩
  t4 := ⟨H.col_bc, H.col_cp1, H.col_bp1.symm, by
    rw [det3c_bcp1]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 H.nα) H.nf_ne) (pow_ne_zero 3 H.D_ne)⟩
  t5 := ⟨H.col_bp3, H.col_ap3.symm, H.col_ab, by
    rw [det3c_bp3a]
    exact mul_ne_zero H.nf_ne H.D_ne⟩
  t6 := ⟨H.col_p2p3.symm, H.col_ap2.symm, H.col_ap3, by
    rw [det3c_p3p2a]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 H.na_ne) H.nf_ne) H.D_ne⟩
  t7 := ⟨H.col_cp2.symm, H.col_ac.symm, H.col_ap2, by
    rw [det3c_p2ca]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 H.nβ) H.nf_ne) (pow_ne_zero 3 H.D_ne)⟩

end Gd

end CFSG.ClassicalInvolution.PhanB3.S.Std.T
