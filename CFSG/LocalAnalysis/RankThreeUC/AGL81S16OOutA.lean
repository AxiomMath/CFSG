module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16ORad

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.Open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus nondegenerate_polarBilin_quadMinus_of_finite
  quadMinus_apply polar_quadMinus)

namespace OutLin

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

abbrev GL6 (F : Type) [Field F] : Type := GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F

@[expose] def Nf (b c x y : F) : F := x ^ 2 + b * x * y + c * y ^ 2

@[expose] def tc (g : GL6 F) : F := gv g (eV F idx1) (Sum.inl idx0)

@[expose] def rho (g : GL6 F) : Matrix (Fin 2) (Fin 2) F :=
  Matrix.of fun k j => gv g (nVec F j) (Sum.inr (Sum.inr k))

@[expose] def mcol (g : GL6 F) (i : Fin (3 - 1)) (k : Fin 2) : F :=
  gv g (fV F i) (Sum.inr (Sum.inr k))

theorem rho_apply (g : GL6 F) (k j : Fin 2) :
    rho g k j = gv g (nVec F j) (Sum.inr (Sum.inr k)) := rfl

structure PEl (b c : F) (g : GL6 F) : Prop where
  iso : ∀ v : OW F, quadMinus 3 F b c (gv g v) = quadMinus 3 F b c v
  fix0 : gv g (eV F idx0) = eV F idx0
  shift : gv g (eV F idx1) = eV F idx1 + tc g • eV F idx0

theorem PEl.mk' {g : GL6 F} (hiso : ∀ v : OW F, quadMinus 3 F b c (gv g v) = quadMinus 3 F b c v)
    (hfix : gv g (eV F idx0) = eV F idx0) {t : F}
    (hsh : gv g (eV F idx1) = eV F idx1 + t • eV F idx0) : PEl b c g := by
  refine ⟨hiso, hfix, ?_⟩
  have hne : idx0 ≠ idx1 := by decide
  have htc : tc g = t := by
    have := congrFun hsh (Sum.inl idx0)
    simpa [tc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, eV_self, eV_ne (i := idx1) (k := idx0) hne]
      using this
  rw [htc]
  exact hsh

theorem fV_inl (i j : Fin (3 - 1)) : fV F i (Sum.inl j) = 0 := by
  simp [Pi.single_apply]

theorem fV_self (i : Fin (3 - 1)) : fV F i (Sum.inr (Sum.inl i)) = 1 := by simp

theorem fV_ne {i k : Fin (3 - 1)} (hk : k ≠ i) : fV F i (Sum.inr (Sum.inl k)) = 0 := by
  simp [Pi.single_apply, hk]

theorem fV_inr_inr (i : Fin (3 - 1)) (j : Fin 2) : fV F i (Sum.inr (Sum.inr j)) = 0 := by
  simp [Pi.single_apply]

theorem tc_one : tc (1 : GL6 F) = 0 := by
  rw [tc, gv_one]
  exact eV_ne (i := idx1) (k := idx0) (by decide)

theorem PEl.y0 {g : GL6 F} (h : PEl b c g) (x : OW F) :
    gv g x (Sum.inr (Sum.inl idx0)) = x (Sum.inr (Sum.inl idx0)) :=
  gv_apply_y0 h.iso h.fix0 x

theorem PEl.y1 {g : GL6 F} (h : PEl b c g) (x : OW F) :
    gv g x (Sum.inr (Sum.inl idx1)) =
      x (Sum.inr (Sum.inl idx1)) + tc g * x (Sum.inr (Sum.inl idx0)) := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h1 := polar_gv h.iso x (eV F idx1)
  rw [h.shift, polar_add_right, polar_smul_right_eq, polar_e_right, polar_e_right,
    polar_e_right, h.y0 x] at h1
  linear_combination h1 - tc g * x (Sum.inr (Sum.inl idx0)) * h2

theorem PEl.coordN {g : GL6 F} (h : PEl b c g) (x : OW F) (k : Fin 2) :
    gv g x (Sum.inr (Sum.inr k)) =
      rho g k 0 * x (Sum.inr (Sum.inr 0)) + rho g k 1 * x (Sum.inr (Sum.inr 1)) +
      (mcol g idx0 k * x (Sum.inr (Sum.inl idx0)) + mcol g idx1 k * x (Sum.inr (Sum.inl idx1))) := by
  rw [gv_apply_decomp, h.fix0, h.shift]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, eV_inr, mul_zero, add_zero, rho_apply, mcol]
  ring

theorem tc_mul {g h : GL6 F} (hg : PEl b c g) (hh : PEl b c h) :
    gv (g * h) (eV F idx1) = eV F idx1 + (tc g + tc h) • eV F idx0 := by
  rw [gv_mul, hh.shift, gv_add, gv_smul, hg.shift, hg.fix0, add_smul]
  abel

theorem tc_mul_eq {g h : GL6 F} (hg : PEl b c g) (hh : PEl b c h) :
    tc (g * h) = tc g + tc h := by
  have hne : idx0 ≠ idx1 := by decide
  have := congrFun (tc_mul hg hh) (Sum.inl idx0)
  simpa [tc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, eV_self, eV_ne (i := idx1) (k := idx0) hne]
    using this

theorem PEl.mul {g h : GL6 F} (hg : PEl b c g) (hh : PEl b c h) : PEl b c (g * h) := by
  refine ⟨fun v => by rw [gv_mul, hg.iso, hh.iso], by rw [gv_mul, hh.fix0, hg.fix0], ?_⟩
  rw [tc_mul hg hh, tc_mul_eq hg hh]

theorem rho_one : rho (1 : GL6 F) = 1 := by
  ext k j
  rw [rho_apply, gv_one]
  simp only [nVec, Pi.single_apply, Matrix.one_apply]
  by_cases hkj : k = j
  · subst hkj
    simp
  · simp [hkj, Ne.symm hkj]

theorem rho_mul {g h : GL6 F} (hg : PEl b c g) (hh : PEl b c h) :
    rho (g * h) = rho g * rho h := by
  ext k j
  rw [rho_apply, gv_mul, hg.coordN, Matrix.mul_apply, Fin.sum_univ_two]
  have hy : ∀ i : Fin (3 - 1), gv h (nVec F j) (Sum.inr (Sum.inl i)) = 0 := by
    intro i
    have hi : ∀ i : Fin (3 - 1), i = idx0 ∨ i = idx1 := by decide
    rcases hi i with rfl | rfl
    · rw [hh.y0, nVec_inr_inl]
    · rw [hh.y1, nVec_inr_inl, nVec_inr_inl]; ring
  rw [hy idx0, hy idx1]
  simp only [rho_apply]
  ring

end OutLin

end CFSG.LocalAnalysis.RankThreeUC
