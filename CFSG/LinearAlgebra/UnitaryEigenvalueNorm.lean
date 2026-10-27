module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UqHeisFrame
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel

public section

namespace CFSG.LinearAlgebra

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel

theorem unitary_eigenvalue_norm_one
    {q f p n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData q f K}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpdvd : p ∣ q ^ f + 1)
    {x : primeFormUnitary h (idGram K n)} {c : Kˣ}
    (hx : (x : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) c)
    (hn : 1 ≤ n) {lam : K} {v : Fin n → K} (hv : v ≠ 0)
    (hlam : ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) v = lam • v) :
    h.bar lam * lam = 1 := by
  classical
  haveI : Fact q.Prime := ⟨h.prime⟩
  haveI : CharP K q := h.charP
  haveI := h.finite
  have hiter : ∀ k : ℕ,
      (((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) ^ k) v = lam ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, hlam, map_smul, ih, smul_smul, pow_succ, mul_comm]
  have hxpow_lin : ((toLinU h n (x ^ p) : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) v = (c : K) • v := by
    rw [toLinU_apply]
    have hx' : (x ^ p : primeFormUnitary h (idGram K n)) =
        ⟨GeneralLinearGroup.scalar (Fin n) c, by rw [← hx]; exact pow_mem x.2 p⟩ :=
      Subtype.ext hx
    rw [hx']
    ext i
    simp [Matrix.GeneralLinearGroup.coe_toLin, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.mulVecLin, Matrix.toLin'_apply]
  have h1 : ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) ^ p = ((toLinU h n (x ^ p) :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) := by
    exact congrArg (fun g : LinearMap.GeneralLinearGroup K (Fin n → K) =>
      (g : Module.End K (Fin n → K))) (map_pow (toLinU h n) x p).symm
  have h2 := hiter p
  rw [h1, hxpow_lin] at h2
  have h3 : ((c : K) - lam ^ p) • v = 0 := by
    rw [sub_smul, h2, sub_self]
  have h4 : (c : K) - lam ^ p = 0 := (smul_eq_zero.mp h3).resolve_right hv
  have hlam_pow : lam ^ p = (c : K) := (sub_eq_zero.mp h4).symm
  have hlam0 : lam ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.pos.ne'] at hlam_pow
    exact c.ne_zero hlam_pow.symm
  let γ : Kˣ := Units.mk0 lam hlam0
  have hγ : (x : GL (Fin n) K) ^ p =
      GeneralLinearGroup.scalar (Fin n) (γ ^ p) := by
    rw [hx]
    congr 1
    apply Units.ext
    simp [γ, hlam_pow]
  have hnorm := CFSG.GH74.GLS.Stage2.Bender.Thm1.uq_norm_of_pow
    (h := h) (n := n) (r := p) (w := (x : GL (Fin n) K)) (γ := γ)
    (by omega : 0 < n) hp hp2
    (by simpa [CFSG.GH74.GLS.Stage2.Bender.Thm1.UqU, idGram] using x.2) hγ hpdvd
  simpa [γ] using hnorm

end CFSG.LinearAlgebra

end
