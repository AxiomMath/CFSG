module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12L4
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU4

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists CFSG.LocalAnalysis.ComponentInitial
open Matrix
open scoped MatrixGroups

section Matrices

variable {K : Type} [Field K]

@[expose] noncomputable def blockGL4 : GL (Fin 2) K →* GL (Fin 4) K where
  toFun X := ⟨l4dMat (X : Matrix (Fin 2) (Fin 2) K),
    l4dMat ((X⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), by
    rw [← l4dMat_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, l4dMat_one], by
    rw [← l4dMat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, l4dMat_one]⟩
  map_one' := Units.ext (by simp [l4dMat_one])
  map_mul' A B := Units.ext (by simp [l4dMat_mul])

theorem coe_blockGL4 (X : GL (Fin 2) K) :
    ((blockGL4 X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      l4dMat (X : Matrix (Fin 2) (Fin 2) K) := rfl

@[expose] def aGL : GL (Fin 4) K := ⟨l4aM, l4aM, l4aM_mul_self, l4aM_mul_self⟩

@[expose] def wGL : GL (Fin 4) K := ⟨l4wM, l4wM, l4wM_mul_self, l4wM_mul_self⟩

theorem coe_aGL : ((aGL : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = l4aM := rfl
theorem coe_wGL : ((wGL : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = l4wM := rfl

theorem aGL_mul_self : (aGL : GL (Fin 4) K) * aGL = 1 := Units.ext l4aM_mul_self
theorem wGL_mul_self : (wGL : GL (Fin 4) K) * wGL = 1 := Units.ext l4wM_mul_self

theorem aGL_mem_statedSU {q : ℕ} (hq : Odd q) : (aGL : GL (Fin 4) K) ∈ StatedSU 4 q K := by
  apply Subgroup.subset_closure
  refine ⟨by simpa [coe_aGL] using det_l4aM, ?_⟩
  rw [coe_aGL]
  have hq0 : (0 : K) ^ q = 0 := zero_pow hq.pos.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [l4aM, Matrix.mul_apply, Fin.sum_univ_succ, hq.neg_one_pow, hq0]

theorem wGL_mem_statedSU {q : ℕ} (hq : 1 ≤ q) : (wGL : GL (Fin 4) K) ∈ StatedSU 4 q K := by
  apply Subgroup.subset_closure
  refine ⟨by simpa [coe_wGL] using det_l4wM, ?_⟩
  rw [coe_wGL]
  have hq0 : (0 : K) ^ q = 0 := zero_pow (by omega)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [l4wM, Matrix.mul_apply, Fin.sum_univ_succ, hq0]

theorem map_blockGL4_statedSU_le {q : ℕ} (hq : 1 ≤ q) :
    (StatedSU 2 q K).map blockGL4 ≤ StatedSU 4 q K := by
  rw [StatedSU, MonoidHom.map_closure, StatedSU]
  apply Subgroup.closure_mono
  rintro _ ⟨A, ⟨hdet, hu⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [coe_blockGL4, det_l4dMat, hdet]
    simp
  · rw [coe_blockGL4]
    have hq0 : (0 : K) ^ q = 0 := zero_pow (by omega)
    have e := fun i j => congrFun (congrFun hu i) j
    have e00 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 ^ q * (A : Matrix (Fin 2) (Fin 2) K) 0 0 +
        (A : Matrix (Fin 2) (Fin 2) K) 1 0 ^ q * (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using e 0 0
    have e01 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 ^ q * (A : Matrix (Fin 2) (Fin 2) K) 0 1 +
        (A : Matrix (Fin 2) (Fin 2) K) 1 0 ^ q * (A : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using e 0 1
    have e10 : (A : Matrix (Fin 2) (Fin 2) K) 0 1 ^ q * (A : Matrix (Fin 2) (Fin 2) K) 0 0 +
        (A : Matrix (Fin 2) (Fin 2) K) 1 1 ^ q * (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using e 1 0
    have e11 : (A : Matrix (Fin 2) (Fin 2) K) 0 1 ^ q * (A : Matrix (Fin 2) (Fin 2) K) 0 1 +
        (A : Matrix (Fin 2) (Fin 2) K) 1 1 ^ q * (A : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using e 1 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [l4dMat, Matrix.mul_apply, Fin.sum_univ_succ, hq0, e00, e01, e10, e11]

end Matrices

section Proj

variable {K : Type} [Field K] {q : ℕ}

theorem mem_scalarsN_iff {x : ↥(StatedSU 4 q K)} :
    x ∈ (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 q K) ↔
      ∃ c : Kˣ, (Matrix.GeneralLinearGroup.scalar (Fin 4) c : GL (Fin 4) K) =
        (x : GL (Fin 4) K) := by
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]

theorem scalar_apply_gl (c : Kˣ) (i j : Fin 4) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 4) c : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j =
      if i = j then (c : K) else 0 := by
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]

@[expose] def aU (hq : Odd q) : ↥(StatedSU 4 q K) := ⟨aGL, aGL_mem_statedSU hq⟩

@[expose] def wU (hq : 1 ≤ q) : ↥(StatedSU 4 q K) := ⟨wGL, wGL_mem_statedSU hq⟩

@[expose] noncomputable def suDiag (hq : 1 ≤ q) : ↥(StatedSU 2 q K) →* ↥(StatedSU 4 q K) :=
  (blockGL4.comp (StatedSU 2 q K).subtype).codRestrict (StatedSU 4 q K) fun A =>
    map_blockGL4_statedSU_le hq ⟨A, A.2, rfl⟩

theorem aU_mul_self (hq : Odd q) : aU hq * aU hq = (1 : ↥(StatedSU 4 q K)) :=
  Subtype.ext aGL_mul_self

theorem wU_mul_self (hq : 1 ≤ q) : wU hq * wU hq = (1 : ↥(StatedSU 4 q K)) :=
  Subtype.ext wGL_mul_self

theorem aU_notMem (hq : Odd q) (h2 : (2 : K) ≠ 0) :
    aU hq ∉ (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 q K) := by
  rw [mem_scalarsN_iff]
  rintro ⟨c, hc⟩
  have h00 := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K) 0 0) hc
  have h22 := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K) 2 2) hc
  simp only [scalar_apply_gl] at h00 h22
  have h1 : ((c : Kˣ) : K) = 1 := by simpa [aU, coe_aGL, l4aM] using h00
  have h1' : ((c : Kˣ) : K) = -1 := by simpa [aU, coe_aGL, l4aM] using h22
  apply h2
  linear_combination h1' - h1

theorem wU_notMem (hq : 1 ≤ q) :
    wU hq ∉ (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 q K) := by
  rw [mem_scalarsN_iff]
  rintro ⟨c, hc⟩
  have h02 := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K) 0 2) hc
  simp only [scalar_apply_gl] at h02
  simp [wU, coe_wGL, l4wM] at h02

theorem wUaU_notMem (hq : Odd q) :
    wU hq.pos * aU hq ∉ (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 q K) := by
  rw [mem_scalarsN_iff]
  rintro ⟨c, hc⟩
  have h02 := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K) 0 2) hc
  simp only [scalar_apply_gl] at h02
  simp [wU, aU, coe_wGL, coe_aGL, l4wM, l4aM, Matrix.mul_apply, Fin.sum_univ_succ] at h02

theorem aU_wU_comm (hq : Odd q) :
    (aU hq * wU hq.pos)⁻¹ * (wU hq.pos * aU hq) ∈
      (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 q K) := by
  rw [mem_scalarsN_iff]
  refine ⟨-1, ?_⟩
  have hai : (aU hq : ↥(StatedSU 4 q K))⁻¹ = aU hq := inv_eq_of_mul_eq_one_right (aU_mul_self hq)
  have hwi : (wU hq.pos : ↥(StatedSU 4 q K))⁻¹ = wU hq.pos :=
    inv_eq_of_mul_eq_one_right (wU_mul_self hq.pos)
  rw [_root_.mul_inv_rev, hai, hwi]
  simp only [Subgroup.coe_mul]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_mul, scalar_apply_gl, wU, aU, coe_wGL, coe_aGL, l4wM, l4aM, Matrix.mul_apply,
      Fin.sum_univ_succ]

end Proj

section Cell

variable {K : Type} [Field K] {q : ℕ}

theorem suDiag_central (hq : 1 ≤ q) (x : ↥(StatedSU 2 q K))
    (hx : suDiag hq x ∈ (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 q K)) :
    ∀ z : ↥(StatedSU 2 q K), z * x = x * z := by
  obtain ⟨c, hc⟩ := mem_scalarsN_iff.1 hx
  have e : ∀ i j : Fin 4, (if i = j then (c : K) else 0) =
      (l4dMat ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) i j := by
    intro i j
    have := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K) i j) hc
    simpa [scalar_apply_gl, suDiag, coe_blockGL4] using this
  have h00 := e 0 0
  have h01 := e 0 1
  have h10 := e 1 0
  have h11 := e 1 1
  simp [l4dMat] at h00 h01 h10 h11
  have hX : ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) (c : K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00.symm, h01.symm, h10.symm, h11.symm]
  intro z
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hX]
  exact ((Matrix.scalar_commute (c : K) (fun _ => Commute.all _ _) _).eq).symm

@[expose] def FU43 (Y : Type) [Group Y] : Prop := CFSG.Blueprint.LieModel Y .PSU 4 3 1

end Cell

theorem cellAbs_U4 (hsurv : CellAbs FU43) : CellAbs FU4 := by
  intro A _ _ zb Sb Vb J hfr hJ hnc hF
  obtain ⟨p, f, hp, hf, hp2, hq8, hL⟩ := hF
  by_cases hq3 : p ^ f = 3
  · have hp3 : p = 3 := by
      have : p ∣ 3 := hq3 ▸ dvd_pow_self p (by omega)
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 this
    subst hp3
    have hf1 : f = 1 := by
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 3)
        (show 3 ^ f = 3 ^ 1 by rw [hq3, pow_one])
    subst hf1
    exact hsurv A zb Sb Vb J hfr hJ hnc hL
  · exfalso
    obtain ⟨K, _, _, hcard, ⟨e₀⟩⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K),
        Nat.card K = (p ^ f) ^ 2 ∧ Nonempty (↥J ⧸ center ↥J ≃*
          StatedProj (StatedSU 4 (p ^ f) K)) := by
      rcases hL with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
      · exact hc.2
      · exact absurd ht (by decide)
      · exact absurd ht (by decide)
      · exact absurd ht (by decide)
    have hnk : ¬ KindFactorAll Kind.ly (↥J ⧸ center ↥J) :=
      not_kindFactorAll_fu4 hp hp2 hf hL Kind.ly
    obtain ⟨hZ, -, -⟩ := hfr.reduce hJ hnk
    let eJ : (↥J ⧸ center ↥J) ≃* ↥J :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    let ι : StatedProj (StatedSU 4 (p ^ f) K) →* A :=
      J.subtype.comp (e₀.symm.trans eJ).toMonoidHom
    have hι : Function.Injective ι :=
      (Subgroup.subtype_injective _).comp (e₀.symm.trans eJ).injective
    have : Fact p.Prime := ⟨hp⟩
    have hUD : UnitaryFieldData p f K := ⟨hp, hf, by rw [hcard, ← pow_mul, mul_comm]⟩
    have : CharP K p := hUD.charP
    have hKfin : Finite K := hUD.finite
    obtain ⟨iso⟩ := nonempty_sl2_mulEquiv_statedSU_two (K := K) (r := p) (f := f) hcard
    have hFcard : Nat.card (CFSG.LieType.Steinberg.fixedSubfield K p f) = p ^ f :=
      CFSG.LieType.Steinberg.card_fixedSubfield hcard
    have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have hFodd : Odd (Nat.card (CFSG.LieType.Steinberg.fixedSubfield K p f)) := by
      rw [hFcard]; exact hqodd
    have h5 : 5 ≤ Nat.card (CFSG.LieType.Steinberg.fixedSubfield K p f) := by
      rw [hFcard]
      have h3 : 3 ≤ p ^ f := by
        have h2' : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
        have := Nat.odd_iff.mp hqodd
        omega
      have := Nat.odd_iff.mp hqodd
      omega
    have h2 : (2 : K) ≠ 0 := by
      have hK2 : ringChar K ≠ 2 := by rwa [ringChar.eq K p]
      exact Ring.two_ne_zero hK2
    have hq1 : 1 ≤ p ^ f := hqodd.pos
    refine false_of_four hfr ι hι hFodd h5 (x := QuotientGroup.mk (aU hqodd))
      (y := QuotientGroup.mk (wU hq1)) ?_ ?_ ?_ ?_ ?_ ?_
      ((QuotientGroup.mk' ((StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (p ^ f) K))).comp
        ((suDiag hq1).comp iso.toMonoidHom)) ?_ ?_ ?_
    · rw [← QuotientGroup.mk_mul, aU_mul_self, QuotientGroup.mk_one]
    · rw [← QuotientGroup.mk_mul, wU_mul_self, QuotientGroup.mk_one]
    · exact fun h => aU_notMem hqodd h2 ((QuotientGroup.eq_one_iff _).1 h)
    · exact fun h => wU_notMem hq1 ((QuotientGroup.eq_one_iff _).1 h)
    · intro h
      have h1 := QuotientGroup.eq.1 h
      have hwi : (wU hq1 : ↥(StatedSU 4 (p ^ f) K))⁻¹ = wU hq1 :=
        inv_eq_of_mul_eq_one_right (wU_mul_self hq1)
      rw [hwi] at h1
      exact wUaU_notMem hqodd h1
    · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact QuotientGroup.eq.2 (aU_wU_comm hqodd)
    · intro g hg
      have hg' : (suDiag hq1 (iso g)) ∈
          (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (p ^ f) K) :=
        (QuotientGroup.eq_one_iff _).1 hg
      have hcen := suDiag_central hq1 (iso g) hg'
      rw [Subgroup.mem_center_iff]
      intro s
      apply iso.injective
      rw [map_mul, map_mul]
      exact hcen (iso s)
    · intro g
      show QuotientGroup.mk (suDiag hq1 (iso g)) * QuotientGroup.mk (aU hqodd) =
        QuotientGroup.mk (aU hqodd) * QuotientGroup.mk (suDiag hq1 (iso g))
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
      exact l4dMat_mul_l4aM _
    · intro g
      show QuotientGroup.mk (suDiag hq1 (iso g)) * QuotientGroup.mk (wU hq1) =
        QuotientGroup.mk (wU hq1) * QuotientGroup.mk (suDiag hq1 (iso g))
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
      exact l4dMat_mul_l4wM _

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
