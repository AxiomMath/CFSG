module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
import CFSG.LinearAlgebra.FrobeniusSemilinearBasis
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoUni

public section

namespace CFSG.LinearAlgebra

open Matrix

variable {L : Type} [Field L] [IsAlgClosed L] {n : ℕ}

private lemma frobUni_tau_apply {p f : ℕ} {σ : L →+* L}
    (hσ : ∀ c, σ c = c ^ p ^ f) (c : L) :
    (σ.comp σ) c = c ^ ((p ^ f) * (p ^ f)) := by
  rw [RingHom.comp_apply, hσ, hσ, ← pow_mul]

private lemma frobUni_Q_two_le {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f) :
    2 ≤ (p ^ f) * (p ^ f) := by
  have h1 : 1 < p ^ f := Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt
  nlinarith

private lemma frobUni_invTransposeHom_mul_transpose (X : GL (Fin n) L) :
    ((CFSG.RankThree.Classical2.invTransposeHom X : GL (Fin n) L) :
      Matrix (Fin n) (Fin n) L) * ((X : Matrix (Fin n) (Fin n) L)ᵀ) = 1 := by
  rw [CFSG.RankThree.Classical2.coe_invTransposeHom, Matrix.coe_units_inv,
    ← Matrix.transpose_mul, ← Matrix.coe_units_inv X, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, Matrix.transpose_one]

private lemma frobUni_inv_invTransposeHom (X : GL (Fin n) L) :
    (((CFSG.RankThree.Classical2.invTransposeHom X)⁻¹ : GL (Fin n) L) :
      Matrix (Fin n) (Fin n) L) = (X : Matrix (Fin n) (Fin n) L)ᵀ := by
  rw [Matrix.coe_units_inv]
  exact Matrix.inv_eq_right_inv (frobUni_invTransposeHom_mul_transpose X)

private lemma frobUni_herm {σ : L →+* L} (C Y : GL (Fin n) L)
    (hY : ((Y : Matrix (Fin n) (Fin n) L).map (σ.comp σ)) =
      (Y : Matrix (Fin n) (Fin n) L) * (C : Matrix (Fin n) (Fin n) L) *
        (((C : Matrix (Fin n) (Fin n) L).map σ)ᵀ)⁻¹) :
    (((Y : Matrix (Fin n) (Fin n) L) * (C : Matrix (Fin n) (Fin n) L) *
      ((Y : Matrix (Fin n) (Fin n) L).map σ)ᵀ).map σ)ᵀ =
      (Y : Matrix (Fin n) (Fin n) L) * (C : Matrix (Fin n) (Fin n) L) *
        ((Y : Matrix (Fin n) (Fin n) L).map σ)ᵀ := by
  set Ym : Matrix (Fin n) (Fin n) L := (Y : Matrix (Fin n) (Fin n) L)
  set Cm : Matrix (Fin n) (Fin n) L := (C : Matrix (Fin n) (Fin n) L)
  have hmm : (Ym.map σ).map σ = Ym.map (σ.comp σ) := by rw [Matrix.map_map]; rfl
  have hc : ((Cm.map σ)ᵀ)⁻¹ * (Cm.map σ)ᵀ = 1 := by
    have h := frobUni_invTransposeHom_mul_transpose (L := L) (n := n)
      (Matrix.GeneralLinearGroup.map σ C)
    have h1 : ((CFSG.RankThree.Classical2.invTransposeHom
        (Matrix.GeneralLinearGroup.map σ C) : GL (Fin n) L) :
          Matrix (Fin n) (Fin n) L) = ((Cm.map σ)ᵀ)⁻¹ := by
      rw [CFSG.RankThree.Classical2.coe_invTransposeHom, Matrix.coe_units_inv,
        CFSG.RankThree.Classical2.coe_generalLinearGroup_map, Matrix.transpose_nonsing_inv]
    rw [h1] at h
    exact h
  calc
    ((Ym * Cm * (Ym.map σ)ᵀ).map σ)ᵀ
        = ((Ym.map σ) * (Cm.map σ) * ((Ym.map σ).map σ)ᵀ)ᵀ := by
            rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    _ = ((Ym.map σ) * (Cm.map σ) * (Ym.map (σ.comp σ))ᵀ)ᵀ := by rw [hmm]
    _ = (Ym.map (σ.comp σ)) * (Cm.map σ)ᵀ * (Ym.map σ)ᵀ := by
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = Ym * Cm * ((Cm.map σ)ᵀ)⁻¹ * (Cm.map σ)ᵀ * (Ym.map σ)ᵀ := by rw [hY]
    _ = Ym * Cm * (Ym.map σ)ᵀ := by
          rw [Matrix.mul_assoc (Ym * Cm) (((Cm.map σ)ᵀ)⁻¹) ((Cm.map σ)ᵀ), hc,
            Matrix.mul_one]

private lemma frobUni_exists_H {p f : ℕ} [Fact p.Prime] [CharP L p] (hf : 1 ≤ f)
    {σ : L →+* L} (hσ : ∀ c, σ c = c ^ p ^ f) (C : GL (Fin n) L) :
    ∃ (Y H : GL (Fin n) L),
      (H : Matrix (Fin n) (Fin n) L) =
        (Y : Matrix (Fin n) (Fin n) L) * (C : Matrix (Fin n) (Fin n) L) *
          ((Y : Matrix (Fin n) (Fin n) L).map σ)ᵀ ∧
      (((H : Matrix (Fin n) (Fin n) L).map σ)ᵀ = (H : Matrix (Fin n) (Fin n) L)) ∧
      (∀ i j, σ ((H : Matrix (Fin n) (Fin n) L) j i) =
        (H : Matrix (Fin n) (Fin n) L) i j) := by
  let τ : L →+* L := σ.comp σ
  have hτ : ∀ c, τ c = c ^ ((p ^ f) * (p ^ f)) := fun c => frobUni_tau_apply hσ c
  have hQ : 2 ≤ (p ^ f) * (p ^ f) := frobUni_Q_two_le hf
  let C' : GL (Fin n) L :=
    C * CFSG.RankThree.Classical2.invTransposeHom (Matrix.GeneralLinearGroup.map σ C)
  obtain ⟨Y, hY⟩ := exists_map_frobenius_eq_mul (σ := τ) (Q := (p ^ f) * (p ^ f)) hQ hτ C'
  let Hunit : GL (Fin n) L :=
    Y * C * (CFSG.RankThree.Classical2.invTransposeHom
      (Matrix.GeneralLinearGroup.map σ Y))⁻¹
  have hHmat : (Hunit : Matrix (Fin n) (Fin n) L) =
      (Y : Matrix (Fin n) (Fin n) L) * (C : Matrix (Fin n) (Fin n) L) *
        ((Y : Matrix (Fin n) (Fin n) L).map σ)ᵀ := by
    rw [Units.val_mul, Units.val_mul, frobUni_inv_invTransposeHom,
      CFSG.RankThree.Classical2.coe_generalLinearGroup_map]
  have hC'mat : ((C' : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      (C : Matrix (Fin n) (Fin n) L) *
        (((C : Matrix (Fin n) (Fin n) L).map σ)ᵀ)⁻¹ := by
    rw [Units.val_mul, CFSG.RankThree.Classical2.coe_invTransposeHom, Matrix.coe_units_inv,
      CFSG.RankThree.Classical2.coe_generalLinearGroup_map, Matrix.transpose_nonsing_inv]
  have hY' : ((Y : Matrix (Fin n) (Fin n) L).map τ) =
      (Y : Matrix (Fin n) (Fin n) L) * (C : Matrix (Fin n) (Fin n) L) *
        (((C : Matrix (Fin n) (Fin n) L).map σ)ᵀ)⁻¹ := by
    rw [hY, hC'mat, Matrix.mul_assoc]
  have hHherm : (((Hunit : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σ)ᵀ =
      (Hunit : Matrix (Fin n) (Fin n) L) := by
    rw [hHmat]
    exact frobUni_herm C Y hY'
  have hHentry : ∀ i j, σ ((Hunit : Matrix (Fin n) (Fin n) L) j i) =
      (Hunit : Matrix (Fin n) (Fin n) L) i j := by
    intro i j
    have h := congrFun (congrFun hHherm i) j
    simpa [Matrix.map_apply, Matrix.transpose_apply] using h
  exact ⟨Y, Hunit, hHmat, hHherm, hHentry⟩

private lemma frobUni_subtype_unitaryInvolution {p f : ℕ} [Fact p.Prime] {K : Subfield L}
    [Finite K] [CharP K p] {σ : L →+* L} (hσ : ∀ c, σ c = c ^ p ^ f) (c : K) :
    ((CFSG.LieType.BorelTits.unitaryInvolution K p f c : K) : L) = σ (c : L) := by
  rw [CFSG.LieType.BorelTits.unitaryInvolution_apply]
  change K.subtype (c ^ p ^ f) = σ (c : L)
  rw [map_pow]
  exact (hσ (c : L)).symm

private lemma frobUni_subtype_tau {p f : ℕ} [Fact p.Prime] {K : Subfield L}
    {σ : L →+* L} (hmemK : ∀ c : L, c ∈ K ↔ c ^ (p ^ f) ^ 2 = c)
    (hσ : ∀ c, σ c = c ^ p ^ f) (c : K) :
    σ (σ (K.subtype c)) = K.subtype c := by
  have hmem : (K.subtype c) ^ (p ^ f) ^ 2 = K.subtype c := (hmemK (K.subtype c)).1 c.2
  rw [hσ, hσ, ← pow_mul]
  simpa [pow_two] using hmem

private lemma frobUni_map_conjTr {p f : ℕ} [Fact p.Prime] {K : Subfield L}
    [Finite K] [CharP K p] {σ : L →+* L} (hσ : ∀ c, σ c = c ^ p ^ f)
    (A : Matrix (Fin n) (Fin n) K) :
    ((CFSG.LieType.Universal.Unitary.conjTr
      (CFSG.LieType.BorelTits.unitaryInvolution K p f) A).map K.subtype) =
      ((A.map K.subtype).map σ)ᵀ := by
  ext i j
  rw [CFSG.LieType.Universal.Unitary.conjTr, Matrix.map_apply, Matrix.transpose_apply,
    Matrix.transpose_apply, Matrix.map_apply, Matrix.map_apply]
  exact frobUni_subtype_unitaryInvolution (p := p) (f := f) (K := K) hσ (A j i)

private lemma frobUni_descent {p f : ℕ} [Fact p.Prime] [CharP L p]
    {K : Subfield L} [Finite K] [CharP K p]
    (hmemK : ∀ c : L, c ∈ K ↔ c ^ (p ^ f) ^ 2 = c)
    {σ : L →+* L} (hσ : ∀ c, σ c = c ^ p ^ f) (H : GL (Fin n) L)
    (hHherm : (((H : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σ)ᵀ =
      (H : Matrix (Fin n) (Fin n) L))
    (hHentry : ∀ i j, σ ((H : Matrix (Fin n) (Fin n) L) j i) =
      (H : Matrix (Fin n) (Fin n) L) i j) :
    ∃ H' : Matrix (Fin n) (Fin n) K,
      H'.map K.subtype = (H : Matrix (Fin n) (Fin n) L) ∧
      H'.det ≠ 0 ∧
      CFSG.LieType.Universal.Unitary.conjTr
        (CFSG.LieType.BorelTits.unitaryInvolution K p f) H' = H' := by
  have hmemH : ∀ i j, (H : Matrix (Fin n) (Fin n) L) i j ∈ K := by
    intro i j
    rw [hmemK]
    have hτc : (H : Matrix (Fin n) (Fin n) L) i j ^ ((p ^ f) * (p ^ f)) =
        (H : Matrix (Fin n) (Fin n) L) i j := by
      rw [pow_mul, ← hσ, ← hσ, hHentry j i, hHentry i j]
    simpa [pow_two] using hτc
  let H' : Matrix (Fin n) (Fin n) K :=
    Matrix.of fun i j => ⟨(H : Matrix (Fin n) (Fin n) L) i j, hmemH i j⟩
  have hH'map : H'.map K.subtype = (H : Matrix (Fin n) (Fin n) L) := by
    ext i j
    rfl
  have hH'entry : ∀ i j, ((H' i j : K) : L) =
      (H : Matrix (Fin n) (Fin n) L) i j := by
    intro i j
    have h := congrFun (congrFun hH'map i) j
    simpa using h
  have hH'det : H'.det ≠ 0 := by
    intro h0
    have hdet : (H : Matrix (Fin n) (Fin n) L).det ≠ 0 :=
      Matrix.GeneralLinearGroup.det_ne_zero H
    have hmapdet := RingHom.map_det K.subtype H'
    change K.subtype H'.det = (H'.map K.subtype).det at hmapdet
    rw [hH'map, h0, map_zero] at hmapdet
    exact hdet hmapdet.symm
  have hH'herm : CFSG.LieType.Universal.Unitary.conjTr
      (CFSG.LieType.BorelTits.unitaryInvolution K p f) H' = H' := by
    ext i j
    rw [CFSG.LieType.Universal.Unitary.conjTr, Matrix.transpose_apply, Matrix.map_apply]
    change ((CFSG.LieType.BorelTits.unitaryInvolution K p f (H' j i) : K) : L) =
      ((H' i j : K) : L)
    rw [frobUni_subtype_unitaryInvolution (p := p) (f := f) (K := K) hσ,
      hH'entry j i, hHentry i j, hH'entry i j]
  exact ⟨H', hH'map, hH'det, hH'herm⟩

private lemma frobUni_orthonormal {p f : ℕ} [Fact p.Prime] [CharP L p]
    {K : Subfield L} [Finite K] [CharP K p]
    (hcard : Nat.card K = (p ^ f) ^ 2) {H' : Matrix (Fin n) (Fin n) K}
    (hH'herm : CFSG.LieType.Universal.Unitary.conjTr
      (CFSG.LieType.BorelTits.unitaryInvolution K p f) H' = H')
    (hH'det : H'.det ≠ 0) :
    ∃ P : GL (Fin n) K,
      CFSG.LieType.Universal.Unitary.conjTr
        (CFSG.LieType.BorelTits.unitaryInvolution K p f)
          (P : Matrix (Fin n) (Fin n) K) * H' *
        (P : Matrix (Fin n) (Fin n) K) = 1 :=
  CFSG.LieType.Steinberg.exists_conjTr_mul_mul_eq_one (F := K) (p := p) (f := f)
    hcard hH'herm hH'det

private lemma frobUni_unitary_conj {p f : ℕ} [Fact p.Prime] [CharP L p]
    {K : Subfield L} [Finite K] [CharP K p]
    (hmemK : ∀ c : L, c ∈ K ↔ c ^ (p ^ f) ^ 2 = c)
    {σ : L →+* L} (hσ : ∀ c, σ c = c ^ p ^ f)
    {H : GL (Fin n) L} {H' : Matrix (Fin n) (Fin n) K}
    (hH'map : H'.map K.subtype = (H : Matrix (Fin n) (Fin n) L))
    {P : GL (Fin n) K}
    (hP : CFSG.LieType.Universal.Unitary.conjTr
      (CFSG.LieType.BorelTits.unitaryInvolution K p f)
        (P : Matrix (Fin n) (Fin n) K) * H' *
      (P : Matrix (Fin n) (Fin n) K) = 1) :
    ∃ PL : GL (Fin n) L,
      (PL : Matrix (Fin n) (Fin n) L) =
        (P : Matrix (Fin n) (Fin n) K).map K.subtype ∧
      ((PL : Matrix (Fin n) (Fin n) L).map σ)ᵀ *
        (H : Matrix (Fin n) (Fin n) L) * (PL : Matrix (Fin n) (Fin n) L) = 1 ∧
      ((PL : Matrix (Fin n) (Fin n) L).map (σ.comp σ)) =
        (PL : Matrix (Fin n) (Fin n) L) := by
  let PL : GL (Fin n) L := Matrix.GeneralLinearGroup.map K.subtype P
  have hPL : (PL : Matrix (Fin n) (Fin n) L) =
      (P : Matrix (Fin n) (Fin n) K).map K.subtype :=
    CFSG.RankThree.Classical2.coe_generalLinearGroup_map K.subtype P
  have hPherm : ((PL : Matrix (Fin n) (Fin n) L).map σ)ᵀ *
      (H : Matrix (Fin n) (Fin n) L) * (PL : Matrix (Fin n) (Fin n) L) = 1 := by
    have hmap := congrArg (fun M : Matrix (Fin n) (Fin n) K => M.map K.subtype) hP
    have hleft : (CFSG.LieType.Universal.Unitary.conjTr
        (CFSG.LieType.BorelTits.unitaryInvolution K p f) (P : Matrix (Fin n) (Fin n) K) *
          H' * (P : Matrix (Fin n) (Fin n) K)).map K.subtype =
        ((PL : Matrix (Fin n) (Fin n) L).map σ)ᵀ *
          (H : Matrix (Fin n) (Fin n) L) * (PL : Matrix (Fin n) (Fin n) L) := by
      simp only [Matrix.map_mul, frobUni_map_conjTr (p := p) (f := f) (K := K) hσ,
        hH'map, hPL]
    rw [hleft] at hmap
    simpa using hmap
  have hPLτ : ((PL : Matrix (Fin n) (Fin n) L).map (σ.comp σ)) =
      (PL : Matrix (Fin n) (Fin n) L) := by
    ext i j
    change σ (σ ((PL : Matrix (Fin n) (Fin n) L) i j)) =
      (PL : Matrix (Fin n) (Fin n) L) i j
    rw [hPL]
    exact frobUni_subtype_tau (p := p) (f := f) (K := K) hmemK hσ
      ((P : Matrix (Fin n) (Fin n) K) i j)
  exact ⟨PL, hPL, hPherm, hPLτ⟩

private lemma frobUni_final (C : GL (Fin n) L) {σ : L →+* L}
    {Y H PL : GL (Fin n) L}
    (hHmat : (H : Matrix (Fin n) (Fin n) L) =
      (Y : Matrix (Fin n) (Fin n) L) * (C : Matrix (Fin n) (Fin n) L) *
        ((Y : Matrix (Fin n) (Fin n) L).map σ)ᵀ)
    (hPherm : ((PL : Matrix (Fin n) (Fin n) L).map σ)ᵀ *
      (H : Matrix (Fin n) (Fin n) L) * (PL : Matrix (Fin n) (Fin n) L) = 1)
    (hPLτ : ((PL : Matrix (Fin n) (Fin n) L).map (σ.comp σ)) =
      (PL : Matrix (Fin n) (Fin n) L)) :
    ∃ Z : GL (Fin n) L, (Z : Matrix (Fin n) (Fin n) L) *
      (C : Matrix (Fin n) (Fin n) L) *
        ((Z : Matrix (Fin n) (Fin n) L).map σ)ᵀ = 1 := by
  set Zmat : Matrix (Fin n) (Fin n) L :=
    ((PL : Matrix (Fin n) (Fin n) L).map σ)ᵀ * (Y : Matrix (Fin n) (Fin n) L) with hZdef
  have hZsigma : (Zmat.map σ)ᵀ =
      ((Y : Matrix (Fin n) (Fin n) L).map σ)ᵀ * (PL : Matrix (Fin n) (Fin n) L) := by
    calc
      (Zmat.map σ)ᵀ
          = ((((PL : Matrix (Fin n) (Fin n) L).map σ)ᵀ).map σ *
              ((Y : Matrix (Fin n) (Fin n) L).map σ))ᵀ := by
              rw [hZdef, Matrix.map_mul]
      _ = ((Y : Matrix (Fin n) (Fin n) L).map σ)ᵀ *
            ((((PL : Matrix (Fin n) (Fin n) L).map σ)ᵀ).map σ)ᵀ := by
              rw [Matrix.transpose_mul]
      _ = ((Y : Matrix (Fin n) (Fin n) L).map σ)ᵀ *
            (((PL : Matrix (Fin n) (Fin n) L).map σ).map σ) := by
              rw [Matrix.transpose_map, Matrix.transpose_transpose]
      _ = ((Y : Matrix (Fin n) (Fin n) L).map σ)ᵀ *
            ((PL : Matrix (Fin n) (Fin n) L).map (σ.comp σ)) := by
              rw [Matrix.map_map]; rfl
      _ = ((Y : Matrix (Fin n) (Fin n) L).map σ)ᵀ *
            (PL : Matrix (Fin n) (Fin n) L) := by rw [hPLτ]
  have hZ : Zmat * (C : Matrix (Fin n) (Fin n) L) * (Zmat.map σ)ᵀ = 1 := by
    calc
      Zmat * (C : Matrix (Fin n) (Fin n) L) * (Zmat.map σ)ᵀ
          = ((PL : Matrix (Fin n) (Fin n) L).map σ)ᵀ *
              (Y : Matrix (Fin n) (Fin n) L) * (C : Matrix (Fin n) (Fin n) L) *
                (((Y : Matrix (Fin n) (Fin n) L).map σ)ᵀ *
                  (PL : Matrix (Fin n) (Fin n) L)) := by rw [hZsigma, hZdef]
      _ = ((PL : Matrix (Fin n) (Fin n) L).map σ)ᵀ *
            ((Y : Matrix (Fin n) (Fin n) L) * (C : Matrix (Fin n) (Fin n) L) *
              ((Y : Matrix (Fin n) (Fin n) L).map σ)ᵀ) *
              (PL : Matrix (Fin n) (Fin n) L) := by
              simp only [Matrix.mul_assoc]
      _ = ((PL : Matrix (Fin n) (Fin n) L).map σ)ᵀ *
            (H : Matrix (Fin n) (Fin n) L) * (PL : Matrix (Fin n) (Fin n) L) := by
              rw [← hHmat]
      _ = 1 := hPherm
  have hZ' : Zmat * ((C : Matrix (Fin n) (Fin n) L) * (Zmat.map σ)ᵀ) = 1 := by
    rw [← Matrix.mul_assoc]
    exact hZ
  have hZ'' : ((C : Matrix (Fin n) (Fin n) L) * (Zmat.map σ)ᵀ) * Zmat = 1 :=
    mul_eq_one_comm.mp hZ'
  exact ⟨Units.mk Zmat ((C : Matrix (Fin n) (Fin n) L) * (Zmat.map σ)ᵀ) hZ' hZ'', hZ⟩

theorem exists_mul_mul_transpose_map_frobenius_eq_one {L : Type} [Field L] [IsAlgClosed L]
    {p f : ℕ} [Fact p.Prime] [CharP L p] (hf : 1 ≤ f) {σ : L →+* L}
    (hσ : ∀ c, σ c = c ^ p ^ f) {n : ℕ} (C : GL (Fin n) L) :
    ∃ Z : GL (Fin n) L, (Z : Matrix (Fin n) (Fin n) L) * (C : Matrix (Fin n) (Fin n) L) *
      ((Z : Matrix (Fin n) (Fin n) L).map σ)ᵀ = 1 := by
  let K : Subfield L :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five.Two.subfieldSq p L f
  haveI hFinK : Finite K :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five.Two.finite_subfieldSq
      (Ω := L) (ℓ := p) (f := f) hf
  haveI hCharK : CharP K p := Subfield.charP K p
  have hmemK : ∀ c : L, c ∈ K ↔ c ^ (p ^ f) ^ 2 = c := by
    intro c
    change c ∈ CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five.Two.subfieldSq p L f ↔ _
    rw [CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five.Two.mem_subfieldSq]
  obtain ⟨Y, H, hHmat, hHherm, hHentry⟩ := frobUni_exists_H hf hσ C
  obtain ⟨H', hH'map, hH'det, hH'herm⟩ := frobUni_descent hmemK hσ H hHherm hHentry
  have hcard : Nat.card K = (p ^ f) ^ 2 := by
    have h := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five.Two.card_subfieldSq
      (Ω := L) (ℓ := p) (f := f) hf
    change Nat.card K = p ^ (2 * f) at h
    rw [h, mul_comm 2 f, pow_mul]
  obtain ⟨P, hP⟩ := frobUni_orthonormal (p := p) (f := f) (K := K)
    hcard hH'herm hH'det
  have huc := frobUni_unitary_conj (L := L) (n := n) (p := p) (f := f)
    (K := K) (H := H) (H' := H') (σ := σ) (P := P) hmemK hσ hH'map hP
  obtain ⟨PL, -, hPherm, hPLτ⟩ := huc
  exact frobUni_final C hHmat hPherm hPLτ

end CFSG.LinearAlgebra
