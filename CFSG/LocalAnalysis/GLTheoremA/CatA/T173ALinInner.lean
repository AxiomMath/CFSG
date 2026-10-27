module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open scoped MatrixGroups

private theorem linInner_mem_SL_iff {d : ℕ} {F : Type} [Field F] {A : GL (Fin d) F} :
    A ∈ LinSL d F ↔ (A : Matrix (Fin d) (Fin d) F).det = 1 := by
  show A ∈ LargeEvenSLGroup (Fin d) F ↔ _
  rw [LargeEvenSLGroup, MonoidHom.mem_ker, Units.ext_iff,
    Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]

private theorem linInner_conj_mem_SL {d : ℕ} {F : Type} [Field F] (g : GL (Fin d) F)
    {A : GL (Fin d) F} (hA : A ∈ LinSL d F) : g * A * g⁻¹ ∈ LinSL d F := by
  rw [linInner_mem_SL_iff] at hA ⊢
  have h1 : (g : Matrix (Fin d) (Fin d) F).det *
      ((g⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hA]
  linear_combination h1

private theorem linInner_graphAut_pow {d : ℕ} {F : Type} [Field F] {R : Type} [Group R]
    (π : ↥(LinSL d F) →* R) {A : GL (Fin d) F} {φ : MulAut R}
    (hφ : LargeEvenGraphAut π (fun h h' => (h' : GL (Fin d) F) = A * h * A⁻¹) φ) :
    ∀ k : ℕ, LargeEvenGraphAut π
      (fun h h' => (h' : GL (Fin d) F) = A ^ k * h * (A ^ k)⁻¹) (φ ^ k) := by
  intro k
  induction k with
  | zero =>
      intro h h' hh'
      rw [pow_zero, one_mul, inv_one, mul_one] at hh'
      rw [pow_zero, Subtype.ext hh', MulAut.one_apply]
  | succ k ih =>
      intro h h' hh'
      let h'' : ↥(LinSL d F) :=
        ⟨A * (h : GL (Fin d) F) * A⁻¹, linInner_conj_mem_SL A h.2⟩
      have hstep : φ (π h) = π h'' := hφ h h'' rfl
      have hrel : (h' : GL (Fin d) F) = A ^ k * (h'' : GL (Fin d) F) * (A ^ k)⁻¹ := by
        rw [show (h'' : GL (Fin d) F) = A * (h : GL (Fin d) F) * A⁻¹ from rfl, hh',
          pow_succ, _root_.mul_inv_rev]
        group
      rw [pow_succ, MulAut.mul_apply, hstep]
      exact ih h'' h' hrel

private theorem exists_pow_eq_of_pow_eq_of_coprime {G : Type} [CommGroup G] {p d : ℕ}
    (hcop : Nat.Coprime p d) {x y : G} (h : x ^ p = y ^ d) :
    ∃ e : G, e ^ d = x := by
  have hbez : (p : ℤ) * Nat.gcdA p d + (d : ℤ) * Nat.gcdB p d = 1 := by
    have h1 := Nat.gcd_eq_gcd_ab p d
    rw [hcop.gcd_eq_one] at h1
    norm_num at h1
    linarith
  have hy : y ^ (d : ℤ) = x ^ (p : ℤ) := by
    rw [zpow_natCast, zpow_natCast, ← h]
  refine ⟨y ^ Nat.gcdA p d * x ^ Nat.gcdB p d, ?_⟩
  have hmain : (y ^ Nat.gcdA p d * x ^ Nat.gcdB p d) ^ (d : ℤ) = x := by
    calc (y ^ Nat.gcdA p d * x ^ Nat.gcdB p d) ^ (d : ℤ)
        = (y ^ Nat.gcdA p d) ^ (d : ℤ) * (x ^ Nat.gcdB p d) ^ (d : ℤ) := by
          rw [mul_zpow]
      _ = y ^ (Nat.gcdA p d * (d : ℤ)) * x ^ (Nat.gcdB p d * (d : ℤ)) := by
          rw [← zpow_mul, ← zpow_mul]
      _ = y ^ ((d : ℤ) * Nat.gcdA p d) * x ^ (Nat.gcdB p d * (d : ℤ)) := by
          rw [mul_comm (Nat.gcdA p d) (d : ℤ)]
      _ = (y ^ (d : ℤ)) ^ Nat.gcdA p d * x ^ (Nat.gcdB p d * (d : ℤ)) := by
          rw [zpow_mul]
      _ = (x ^ (p : ℤ)) ^ Nat.gcdA p d * x ^ (Nat.gcdB p d * (d : ℤ)) := by rw [hy]
      _ = x ^ ((p : ℤ) * Nat.gcdA p d) * x ^ (Nat.gcdB p d * (d : ℤ)) := by
          rw [← zpow_mul]
      _ = x ^ ((p : ℤ) * Nat.gcdA p d + Nat.gcdB p d * (d : ℤ)) := by rw [← zpow_add]
      _ = x ^ (1 : ℤ) := by
          congr 1
          rw [mul_comm (Nat.gcdB p d) (d : ℤ)]
          exact hbez
      _ = x := by rw [zpow_one]
  simpa [zpow_natCast] using hmain

theorem lin_conjImage_pPower_inner {p n d : ℕ} {F : Type} [Field F] [Finite F]
    (h : LinArith p n d F) {φ : MulAut (LinPSL d F)}
    (hφ : φ ∈ LargeEvenMatConjImage (LinMk d F) Set.univ) (hφp : φ ^ p = 1) :
    ∃ r : LinPSL d F, ∀ y : LinPSL d F, φ y = r * y * r⁻¹ := by
  obtain ⟨hp, _hpm, _hpdvd, hpndvd, hcard, _hn2, hd2⟩ := h
  obtain ⟨A, -, hA⟩ := hφ
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hpow : LargeEvenGraphAut (LinMk d F)
      (fun h h' => (h' : GL (Fin d) F) = A ^ p * h * (A ^ p)⁻¹) (φ ^ p) :=
    linInner_graphAut_pow (LinMk d F) hA p
  have hcomm : ∀ t : Matrix.TransvectionStruct (Fin d) F,
      Commute t.toMatrix ((A ^ p : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) := by
    intro t
    obtain ⟨i, j, hij, c⟩ := t
    let T : GL (Fin d) F := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j c)
      (by rw [Matrix.det_transvection_of_ne i j hij]; exact one_ne_zero)
    have hTmem : T ∈ LinSL d F := by
      rw [linInner_mem_SL_iff, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
        Matrix.det_transvection_of_ne i j hij]
    let T' : ↥(LinSL d F) := ⟨T, hTmem⟩
    have hT2 : T ^ 2 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, pow_two]
      rw [show (T : Matrix (Fin d) (Fin d) F) = Matrix.transvection i j c from
        Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _]
      rw [Matrix.transvection_mul_transvection_same i j hij c c, CharTwo.add_self_eq_zero,
        Matrix.transvection_zero]
    have hT'2 : T' ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hT2
    have hconjT : A ^ p * T * (A ^ p)⁻¹ ∈ LinSL d F := linInner_conj_mem_SL (A ^ p) hTmem
    let x : ↥(LinSL d F) := ⟨A ^ p * T * (A ^ p)⁻¹, hconjT⟩
    have hxT : LinMk d F x = LinMk d F T' := by
      have h1 : (φ ^ p) (LinMk d F T') = LinMk d F x := hpow T' x rfl
      rw [hφp, MulAut.one_apply] at h1
      exact h1.symm
    obtain ⟨z, hzmem, hxz⟩ :=
      (QuotientGroup.mk'_eq_mk'
        (N := (LargeEvenScalars (Fin d) F).subgroupOf (LinSL d F))).mp hxT
    rw [Subgroup.mem_subgroupOf] at hzmem
    obtain ⟨u, hu⟩ := hzmem
    have hx2 : x ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      show (A ^ p * T * (A ^ p)⁻¹) ^ 2 = 1
      rw [pow_two]
      calc A ^ p * T * (A ^ p)⁻¹ * (A ^ p * T * (A ^ p)⁻¹)
          = A ^ p * (T * T) * (A ^ p)⁻¹ := by group
        _ = 1 := by rw [← pow_two, hT2, mul_one, mul_inv_cancel]
    have hzcent : z * x = x * z := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hu]
      exact Matrix.GeneralLinearGroup.scalar_commute u (x : GL (Fin d) F)
    have hz2 : z ^ 2 = 1 := by
      have h1 : (x * z) ^ 2 = T' ^ 2 := by rw [hxz]
      rw [Commute.mul_pow (show Commute x z from hzcent.symm) 2, hx2, one_mul, hT'2] at h1
      exact h1
    have hu2 : u ^ 2 = 1 := by
      have hz2'' : (Matrix.GeneralLinearGroup.scalar (Fin d) u) ^ 2 = 1 := by
        have h := congrArg (fun g : ↥(LinSL d F) => (g : GL (Fin d) F)) hz2
        rw [Subgroup.coe_pow, Subgroup.coe_one, ← hu] at h
        exact h
      have hmat : (Matrix.scalar (Fin d) (((u ^ 2 : Fˣ) : F)) :
          Matrix (Fin d) (Fin d) F) = 1 := by
        have h : (Matrix.GeneralLinearGroup.scalar (Fin d) (u ^ 2) : GL (Fin d) F) = 1 := by
          rw [map_pow]
          exact hz2''
        have h2 := congrArg (fun g : GL (Fin d) F => (g : Matrix (Fin d) (Fin d) F)) h
        rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_one] at h2
        exact h2
      haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
      exact Units.ext ((Matrix.scalar_inj (n := Fin d)).mp (by rw [hmat, Units.val_one, map_one]))
    have hu1 : u = 1 := by
      have hu2F : (u : F) ^ 2 = 1 := by
        have h := congrArg (fun x : Fˣ => (x : F)) hu2
        rw [Units.val_pow_eq_pow_val, Units.val_one] at h
        exact h
      rcases sq_eq_one_iff.mp hu2F with h | h
      · exact Units.ext h
      · rw [CharTwo.neg_eq] at h
        exact Units.ext h
    have hz1 : z = 1 := by
      apply Subtype.ext
      simp [← hu, hu1]
    have hxT' : x = T' := by
      have h1 := hxz
      rw [hz1, mul_one] at h1
      exact h1
    have hcommT : (A ^ p : GL (Fin d) F) * T = T * (A ^ p : GL (Fin d) F) := by
      have hxval : (x : GL (Fin d) F) = A ^ p * T * (A ^ p)⁻¹ := rfl
      have h1 : A ^ p * T * (A ^ p)⁻¹ = T := by rw [← hxval, hxT']
      calc (A ^ p : GL (Fin d) F) * T = A ^ p * T * (A ^ p)⁻¹ * (A ^ p) := by group
        _ = T * (A ^ p) := by rw [h1]
    have hTval : (T : Matrix (Fin d) (Fin d) F) = Matrix.transvection i j c :=
      Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _
    have hmat := congrArg (fun g : GL (Fin d) F => (g : Matrix (Fin d) (Fin d) F)) hcommT
    rw [Units.val_mul, Units.val_mul, hTval] at hmat
    exact hmat.symm
  have hscalar : ((A ^ p : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) ∈
      Set.range (Matrix.scalar (Fin d)) :=
    Matrix.mem_range_scalar_of_commute_transvectionStruct hcomm
  have hcenter : A ^ p ∈ Subgroup.center (GL (Fin d) F) :=
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr hscalar
  have hmemrange : A ^ p ∈ (Matrix.GeneralLinearGroup.scalar (Fin d)).range := by
    rw [← Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact hcenter
  obtain ⟨cunit, hcunit⟩ := hmemrange
  have hdet : (A.det) ^ p = cunit ^ d := by
    have h1 : (A ^ p : GL (Fin d) F).det = cunit ^ d := by
      rw [← hcunit, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
    rwa [map_pow] at h1
  have hcop : Nat.Coprime p d := hp.coprime_iff_not_dvd.mpr hpndvd
  obtain ⟨e, he⟩ := exists_pow_eq_of_pow_eq_of_coprime hcop hdet
  let S : GL (Fin d) F := Matrix.GeneralLinearGroup.scalar (Fin d) e⁻¹ * A
  have hS : S ∈ LinSL d F := by
    rw [linInner_mem_SL_iff, ← Matrix.GeneralLinearGroup.val_det_apply]
    show ((Matrix.GeneralLinearGroup.scalar (Fin d) e⁻¹ * A).det : F) = 1
    rw [map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, inv_pow, he,
      inv_mul_cancel]
    rfl
  have hAeq : A = Matrix.GeneralLinearGroup.scalar (Fin d) e * S := by
    show A = Matrix.GeneralLinearGroup.scalar (Fin d) e *
      (Matrix.GeneralLinearGroup.scalar (Fin d) e⁻¹ * A)
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  refine ⟨LinMk d F ⟨S, hS⟩, fun y => ?_⟩
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective
    ((LargeEvenScalars (Fin d) F).subgroupOf (LinSL d F)) y
  have hconjh : A * (h : GL (Fin d) F) * A⁻¹ ∈ LinSL d F := linInner_conj_mem_SL A h.2
  let h' : ↥(LinSL d F) := ⟨A * (h : GL (Fin d) F) * A⁻¹, hconjh⟩
  have h1 : φ (LinMk d F h) = LinMk d F h' := hA h h' rfl
  rw [h1, ← map_mul, ← map_inv, ← map_mul]
  congr 1
  apply Subtype.ext
  show A * (h : GL (Fin d) F) * A⁻¹ = S * (h : GL (Fin d) F) * S⁻¹
  rw [hAeq, mul_inv_rev]
  rw [show (Matrix.GeneralLinearGroup.scalar (Fin d) e * S) * (h : GL (Fin d) F) *
      (S⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin d) e)⁻¹) =
      Matrix.GeneralLinearGroup.scalar (Fin d) e * (S * (h : GL (Fin d) F) * S⁻¹) *
        (Matrix.GeneralLinearGroup.scalar (Fin d) e)⁻¹ by group]
  rw [Matrix.GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
