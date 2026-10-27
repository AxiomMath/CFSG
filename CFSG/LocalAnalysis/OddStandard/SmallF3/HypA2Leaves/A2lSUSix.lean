module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lWeilSp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCoverStated
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvShape

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.RankThree.Classical
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups Matrix

section Frame

variable {F : Type} [Field F]

@[expose] def a2lDiag (c : F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F :=
  Matrix.fromBlocks 1 0 0 (c • 1)

theorem a2lDiag_mul (c d : F) : a2lDiag c * a2lDiag d = a2lDiag (c * d) := by
  simp [a2lDiag, Matrix.fromBlocks_multiply, smul_smul, mul_comm]

theorem a2lDiag_one : a2lDiag (1 : F) = 1 := by
  simp [a2lDiag, Matrix.fromBlocks_one]

theorem hadj_a2lDiag {p f : ℕ} (h : UnitaryFieldData p f F) (c : F) :
    hadj h (a2lDiag c) = a2lDiag (h.bar c) := by
  have hs : ∀ x : F, hadj h (x • (1 : Matrix (Fin 3) (Fin 3) F)) =
      h.bar x • (1 : Matrix (Fin 3) (Fin 3) F) := fun x => by
    ext a b
    simp [hadj, Matrix.one_apply, apply_ite h.bar, eq_comm]
  simp only [a2lDiag, hadj_fromBlocks, hadj_one, hadj_zero, hs]

theorem a2lDiag_conj_gram {i : F} :
    a2lDiag (-i) * hypGram2 3 F * a2lDiag i =
      i • (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) := by
  simp [a2lDiag, hypGram2, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul, neg_smul,
    smul_neg]

theorem a2lDiag_conj_symp {i : F} (hi : i * i = -1) :
    a2lDiag i * (i • (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)) *
      a2lDiag (-i) = hypGram2 3 F := by
  have e : i * -i = 1 := by rw [mul_neg, hi, neg_neg]
  simp [a2lDiag, hypGram2, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul, smul_smul, e, hi]

theorem a2lSp_isometry {p f : ℕ} (h : UnitaryFieldData p f F) {i : F} (hi : i * i = -1)
    (hbar : h.bar i = -i) {g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F} (hgr : g.map h.bar = g)
    (hg : gᵀ * Matrix.fromBlocks 0 1 (-1) 0 * g = Matrix.fromBlocks 0 1 (-1) 0) :
    hadj h (a2lDiag i * g * a2lDiag (-i)) * hypGram2 3 F * (a2lDiag i * g * a2lDiag (-i)) =
      hypGram2 3 F := by
  have hadj_g : hadj h g = gᵀ := by rw [hadj, hgr]
  simp only [hadj_mul, hadj_a2lDiag, hadj_g, map_neg, hbar, neg_neg]
  calc _ = a2lDiag i * (gᵀ * (a2lDiag (-i) * hypGram2 3 F * a2lDiag i) * g) * a2lDiag (-i) := by
        simp only [Matrix.mul_assoc]
    _ = hypGram2 3 F := by
        rw [a2lDiag_conj_gram, Matrix.mul_smul, Matrix.smul_mul, hg, a2lDiag_conj_symp hi]

end Frame

section Hom

variable {F : Type} [Field F]

@[expose] noncomputable def a2lSpFrame (φ : ZMod 3 →+* F) (i : F) (m : ℕ)
    (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 3)) :
    Matrix ((Fin 3 ⊕ Fin 3) ⊕ Fin m) ((Fin 3 ⊕ Fin 3) ⊕ Fin m) F :=
  Matrix.fromBlocks (a2lDiag i * g.map φ * a2lDiag (-i)) 0 0 1

variable (φ : ZMod 3 →+* F) {i : F} (hi : i * i = -1) (m : ℕ)

include hi

theorem a2lDiag_mul_neg : a2lDiag i * a2lDiag (-i) = (1 : Matrix (Fin 3 ⊕ Fin 3) _ F) := by
  rw [a2lDiag_mul, mul_neg, hi, neg_neg, a2lDiag_one]

theorem a2lDiag_neg_mul : a2lDiag (-i) * a2lDiag i = (1 : Matrix (Fin 3 ⊕ Fin 3) _ F) := by
  rw [a2lDiag_mul, neg_mul, hi, neg_neg, a2lDiag_one]

theorem a2lSpFrame_mul (g g' : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 3)) :
    a2lSpFrame φ i m g * a2lSpFrame φ i m g' = a2lSpFrame φ i m (g * g') := by
  have key : (a2lDiag i * g.map φ * a2lDiag (-i)) * (a2lDiag i * g'.map φ * a2lDiag (-i)) =
      a2lDiag i * (g * g').map φ * a2lDiag (-i) := by
    rw [Matrix.map_mul]
    calc _ = a2lDiag i * g.map φ * (a2lDiag (-i) * a2lDiag i) * g'.map φ * a2lDiag (-i) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [a2lDiag_neg_mul hi, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  simp [a2lSpFrame, Matrix.fromBlocks_multiply, key]

theorem a2lSpFrame_one :
    a2lSpFrame φ i m (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 3)) = 1 := by
  simp [a2lSpFrame, a2lDiag_mul_neg hi, Matrix.fromBlocks_one]

theorem a2lSpFrame_isometry {p f : ℕ} (h : UnitaryFieldData p f F) (hbar : h.bar i = -i)
    (hφ : ∀ a, h.bar (φ a) = φ a) {g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 3)}
    (hg : gᵀ * Matrix.fromBlocks 0 1 (-1) 0 * g = Matrix.fromBlocks 0 1 (-1) 0) :
    hadj h (a2lSpFrame φ i m g) * frameGram 3 m F * a2lSpFrame φ i m g = frameGram 3 m F := by
  have hgr : (g.map φ).map h.bar = g.map φ := by
    ext a b
    simp [hφ]
  have hJ : (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 3)).map φ = Matrix.fromBlocks 0 1 (-1) 0 := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.one_apply, apply_ite φ]
  have hg' := congrArg (fun M => M.map φ) hg
  simp only [Matrix.map_mul, Matrix.transpose_map, hJ] at hg'
  rw [a2lSpFrame, frameGram, hadj_fromBlocks, hadj_one, hadj_zero, hadj_zero,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [a2lSp_isometry h hi hbar hgr hg']

theorem det_a2lSpFrame (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 3)) :
    (a2lSpFrame φ i m g).det = φ g.det := by
  have h1 : (a2lDiag i).det * (a2lDiag (-i)).det = 1 := by
    rw [← Matrix.det_mul, a2lDiag_mul_neg hi, Matrix.det_one]
  rw [a2lSpFrame, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one, Matrix.det_mul,
    Matrix.det_mul]
  calc (a2lDiag i).det * (g.map φ).det * (a2lDiag (-i)).det
      = ((a2lDiag i).det * (a2lDiag (-i)).det) * (g.map φ).det := by ring
    _ = φ g.det := by
        rw [h1, one_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det]

theorem a2lSpFrame_neg_one (hm0 : m = 0) :
    a2lSpFrame φ i m (-1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 3)) = -1 := by
  subst hm0
  have h0 : (-1 : Matrix (Fin 0) (Fin 0) F) = 1 := Subsingleton.elim _ _
  have h1 : (-1 : Matrix ((Fin 3 ⊕ Fin 3) ⊕ Fin 0) ((Fin 3 ⊕ Fin 3) ⊕ Fin 0) F) =
      Matrix.fromBlocks (-1) 0 0 (-1) := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp
  have h2 : (-1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 3)).map φ = -1 := by
    rw [← RingHom.mapMatrix_apply, map_neg, map_one]
  rw [h1, h0, a2lSpFrame, h2]
  simp [Matrix.mul_neg, a2lDiag_mul_neg hi]

variable (h : UnitaryFieldData 3 1 F) (hbar : h.bar i = -i) (hφ : ∀ a, h.bar (φ a) = φ a)
  {n : ℕ} {P : Matrix (Fin n) ((Fin 3 ⊕ Fin 3) ⊕ Fin m) F}
  (hP : hadj h P * P = frameGram 3 m F) (hnm : 2 * 3 + m = n)

@[expose] noncomputable def a2lSpSU {G : Type} [Group G] (W : G →* StatedSp 3 (ZMod 3))
    (hdet : ∀ x, ((W x : GL (Fin 3 ⊕ Fin 3) (ZMod 3)) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 3)).det = 1) : G →* unitarySU 3 1 F n where
  toFun x := frameSU h hP hnm
    (a2lSpFrame φ i m (((W x : StatedSp 3 (ZMod 3)) : GL (Fin 3 ⊕ Fin 3) (ZMod 3)) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 3)))
    (a2lSpFrame_isometry φ hi m h hbar hφ (Open.StatedAPI.mem_statedSp_iff.1 (W x).2))
    (by rw [det_a2lSpFrame φ hi, hdet, map_one])
  map_one' := Subtype.ext (Units.ext (by
    rw [Subgroup.coe_one, Units.val_one, coe_frameSU]
    have h1 : (((W 1 : StatedSp 3 (ZMod 3)) : GL (Fin 3 ⊕ Fin 3) (ZMod 3)) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 3)) = 1 := by
      rw [map_one, Subgroup.coe_one, Units.val_one]
    rw [h1, a2lSpFrame_one φ hi, frameConj_one h hP hnm]))
  map_mul' x y := Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Units.val_mul, coe_frameSU, coe_frameSU, coe_frameSU, frameConj_mul h hP,
      a2lSpFrame_mul φ hi]
    have h1 : (((W (x * y) : StatedSp 3 (ZMod 3)) : GL (Fin 3 ⊕ Fin 3) (ZMod 3)) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 3)) =
        (((W x : StatedSp 3 (ZMod 3)) : GL (Fin 3 ⊕ Fin 3) (ZMod 3)) :
          Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 3)) *
        (((W y : StatedSp 3 (ZMod 3)) : GL (Fin 3 ⊕ Fin 3) (ZMod 3)) :
          Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 3)) := by
      rw [map_mul, Subgroup.coe_mul, Units.val_mul]
    rw [h1]))

end Hom

section Embed

variable {F : Type} [Field F] (φ : ZMod 3 →+* F) {i : F} (hi : i * i = -1) (m : ℕ)
  (h : UnitaryFieldData 3 1 F) (hbar : h.bar i = -i) (hφ : ∀ a, h.bar (φ a) = φ a)
  {n : ℕ} {P : Matrix (Fin n) ((Fin 3 ⊕ Fin 3) ⊕ Fin m) F}
  (hP : hadj h P * P = frameGram 3 m F) (hnm : 2 * 3 + m = n)

include hi hbar hφ

theorem a2lSpSU_injective {G : Type} [Group G] (W : G →* StatedSp 3 (ZMod 3))
    (hdet : ∀ x, ((W x : GL (Fin 3 ⊕ Fin 3) (ZMod 3)) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 3)).det = 1)
    (hφinj : Function.Injective φ) (hW : Function.Injective W) :
    Function.Injective (a2lSpSU φ hi m h hbar hφ hP hnm W hdet) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  set mat : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 3) :=
    (((W x : StatedSp 3 (ZMod 3)) : GL (Fin 3 ⊕ Fin 3) (ZMod 3)) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 3)) with hmat
  have h1 : frameConj h P (a2lSpFrame φ i m mat) = Matrix.scalar (Fin n) 1 := by
    have := congrArg (fun g : unitarySU 3 1 F n => ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
      hx
    simpa [a2lSpSU, coe_frameSU] using this
  have h2 := eq_smul_of_frameConj_eq_scalar h hP h1
  rw [one_smul, a2lSpFrame, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at h2
  obtain ⟨h3, -⟩ := h2
  have h4 : mat.map φ = 1 := by
    calc mat.map φ = (a2lDiag (-i) * a2lDiag i) * mat.map φ * (a2lDiag (-i) * a2lDiag i) := by
          rw [a2lDiag_neg_mul hi, Matrix.one_mul, Matrix.mul_one]
      _ = a2lDiag (-i) * (a2lDiag i * mat.map φ * a2lDiag (-i)) * a2lDiag i := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h3, Matrix.mul_one, a2lDiag_neg_mul hi]
  have h5 : mat = 1 := by
    apply Matrix.map_injective hφinj
    show mat.map φ = (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 3)).map φ
    rw [h4, Matrix.map_one φ (map_zero φ) (map_one φ)]
  have h6 : W x = 1 := Subtype.ext (Units.ext h5)
  exact hW (h6.trans (map_one W).symm)

theorem coe_a2lSpSU_neg_one {G : Type} [Group G] (W : G →* StatedSp 3 (ZMod 3))
    (hdet : ∀ x, ((W x : GL (Fin 3 ⊕ Fin 3) (ZMod 3)) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 3)).det = 1) {x : G}
    (hx : ((W x : StatedSp 3 (ZMod 3)) : GL (Fin 3 ⊕ Fin 3) (ZMod 3)) =
      Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3) (-1 : (ZMod 3)ˣ)) (hm0 : m = 0) :
    ((a2lSpSU φ hi m h hbar hφ hP hnm W hdet x : unitarySU 3 1 F n) : GL (Fin n) F) =
      Matrix.GeneralLinearGroup.scalar (Fin n) (-1 : Fˣ) := by
  refine Units.ext ?_
  have h1 : (((W x : StatedSp 3 (ZMod 3)) : GL (Fin 3 ⊕ Fin 3) (ZMod 3)) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 3)) = -1 := by
    rw [hx, Matrix.GeneralLinearGroup.coe_scalar, Units.val_neg, Units.val_one, map_neg, map_one]
  change frameConj h P (a2lSpFrame φ i m _) = _
  rw [h1, a2lSpFrame_neg_one φ hi m hm0, Matrix.GeneralLinearGroup.coe_scalar]
  simp only [frameConj, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, frame_mul_inv h hP hnm,
    Units.val_neg, Units.val_one, map_neg, map_one]

end Embed

theorem a2l_exists_sl2_27_statedSU {F : Type} [Field F] (hF : Nat.card F = 9) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (ψ : SL(2, E) →* StatedSU 6 3 F),
      Nat.card E = 27 ∧ Function.Injective ψ ∧
        ((ψ (a2lNegOne E) : StatedSU 6 3 F) : GL (Fin 6) F) =
          Matrix.GeneralLinearGroup.scalar (Fin 6) (-1 : Fˣ) := by
  have hd : UnitaryFieldData 3 1 F := a2l_unitaryFieldData_three (by rw [hF]; norm_num)
  haveI := hd.finite
  haveI := hd.charP
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := Fintype.ofFinite F
  have hFc : Fintype.card F = 9 := by rw [← Nat.card_eq_fintype_card]; exact hF
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (a2l_ringChar_ne_two (by rw [hFc]; decide))
  obtain ⟨P, hPraw⟩ := exists_evenFrame hd h2 (n := 6) (r := 3) (by norm_num)
  have hP : hadj hd P * P = frameGram 3 (6 - 2 * 3) F := hPraw
  obtain ⟨i, hi'⟩ : IsSquare (-1 : F) := FiniteField.isSquare_neg_one_iff.2 (by rw [hFc]; norm_num)
  have hi : i * i = -1 := hi'.symm
  have hbar : hd.bar i = -i := by
    rw [hd.bar_apply, pow_one]
    calc i ^ 3 = i * (i * i) := by ring
      _ = -i := by rw [hi]; ring
  let φ : ZMod 3 →+* F := ZMod.castHom (dvd_refl 3) F
  have hφ : ∀ a, hd.bar (φ a) = φ a := fun a => by
    rw [hd.bar_apply, pow_one, ← map_pow, ZMod.pow_card]
  obtain ⟨E, _, _, W, hEc, hWinj, hWneg⟩ := a2l_exists_weil_sl2_27 (ZMod 3) (Nat.card_zmod 3)
  have hE4 : 4 ≤ Nat.card E := by rw [hEc]; norm_num
  haveI : Group.IsPerfect SL(2, E) := (CFSG.GH74.GLS.IVK.GHInv.isQuasisimple_sl2 hE4).1
  have hdet : ∀ x : SL(2, E), ((W x : GL (Fin 3 ⊕ Fin 3) (ZMod 3)) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 3)).det = 1 := fun x => by
    let δ : SL(2, E) →* (ZMod 3)ˣ :=
      (Matrix.GeneralLinearGroup.det.comp (StatedSp 3 (ZMod 3)).subtype).comp W
    have hx : x ∈ commutator SL(2, E) := by
      rw [Group.IsPerfect.commutator_eq_top]
      exact Subgroup.mem_top x
    have h1 := congrArg Units.val (MonoidHom.mem_ker.1 (Abelianization.commutator_subset_ker δ hx))
    simpa [δ, Matrix.GeneralLinearGroup.val_det_apply] using h1
  refine ⟨E, inferInstance, inferInstance,
    a2lSpSU φ hi (6 - 2 * 3) hd hbar hφ hP (by norm_num) W hdet, hEc,
    a2lSpSU_injective φ hi (6 - 2 * 3) hd hbar hφ hP (by norm_num) W hdet φ.injective hWinj,
    coe_a2lSpSU_neg_one φ hi (6 - 2 * 3) hd hbar hφ hP (by norm_num) W hdet
      (hWneg _ rfl) (by norm_num)⟩

end CFSG.OddStandard.SmallF3.HypA2Leaves
