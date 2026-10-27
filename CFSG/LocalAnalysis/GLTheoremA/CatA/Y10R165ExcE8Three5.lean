module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Three4
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.RankThree.PartOne.KE6.E8T3Data
public import CFSG.RankThree.PartOne.KLR.RootKernel

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KLR
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec charVal charVal_add charVal_neg
  charVal_smul charVal_mulVec charVal_smul_col)

open scoped Matrix MatrixGroups

section Certs

@[expose] def e8T3XAVec : Fin Tag.E8.rank → ℤ :=
  Pi.single (3 : Fin Tag.E8.rank) 1 - (2 : ℤ) • Pi.single (4 : Fin Tag.E8.rank) 1 +
    Pi.single (5 : Fin Tag.E8.rank) 1

@[expose] def e8T3XDVec : Fin Tag.E8.rank → ℤ :=
  -Pi.single (4 : Fin Tag.E8.rank) 1 + Pi.single (5 : Fin Tag.E8.rank) 1

@[expose] def e8T3ZAVec : Fin Tag.E8.rank → ℤ :=
  Pi.single (2 : Fin Tag.E8.rank) 1 - (2 : ℤ) • Pi.single (4 : Fin Tag.E8.rank) 1 +
    Pi.single (5 : Fin Tag.E8.rank) 1 + Pi.single (6 : Fin Tag.E8.rank) 1

@[expose] def e8T3ZDVec : Fin Tag.E8.rank → ℤ :=
  -Pi.single (4 : Fin Tag.E8.rank) 1 + Pi.single (6 : Fin Tag.E8.rank) 1 +
    Pi.single (7 : Fin Tag.E8.rank) 1

theorem e8T3XAVec_three : e8T3XAVec (3 : Fin Tag.E8.rank) = 1 := by decide

theorem e8T3XDVec_three : e8T3XDVec (3 : Fin Tag.E8.rank) = 0 := by decide

theorem e8T3ZAVec_two : e8T3ZAVec (2 : Fin Tag.E8.rank) = 1 := by decide

theorem e8T3ZDVec_two : e8T3ZDVec (2 : Fin Tag.E8.rank) = 0 := by decide

theorem e8T3W_transpose_mulVec_XA :
    (toMat Tag.E8.rank e8T3MList).transpose *ᵥ e8T3XAVec = -e8T3XDVec := by
  decide +kernel

theorem e8T3W_transpose_mulVec_XD :
    (toMat Tag.E8.rank e8T3MList).transpose *ᵥ e8T3XDVec = e8T3XAVec - e8T3XDVec := by
  decide +kernel

theorem e8T3W_transpose_mulVec_ZA :
    (toMat Tag.E8.rank e8T3MList).transpose *ᵥ e8T3ZAVec = -e8T3ZDVec := by
  decide +kernel

theorem e8T3W_transpose_mulVec_ZD :
    (toMat Tag.E8.rank e8T3MList).transpose *ᵥ e8T3ZDVec = e8T3ZAVec - e8T3ZDVec := by
  decide +kernel

theorem e8T3XColumn_eq_add_smul {p : ℕ} {ε : ℤ} {q : ZMod p} :
    e8T3XColumn ε q = (fun i => (e8T3XAVec i : ZMod p)) + ((ε : ZMod p) * q) •
      (fun i => (e8T3XDVec i : ZMod p)) := by
  funext i
  fin_cases i <;>
    simp only [e8T3XColumn, e8T3XAVec, e8T3XDVec, Pi.single_apply, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Pi.neg_apply] <;>
    split_ifs <;> ring

theorem e8T3ZColumn_eq_add_smul {p : ℕ} {ε : ℤ} {q : ZMod p} :
    e8T3ZColumn ε q = (fun i => (e8T3ZAVec i : ZMod p)) + ((ε : ZMod p) * q) •
      (fun i => (e8T3ZDVec i : ZMod p)) := by
  funext i
  fin_cases i <;>
    simp only [e8T3ZColumn, e8T3ZAVec, e8T3ZDVec, Pi.single_apply, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Pi.neg_apply] <;>
    split_ifs <;> ring

theorem e8T3XColumn_apply_three {p : ℕ} {ε : ℤ} {q : ZMod p} :
    e8T3XColumn ε q (3 : Fin Tag.E8.rank) = 1 := by
  rw [e8T3XColumn_eq_add_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [e8T3XAVec_three, e8T3XDVec_three]
  simp

theorem e8T3ZColumn_apply_two {p : ℕ} {ε : ℤ} {q : ZMod p} :
    e8T3ZColumn ε q (2 : Fin Tag.E8.rank) = 1 := by
  rw [e8T3ZColumn_eq_add_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [e8T3ZAVec_two, e8T3ZDVec_two]
  simp

theorem e8T3XColumn_ne_zero {p : ℕ} (hp : p.Prime) {ε : ℤ} {q : ZMod p} :
    e8T3XColumn ε q ≠ 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro h
  have h3 := congrFun h (3 : Fin Tag.E8.rank)
  rw [e8T3XColumn_apply_three] at h3
  have hdvd : (p : ℤ) ∣ (1 : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (1 : ℤ) p).1 (by simpa using h3)
  have hle := Int.le_of_dvd (by norm_num) hdvd
  have hp2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
  omega

end Certs

private theorem e8T3_eigen_coord {p : ℕ} {ε q : ZMod p} (hε : ε * ε = 1)
    (hq : q * q + ε * q + 1 = 0) (A D : ZMod p) :
    ε * -D + ε * q * (ε * (A - D)) = q * (A + ε * q * D) := by
  have h : ε + q + ε * q * q = 0 := by linear_combination ε * hq - q * hε
  linear_combination (q * A - D * q) * hε - D * h

section Certs

theorem e8T3XColumn_eigen {p : ℕ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {q : ℕ}
    (hq : (q : ZMod p) ^ 2 + (ε : ZMod p) * (q : ZMod p) + 1 = 0) :
    ((weylMatrix (e8T3We ε)).map (Int.cast : ℤ → ZMod p)).transpose *ᵥ
        e8T3XColumn ε (q : ZMod p) = (q : ZMod p) • e8T3XColumn ε (q : ZMod p) := by
  have hε2 : (ε : ZMod p) * (ε : ZMod p) = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hMε : ((weylMatrix (e8T3We ε)).map (Int.cast : ℤ → ZMod p)) =
      (ε : ZMod p) • ((toMat Tag.E8.rank e8T3MList).map (Int.cast : ℤ → ZMod p)) := by
    rw [weylMatrix_e8T3We hε]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hA : ((toMat Tag.E8.rank e8T3MList).map (Int.cast : ℤ → ZMod p)).transpose *ᵥ
      (fun i => (e8T3XAVec i : ZMod p)) = -(fun i => (e8T3XDVec i : ZMod p)) := by
    funext j
    have h : (((toMat Tag.E8.rank e8T3MList).transpose *ᵥ e8T3XAVec) j : ZMod p) =
        (((-e8T3XDVec : Fin Tag.E8.rank → ℤ)) j : ZMod p) := by
      rw [e8T3W_transpose_mulVec_XA]
    rw [show ((((toMat Tag.E8.rank e8T3MList).map (Int.cast : ℤ → ZMod p)).transpose) *ᵥ
        (fun i => (e8T3XAVec i : ZMod p))) j =
        (((toMat Tag.E8.rank e8T3MList).transpose *ᵥ e8T3XAVec) j : ZMod p) by
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply,
        Int.cast_sum, Int.cast_mul]]
    rw [h]
    simp
  have hB : ((toMat Tag.E8.rank e8T3MList).map (Int.cast : ℤ → ZMod p)).transpose *ᵥ
      (fun i => (e8T3XDVec i : ZMod p)) =
        (fun i => (e8T3XAVec i : ZMod p)) - (fun i => (e8T3XDVec i : ZMod p)) := by
    funext j
    have h : (((toMat Tag.E8.rank e8T3MList).transpose *ᵥ e8T3XDVec) j : ZMod p) =
        (((e8T3XAVec - e8T3XDVec : Fin Tag.E8.rank → ℤ)) j : ZMod p) := by
      rw [e8T3W_transpose_mulVec_XD]
    rw [show ((((toMat Tag.E8.rank e8T3MList).map (Int.cast : ℤ → ZMod p)).transpose) *ᵥ
        (fun i => (e8T3XDVec i : ZMod p))) j =
        (((toMat Tag.E8.rank e8T3MList).transpose *ᵥ e8T3XDVec) j : ZMod p) by
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply,
        Int.cast_sum, Int.cast_mul]]
    rw [h]
    simp
  rw [hMε, e8T3XColumn_eq_add_smul]
  simp only [Matrix.transpose_smul, Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
    hA, hB]
  funext i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
  have hq' : (q : ZMod p) * (q : ZMod p) + (ε : ZMod p) * (q : ZMod p) + 1 = 0 := by
    rw [sq] at hq; exact hq
  exact e8T3_eigen_coord hε2 hq' _ _

theorem e8T3ZColumn_eigen {p : ℕ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {q : ℕ}
    (hq : (q : ZMod p) ^ 2 + (ε : ZMod p) * (q : ZMod p) + 1 = 0) :
    ((weylMatrix (e8T3We ε)).map (Int.cast : ℤ → ZMod p)).transpose *ᵥ
        e8T3ZColumn ε (q : ZMod p) = (q : ZMod p) • e8T3ZColumn ε (q : ZMod p) := by
  have hε2 : (ε : ZMod p) * (ε : ZMod p) = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hMε : ((weylMatrix (e8T3We ε)).map (Int.cast : ℤ → ZMod p)) =
      (ε : ZMod p) • ((toMat Tag.E8.rank e8T3MList).map (Int.cast : ℤ → ZMod p)) := by
    rw [weylMatrix_e8T3We hε]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hA : ((toMat Tag.E8.rank e8T3MList).map (Int.cast : ℤ → ZMod p)).transpose *ᵥ
      (fun i => (e8T3ZAVec i : ZMod p)) = -(fun i => (e8T3ZDVec i : ZMod p)) := by
    funext j
    have h : (((toMat Tag.E8.rank e8T3MList).transpose *ᵥ e8T3ZAVec) j : ZMod p) =
        (((-e8T3ZDVec : Fin Tag.E8.rank → ℤ)) j : ZMod p) := by
      rw [e8T3W_transpose_mulVec_ZA]
    rw [show ((((toMat Tag.E8.rank e8T3MList).map (Int.cast : ℤ → ZMod p)).transpose) *ᵥ
        (fun i => (e8T3ZAVec i : ZMod p))) j =
        (((toMat Tag.E8.rank e8T3MList).transpose *ᵥ e8T3ZAVec) j : ZMod p) by
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply,
        Int.cast_sum, Int.cast_mul]]
    rw [h]
    simp
  have hB : ((toMat Tag.E8.rank e8T3MList).map (Int.cast : ℤ → ZMod p)).transpose *ᵥ
      (fun i => (e8T3ZDVec i : ZMod p)) =
        (fun i => (e8T3ZAVec i : ZMod p)) - (fun i => (e8T3ZDVec i : ZMod p)) := by
    funext j
    have h : (((toMat Tag.E8.rank e8T3MList).transpose *ᵥ e8T3ZDVec) j : ZMod p) =
        (((e8T3ZAVec - e8T3ZDVec : Fin Tag.E8.rank → ℤ)) j : ZMod p) := by
      rw [e8T3W_transpose_mulVec_ZD]
    rw [show ((((toMat Tag.E8.rank e8T3MList).map (Int.cast : ℤ → ZMod p)).transpose) *ᵥ
        (fun i => (e8T3ZDVec i : ZMod p))) j =
        (((toMat Tag.E8.rank e8T3MList).transpose *ᵥ e8T3ZDVec) j : ZMod p) by
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply,
        Int.cast_sum, Int.cast_mul]]
    rw [h]
    simp
  rw [hMε, e8T3ZColumn_eq_add_smul]
  simp only [Matrix.transpose_smul, Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
    hA, hB]
  funext i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
  have hq' : (q : ZMod p) * (q : ZMod p) + (ε : ZMod p) * (q : ZMod p) + 1 = 0 := by
    rw [sq] at hq; exact hq
  exact e8T3_eigen_coord hε2 hq' _ _

end Certs

section General

variable {τ : Tag} {L : Type} [Field L]

theorem rootDiagUnit_mem_twistedTorus_of_eigenColumn {p : ℕ} [NeZero p] {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ p) {n : ModGL τ L} {Fr : L →+* L} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q)
    {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    (hT : twistedTorusOf n (Units.map (entrywiseHom Fr)) =
      (fixedCharTuples M Fr).map (rootDiagUnitHom τ L))
    {z : Fin τ.rank → ZMod p}
    (hz : ((M.map (Int.cast : ℤ → ZMod p)).transpose) *ᵥ z = (q : ZMod p) • z) :
    rootDiagUnit τ (fun i => ζ ^ (z i).val) ∈ twistedTorusOf n (Units.map (entrywiseHom Fr)) := by
  rw [hT]
  refine ⟨fun i => ζ ^ (z i).val, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_fixedCharTuples_iff]
  intro u
  have hker : ∀ v : Fin τ.rank → ℤ,
      rootChar (fun i => ζ ^ (z i).val) v = 1 ↔ charVal z v = 0 :=
    fun v => rootChar_zetaPow_eq_one_iff_charVal hζ z v
  have hsplit : rootChar (fun i => ζ ^ (z i).val) (M *ᵥ u) =
      rootChar (fun i => ζ ^ (z i).val) u ^ q := by
    have h1 : rootChar (fun i => ζ ^ (z i).val) (M *ᵥ u) *
        (rootChar (fun i => ζ ^ (z i).val) u ^ q)⁻¹ = 1 := by
      have h2 : rootChar (fun i => ζ ^ (z i).val) (M *ᵥ u) *
          (rootChar (fun i => ζ ^ (z i).val) u ^ q)⁻¹ =
          rootChar (fun i => ζ ^ (z i).val) (M *ᵥ u + (-(q : ℤ)) • u) := by
        rw [rootChar_add, rootChar_zsmul, _root_.zpow_neg, zpow_natCast]
      rw [h2, hker]
      rw [charVal_add, charVal_smul, ← charVal_mulVec, hz, charVal_smul_col]
      push_cast
      ring
    exact (mul_inv_eq_one.1 h1)
  rw [CTTorus.map_units_eq_pow hFr, hsplit]

end General

section Certs

theorem e8T3XColumn_mem_twistedTorus {L : Type} [Field L] {p : ℕ} [NeZero p] {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ p) {n : ModGL Tag.E8 L} {Fr : L →+* L} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hq : (q : ZMod p) ^ 2 + (ε : ZMod p) * (q : ZMod p) + 1 = 0)
    (hT : twistedTorusOf n (Units.map (entrywiseHom Fr)) =
      (fixedCharTuples (weylMatrix (e8T3We ε)) Fr).map (rootDiagUnitHom Tag.E8 L)) :
    rootDiagUnit Tag.E8 (fun i => ζ ^ ((e8T3XColumn ε (q : ZMod p)) i).val) ∈
      twistedTorusOf n (Units.map (entrywiseHom Fr)) :=
  rootDiagUnit_mem_twistedTorus_of_eigenColumn hζ hFr hT (e8T3XColumn_eigen hε hq)

theorem e8T3ZColumn_mem_twistedTorus {L : Type} [Field L] {p : ℕ} [NeZero p] {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ p) {n : ModGL Tag.E8 L} {Fr : L →+* L} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hq : (q : ZMod p) ^ 2 + (ε : ZMod p) * (q : ZMod p) + 1 = 0)
    (hT : twistedTorusOf n (Units.map (entrywiseHom Fr)) =
      (fixedCharTuples (weylMatrix (e8T3We ε)) Fr).map (rootDiagUnitHom Tag.E8 L)) :
    rootDiagUnit Tag.E8 (fun i => ζ ^ ((e8T3ZColumn ε (q : ZMod p)) i).val) ∈
      twistedTorusOf n (Units.map (entrywiseHom Fr)) :=
  rootDiagUnit_mem_twistedTorus_of_eigenColumn hζ hFr hT (e8T3ZColumn_eigen hε hq)

theorem ncard_rootKernel_e8T3XColumn {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {q : ZMod p} (hq : q ^ 2 + (ε : ZMod p) * q + 1 = 0) :
    (rootKernel (e8T3XColumn ε q)).ncard = 72 := by
  rw [rootKernel_e8T3XColumn hp hp3 hε hq]
  show (e8T3XKernel).ncard = 72
  rw [show e8T3XKernel = {v : Fin Tag.E8.rank → ℤ |
      IsRoot Tag.E8 v ∧ (v 3 = v 4 ∧ v 4 = v 5)} by
    ext v; simp [e8T3XKernel]]
  rw [ncard_isRoot_and (P := fun v : Fin Tag.E8.rank → ℤ => v 3 = v 4 ∧ v 4 = v 5)]
  decide +kernel

theorem ncard_rootKernel_e8T3ZColumn {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {q : ZMod p} (hq : q ^ 2 + (ε : ZMod p) * q + 1 = 0) :
    (rootKernel (e8T3ZColumn ε q)).ncard = 30 := by
  rw [rootKernel_e8T3ZColumn hp hp3 hε hq]
  show (e8T3ZKernel).ncard = 30
  rw [show e8T3ZKernel = {v : Fin Tag.E8.rank → ℤ |
      IsRoot Tag.E8 v ∧ (v 2 - 2 * v 4 + v 5 + v 6 = 0 ∧ -v 4 + v 6 + v 7 = 0)} by
    ext v; simp [e8T3ZKernel]]
  rw [ncard_isRoot_and (P := fun v : Fin Tag.E8.rank → ℤ =>
    v 2 - 2 * v 4 + v 5 + v 6 = 0 ∧ -v 4 + v 6 + v 7 = 0)]
  decide +kernel

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three
