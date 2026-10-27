module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSz32Field
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sz32

open CFSG.Blueprint Matrix

abbrev Mat := Matrix (Fin 4) (Fin 4) F32

abbrev Vec := Fin 4 → F32

@[expose] def toMat (A : Array F32) : Mat := Matrix.of fun i j => A[4 * i.val + j.val]!

@[expose] def omega : F32 := ⟨0, 1, 0, 0, 0⟩

@[expose] def g0Mat : Mat := suzukiW F32 * suzukiS 2 0 omega

@[expose] def g0A : Array F32 :=
  #[⟨1, 0, 1, 1, 0⟩, ⟨0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨1, 0, 0, 0, 0⟩,
    ⟨0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩,
    ⟨0, 0, 0, 0, 0⟩, ⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩,
    ⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩]

theorem toMat_g0A : toMat g0A = g0Mat := by decide +kernel

@[expose] def mulA (A B : Array F32) : Array F32 :=
  let e := fun i j : ℕ => A[4 * i]! * B[j]! + A[4 * i + 1]! * B[4 + j]! +
    A[4 * i + 2]! * B[8 + j]! + A[4 * i + 3]! * B[12 + j]!
  #[e 0 0, e 0 1, e 0 2, e 0 3, e 1 0, e 1 1, e 1 2, e 1 3,
    e 2 0, e 2 1, e 2 2, e 2 3, e 3 0, e 3 1, e 3 2, e 3 3]

@[expose] def idA : Array F32 := #[1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]

@[expose] def gArr : ℕ → Array F32
  | 0 => idA
  | n + 1 => mulA (gArr n) g0A

@[expose] def gList : List (Array F32) := (List.range 25).map gArr

@[expose] def t1A : Array F32 :=
  #[⟨1, 0, 0, 1, 1⟩, ⟨1, 0, 1, 0, 0⟩, ⟨1, 1, 0, 0, 0⟩, ⟨1, 1, 1, 1, 0⟩,
    ⟨1, 0, 1, 0, 0⟩, ⟨1, 1, 1, 0, 1⟩, ⟨0, 1, 1, 0, 1⟩, ⟨1, 1, 0, 0, 0⟩,
    ⟨1, 1, 0, 0, 0⟩, ⟨0, 1, 1, 0, 1⟩, ⟨1, 0, 0, 0, 1⟩, ⟨1, 1, 0, 1, 1⟩,
    ⟨1, 1, 1, 1, 0⟩, ⟨1, 1, 0, 0, 0⟩, ⟨1, 1, 0, 1, 1⟩, ⟨0, 1, 1, 1, 1⟩]
@[expose] def t2A : Array F32 :=
  #[⟨1, 0, 1, 1, 0⟩, ⟨1, 0, 1, 1, 1⟩, ⟨1, 0, 0, 0, 1⟩, ⟨1, 1, 1, 1, 0⟩,
    ⟨1, 0, 1, 1, 1⟩, ⟨1, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1⟩, ⟨1, 0, 0, 0, 1⟩,
    ⟨1, 0, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1⟩, ⟨0, 1, 0, 0, 1⟩, ⟨1, 1, 0, 0, 0⟩,
    ⟨1, 1, 1, 1, 0⟩, ⟨1, 0, 0, 0, 1⟩, ⟨1, 1, 0, 0, 0⟩, ⟨1, 1, 0, 1, 0⟩]
@[expose] def t3A : Array F32 :=
  #[⟨1, 1, 0, 1, 0⟩, ⟨1, 1, 0, 0, 0⟩, ⟨1, 0, 0, 0, 1⟩, ⟨1, 1, 1, 1, 0⟩,
    ⟨1, 1, 0, 0, 0⟩, ⟨0, 1, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1⟩, ⟨1, 0, 0, 0, 1⟩,
    ⟨1, 0, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1⟩, ⟨1, 0, 1, 0, 1⟩, ⟨1, 0, 1, 1, 1⟩,
    ⟨1, 1, 1, 1, 0⟩, ⟨1, 0, 0, 0, 1⟩, ⟨1, 0, 1, 1, 1⟩, ⟨1, 0, 1, 1, 0⟩]

@[expose] def t0Mat : Mat := toMat t1A

@[expose] def t0Mat2 : Mat := toMat t2A

@[expose] def t0Mat3 : Mat := toMat t3A

theorem t0Mat_eq : t0Mat = g0Mat ^ 5 := by decide +kernel

theorem t0Mat2_eq : t0Mat2 = t0Mat * t0Mat := by decide +kernel

theorem t0Mat3_eq : t0Mat3 = t0Mat2 * t0Mat := by decide +kernel

theorem g0Mat_pow_25 : g0Mat ^ 25 = 1 := by decide +kernel

theorem g0Mat_pow_5_ne : g0Mat ^ 5 ≠ 1 := by decide +kernel

@[expose] def e0 : Vec := ![1, 0, 0, 0]

@[expose] def bMat : Mat :=
  Matrix.of fun i j => (![1, t0Mat, t0Mat2, t0Mat3] j *ᵥ e0) i

@[expose] def bInvA : Array F32 :=
  #[⟨1, 0, 0, 0, 0⟩, ⟨1, 1, 1, 0, 1⟩, ⟨0, 1, 1, 1, 1⟩, ⟨1, 1, 1, 1, 0⟩,
    ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0⟩,
    ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 0, 1⟩, ⟨1, 1, 0, 1, 0⟩, ⟨1, 0, 0, 1, 1⟩,
    ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 0, 1⟩, ⟨1, 0, 0, 1, 0⟩, ⟨0, 1, 0, 0, 1⟩]

@[expose] def bInv : Mat := toMat bInvA

theorem bMat_mul_bInv : bMat * bInv = 1 := by decide +kernel

@[expose] def polyMat (c0 c1 c2 c3 : F32) : Mat :=
  Matrix.of fun i j => c0 * (1 : Mat) i j + c1 * t0Mat i j + c2 * t0Mat2 i j + c3 * t0Mat3 i j

theorem polyMat_eq (c0 c1 c2 c3 : F32) :
    polyMat c0 c1 c2 c3 = c0 • (1 : Mat) + c1 • t0Mat + c2 • t0Mat2 + c3 • t0Mat3 := by
  refine Matrix.ext fun i j => ?_
  simp [polyMat]

theorem commute_t0Mat2 {h : Mat} (hc : Commute h t0Mat) : Commute h t0Mat2 := by
  rw [t0Mat2_eq]
  exact hc.mul_right hc

theorem commute_t0Mat3 {h : Mat} (hc : Commute h t0Mat) : Commute h t0Mat3 := by
  rw [t0Mat3_eq]
  exact (commute_t0Mat2 hc).mul_right hc

theorem commute_polyMat (c0 c1 c2 c3 : F32) : Commute (polyMat c0 c1 c2 c3) t0Mat := by
  rw [polyMat_eq]
  have h1 : Commute t0Mat t0Mat := Commute.refl _
  refine Commute.add_left (Commute.add_left (Commute.add_left ?_ ?_) ?_) ?_
  · exact Commute.smul_left (Commute.one_left _) _
  · exact Commute.smul_left h1 _
  · exact Commute.smul_left (commute_t0Mat2 h1).symm _
  · exact Commute.smul_left (commute_t0Mat3 h1).symm _

theorem commute_column {M : Mat} (hM : Commute M t0Mat) (j : Fin 4) :
    Commute M (![1, t0Mat, t0Mat2, t0Mat3] j) := by
  fin_cases j
  · exact Commute.one_right _
  · exact hM
  · exact commute_t0Mat2 hM
  · exact commute_t0Mat3 hM

theorem eq_polyMat_of_commute {h : Mat} (hc : Commute h t0Mat) :
    h = polyMat ((bInv *ᵥ (h *ᵥ e0)) 0) ((bInv *ᵥ (h *ᵥ e0)) 1) ((bInv *ᵥ (h *ᵥ e0)) 2)
      ((bInv *ᵥ (h *ᵥ e0)) 3) := by
  set c : Vec := bInv *ᵥ (h *ᵥ e0) with hcdef
  set P : Mat := polyMat (c 0) (c 1) (c 2) (c 3) with hP
  have hPc : Commute P t0Mat := commute_polyMat _ _ _ _
  have hPe : P *ᵥ e0 = h *ᵥ e0 := by
    have h1 : P *ᵥ e0 = bMat *ᵥ c := by
      funext i
      simp only [mulVec, dotProduct, polyMat, Fin.isValue, of_apply, e0, Fin.sum_univ_four,
        cons_val_zero, mul_one, cons_val_one, mul_zero, add_zero, cons_val, bMat,
        Nat.succ_eq_add_one, Nat.reduceAdd, P]
      ring
    rw [h1, hcdef, Matrix.mulVec_mulVec, bMat_mul_bInv, Matrix.one_mulVec]
  have hB : h * bMat = P * bMat := by
    refine Matrix.ext fun i j => ?_
    have key : ∀ M : Mat, Commute M t0Mat →
        (M * bMat) i j = (![1, t0Mat, t0Mat2, t0Mat3] j *ᵥ (M *ᵥ e0)) i := by
      intro M hM
      have h2 : M *ᵥ (![1, t0Mat, t0Mat2, t0Mat3] j *ᵥ e0) =
          ![1, t0Mat, t0Mat2, t0Mat3] j *ᵥ (M *ᵥ e0) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, (commute_column hM j).eq]
      rw [← h2]
      simp [Matrix.mul_apply, bMat, Matrix.mulVec, dotProduct]
    rw [key h hc, key P hPc, hPe]
  calc h = h * (bMat * bInv) := by rw [bMat_mul_bInv, mul_one]
    _ = (h * bMat) * bInv := (mul_assoc _ _ _).symm
    _ = (P * bMat) * bInv := by rw [hB]
    _ = P := by rw [mul_assoc, bMat_mul_bInv, mul_one]

@[expose] def polyEntry (c0 c1 c2 c3 : F32) (i j : Fin 4) : F32 :=
  c0 * (if i = j then 1 else 0) + c1 * t1A[4 * i.val + j.val]! + c2 * t2A[4 * i.val + j.val]! +
    c3 * t3A[4 * i.val + j.val]!

@[expose] def OnOmega4 (a : ℕ) {K : Type} [Field K] (y0 y1 y2 y3 : K) : Prop :=
  (y0 = 0 ∧ y1 = 0 ∧ y2 = 0 ∧ y3 ≠ 0) ∨
    (y0 ≠ 0 ∧ y3 * y0 ^ (2 ^ (a + 1) + 1) =
      y1 ^ (2 ^ (a + 1) + 2) + y1 * y2 * y0 ^ 2 ^ (a + 1) + y2 ^ 2 ^ (a + 1) * y0 ^ 2)

instance instDecidableOnOmega4 (a : ℕ) {K : Type} [Field K] [DecidableEq K] (y0 y1 y2 y3 : K) :
    Decidable (OnOmega4 a y0 y1 y2 y3) := by
  unfold OnOmega4
  infer_instance

@[expose] def OnOmegaGen (a : ℕ) {K : Type} [Field K] (y : Fin 4 → K) : Prop :=
  OnOmega4 a (y 0) (y 1) (y 2) (y 3)

@[expose] def lineVec (u v : F32) : Vec := ![1, u, v, suzukiN 2 u v]

@[expose] def inftyVec : Vec := ![0, 0, 0, 1]

@[expose] def lineA (u v : F32) : Array F32 := #[1, u, v, suzukiN 2 u v]

@[expose] def inftyA : Array F32 := #[0, 0, 0, 1]

@[expose] def testUV : List (F32 × F32) :=
  [(0, 0), (1, 0), (omega, 0), (0, 1), (omega, ⟨1, 1, 0, 0, 0⟩),
    (⟨1, 0, 1, 0, 0⟩, ⟨1, 1, 1, 0, 0⟩)]

@[expose] def testPtsA : List (Array F32) := inftyA :: testUV.map fun p => lineA p.1 p.2

@[expose] def mulVecA (A v : Array F32) : Array F32 :=
  let e := fun i : ℕ => A[4 * i]! * v[0]! + A[4 * i + 1]! * v[1]! + A[4 * i + 2]! * v[2]! +
    A[4 * i + 3]! * v[3]!
  #[e 0, e 1, e 2, e 3]

@[expose] def testData : List (Array F32 × Array F32 × Array F32 × Array F32) :=
  testPtsA.map fun p => (p, mulVecA t1A p, mulVecA t2A p, mulVecA t3A p)

@[expose] def imgTest (c0 c1 c2 c3 : F32) (q : Array F32 × Array F32 × Array F32 × Array F32) :
    Prop :=
  OnOmega4 2 (c0 * q.1[0]! + c1 * q.2.1[0]! + c2 * q.2.2.1[0]! + c3 * q.2.2.2[0]!)
    (c0 * q.1[1]! + c1 * q.2.1[1]! + c2 * q.2.2.1[1]! + c3 * q.2.2.2[1]!)
    (c0 * q.1[2]! + c1 * q.2.1[2]! + c2 * q.2.2.1[2]! + c3 * q.2.2.2[2]!)
    (c0 * q.1[3]! + c1 * q.2.1[3]! + c2 * q.2.2.1[3]! + c3 * q.2.2.2[3]!)

instance instDecidableImgTest (c0 c1 c2 c3 : F32)
    (q : Array F32 × Array F32 × Array F32 × Array F32) :
    Decidable (imgTest c0 c1 c2 c3 q) := by
  unfold imgTest
  infer_instance

@[expose] def GoodC (c0 c1 c2 c3 : F32) : Prop :=
  (∀ q ∈ testData, imgTest c0 c1 c2 c3 q) →
    ∃ A ∈ gList, ∃ l : F32, ∀ i j : Fin 4,
      polyEntry c0 c1 c2 c3 i j = l * A[4 * i.val + j.val]!

instance instDecidableGoodC (c0 c1 c2 c3 : F32) : Decidable (GoodC c0 c1 c2 c3) := by
  unfold GoodC
  infer_instance

@[expose] def coef (i : ℕ) (w0 w1 w2 w3 : F32) : F32 :=
  bInvA[4 * i]! * w0 + bInvA[4 * i + 1]! * w1 + bInvA[4 * i + 2]! * w2 +
    bInvA[4 * i + 3]! * w3

@[expose] def GoodW (w0 w1 w2 w3 : F32) : Prop :=
  GoodC (coef 0 w0 w1 w2 w3) (coef 1 w0 w1 w2 w3) (coef 2 w0 w1 w2 w3) (coef 3 w0 w1 w2 w3)

instance instDecidableGoodW (w0 w1 w2 w3 : F32) : Decidable (GoodW w0 w1 w2 w3) := by
  unfold GoodW
  infer_instance

@[expose] def CheckAll : Prop :=
  (∀ u v : F32, GoodW 1 u v (suzukiN 2 u v)) ∧ GoodW 0 0 0 1

instance instDecidableCheckAll : Decidable CheckAll := by
  unfold CheckAll
  infer_instance

end CFSG.AGLEmbedding.KFactProofs.Sz32
