module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.ClsBits
public import Mathlib.LinearAlgebra.Matrix.Notation

public section

namespace CFSG.EvenSporadicStandard.Wong77.Cls

open Matrix

@[expose] def aN : Fin 2 → ℕ := ![739, 1141]

@[expose] def YN : Fin 2 → List ℕ :=
  ![[1, 411, 512, 4, 1644, 739, 16, 1685, 367, 64, 1393],
    [1, 870, 512, 4, 493, 1141, 16, 1972, 1355, 64, 1594]]

@[expose] def BinvN : Fin 2 → List ℕ :=
  ![[2, 948, 1477, 512, 1024, 605, 128, 303, 32, 4, 2047],
    [2, 1167, 1865, 512, 1024, 1141, 128, 571, 32, 4, 2046]]

@[expose] def yN : Fin 2 → ℕ := ![720, 797]

@[expose] def stdAN : Fin 2 → List ℕ :=
  ![[1367, 621, 1004, 615, 1833, 436, 572, 147, 1474, 1878, 1024],
    [1594, 797, 4, 8, 1972, 32, 1740, 512, 256, 128, 1024]]

@[expose] def stdBN : Fin 2 → List ℕ :=
  ![[621, 1004, 615, 1833, 436, 572, 147, 1474, 1878, 1024, 887],
    [797, 4, 8, 1972, 32, 1740, 512, 256, 128, 1024, 870]]

@[expose] def stdA : Fin 2 → Mat :=
  ![!![1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0;
      1, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0;
      1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0;
      0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0;
      0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0;
      1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0;
      0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0;
      1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0;
      0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0;
      1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1],
    !![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0;
      1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0;
      1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0;
      0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0;
      1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0;
      1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1]]

@[expose] def stdB : Fin 2 → Mat :=
  ![!![1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1;
      0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1;
      1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1;
      1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1;
      1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1;
      1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1;
      0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0;
      0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1;
      1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1;
      0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0],
    !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
      1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1;
      1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0;
      1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1;
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1;
      0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0;
      1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1;
      1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1;
      0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0]]


@[expose] def aStd (i : Fin 2) : Vec := toVec (aN i)

@[expose] def cM (i : Fin 2) : Mat := comp (aStd i)

@[expose] def yM (i : Fin 2) : Mat := toMat (YN i)

@[expose] def upM (i : Fin 2) : Mat := cM i ^ 9 * yM i ^ 5

@[expose] def epV (i : Fin 2) : Vec := (cM i ^ 12) *ᵥ e0

@[expose] def binvM (i : Fin 2) : Mat := toMat (BinvN i)

@[expose] def yV (i : Fin 2) : Vec := toVec (yN i)

@[expose] def xM (i : Fin 2) : Mat := phi (yM i) (binvM i) (yV i)

@[expose] def checkCyc : Bool :=
  (List.range 2048).all fun a => !eqV (itN (compN a) 23 1) 1 || a == aN 0 || a == aN 1

@[expose] def checkY (Y C : List ℕ) : Bool :=
  eqV (mvN Y 1) 1 && eqM (mulN Y C) (mulN (powN C 16) Y)

@[expose] def checkFix (Y : List ℕ) : Bool :=
  (List.range 2048).all fun z => !eqV (mvN Y z) z || z == 0 || z == 1

@[expose] def checkEp (Up : List ℕ) (ep : ℕ) : Bool := eqV (mvN Up ep) ep && !eqV ep 0

@[expose] def checkBinv (Up : List ℕ) (ep : ℕ) (Binv : List ℕ) : Bool :=
  eqM (mulN (kryN Up ep 1) Binv) oneN

@[expose] def uniqTest (Y Up X : List ℕ) (y y₀ : ℕ) : Bool :=
  !eqM (mulN Y X) (mulN X Up) || !eqM (powN X 4) oneN || y == y₀

@[expose] def checkUniq (Y Up Binv : List ℕ) (y₀ : ℕ) : Bool :=
  (List.range 2048).all fun y => uniqTest Y Up (mulN (kryN Y 1 y) Binv) y y₀

@[expose] def wordAN (C Y X : List ℕ) : List ℕ :=
  mulN (mulN (mulN (mulN (mulN (mulN (mulN (mulN (mulN (powN X 3) C) X) (powN C 21)) Y)
    (powN X 3)) (powN C 22)) (powN X 3)) Y) (powN X 3)

@[expose] def checkWords (A B C Y X : List ℕ) : Bool :=
  eqM A (wordAN C Y X) && eqM B (mulN A C)

@[expose] def checkOneAux (C Y Binv : List ℕ) (y₀ : ℕ) (A B : List ℕ) : Bool :=
  let Up := mulN (powN C 9) (powN Y 5)
  let ep := mvN (powN C 12) 1
  checkY Y C && checkFix Y && checkEp Up ep && checkBinv Up ep Binv && checkUniq Y Up Binv y₀ &&
    checkWords A B C Y (mulN (kryN Y 1 y₀) Binv)

@[expose] def checkOne (i : Fin 2) : Bool :=
  checkOneAux (compN (aN i)) (YN i) (BinvN i) (yN i) (stdAN i) (stdBN i)

@[expose] def clsCheck : Bool := checkCyc && checkOne 0 && checkOne 1

structure ClsSpec : Prop where
  cyc : ∀ a : Vec, (comp a ^ 23) *ᵥ e0 = e0 → ∃ i : Fin 2, a = aStd i
  yfix : ∀ i, yM i *ᵥ e0 = e0 ∧ yM i * cM i = cM i ^ 16 * yM i
  fix : ∀ (i : Fin 2) (z : Vec), yM i *ᵥ z = z → z = 0 ∨ z = e0
  ep : ∀ i, upM i *ᵥ epV i = epV i ∧ epV i ≠ 0
  binv : ∀ i, kry (upM i) (epV i) e0 * binvM i = 1
  uniq : ∀ (i : Fin 2) (y : Vec),
    yM i * phi (yM i) (binvM i) y = phi (yM i) (binvM i) y * upM i →
      phi (yM i) (binvM i) y ^ 4 = 1 → y = yV i
  words : ∀ i, stdA i = wordA (cM i) (yM i) (xM i) ∧ stdB i = stdA i * cM i

theorem stdA_eq (i : Fin 2) : stdA i = toMat (stdAN i) := by
  fin_cases i <;> decide

theorem stdB_eq (i : Fin 2) : stdB i = toMat (stdBN i) := by
  fin_cases i <;> decide

theorem toMat_compN_aN (i : Fin 2) : toMat (compN (aN i)) = cM i := toMat_compN _

theorem toMat_up (i : Fin 2) :
    toMat (mulN (powN (compN (aN i)) 9) (powN (YN i) 5)) = upM i := by
  rw [mulN_eq, powN_eq, powN_eq, toMat_compN_aN]
  rfl

theorem toVec_ep (i : Fin 2) : toVec (mvN (powN (compN (aN i)) 12) 1) = epV i := by
  rw [mvN_eq, powN_eq, toMat_compN_aN, toVec_one]
  rfl

theorem toMat_xcand (i : Fin 2) (y : ℕ) :
    toMat (mulN (kryN (YN i) 1 y) (BinvN i)) = phi (yM i) (binvM i) (toVec y) := by
  rw [mulN_eq, toMat_kryN, toVec_one]
  rfl

theorem checkCyc_spec (h : checkCyc = true) :
    ∀ a : Vec, (comp a ^ 23) *ᵥ e0 = e0 → ∃ i : Fin 2, a = aStd i := by
  intro a ha
  obtain ⟨n, hn, rfl⟩ := exists_lt_toVec a
  have h1 := List.all_eq_true.1 h n (List.mem_range.2 hn)
  have h2 : eqV (itN (compN n) 23 1) 1 = true := by
    rw [eqV_iff, itN_eq, toMat_compN, toVec_one, ha]
  rw [h2] at h1
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h1
  rcases h1 with h1 | h1
  · exact ⟨0, by rw [h1]; rfl⟩
  · exact ⟨1, by rw [h1]; rfl⟩

theorem checkOne_spec (i : Fin 2) (h : checkOne i = true) :
    (yM i *ᵥ e0 = e0 ∧ yM i * cM i = cM i ^ 16 * yM i) ∧
    (∀ z : Vec, yM i *ᵥ z = z → z = 0 ∨ z = e0) ∧
    (upM i *ᵥ epV i = epV i ∧ epV i ≠ 0) ∧
    kry (upM i) (epV i) e0 * binvM i = 1 ∧
    (∀ y : Vec, yM i * phi (yM i) (binvM i) y = phi (yM i) (binvM i) y * upM i →
      phi (yM i) (binvM i) y ^ 4 = 1 → y = yV i) ∧
    (stdA i = wordA (cM i) (yM i) (xM i) ∧ stdB i = stdA i * cM i) := by
  simp only [checkOne, checkOneAux, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hy, hfix⟩, hep⟩, hbinv⟩, huniq⟩, hw⟩ := h
  have hX : ∀ y : ℕ, toMat (mulN (kryN (YN i) 1 y) (BinvN i)) =
      phi (yM i) (binvM i) (toVec y) := toMat_xcand i
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [checkY, Bool.and_eq_true] at hy
    obtain ⟨hy1, hy2⟩ := hy
    rw [eqV_iff, mvN_eq, toVec_one] at hy1
    rw [eqM_iff, mulN_eq, mulN_eq, powN_eq, toMat_compN_aN] at hy2
    exact ⟨hy1, hy2⟩
  · intro z hz
    obtain ⟨n, hn, rfl⟩ := exists_lt_toVec z
    have h1 := List.all_eq_true.1 hfix n (List.mem_range.2 hn)
    have h2 : eqV (mvN (YN i) n) n = true := by
      rw [eqV_iff, mvN_eq]; exact hz
    rw [h2] at h1
    simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h1
    rcases h1 with h1 | h1
    · left; rw [h1, toVec_zero]
    · right; rw [h1, toVec_one]
  · simp only [checkEp, Bool.and_eq_true] at hep
    obtain ⟨hep1, hep2⟩ := hep
    rw [eqV_iff, mvN_eq, toVec_ep] at hep1
    refine ⟨?_, ?_⟩
    · rw [toMat_up] at hep1
      exact hep1
    · intro h0
      have : eqV (mvN (powN (compN (aN i)) 12) 1) 0 = true := by
        rw [eqV_iff, toVec_ep, toVec_zero, h0]
      rw [this] at hep2
      exact absurd hep2 (by simp)
  · simp only [checkBinv] at hbinv
    rw [eqM_iff, mulN_eq, toMat_kryN, toMat_oneN, toVec_one, toVec_ep, toMat_up] at hbinv
    exact hbinv
  · intro y h1 h2
    obtain ⟨n, hn, rfl⟩ := exists_lt_toVec y
    have h3 := List.all_eq_true.1 huniq n (List.mem_range.2 hn)
    simp only [uniqTest, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h3
    have e1 : eqM (mulN (YN i) (mulN (kryN (YN i) 1 n) (BinvN i)))
        (mulN (mulN (kryN (YN i) 1 n) (BinvN i)) (mulN (powN (compN (aN i)) 9) (powN (YN i) 5))) =
        true := by
      rw [eqM_iff]
      simp only [mulN_eq, powN_eq, toMat_kryN, toVec_one, toMat_compN_aN]
      exact h1
    have e2 : eqM (powN (mulN (kryN (YN i) 1 n) (BinvN i)) 4) oneN = true := by
      rw [eqM_iff, powN_eq, hX, toMat_oneN]
      exact h2
    rcases h3 with (h3 | h3) | h3
    · rw [e1] at h3; exact absurd h3 (by simp)
    · rw [e2] at h3; exact absurd h3 (by simp)
    · rw [h3]; rfl
  · simp only [checkWords, Bool.and_eq_true] at hw
    obtain ⟨hw1, hw2⟩ := hw
    rw [eqM_iff, ← stdA_eq] at hw1
    rw [eqM_iff, mulN_eq, ← stdA_eq, ← stdB_eq, toMat_compN_aN] at hw2
    refine ⟨?_, hw2⟩
    rw [hw1]
    simp only [wordAN, wordA, mulN_eq, powN_eq, toMat_compN_aN, hX]
    rfl

theorem clsCheck_spec (h : clsCheck = true) : ClsSpec := by
  simp only [clsCheck, Bool.and_eq_true] at h
  obtain ⟨⟨hcyc, h0⟩, h1⟩ := h
  have hone : ∀ i : Fin 2, checkOne i = true := by
    intro i
    fin_cases i
    · exact h0
    · exact h1
  exact ⟨checkCyc_spec hcyc, fun i => (checkOne_spec i (hone i)).1,
    fun i => (checkOne_spec i (hone i)).2.1, fun i => (checkOne_spec i (hone i)).2.2.1,
    fun i => (checkOne_spec i (hone i)).2.2.2.1, fun i => (checkOne_spec i (hone i)).2.2.2.2.1,
    fun i => (checkOne_spec i (hone i)).2.2.2.2.2⟩

end CFSG.EvenSporadicStandard.Wong77.Cls
