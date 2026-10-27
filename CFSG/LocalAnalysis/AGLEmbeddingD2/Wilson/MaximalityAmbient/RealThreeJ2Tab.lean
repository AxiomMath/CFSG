module

public import CFSG.Sporadic.J2.Simple
public import CFSG.Certificates.Kernel.Common.ListGroup
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree.J2Tab

open CFSG.Sporadic.J1.Native (mulL idL colsL dotL)
open CFSG.KC.ListGroup (grp)

@[expose] def mulF (p : ℕ) (X C : List (List ℕ)) : List (List ℕ) :=
  X.map fun r => C.map fun c => dotL r c % p

theorem mulL_eq (p d : ℕ) (X Y : List (List ℕ)) : mulL p d X Y = mulF p X (colsL d Y) := rfl

@[expose] def abL (l : ℕ) : List (List ℕ) :=
  if l = 1 then CFSG.Sporadic.J2.Native.mA else CFSG.Sporadic.J2.Native.mB

@[expose] def wordR : List ℕ → List (List ℕ)
  | [] => idL 14
  | l :: w => mulL 5 14 (abL l) (wordR w)

theorem wordR_rep {G : Type} [Monoid G] (R : List (List ℕ) → G → Prop)
    (mul : ∀ {L M : List (List ℕ)} {g h : G}, R L g → R M h → R (mulL 5 14 L M) (g * h))
    (one : R (idL 14) 1) (e : ℕ → G) (hL : ∀ l, R (abL l) (e l)) :
    ∀ w : List ℕ, R (wordR w) ((w.map e).prod)
  | [] => one
  | l :: w => by
    rw [wordR, List.map_cons, List.prod_cons]
    exact mul (hL l) (wordR_rep R mul one e hL w)

#kc_repo #kc_decls CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree.J2Tab "CFSG/LocalAnalysis/AGLEmbeddingD2/Wilson/MaximalityAmbient/data/realthreej2_tab.txt" 67693 6767314375548514488

@[expose] noncomputable def xC : List (List ℕ) := grp 14 xCF

@[expose] noncomputable def yC : List (List ℕ) := grp 14 yCF

@[expose] noncomputable def zC : List (List ℕ) := grp 14 zCF

@[expose] def ix (p : Fin 3 × Fin 3 × Fin 3) : ℕ := 9 * (p.1 : ℕ) + 3 * (p.2.1 : ℕ) + (p.2.2 : ℕ)

@[expose] def unix (n : ℕ) : Fin 3 × Fin 3 × Fin 3 :=
  (⟨n / 9 % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨n / 3 % 3, Nat.mod_lt _ (by norm_num)⟩,
    ⟨n % 3, Nat.mod_lt _ (by norm_num)⟩)

@[expose] noncomputable def ftL : List (List (List ℕ)) := grp 14 (grp 14 ftF)

@[expose] noncomputable def fcL : List (List (List ℕ)) := grp 14 (grp 14 fcF)

@[expose] def FT (p : Fin 3 × Fin 3 × Fin 3) : List (List ℕ) := ftL.getD (ix p) []

@[expose] def FTn (i j k : ℕ) : List (List ℕ) := ftL.getD (9 * i + 3 * j + k) []

@[expose] def FC (p : Fin 3 × Fin 3 × Fin 3) : List (List ℕ) := fcL.getD (ix p) []

@[expose] def sqL : List ℕ := [0, 2, 1, 6, 8, 7, 3, 5, 4, 18, 20, 19, 26, 25, 24, 22, 21, 23, 9, 11, 10, 16, 15, 17, 14, 13, 12]

@[expose] def sq (p : Fin 3 × Fin 3 × Fin 3) : Fin 3 × Fin 3 × Fin 3 := unix (sqL.getD (ix p) 0)

@[expose] def bwL : List (List ℕ) :=
  [[2, 1, 2, 2, 1, 2, 1, 2, 2],
    [1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2]]

@[expose] noncomputable def bwmL : List (List (List ℕ)) := grp 14 (grp 14 bwmF)

@[expose] noncomputable def bwcL : List (List (List ℕ)) := grp 14 (grp 14 bwcF)

@[expose] def qL : List ℕ := [0, 0, 0, 9, 18, 0, 9, 0, 18, 0, 6, 3, 0, 6, 3, 0, 6, 3, 0, 3, 6, 6, 0, 3, 3, 6, 0]

@[expose] def bL : List ℕ := [0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

@[expose] noncomputable def tL : List (List (List ℕ)) := grp 14 (grp 14 tF)

@[expose] noncomputable def tcL : List (List (List ℕ)) := grp 14 (grp 14 tcF)

@[expose] def BW (b : ℕ) : List ℕ := bwL.getD b []
@[expose] def BWM (b : ℕ) : List (List ℕ) := bwmL.getD b []
@[expose] def BWC (b : ℕ) : List (List ℕ) := bwcL.getD b []
@[expose] def QQ (p : Fin 3 × Fin 3 × Fin 3) : Fin 3 × Fin 3 × Fin 3 := unix (qL.getD (ix p) 0)
@[expose] def BB (p : Fin 3 × Fin 3 × Fin 3) : ℕ := bL.getD (ix p) 0
@[expose] def T (p : Fin 3 × Fin 3 × Fin 3) : List (List ℕ) := tL.getD (ix p) []
@[expose] def TC (p : Fin 3 × Fin 3 × Fin 3) : List (List ℕ) := tcL.getD (ix p) []

theorem ft0 : FTn 0 0 0 = idL 14 := by decide +kernel

theorem chkx : ∀ i < 2, (mulF 5 (FTn i 0 0) xC == FTn (i + 1) 0 0) = true := by decide +kernel

theorem chky : ∀ i < 3, ∀ j < 2, (mulF 5 (FTn i j 0) yC == FTn i (j + 1) 0) = true := by
  decide +kernel

theorem chkz : ∀ i < 3, ∀ j < 3, ∀ k < 2, (mulF 5 (FTn i j k) zC == FTn i j (k + 1)) = true := by
  decide +kernel

theorem bw_chkB : ∀ b : Fin 2, (wordR (BW b) == BWM b) = true := by decide +kernel

theorem bwc_chkB : ∀ b : Fin 2, (colsL 14 (BWM b) == BWC b) = true := by decide +kernel

theorem bb_lt : ∀ p, BB p < 2 := by decide +kernel

theorem fc_chkB : ∀ p, (colsL 14 (FT p) == FC p) = true := by decide +kernel

theorem tc_chkB : ∀ p, (colsL 14 (T p) == TC p) = true := by decide +kernel

theorem t_chkB : ∀ p,
    (mulF 5 (mulF 5 (FT (QQ p)) (BWC (BB p))) (FC (sq (QQ p))) == T p) = true := by decide +kernel

theorem sq_chkB : ∀ p, (mulF 5 (FT p) (FC p) == FT (sq p)) = true := by decide +kernel

theorem h3_chkB : ∀ p, (mulF 5 (FT (sq p)) (FC p) == idL 14) = true := by decide +kernel

theorem tinv_chkB : ∀ p, (mulF 5 (T p) (FC p) == mulF 5 (FT (sq p)) (TC p)) = true := by
  decide +kernel

theorem sx_chkB : ∀ p,
    (mulF 5 (FT p) xC == FT (p.1 + 1, p.2.1, p.2.2 - p.2.1)) = true := by decide +kernel

theorem sy_chkB : ∀ p, (mulF 5 (FT p) yC == FT (p.1, p.2.1 + 1, p.2.2)) = true := by decide +kernel

theorem ft_inj : ∀ p q, FT p = FT q → p = q := by
  have h : ∀ p q, (FT p == FT q) = true → p = q := by decide +kernel
  intro p q e
  exact h p q (by rw [e]; exact beq_self_eq_true _)

theorem ft_lt : ∀ p, ∀ r ∈ FT p, ∀ e ∈ r, e < 5 := by
  have h : ∀ p, ((FT p).all fun r => r.all fun e => Nat.blt e 5) = true := by decide +kernel
  intro p r hr e he
  have := List.all_eq_true.1 (List.all_eq_true.1 (h p) r hr) e he
  simpa using this

theorem fc_eq (p : Fin 3 × Fin 3 × Fin 3) : colsL 14 (FT p) = FC p := eq_of_beq (fc_chkB p)

theorem sq_eq (p : Fin 3 × Fin 3 × Fin 3) : mulL 5 14 (FT p) (FT p) = FT (sq p) := by
  rw [mulL_eq, fc_eq]
  exact eq_of_beq (sq_chkB p)

theorem h3_chk (p : Fin 3 × Fin 3 × Fin 3) :
    mulL 5 14 (mulL 5 14 (FT p) (FT p)) (FT p) = idL 14 := by
  rw [sq_eq, mulL_eq, fc_eq]
  exact eq_of_beq (h3_chkB p)

theorem tinv_chk (p : Fin 3 × Fin 3 × Fin 3) :
    mulL 5 14 (T p) (FT p) = mulL 5 14 (mulL 5 14 (FT p) (FT p)) (T p) := by
  have hw : colsL 14 (T p) = TC p := eq_of_beq (tc_chkB p)
  rw [sq_eq, mulL_eq, mulL_eq, fc_eq, hw]
  exact eq_of_beq (tinv_chkB p)

theorem sx_chk (X : List (List ℕ)) (hX : colsL 14 X = xC) (p : Fin 3 × Fin 3 × Fin 3) :
    mulL 5 14 (FT p) X = FT (p.1 + 1, p.2.1, p.2.2 - p.2.1) := by
  rw [mulL_eq, hX]
  exact eq_of_beq (sx_chkB p)

theorem sy_chk (Y : List (List ℕ)) (hY : colsL 14 Y = yC) (p : Fin 3 × Fin 3 × Fin 3) :
    mulL 5 14 (FT p) Y = FT (p.1, p.2.1 + 1, p.2.2) := by
  rw [mulL_eq, hY]
  exact eq_of_beq (sy_chkB p)

theorem ft_rep {G : Type} [Monoid G] (R : List (List ℕ) → G → Prop)
    (mul : ∀ {L M : List (List ℕ)} {g h : G}, R L g → R M h → R (mulL 5 14 L M) (g * h))
    (one : R (idL 14) 1) (x y z : G) (X Y Z : List (List ℕ)) (hX : R X x) (hY : R Y y)
    (hZ : R Z z) (hXc : colsL 14 X = xC) (hYc : colsL 14 Y = yC) (hZc : colsL 14 Z = zC)
    (p : Fin 3 × Fin 3 × Fin 3) :
    R (FT p) (x ^ (p.1 : ℕ) * y ^ (p.2.1 : ℕ) * z ^ (p.2.2 : ℕ)) := by
  have hA : ∀ i, i < 3 → R (FTn i 0 0) (x ^ i) := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [ft0, pow_zero]
      exact one
    | succ i ih =>
      intro hi
      have e : FTn (i + 1) 0 0 = mulL 5 14 (FTn i 0 0) X := by
        rw [mulL_eq, hXc]
        exact (eq_of_beq (chkx i (by omega))).symm
      rw [e, pow_succ]
      exact mul (ih (by omega)) hX
  have hB : ∀ i j, i < 3 → j < 3 → R (FTn i j 0) (x ^ i * y ^ j) := by
    intro i j
    induction j with
    | zero =>
      intro hi _
      rw [pow_zero, mul_one]
      exact hA i hi
    | succ j ih =>
      intro hi hj
      have e : FTn i (j + 1) 0 = mulL 5 14 (FTn i j 0) Y := by
        rw [mulL_eq, hYc]
        exact (eq_of_beq (chky i hi j (by omega))).symm
      rw [e, pow_succ, ← mul_assoc]
      exact mul (ih hi (by omega)) hY
  have hC : ∀ i j k, i < 3 → j < 3 → k < 3 → R (FTn i j k) (x ^ i * y ^ j * z ^ k) := by
    intro i j k
    induction k with
    | zero =>
      intro hi hj _
      rw [pow_zero, mul_one]
      exact hB i j hi hj
    | succ k ih =>
      intro hi hj hk
      have e : FTn i j (k + 1) = mulL 5 14 (FTn i j k) Z := by
        rw [mulL_eq, hZc]
        exact (eq_of_beq (chkz i hi j hj k (by omega))).symm
      rw [e, pow_succ, ← mul_assoc]
      exact mul (ih hi hj (by omega)) hZ
  exact hC _ _ _ p.1.2 p.2.1.2 p.2.2.2

theorem t_rep {G : Type} [Monoid G] (R : List (List ℕ) → G → Prop)
    (mul : ∀ {L M : List (List ℕ)} {g h : G}, R L g → R M h → R (mulL 5 14 L M) (g * h))
    (one : R (idL 14) 1) (x y z : G) (X Y Z : List (List ℕ)) (hX : R X x) (hY : R Y y)
    (hZ : R Z z) (hXc : colsL 14 X = xC) (hYc : colsL 14 Y = yC) (hZc : colsL 14 Z = zC)
    (e : ℕ → G) (hL : ∀ l, R (abL l) (e l)) (p : Fin 3 × Fin 3 × Fin 3) :
    R (T p) (x ^ ((QQ p).1 : ℕ) * y ^ ((QQ p).2.1 : ℕ) * z ^ ((QQ p).2.2 : ℕ) *
      ((BW (BB p)).map e).prod *
      (x ^ ((sq (QQ p)).1 : ℕ) * y ^ ((sq (QQ p)).2.1 : ℕ) * z ^ ((sq (QQ p)).2.2 : ℕ))) := by
  have h1 := ft_rep R mul one x y z X Y Z hX hY hZ hXc hYc hZc (QQ p)
  have h2 := wordR_rep R mul one e hL (BW (BB p))
  have h3 := ft_rep R mul one x y z X Y Z hX hY hZ hXc hYc hZc (sq (QQ p))
  have h := mul (mul h1 h2) h3
  have hw : wordR (BW (BB p)) = BWM (BB p) := eq_of_beq (bw_chkB ⟨BB p, bb_lt p⟩)
  have hc : colsL 14 (BWM (BB p)) = BWC (BB p) := eq_of_beq (bwc_chkB ⟨BB p, bb_lt p⟩)
  rw [hw, mulL_eq, mulL_eq, fc_eq, hc, eq_of_beq (t_chkB p)] at h
  exact h

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree.J2Tab
