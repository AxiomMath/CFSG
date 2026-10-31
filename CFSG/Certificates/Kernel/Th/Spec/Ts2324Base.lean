
module

public import CFSG.Certificates.Kernel.Th.Spec.MirrorBase
public import CFSG.Certificates.Kernel.Th.Spec.TsLeaves
public import CFSG.Certificates.Kernel.Th.Spec.WordBase

@[expose] public section

namespace CFSG.KC.Th.Spec

open CFSG.KC.Th CFSG.KC.Th.Gen CFSG.KC.Th.BigS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Th.Max3 CFSG.Sporadic.ThSchreier CFSG.KC.Th.Spec.Mir

section Consts

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
  (K : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)

include K in
theorem pk_word84 (A B Bi : ℕ) :
    pkMat (wordAB c rm ONE A B Bi 84 4) = pkMat A * (pkMat B * (pkMat B * pkMat B)) := by
  rw [pk_wordAB K]
  have e0 : codeLetter (pkMat A) (pkMat B) (pkMat Bi) (bitsN 84 (2 * 0) 2) = pkMat A := by
    have : bitsN 84 (2 * 0) 2 = 0 := by decide +kernel
    rw [this]; simp [codeLetter]
  have e1 : ∀ i, i = 1 ∨ i = 2 ∨ i = 3 →
      codeLetter (pkMat A) (pkMat B) (pkMat Bi) (bitsN 84 (2 * i) 2) = pkMat B := by
    intro i hi
    have : bitsN 84 (2 * i) 2 = 1 := by rcases hi with rfl | rfl | rfl <;> decide +kernel
    rw [this]; simp [codeLetter]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, mul_one]
  rw [e0, e1 1 (by simp), e1 2 (by simp), e1 3 (by simp)]
  simp [mul_assoc]

end Consts

theorem wordCode_one : wordCode 1 = 0 := by decide

theorem wordCode_neg_one : wordCode (-1) = 0 := by decide

theorem wordCode_two : wordCode 2 = 1 := by decide

theorem wordCode_neg_two : wordCode (-2) = 2 := by decide

theorem rowsMatrix_pLet {RA RB : Array V4} {X Y Y5 : Matrix (Fin 248) (Fin 248) (ZMod 2)}
    (hx : rowsMatrix (m3x RA RB) = X) (hy : rowsMatrix (m3y RA RB) = Y)
    (hy5 : rowsMatrix (powRows (m3y RA RB) 5) = Y5) {l : ℤ}
    (hl : l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2) :
    rowsMatrix (pLet RA RB l) = codeLetter X Y Y5 (wordCode l) := by
  rcases hl with rfl | rfl | rfl | rfl
  · rw [show pLet RA RB 1 = m3x RA RB from if_pos (Or.inl rfl), hx, wordCode_one]
    exact (if_pos rfl).symm
  · rw [show pLet RA RB (-1) = m3x RA RB from if_pos (Or.inr rfl), hx, wordCode_neg_one]
    exact (if_pos rfl).symm
  · rw [show pLet RA RB 2 = m3y RA RB from by
        unfold pLet; rw [if_neg (by decide), if_pos rfl], hy, wordCode_two]
    unfold codeLetter; rw [if_neg (by decide), if_pos rfl]
  · rw [show pLet RA RB (-2) = powRows (m3y RA RB) 5 from by
        unfold pLet; rw [if_neg (by decide), if_neg (by decide), if_pos rfl], hy5, wordCode_neg_two]
    unfold codeLetter; rw [if_neg (by decide), if_neg (by decide)]

theorem wfRows_pLet {RA RB : Array V4} (hx : WfRows (m3x RA RB)) (hy : WfRows (m3y RA RB))
    (l : ℤ) : WfRows (pLet RA RB l) := by
  unfold pLet
  by_cases h1 : l = 1 ∨ l = -1
  · rw [if_pos h1]; exact hx
  · rw [if_neg h1]
    by_cases h2 : l = 2
    · rw [if_pos h2]; exact hy
    · rw [if_neg h2]
      by_cases h3 : l = -2
      · rw [if_pos h3]; exact hy.powRows 5
      · rw [if_neg h3]; exact wfRows_idRows

section Ts

variable {D : TsData} (L : TsLeaves D) {RA RB : Array V4} (hA : WfRows RA) (hB : WfRows RB)
  (hSA : pkMat D.ThSeed_SA = rowsMatrix RA) (hSB : pkMat D.ThSeed_SB = rowsMatrix RB)

end Ts

def twRegE : ℕ → ℕ
  | 0 => 4 | 1 => 5 | 2 => 8 | 3 => 9 | 4 => 11 | 5 => 13 | 6 => 14 | 7 => 15 | 8 => 16
  | 9 => 18 | _ => 0

def twRegF : ℕ → ℕ
  | 0 => 19 | 1 => 12 | 2 => 20 | 3 => 10 | 4 => 21 | 5 => 22 | 6 => 23 | 7 => 24 | 8 => 17
  | 9 => 25 | _ => 0

def tupM {M : Type*} (E F : ℕ → M) (l : ℤ) : M :=
  if 0 < l then E (l.toNat - 1) else F ((-l).toNat - 1)

def TwEntry (R : Array V4) (E F : Matrix (Fin 248) (Fin 248) (ZMod 2)) : Prop :=
  WfRows R ∧ rowsMatrix R = E ∧ WfRows (invRows R) ∧ rowsMatrix (invRows R) = F

def TwEnts (Rs : List (Array V4)) (n : ℕ)
    (E F : ℕ → Matrix (Fin 248) (Fin 248) (ZMod 2)) : Prop :=
  Rs.length = n ∧ ∀ i < n, TwEntry (Rs.getD i idRows) (E i) (F i)

theorem tupleRows_spec {Rs : List (Array V4)} {n : ℕ}
    {E F : ℕ → Matrix (Fin 248) (Fin 248) (ZMod 2)}
    (h : TwEnts Rs n E F) {l : ℤ} (hl : l ≠ 0) (hn : l.natAbs ≤ n) :
    WfRows (tupleRows Rs l) ∧ rowsMatrix (tupleRows Rs l) = tupM E F l := by
  unfold tupleRows tupM
  by_cases hp : 0 < l
  · rw [if_pos hp, if_pos hp]
    have hi : l.toNat - 1 < n := by omega
    obtain ⟨h1, h2, -, -⟩ := h.2 _ hi
    exact ⟨h1, h2⟩
  · rw [if_neg hp, if_neg hp]
    have hi : (-l).toNat - 1 < n := by omega
    have hlen : (-l).toNat - 1 < Rs.length := h.1 ▸ hi
    have e : (Rs.map invRows).getD ((-l).toNat - 1) idRows =
        invRows (Rs.getD ((-l).toNat - 1) idRows) := by
      rw [List.getD_eq_getElem _ _ (by simpa using hlen), List.getD_eq_getElem _ _ hlen,
        List.getElem_map]
    rw [e]
    obtain ⟨-, -, h3, h4⟩ := h.2 _ hi
    exact ⟨h3, h4⟩

theorem prod_cons_foldl {M : Type*} [Monoid M] (a : M) (l : List M) :
    (a :: l).prod = l.foldl (· * ·) a := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    rw [List.foldl_cons, ← ih (a * b)]
    simp only [List.prod_cons, mul_assoc]

section Ts

variable {D : TsData} (L : TsLeaves D) {RA RB : Array V4} (hA : WfRows RA) (hB : WfRows RB)
  (hSA : pkMat D.ThSeed_SA = rowsMatrix RA) (hSB : pkMat D.ThSeed_SB = rowsMatrix RB)

end Ts

end CFSG.KC.Th.Spec

end
