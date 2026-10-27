module

public import Certificates.Data.Kernel.F4T
public import CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Elem
import all CFSG.Fischer.F4

public section

namespace CFSG.KC.F4T

open CFSG.Fischer CFSG.LieType.SeitzGeneration.HeisSmall CFSG.KC.HeisN
open CFSG.RankThree.PartTwo.Sec10.KS1012GL34
open CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Light CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Bridge
open CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Elem

@[expose] def f4 (n : Nat) : F4 := ⟨⟨n % 4, Nat.mod_lt _ (by decide)⟩⟩

@[expose] def toLT (A : M3 Nat) : Light.M3 :=
  ⟨f4 A.a00, f4 A.a01, f4 A.a02, f4 A.a10, f4 A.a11, f4 A.a12, f4 A.a20, f4 A.a21, f4 A.a22⟩

@[expose] def toMT (A : M3 Nat) : Matrix (Fin 3) (Fin 3) F4 := toMat (toLT A)

@[expose] def OK (A : M3 Nat) : Prop :=
  A.a00 < 4 ∧ A.a01 < 4 ∧ A.a02 < 4 ∧ A.a10 < 4 ∧ A.a11 < 4 ∧ A.a12 < 4 ∧ A.a20 < 4 ∧
    A.a21 < 4 ∧ A.a22 < 4

theorem mT_lt (a b : Nat) : mT a b < 4 :=
  Nat.lt_of_le_of_lt (Nat.and_le_right (n := Nat.shiftRight tabT (2 * (4 * a + b))) (m := 3))
    (by decide)

theorem aT_lt_all : ∀ a < 4, ∀ b < 4, aT a b < 4 := by decide +kernel

theorem aT_lt {a b : Nat} (ha : a < 4) (hb : b < 4) : aT a b < 4 := aT_lt_all a ha b hb

theorem f4_mT_all : ∀ a < 4, ∀ b < 4, f4 (mT a b) = f4 a * f4 b := by decide +kernel

theorem f4_aT_all : ∀ a < 4, ∀ b < 4, f4 (aT a b) = f4 a + f4 b := by decide +kernel

theorem f4_mT {a b : Nat} (ha : a < 4) (hb : b < 4) : f4 (mT a b) = f4 a * f4 b :=
  f4_mT_all a ha b hb

theorem f4_aT {a b : Nat} (ha : a < 4) (hb : b < 4) : f4 (aT a b) = f4 a + f4 b :=
  f4_aT_all a ha b hb

theorem dotT_lt (a0 a1 a2 b0 b1 b2 : Nat) : dotT a0 a1 a2 b0 b1 b2 < 4 :=
  aT_lt (aT_lt (mT_lt _ _) (mT_lt _ _)) (mT_lt _ _)

theorem f4_dotT {a0 a1 a2 b0 b1 b2 : Nat} (ha0 : a0 < 4) (ha1 : a1 < 4) (ha2 : a2 < 4)
    (hb0 : b0 < 4) (hb1 : b1 < 4) (hb2 : b2 < 4) :
    f4 (dotT a0 a1 a2 b0 b1 b2) = f4 a0 * f4 b0 + f4 a1 * f4 b1 + f4 a2 * f4 b2 := by
  unfold dotT
  rw [f4_aT (aT_lt (mT_lt _ _) (mT_lt _ _)) (mT_lt _ _), f4_aT (mT_lt _ _) (mT_lt _ _),
    f4_mT ha0 hb0, f4_mT ha1 hb1, f4_mT ha2 hb2]

theorem mMulT_OK (A B : M3 Nat) : OK (mMulT A B) :=
  ⟨dotT_lt _ _ _ _ _ _, dotT_lt _ _ _ _ _ _, dotT_lt _ _ _ _ _ _, dotT_lt _ _ _ _ _ _,
    dotT_lt _ _ _ _ _ _, dotT_lt _ _ _ _ _ _, dotT_lt _ _ _ _ _ _, dotT_lt _ _ _ _ _ _,
    dotT_lt _ _ _ _ _ _⟩

theorem mOne_OK : OK mOne := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem toLT_mMulT {A B : M3 Nat} (hA : OK A) (hB : OK B) :
    toLT (mMulT A B) = mulL (toLT A) (toLT B) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := hA
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8⟩ := hB
  simp only [toLT, mMulT, mulL]
  rw [f4_dotT a0 a1 a2 b0 b3 b6, f4_dotT a0 a1 a2 b1 b4 b7, f4_dotT a0 a1 a2 b2 b5 b8,
    f4_dotT a3 a4 a5 b0 b3 b6, f4_dotT a3 a4 a5 b1 b4 b7, f4_dotT a3 a4 a5 b2 b5 b8,
    f4_dotT a6 a7 a8 b0 b3 b6, f4_dotT a6 a7 a8 b1 b4 b7, f4_dotT a6 a7 a8 b2 b5 b8]

theorem toMT_mMulT {A B : M3 Nat} (hA : OK A) (hB : OK B) :
    toMT (mMulT A B) = toMT A * toMT B := by
  rw [toMT, toLT_mMulT hA hB, toMat_mulL]
  rfl

theorem toLT_mOne : toLT mOne = oneL := rfl

theorem toMT_mOne : toMT mOne = 1 := by
  rw [toMT, toLT_mOne, toMat_oneL]

theorem getD_lt {l : List Nat} (h : ∀ x ∈ l, x < 4) (i : Nat) : l.getD i 0 < 4 := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => exact Nat.zero_lt_succ _
  | some x => exact h x (List.mem_of_getElem? hi)

theorem matN_OK {l : List Nat} (h : codeOK l = true) : OK (matN l) := by
  simp only [codeOK, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at h
  exact ⟨getD_lt h.2 _, getD_lt h.2 _, getD_lt h.2 _, getD_lt h.2 _, getD_lt h.2 _,
    getD_lt h.2 _, getD_lt h.2 _, getD_lt h.2 _, getD_lt h.2 _⟩

theorem mEq_eq {A B : M3 Nat} (h : mEq A B = true) : A = B := by
  simp only [mEq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact M3.ext h0 h1 h2 h3 h4 h5 h6 h7 h8

@[expose] def GensIn (H : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)) (gens : List (M3 Nat)) :
    Prop :=
  ∀ g ∈ gens, OK g ∧ InM H (toMT g)

theorem getD_gens {H : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)} {gens : List (M3 Nat)}
    (hg : GensIn H gens) (k : Nat) : OK (gens.getD k mOne) ∧ InM H (toMT (gens.getD k mOne)) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : gens[k]? with
  | none => exact ⟨mOne_OK, by rw [Option.getD_none, toMT_mOne]; exact InM_one H⟩
  | some g => exact hg g (List.mem_of_getElem? h)

theorem foldl_evalT {H : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)} {gens : List (M3 Nat)}
    (hg : GensIn H gens) (w : List Nat) :
    ∀ acc : M3 Nat, OK acc → InM H (toMT acc) →
      InM H (toMT (w.foldl (fun acc k => mMulT acc (gens.getD k mOne)) acc)) := by
  induction w with
  | nil => intro acc _ h; exact h
  | cons k w ih =>
    intro acc hok h
    obtain ⟨hk1, hk2⟩ := getD_gens hg k
    apply ih _ (mMulT_OK _ _)
    rw [toMT_mMulT hok hk1]
    exact InM_mul h hk2

theorem evalT_OK (gens : List (M3 Nat)) (w : List Nat) : OK (evalT gens w) := by
  unfold evalT
  induction w using List.reverseRecOn with
  | nil => exact mOne_OK
  | append_singleton w k _ => rw [List.foldl_append, List.foldl_cons, List.foldl_nil]; exact mMulT_OK _ _

theorem InM_evalT {H : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)} {gens : List (M3 Nat)}
    (hg : GensIn H gens) (w : List Nat) : InM H (toMT (evalT gens w)) :=
  foldl_evalT hg w mOne mOne_OK (by rw [toMT_mOne]; exact InM_one H)

theorem toMT_esT :
    esT.map toMT = [elemM 0 1 1, elemM 0 2 1, elemM 1 0 1, elemM 1 2 1, elemM 2 0 1, elemM 2 1 1] := by
  have h : esT.map toLT = [E01L, E02L, E10L, E12L, E20L, E21L] := rfl
  have h2 : esT.map toMT = (esT.map toLT).map toMat := by
    simp only [List.map_map]
    rfl
  rw [h2, h]
  simp only [List.map_cons, List.map_nil, toMat_E01L, toMat_E02L, toMat_E10L, toMat_E12L,
    toMat_E20L, toMat_E21L]

theorem w6OK_sound {H : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)} {gens : List (M3 Nat)}
    (hg : GensIn H gens) {ws : List (List Nat)} (h : w6OK gens ws = true) :
    InM H (elemM 0 1 1) ∧ InM H (elemM 0 2 1) ∧ InM H (elemM 1 0 1) ∧
      InM H (elemM 1 2 1) ∧ InM H (elemM 2 0 1) ∧ InM H (elemM 2 1 1) := by
  have hall : ∀ e ∈ esT, InM H (toMT e) := by
    intro e he
    simp only [w6OK, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true] at h
    obtain ⟨hlen, hz⟩ := h
    have hlen' : ws.length = esT.length := by rw [hlen]; rfl
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    have hi' : i < ws.length := by rw [hlen']; exact hi
    have hp : (ws[i], esT[i]) ∈ ws.zip esT := by
      rw [List.mem_iff_getElem]
      exact ⟨i, by simp [List.length_zip, hi, hi'], by simp⟩
    have := mEq_eq (hz _ hp)
    simp only at this
    rw [← this]
    exact InM_evalT hg _
  have hm : ∀ M ∈ esT.map toMT, InM H M := by
    intro M hM
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hM
    exact hall e he
  rw [toMT_esT] at hm
  exact ⟨hm _ (by simp), hm _ (by simp), hm _ (by simp), hm _ (by simp), hm _ (by simp),
    hm _ (by simp)⟩

end CFSG.KC.F4T

end
