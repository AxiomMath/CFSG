
module

public import CFSG.Certificates.Kernel.Th.Spec.FwdRelBase

public import CFSG.Certificates.Kernel.Th.S.BigS
public import CFSG.Certificates.Kernel.Th.S.OutS
public import CFSG.Certificates.Kernel.Th.Spec.Big
public import CFSG.Certificates.Kernel.Th.Spec.DceHsw
public import CFSG.Sporadic.Bridge.Common
public import CFSG.Sporadic.Th.ChainBase1
import CFSG.Certificates.Kernel.Th.Max3S.Words
public import CFSG.Sporadic.Th.BaseBase1

public section

namespace CFSG.KC.Th.Spec.FwdRel

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.Sporadic.Bridge CFSG.Sporadic.Th

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
  {J : Subgroup (GL (Fin 248) (ZMod 2))}

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

theorem mat_mul (g h : J) : 𝕄 (g * h) = 𝕄 g * 𝕄 h := rfl

theorem mat_one : 𝕄 ((1 : J)) = 1 := rfl

theorem mat_inv_mul (g : J) : 𝕄 (g⁻¹) * 𝕄 g = 1 := Units.inv_mul (g : GL (Fin 248) (ZMod 2))

theorem mat_mul_inv (g : J) : 𝕄 g * 𝕄 (g⁻¹) = 1 := Units.mul_inv (g : GL (Fin 248) (ZMod 2))

theorem mat_pow (g : J) (e : ℕ) : 𝕄 (g ^ e) = 𝕄 g ^ e := by
  induction e with
  | zero => rfl
  | succ e ih => rw [pow_succ, mat_mul, ih, pow_succ]

theorem mat_list_prod : ∀ L : List J, 𝕄 (L.prod) = (L.map fun g => 𝕄 g).prod
  | [] => rfl
  | g :: L => by rw [List.prod_cons, mat_mul, mat_list_prod L, List.map_cons, List.prod_cons]

theorem mat_inv_eq {g : J} {N : Matrix (Fin 248) (Fin 248) (ZMod 2)} (h : 𝕄 g * N = 1) :
    𝕄 (g⁻¹) = N := by
  calc 𝕄 (g⁻¹) = 𝕄 (g⁻¹) * (𝕄 g * N) := by rw [h, Matrix.mul_one]
    _ = (𝕄 (g⁻¹) * 𝕄 g) * N := (Matrix.mul_assoc _ _ _).symm
    _ = N := by rw [mat_inv_mul, Matrix.one_mul]

@[expose] def RegIn (S : Subgroup J) (RB : ℕ → ℕ) (k : ℕ) : Prop :=
  ∃ g ∈ S, 𝕄 g = pkMat (RB k)

section Regs

variable (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
  {S : Subgroup J} {RB : ℕ → ℕ}
include hk

theorem regIn_mul {r a b : ℕ} (ha : RegIn S RB a) (hb : RegIn S RB b)
    (h : RB r = mulB c rm (RB a) (RB b)) : RegIn S RB r := by
  obtain ⟨x, hx, ex⟩ := ha
  obtain ⟨y, hy, ey⟩ := hb
  refine ⟨x * y, S.mul_mem hx hy, ?_⟩
  rw [h, pkMat_mulB hk, ← ex, ← ey]
  rfl

theorem regIn_pow {r a e : ℕ} (ha : RegIn S RB a) (he : e < 16)
    (h : RB r = powB c rm ONE (RB a) e 4) : RegIn S RB r := by
  obtain ⟨x, hx, ex⟩ := ha
  refine ⟨x ^ e, S.pow_mem hx e, ?_⟩
  rw [h, pkMat_powB hk _ e 4 (by norm_num; omega), ← ex, mat_pow]

theorem regIn_inv {r a : ℕ} (ha : RegIn S RB a) (h : mulB c rm (RB a) (RB r) = ONE) :
    RegIn S RB r := by
  obtain ⟨x, hx, ex⟩ := ha
  refine ⟨x⁻¹, S.inv_mem hx, mat_inv_eq ?_⟩
  rw [ex, ← pkMat_mulB hk, h, pkMat_one hk]

end Regs

theorem letV_eq (RB : ℕ → ℕ) (GR IR x : ℕ) :
    letV RB GR IR x = RB (if x % 2 = 1 then regAt IR (x / 2) else regAt GR (x / 2)) := by
  unfold letV
  have e1 : Nat.shiftRight x 1 = x / 2 := Nat.shiftRight_one x
  have e2 : Nat.land x 1 = x % 2 := Nat.and_one_is_mod x
  rw [e1, e2]
  rcases Nat.mod_two_eq_zero_or_one x with h | h
  · rw [h]
    rfl
  · rw [h]
    rfl

section Letters

variable {RB : ℕ → ℕ} {GR IR : ℕ} (x : ℕ → J)
  (hx : ∀ g < 8, 𝕄 (x g) = pkMat (RB (regAt GR g)))
  (hxi : ∀ g < 8, 𝕄 ((x g)⁻¹) = pkMat (RB (regAt IR g)))
include hx hxi

theorem pkMat_letV_code {g : ℕ} (hg : g < 8) (b : Bool) :
    pkMat (letV RB GR IR (2 * g + if b then 0 else 1)) = 𝕄 (if b then x g else (x g)⁻¹) := by
  rw [letV_eq]
  cases b
  · have e1 : (2 * g + if false = true then 0 else 1) % 2 = 1 := by
      simp only [Bool.false_eq_true, if_false]
      omega
    have e2 : (2 * g + if false = true then 0 else 1) / 2 = g := by
      simp only [Bool.false_eq_true, if_false]
      omega
    rw [if_pos e1, e2, ← hxi g hg]
    rfl
  · have e1 : ¬ (2 * g + if true = true then 0 else 1) % 2 = 1 := by
      simp only [if_true]
      omega
    have e2 : (2 * g + if true = true then 0 else 1) / 2 = g := by
      simp only [if_true]
      omega
    rw [if_neg e1, e2, ← hx g hg]
    rfl

theorem wordProd_take_succ (r : List (ℕ × Bool)) {n : ℕ} (hn : n < r.length) :
    wordProd x (r.take (n + 1)) =
      wordProd x (r.take n) * (if (r[n]'hn).2 then x (r[n]'hn).1 else (x (r[n]'hn).1)⁻¹) := by
  rw [List.take_succ, List.getElem?_eq_getElem hn]
  simp only [wordProd, List.map_append, List.prod_append, Option.toList_some, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one]

theorem wordProd_eq_one (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    {r : List (ℕ × Bool)} (hl : ∀ l ∈ r, l.1 < 8) (hlen : r.length < 1024) {k : ℕ}
    (hsel : Hsw.sel k = Dce.enT r) (h : relOK RB c rm ONE GR IR k = true) : wordProd x r = 1 := by
  unfold relOK at h
  rw [hsel] at h
  have hONE := Nat.eq_of_beq_eq_true (CFSG.KC.Th.Gen.andB_right h)
  obtain ⟨he1, he2⟩ := enT_decode r hl hlen
  rw [he1] at hONE
  have key : ∀ n, n ≤ r.length → pkMat (Nat.rec (motive := fun _ => ℕ) ONE (fun i acc =>
      mulB c rm acc (letV RB GR IR
        (Nat.land (Nat.shiftRight (Nat.shiftRight (Dce.enT r) 12) (Nat.mul 8 i)) 255))) n) =
      𝕄 (wordProd x (r.take n)) := by
    intro n
    induction n with
    | zero =>
      intro _
      show pkMat ONE = _
      rw [pkMat_one hk]
      rfl
    | succ n ih =>
      intro hn'
      have hlt : n < r.length := by omega
      show pkMat (mulB c rm _ _) = _
      rw [pkMat_mulB hk, ih (by omega), he2 n hlt,
        pkMat_letV_code x hx hxi (hl _ (List.getElem_mem hlt)), wordProd_take_succ x hx hxi r hlt,
        mat_mul]
  have h := key r.length le_rfl
  rw [List.take_length, ← hONE, pkMat_one hk] at h
  exact mat_injective (h.symm.trans mat_one.symm)

theorem pkMat_prodWord (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    (w : ℕ) : ∀ n, pkMat (OutS.prodWord RB c rm ONE GR IR w n) = 𝕄 (wordProd x (codeWord w n))
  | 0 => by
    rw [show OutS.prodWord RB c rm ONE GR IR w 0 = ONE from rfl, pkMat_one hk]
    rfl
  | n + 1 => by
    have e : OutS.prodWord RB c rm ONE GR IR w (n + 1) = mulB c rm
        (OutS.prodWord RB c rm ONE GR IR w n) (letV RB GR IR (bitsN w (4 * n) 4)) := rfl
    have hc : bitsN w (4 * n) 4 < 16 := by
      rw [bitsN_eq]
      exact Nat.mod_lt _ (by norm_num)
    set y := bitsN w (4 * n) 4 with hy
    have hy2 : y = 2 * (y / 2) + if decide (y % 2 = 0) then 0 else 1 := by
      rcases Nat.mod_two_eq_zero_or_one y with h | h <;> simp [h] <;> omega
    have hw : codeWord w (n + 1) = codeWord w n ++ [codeLetter y] := by
      rw [codeWord, codeWord, List.range_succ, List.map_append, List.map_singleton]
    rw [e, pkMat_mulB hk, pkMat_prodWord hk w n, hw, hy2,
      pkMat_letV_code x hx hxi (by omega : y / 2 < 8) (decide (y % 2 = 0)), ← mat_mul]
    simp only [wordProd, List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, codeLetter]
    have hy3 : (2 * (y / 2) + if decide (y % 2 = 0) then 0 else 1) / 2 = y / 2 := by
      split_ifs <;> omega
    have hy4 : (2 * (y / 2) + if decide (y % 2 = 0) then 0 else 1) % 2 = y % 2 := by
      rw [← hy2]
    rw [hy3, hy4]

end Letters

section Words

variable (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
include hk

theorem pkMat_wordG (a b : J) {A B Bi : ℕ} (hA : 𝕄 a = pkMat A) (hB : 𝕄 b = pkMat B)
    (hA2 : pkMat A * pkMat A = 1) (hBi : pkMat B * pkMat Bi = 1) {w : List ℤ}
    (hw : CFSG.Sporadic.Th.lettersOK w = true) :
    𝕄 (wordG (pairLetters a b) w) = ((w.map digitOf).map fun d => pkMat (wordLetter A B Bi d)).prod := by
  have hlet : ∀ l ∈ w, 𝕄 (pairLetters a b l) = pkMat (wordLetter A B Bi (digitOf l)) := by
    intro l hl
    have hl' := List.all_eq_true.1 hw l hl
    simp only [decide_eq_true_eq] at hl'
    have e1 : 𝕄 (a⁻¹) = pkMat A := mat_inv_eq (by rw [hA, hA2])
    have e2 : 𝕄 (b⁻¹) = pkMat Bi := mat_inv_eq (by rw [hB, hBi])
    rcases hl' with rfl | rfl | rfl | rfl
    · rw [show pairLetters a b 1 = a by simp [pairLetters], show digitOf 1 = 0 by decide, hA]
      rfl
    · rw [show pairLetters a b (-1) = a⁻¹ by simp [pairLetters], show digitOf (-1) = 0 by decide,
        e1]
      rfl
    · rw [show pairLetters a b 2 = b by simp [pairLetters], show digitOf 2 = 1 by decide, hB]
      rfl
    · rw [show pairLetters a b (-2) = b⁻¹ by simp [pairLetters], show digitOf (-2) = 2 by decide,
        e2]
      rfl
  rw [wordG, mat_list_prod, List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun l hl => hlet l hl

theorem pkMat_wordAB_digits (A B Bi w n : ℕ) {L : List ℤ}
    (hd : (List.range n).map (fun i => bitsN w (2 * i) 2) = L.map digitOf) :
    pkMat (wordAB c rm ONE A B Bi w n) =
      ((L.map digitOf).map fun d => pkMat (wordLetter A B Bi d)).prod := by
  rw [CFSG.KC.Th.Max3S.pkMat_wordAB_range hk, ← hd, List.map_map]
  rfl

end Words

end CFSG.KC.Th.Spec.FwdRel

end
