
module

public import CFSG.Certificates.Kernel.ThCent.PinSoundBase

public import Certificates.Data.Kernel.ThCent.Pin
public import CFSG.Certificates.Kernel.Th.Spec.FwdRel

public section

namespace CFSG.KC.ThCent

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.Th.Spec.FwdRel CFSG.SectionRank.Native
  CFSG.Sporadic.Th

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
  {J : Subgroup (GL (Fin 248) (ZMod 2))}
  (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
include hk

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

theorem pkMat_wordZ (a b : J) {A B Bi : ℕ} (hA : 𝕄 a = pkMat A) (hB : 𝕄 b = pkMat B)
    (hA2 : pkMat A * pkMat A = 1) (hBi : pkMat B * pkMat Bi = 1) {w : List ℤ}
    (hw : CFSG.Sporadic.Th.lettersOK w = true) :
    pkMat (wordZ c rm ONE A B Bi w) = 𝕄 (wordG (pairLetters a b) w) := by
  have e1 : 𝕄 (a⁻¹) = pkMat A := mat_inv_eq (by rw [hA, hA2])
  have e2 : 𝕄 (b⁻¹) = pkMat Bi := mat_inv_eq (by rw [hB, hBi])
  have hlet : ∀ l : ℤ, (l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2) →
      pkMat (letZ A B Bi l) = 𝕄 (pairLetters a b l) := by
    rintro l (rfl | rfl | rfl | rfl)
    · rw [show pairLetters a b 1 = a by simp [pairLetters], hA]
      rfl
    · rw [show pairLetters a b (-1) = a⁻¹ by simp [pairLetters], e1]
      rfl
    · rw [show pairLetters a b 2 = b by simp [pairLetters], hB]
      rfl
    · rw [show pairLetters a b (-2) = b⁻¹ by simp [pairLetters], e2]
      rfl
  suffices H : ∀ (w : List ℤ), CFSG.Sporadic.Th.lettersOK w = true → ∀ (X : ℕ) (g : J), pkMat X = 𝕄 g →
      pkMat (wordFrom c rm A B Bi w X) = 𝕄 (g * wordG (pairLetters a b) w) by
    have := H w hw ONE 1 (pkMat_one hk)
    rwa [one_mul] at this
  intro w
  induction w with
  | nil =>
    intro _ X g hX
    change pkMat X = _
    rw [hX, wordG, List.map_nil, List.prod_nil, mul_one]
  | cons l w ih =>
    intro hw X g hX
    have hl : l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2 := by
      have := List.all_eq_true.1 hw l List.mem_cons_self
      simpa only [decide_eq_true_eq] using this
    have hw' : CFSG.Sporadic.Th.lettersOK w = true :=
      List.all_eq_true.2 fun l' hl' => List.all_eq_true.1 hw l' (List.mem_cons_of_mem _ hl')
    change pkMat (strictF (mulB c rm X (letZ A B Bi l)) (wordFrom c rm A B Bi w)) = _
    rw [strictF_eq, ih hw' _ (g * pairLetters a b l) (by rw [pkMat_mulB hk, hX, hlet l hl,
      mat_mul]), wordG, wordG, List.map_cons, List.prod_cons, mul_assoc]

theorem pkMat_initPk (g h : J) {A B : ℕ} (hA : 𝕄 g = pkMat A) (hB : 𝕄 h = pkMat B) :
    ∀ r, pkMat (initPk A B ONE r) = 𝕄 (initG g h r) := by
  intro r
  unfold initPk initG
  by_cases h0 : r = 0
  · subst h0
    exact hA.symm
  · by_cases h1 : r = 1
    · subst h1
      exact hB.symm
    · have e0 : Nat.beq r 0 = false := beq_false' h0
      have e1 : Nat.beq r 1 = false := beq_false' h1
      rw [e0, e1, if_neg h0, if_neg h1]
      exact (pkMat_one hk).trans mat_one.symm

theorem pkMat_runPk : ∀ (prog : List Op), powsOK prog = true → ∀ (R : ℕ → ℕ) (RJ : ℕ → J),
    (∀ r, pkMat (R r) = 𝕄 (RJ r)) → ∀ r, pkMat (runPk c rm ONE prog R r) = 𝕄 (prog.foldl opG RJ r)
  | [], _, R, RJ, hR, r => hR r
  | op :: prog, hp, R, RJ, hR, r => by
    have hp' : powsOK prog = true :=
      List.all_eq_true.2 fun o ho => List.all_eq_true.1 hp o (List.mem_cons_of_mem _ ho)
    have hop := List.all_eq_true.1 hp op List.mem_cons_self
    have hupd : ∀ (k v : ℕ) (x : J), pkMat v = 𝕄 x →
        ∀ r, pkMat (updN R k v r) = 𝕄 (Function.update RJ k x r) := by
      intro k v x hv r
      unfold updN
      by_cases hrk : r = k
      · subst hrk
        rw [show Nat.beq r r = true from Nat.beq_refl r, Function.update_self]
        exact hv
      · rw [beq_false' hrk, Function.update_of_ne hrk]
        exact hR r
    rw [List.foldl_cons]
    cases op with
    | mul i j k =>
      change pkMat (strictF (mulB c rm (R i) (R j))
        (fun v => runPk c rm ONE prog (updN R k v)) r) = _
      rw [strictF_eq]
      exact pkMat_runPk prog hp' _ _ (hupd k _ (RJ i * RJ j) (by rw [pkMat_mulB hk, hR, hR,
        mat_mul])) r
    | pow e i k =>
      have he : e < 64 := Nat.blt_eq.mp hop
      change pkMat (strictF (powB c rm ONE (R i) e 6)
        (fun v => runPk c rm ONE prog (updN R k v)) r) = _
      rw [strictF_eq]
      exact pkMat_runPk prog hp' _ _ (hupd k _ (RJ i ^ e) (by rw [pkMat_powB hk _ _ _ (by
        norm_num; omega), hR, mat_pow])) r

end CFSG.KC.ThCent

end
