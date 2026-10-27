module

public import Certificates.Data.Kernel.OpsMcertB
public import CFSG.Certificates.Kernel.OpsMcertNSound
public import CFSG.Certificates.Kernel.MonsterB.FischerBTSound
import CFSG.Certificates.Kernel.OpsKSound

public section

namespace CFSG.KC.OpsMB

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.KC.OpsK CFSG.KC.FischerB
open CFSG.KC.OpsMN

variable {V : Type} (O : Ops Nat V)

@[expose] noncomputable def stepTB (T : BT) : Op → BT
  | .mul i j t => setT T t (O.mul (getT T i) (getT T j))
  | .pow e i t => setT T t (O.pow (getT T i) e)

theorem runB_eq : ∀ (prog : List Op) (T : BT) (k : BT → Bool),
    runB O prog T k = k (prog.foldl (stepTB O) T)
  | [], _, _ => rfl
  | op :: prog, T, k => by
    change stepB O T (fun T' => runB O prog T' k) op = _
    cases op with
    | mul i j t =>
      change forceB _ (fun a => runB O prog (setT T t a) k) = _
      rw [forceB_eq, runB_eq prog]
      rfl
    | pow e i t =>
      change forceB _ (fun a => runB O prog (setT T t a) k) = _
      rw [forceB_eq, powN_eq O _ _ _ (Nat.lt_succ_self e), runB_eq prog]
      rfl

theorem full_setT {T : BT} (hT : Full 11 T) (t v : Nat) : Full 11 (setT T t v) := by
  rw [setT_eq]
  split_ifs
  · exact full_setB 11 T t v hT
  · exact hT

theorem getT_setT {T : BT} (hT : Full 11 T) {t i : Nat} (ht : t < 2048) (hi : i < 2048)
    (v : Nat) : getT (setT T t v) i = if t = i then v else getT T i := by
  have h2 : (2 : Nat) ^ 11 = 2048 := rfl
  rw [setT_eq, if_pos ht, getT_eq, if_pos hi, getT_eq, if_pos hi]
  exact getB_setB 11 T t v i hT (by rw [h2]; exact ht) (by rw [h2]; exact hi)

@[expose] def Inv (T : BT) (R : List Nat) : Prop :=
  Full 11 T ∧ R.length ≤ 2048 ∧ ∀ i < R.length, getT T i = getN R i

theorem inv_set {T : BT} {R : List Nat} (h : Inv T R) {t : Nat} (ht : t < R.length) (v : Nat) :
    Inv (setT T t v) (R.set t v) := by
  obtain ⟨hF, hn, hR⟩ := h
  refine ⟨full_setT hF t v, by rw [List.length_set]; exact hn, fun i hi => ?_⟩
  rw [List.length_set] at hi
  rw [getT_setT hF (by omega) (by omega)]
  by_cases e : t = i
  · subst e
    rw [if_pos rfl, getN_set_eq ht]
  · rw [if_neg e, getN_set_ne R e, hR i hi]

theorem inv_step {T : BT} {R : List Nat} (h : Inv T R) (op : Op) (hop : op.lt R.length = true) :
    Inv (stepTB O T op) (stepL O R op) := by
  cases op with
  | mul i j t =>
    simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hop
    obtain ⟨⟨hi, hj⟩, ht⟩ := hop
    change Inv (setT T t (O.mul (getT T i) (getT T j))) (R.set t (O.mul (getN R i) (getN R j)))
    rw [h.2.2 i hi, h.2.2 j hj]
    exact inv_set h ht _
  | pow e i t =>
    simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hop
    obtain ⟨hi, ht⟩ := hop
    change Inv (setT T t (O.pow (getT T i) e)) (R.set t (O.pow (getN R i) e))
    rw [h.2.2 i hi]
    exact inv_set h ht _

theorem inv_run : ∀ (prog : List Op) {T : BT} {R : List Nat}, Inv T R →
    prog.all (Op.lt R.length) = true → Inv (prog.foldl (stepTB O) T) (prog.foldl (stepL O) R)
  | [], _, _, h, _ => h
  | op :: prog, T, R, h, hp => by
    rw [List.all_cons, Bool.and_eq_true] at hp
    change Inv (prog.foldl (stepTB O) (stepTB O T op)) (prog.foldl (stepL O) (stepL O R op))
    refine inv_run prog (inv_step O h op hp.1) ?_
    rw [length_stepL]
    exact hp.2

theorem inv_init (A B : Nat) {n : Nat} (hn : n ≤ 2048) : Inv (initB O A B) (initN O A B n) := by
  have hF : Full 11 (mkB O.one 11) := full_mkB O.one 11
  refine ⟨full_setT (full_setT hF 0 A) 1 B, by rw [length_initN]; exact hn, fun i hi => ?_⟩
  rw [length_initN] at hi
  have hi' : i < 2048 := by omega
  unfold initB
  rw [getT_setT (full_setT hF 0 A) (by omega) hi', getT_setT hF (by omega) hi', getT_eq,
    if_pos hi', getB_mkB]
  simp only [getN, initN, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]
  by_cases h0 : i = 0
  · subst h0
    simp
  · by_cases h1 : i = 1
    · subst h1
      simp
    · rw [if_neg (Ne.symm h1), if_neg (Ne.symm h0), if_neg h0, if_neg h1]

theorem evalWB_eq {T : BT} {R : List Nat} (h : Inv T R) :
    ∀ w : Word, wordLt R.length w = true → evalWB O T w = evalWN O R w
  | [], _ => rfl
  | (r, e) :: w, hw => by
    obtain ⟨hr, hw⟩ := wordLt_cons hw
    change O.mul (powN O (Nat.succ e) (getT T r) e) (evalWB O T w) =
      O.mul (powN O (Nat.succ e) (getN R r) e) (evalWN O R w)
    rw [h.2.2 r hr, evalWB_eq h w hw]

theorem factB_eq {T : BT} {R : List Nat} (h : Inv T R) (f : MFact) :
    factB O T R.length f = factN O R R.length f := by
  cases f with
  | ord r e =>
    simp only [factB, factN]
    by_cases hr : r < R.length
    · rw [h.2.2 r hr]
    · simp [hr]
  | conj c u w =>
    simp only [factB, factN]
    by_cases hc : c < R.length
    · by_cases hu : wordLt R.length u = true
      · by_cases hw : wordLt R.length w = true
        · rw [h.2.2 c hc, evalWB_eq O h u hu, evalWB_eq O h w hw]
        · simp [hw]
      · simp [hu]
    · simp [hc]
  | ne w₁ w₂ t =>
    simp only [factB, factN]
    by_cases h1 : wordLt R.length w₁ = true
    · by_cases h2 : wordLt R.length w₂ = true
      · rw [evalWB_eq O h w₁ h1, evalWB_eq O h w₂ h2]
      · simp [h2]
    · simp [h1]
  | eq w₁ w₂ =>
    simp only [factB, factN]
    by_cases h1 : wordLt R.length w₁ = true
    · by_cases h2 : wordLt R.length w₂ = true
      · rw [evalWB_eq O h w₁ h1, evalWB_eq O h w₂ h2]
      · simp [h2]
    · simp [h1]

theorem seedRunB_sound {A B : Nat} {C : MCert} (h : seedRunB O A B C = true) :
    2 ≤ C.nregs ∧ regsN O A B C.nregs C.prog
      (fun R => certN O R C && O.eq (getN R 0) A && O.eq (getN R 1) B) = true := by
  unfold seedRunB at h
  rw [runB_eq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h2, hn⟩, hp⟩, hf⟩, h0⟩, h1⟩ := h
  have hI := inv_run O C.prog (inv_init O A B hn) (by rw [length_initN]; exact hp)
  have hl : (C.prog.foldl (stepL O) (initN O A B C.nregs)).length = C.nregs := by
    rw [length_run, length_initN]
  refine ⟨h2, ?_⟩
  rw [regsN_eq]
  unfold certN
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨h2, hp⟩, ?_⟩, ?_⟩, ?_⟩
  · have e := List.all_congr (l₁ := C.facts) rfl fun f => factB_eq O hI f
    rw [hl] at e
    rw [← e]
    exact hf
  · rw [← hI.2.2 0 (by rw [hl]; omega)]
    exact h0
  · rw [← hI.2.2 1 (by rw [hl]; omega)]
    exact h1

end CFSG.KC.OpsMB

end
