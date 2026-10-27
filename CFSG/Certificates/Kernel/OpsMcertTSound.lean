module

public import Certificates.Data.Kernel.OpsMcertT
public import CFSG.Certificates.Kernel.OpsMcertNSound
import CFSG.Certificates.Kernel.OpsKSound

public section

namespace CFSG.KC.OpsMT

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.KC.OpsK CFSG.KC.OpsMN

theorem brecE {α : Sort _} (n m : Nat) (x e : α) :
    Bool.rec (motive := fun _ => α) e x (Nat.beq n m) = if n = m then x else e := by
  cases h : Nat.beq n m
  · rw [if_neg (Nat.ne_of_beq_eq_false h)]
  · rw [if_pos (Nat.eq_of_beq_eq_true h)]

theorem brec2 {α : Sort _} (i : Nat) (x a b : α) :
    Bool.rec (motive := fun _ => α) (Bool.rec (motive := fun _ => α) b a (Nat.beq (i % 2) 1)) x
      (Nat.beq i 0) = if i = 0 then x else if i % 2 = 1 then a else b := by
  rw [brecE, brecE]

theorem getR_node (l r : RT) (x i : Nat) : getR (.node l x r) i =
    if i = 0 then x else if i % 2 = 1 then getR l ((i - 1) / 2) else getR r ((i - 1) / 2) :=
  brec2 (α := Nat) i x _ _

theorem domR_node (l r : RT) (x i : Nat) : domR (.node l x r) i =
    if i = 0 then true else if i % 2 = 1 then domR l ((i - 1) / 2) else domR r ((i - 1) / 2) :=
  brec2 (α := Bool) i true _ _

theorem setR_node (l r : RT) (x t a : Nat) : setR (.node l x r) t a =
    if t = 0 then .node l a r else if t % 2 = 1 then .node (setR l ((t - 1) / 2) a) x r
    else .node l x (setR r ((t - 1) / 2) a) :=
  brec2 (α := RT) t _ _ _

theorem setK_eq : ∀ (T : RT) (t a : Nat) (k : RT → Bool), setK T t a k = k (setR T t a)
  | .leaf, _, _, _ => rfl
  | .node l x r, t, a, k => by
    have e : setK (.node l x r) t a k = if t = 0 then k (.node l a r) else if t % 2 = 1 then
        setK l ((t - 1) / 2) a (fun l' => k (.node l' x r)) else
        setK r ((t - 1) / 2) a (fun r' => k (.node l x r')) :=
      brec2 (α := Bool) t _ _ _
    rw [e, setR_node, setK_eq l, setK_eq r]
    split_ifs <;> rfl

theorem getR_setR : ∀ (T : RT) (t a r : Nat),
    getR (setR T t a) r = if domR T t = true ∧ r = t then a else getR T r
  | .leaf, _, _, _ => by simp [setR, domR]
  | .node l x rt, t, a, r => by
    rw [setR_node, domR_node]
    by_cases ht0 : t = 0
    · subst ht0
      rw [if_pos rfl, getR_node, getR_node]
      by_cases hr : r = 0 <;> simp [hr]
    · rw [if_neg ht0]
      by_cases ht : t % 2 = 1
      · rw [if_pos ht, if_pos ht, getR_node, getR_node, getR_setR l]
        by_cases hr0 : r = 0
        · simp [hr0, ht0, Ne.symm ht0]
        · by_cases hr : r % 2 = 1
          · simp only [hr0, hr, if_false, if_true]
            by_cases hd : domR l ((t - 1) / 2) = true
            · by_cases hrt : r = t
              · subst hrt
                simp [hd]
              · have : (r - 1) / 2 ≠ (t - 1) / 2 := by omega
                simp [hd, hrt, this]
            · simp [hd, ht0]
          · have : r ≠ t := by omega
            simp [hr0, hr, this]
      · rw [if_neg ht, if_neg ht, getR_node, getR_node, getR_setR rt]
        by_cases hr0 : r = 0
        · simp [hr0, Ne.symm ht0]
        · by_cases hr : r % 2 = 1
          · have : r ≠ t := by omega
            simp [hr0, hr, this]
          · simp only [hr0, hr, if_false]
            by_cases hd : domR rt ((t - 1) / 2) = true
            · by_cases hrt : r = t
              · subst hrt
                simp [hd]
              · have : (r - 1) / 2 ≠ (t - 1) / 2 := by omega
                simp [hd, hrt, this]
            · simp [hd, ht0]

theorem domR_setR : ∀ (T : RT) (t a r : Nat), domR (setR T t a) r = domR T r
  | .leaf, _, _, _ => rfl
  | .node l x rt, t, a, r => by
    rw [setR_node]
    split_ifs with h0 h1
    · rw [domR_node, domR_node]
    · rw [domR_node, domR_node, domR_setR l]
    · rw [domR_node, domR_node, domR_setR rt]

theorem mkT_spec : ∀ (fuel n : Nat) (f : Nat → Nat), n ≤ fuel → ∀ r,
    getR (mkT fuel n f) r = (if r < n then f r else 0) ∧ domR (mkT fuel n f) r = decide (r < n)
  | 0, n, f, h, r => by
    have : n = 0 := by omega
    subst this
    exact ⟨rfl, rfl⟩
  | fuel + 1, n, f, h, r => by
    have hm : mkT (fuel + 1) n f = if n = 0 then RT.leaf else
        RT.node (mkT fuel (n / 2) fun j => f (2 * j + 1)) (f 0)
          (mkT fuel ((n - 1) / 2) fun j => f (2 * j + 2)) :=
      brecE (α := RT) n 0 _ _
    rw [hm]
    by_cases hn : n = 0
    · subst hn
      simp [getR, domR]
    · rw [if_neg hn, getR_node, domR_node]
      have hl := mkT_spec fuel (n / 2) (fun j => f (2 * j + 1)) (by omega) ((r - 1) / 2)
      have hr := mkT_spec fuel ((n - 1) / 2) (fun j => f (2 * j + 2)) (by omega) ((r - 1) / 2)
      by_cases hr0 : r = 0
      · subst hr0
        simp [Nat.pos_of_ne_zero hn]
      · by_cases h2 : r % 2 = 1
        · simp only [hr0, h2, if_false, if_true, hl.1, hl.2]
          have e : 2 * ((r - 1) / 2) + 1 = r := by omega
          rw [e]
          have : (r - 1) / 2 < n / 2 ↔ r < n := by omega
          simp only [this, and_self]
        · simp only [hr0, h2, if_false, hr.1, hr.2]
          have e : 2 * ((r - 1) / 2) + 2 = r := by omega
          rw [e]
          have : (r - 1) / 2 < (n - 1) / 2 ↔ r < n := by omega
          simp only [this, and_self]

variable {V : Type} (O : Ops Nat V)

@[expose] noncomputable def stepRT (T : RT) : Op → RT
  | .mul i j t => setR T t (O.mul (getR T i) (getR T j))
  | .pow e i t => setR T t (O.pow (getR T i) e)

theorem runT_eq : ∀ (prog : List Op) (T : RT) (k : RT → Bool),
    runT O prog T k = k (prog.foldl (stepRT O) T)
  | [], _, _ => rfl
  | op :: prog, T, k => by
    change stepT O T (fun T' => runT O prog T' k) op = _
    cases op with
    | mul i j t =>
      change forceB _ (fun a => setK T t a fun T' => runT O prog T' k) = _
      rw [forceB_eq, setK_eq, runT_eq prog]
      rfl
    | pow e i t =>
      change forceB _ (fun a => setK T t a fun T' => runT O prog T' k) = _
      rw [forceB_eq, setK_eq, powN_eq O _ _ _ (Nat.lt_succ_self e), runT_eq prog]
      rfl

def Inv (T : RT) (L : List Nat) : Prop :=
  (∀ r, getR T r = getN L r) ∧ ∀ r, domR T r = decide (r < L.length)

theorem getN_set (L : List Nat) (t x r : Nat) :
    getN (L.set t x) r = if t < L.length ∧ r = t then x else getN L r := by
  by_cases ht : t < L.length
  · by_cases hr : r = t
    · subst hr
      rw [getN_set_eq ht, if_pos ⟨ht, rfl⟩]
    · rw [getN_set_ne L (Ne.symm hr), if_neg (fun h => hr h.2)]
  · rw [List.set_eq_of_length_le (by omega), if_neg (fun h => ht h.1)]

theorem inv_set {T : RT} {L : List Nat} (h : Inv T L) (t x : Nat) :
    Inv (setR T t x) (L.set t x) := by
  refine ⟨fun r => ?_, fun r => ?_⟩
  · rw [getR_setR, getN_set, h.1 r, h.2 t]
    simp
  · rw [domR_setR, h.2 r, List.length_set]

theorem inv_step {T : RT} {L : List Nat} (h : Inv T L) (op : Op) :
    Inv (stepRT O T op) (stepL O L op) := by
  cases op with
  | mul i j t =>
    change Inv (setR T t _) (L.set t _)
    rw [h.1 i, h.1 j]
    exact inv_set h t _
  | pow e i t =>
    change Inv (setR T t _) (L.set t _)
    rw [h.1 i]
    exact inv_set h t _

theorem inv_run : ∀ (prog : List Op) {T : RT} {L : List Nat}, Inv T L →
    Inv (prog.foldl (stepRT O) T) (prog.foldl (stepL O) L)
  | [], _, _, h => h
  | op :: prog, _, _, h => inv_run prog (inv_step O h op)

theorem inv_init (A B n : Nat) : Inv (mkT n n (initF A B O.one)) (initN O A B n) := by
  refine ⟨fun r => ?_, fun r => ?_⟩
  · rw [(mkT_spec n n _ (Nat.le_refl n) r).1]
    simp only [getN, initN, List.getD_eq_getElem?_getD, List.getElem?_map]
    by_cases hr : r < n
    · rw [if_pos hr, List.getElem?_range hr]
      simp only [Option.map_some, Option.getD_some, initF, brecE]
    · rw [if_neg hr, List.getElem?_eq_none (by simpa using hr)]
      rfl
  · rw [(mkT_spec n n _ (Nat.le_refl n) r).2, length_initN]

theorem regsT_eq (A B n : Nat) (prog : List Op) (k : (Nat → Nat) → Bool) :
    regsT O A B n prog (fun T => k (getR T)) = regsN O A B n prog (fun R => k (getN R)) := by
  unfold regsT
  rw [forceB_eq, runT_eq, regsN_eq]
  congr 1
  funext r
  exact (inv_run O prog (inv_init O A B n)).1 r

theorem evalWG_getN (R : List Nat) : ∀ w : Word, evalWG O (getN R) w = evalWN O R w
  | [] => rfl
  | (r, e) :: w => by
    rw [evalWG, evalWN, evalWG_getN R w]

theorem factG_getN (R : List Nat) (n : Nat) (f : MFact) :
    factG O (getN R) n f = factN O R n f := by
  cases f <;> simp only [factG, factN, evalWG_getN]

theorem certG_getN (R : List Nat) (C : MCert) : certG O (getN R) C = certN O R C := by
  unfold certG certN
  congr 1
  exact List.all_congr rfl fun f => factG_getN O R C.nregs f

theorem mcertT_eq (A B : Nat) (C : MCert) : mcertT O A B C = mcertN O A B C := by
  unfold mcertT mcertN
  rw [regsT_eq O A B C.nregs C.prog (fun g => certG O g C)]
  simp only [certG_getN]

theorem seedsT_eq (A B n : Nat) (prog : List Op) (fs : List MFact) (rA rB : Nat) :
    seedsT O A B n prog fs rA rB = regsN O A B n prog (fun R => certN O R ⟨n, prog, fs⟩ &&
      O.eq (getN R rA) A && O.eq (getN R rB) B) := by
  unfold seedsT
  rw [regsT_eq O A B n prog
    (fun g => certG O g ⟨n, prog, fs⟩ && O.eq (g rA) A && O.eq (g rB) B)]
  simp only [certG_getN]

end CFSG.KC.OpsMT

end
