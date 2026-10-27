module

public import Certificates.Data.Kernel.U43Mod.Defs
public import CFSG.Quasithin.H13.GoldschmidtU43ModInputs
public import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KS.U43Mod

open CFSG.KC.Enum CFSG.KC.U43Mod CFSG.Quasithin.H13.U43

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

@[expose] def LetRep (n : ℕ) (G Gi : ℕ → ℕ → ℕ) (g : ℕ → Equiv.Perm (Fin n)) (i : ℕ) : Prop :=
  ∀ q (hq : q < n), G i q = (g i ⟨q, hq⟩ : ℕ) ∧ Gi i q = ((g i)⁻¹ ⟨q, hq⟩ : ℕ)

variable {n : ℕ} {G Gi : ℕ → ℕ → ℕ} {g : ℕ → Equiv.Perm (Fin n)}

theorem lpt_eq {l : ℕ × Bool} (h : LetRep n G Gi g l.1) {q : ℕ} (hq : q < n) :
    lpt G Gi l q = (letterVal g l ⟨q, hq⟩ : ℕ) := by
  obtain ⟨i, s⟩ := l
  cases s
  · exact (h q hq).2
  · exact (h q hq).1

theorem lpt_swap_eq {l : ℕ × Bool} (h : LetRep n G Gi g l.1) {q : ℕ} (hq : q < n) :
    lpt Gi G l q = ((letterVal g l)⁻¹ ⟨q, hq⟩ : ℕ) := by
  obtain ⟨i, s⟩ := l
  cases s
  · change G i q = _
    simp only [letterVal, Bool.false_eq_true, ↓reduceIte, inv_inv]
    exact (h q hq).1
  · change Gi i q = _
    simp only [letterVal, ↓reduceIte]
    exact (h q hq).2

theorem evalG_cons (l : ℕ × Bool) (w : List (ℕ × Bool)) :
    evalG g (l :: w) = letterVal g l * evalG g w := by
  simp [evalG]

theorem wv_eq : ∀ (w : List (ℕ × Bool)), (∀ l ∈ w, LetRep n G Gi g l.1) →
    ∀ q (hq : q < n), wv G Gi w q = (evalG g w ⟨q, hq⟩ : ℕ)
  | [], _, q, hq => by simp [wv, evalG]
  | l :: w, hw, q, hq => by
    have ih := wv_eq w (fun l' h' => hw l' (List.mem_cons_of_mem _ h')) q hq
    change strictN (wv G Gi w q) (lpt G Gi l) = _
    rw [strictN_eq, ih, lpt_eq (hw l List.mem_cons_self) (Fin.is_lt _), evalG_cons,
      Equiv.Perm.mul_apply]

theorem wvI_eq : ∀ (w : List (ℕ × Bool)), (∀ l ∈ w, LetRep n G Gi g l.1) →
    ∀ q (hq : q < n), wvI G Gi w q = ((evalG g w)⁻¹ ⟨q, hq⟩ : ℕ)
  | [], _, q, hq => by simp [wvI, evalG]
  | l :: w, hw, q, hq => by
    change strictN (lpt Gi G l q) (wvI G Gi w) = _
    rw [strictN_eq, lpt_swap_eq (hw l List.mem_cons_self) hq,
      wvI_eq w (fun l' h' => hw l' (List.mem_cons_of_mem _ h')) _ (Fin.is_lt _), evalG_cons,
      mul_inv_rev, Equiv.Perm.mul_apply]

theorem wSel_eq : ∀ (W : List (List (ℕ × Bool))) (i : ℕ), wSel W i = W.getD i []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: W, i + 1 => wSel_eq W i

theorem letRep_wG {W : List (List (ℕ × Bool))} {i : ℕ}
    (hW : ∀ l ∈ W.getD i [], LetRep n G Gi g l.1) :
    LetRep n (wG G Gi W) (wGi G Gi W) (fun i => evalG g (W.getD i [])) i := by
  intro q hq
  change wv G Gi (wSel W i) q = _ ∧ wvI G Gi (wSel W i) q = _
  rw [wSel_eq]
  exact ⟨wv_eq _ hW q hq, wvI_eq _ hW q hq⟩

theorem beq_iff {a b : ℕ} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => by rw [h]; exact Nat.beq_refl b⟩

theorem baseEq_iff {bs : List ℕ} {f f' : ℕ → ℕ} :
    baseEq bs f f' = true ↔ ∀ p ∈ bs, f p = f' p := by
  induction bs with
  | nil => simp [baseEq]
  | cons p bs ih =>
    change Bool.rec (motive := fun _ => Bool) false (baseEq bs f f') (Nat.beq (f p) (f' p)) =
      true ↔ _
    rw [bAnd_iff, ih, List.forall_mem_cons, beq_iff]

theorem relsB_iff {bs : List ℕ} {rs : List (List (ℕ × Bool))} :
    relsB bs G Gi rs = true ↔ ∀ r ∈ rs, ∀ p ∈ bs, wv G Gi r p = p := by
  induction rs with
  | nil => simp [relsB]
  | cons r rs ih =>
    change Bool.rec (motive := fun _ => Bool) false (relsB bs G Gi rs)
      (baseEq bs (wv G Gi r) (fun q => q)) = true ↔ _
    rw [bAnd_iff, ih, baseEq_iff, List.forall_mem_cons]

end CFSG.KS.U43Mod

end
