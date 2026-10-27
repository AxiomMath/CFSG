module

public import Certificates.Data.Kernel.L34W.ChCover
public import CFSG.Certificates.Kernel.L34W.ModelSound

public section

namespace CFSG.KC.L34W

open CFSG.KC.Enum CFSG.KS CFSG.OddStandard.ChengHeldData
open CFSG.ComponentClassification.GrSLit.L34Facts.Real

variable {T A : ℕ → ℕ}

theorem bAnd_and (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

theorem dec_zero_one : dec 0 = oneM := by decide

theorem evalC_var (σ : ℕ → ℕ) (i : ℕ) : evalC T σ (.var i) = σ i := rfl
theorem evalC_one (σ : ℕ → ℕ) : evalC T σ .one = 0 := rfl
theorem evalC_mul (σ : ℕ → ℕ) (a b : Tm) :
    evalC T σ (.mul a b) = mulC T (evalC T σ a) (evalC T σ b) := rfl
theorem evalC_inv (σ : ℕ → ℕ) (a : Tm) : evalC T σ (.inv a) = invC T (evalC T σ a) := rfl

theorem evalC_lt (hb : boundsOK T A = true) {σ : ℕ → ℕ} (hσ : ∀ i, σ i < 1024) :
    ∀ t : Tm, evalC T σ t < 1024
  | .var i => hσ i
  | .one => by rw [evalC_one]; norm_num
  | .mul a b => by
    rw [evalC_mul]
    exact mulC_lt hb (evalC_lt hb hσ a) (evalC_lt hb hσ b)
  | .inv a => by
    rw [evalC_inv]
    exact invC_lt

theorem evalM_eq (hT : T1Of T) (hb : boundsOK T A = true) {σ : ℕ → ℕ} (hσ : ∀ i, σ i < 1024) :
    ∀ t : Tm, t.evalM (fun i => dec (σ i)) = dec (evalC T σ t)
  | .var i => rfl
  | .one => by rw [evalC_one, dec_zero_one]; rfl
  | .mul a b => by
    rw [evalC_mul, dec_mulC hT (evalC_lt hb hσ a) (evalC_lt hb hσ b), ← evalM_eq hT hb hσ a,
      ← evalM_eq hT hb hσ b]
    rfl
  | .inv a => by
    rw [evalC_inv, dec_invC hT (evalC_lt hb hσ a), ← evalM_eq hT hb hσ a]
    rfl

theorem inKC12_aux : ∀ p : ℕ, p < 4 → ∀ q : ℕ, q < 4 → ∀ r : ℕ, r < 4 → ∀ s : ℕ, s < 4 →
    decide (inKC ((1 : ZMod 4), (2 : ZMod 4)) ((p : ZMod 4) - (q : ZMod 4))
      ((r : ZMod 4) - (s : ZMod 4))) = inKN 1 2 (subM p q) (subM r s) := by
  decide +kernel

theorem inKC10_aux : ∀ p : ℕ, p < 4 → ∀ q : ℕ, q < 4 → ∀ r : ℕ, r < 4 → ∀ s : ℕ, s < 4 →
    decide (inKC ((1 : ZMod 4), (0 : ZMod 4)) ((p : ZMod 4) - (q : ZMod 4))
      ((r : ZMod 4) - (s : ZMod 4))) = inKN 1 0 (subM p q) (subM r s) := by
  decide +kernel

theorem n2_aux : ∀ r : ℕ, r < 4 → ∀ s : ℕ, s < 4 →
    ((((r : ZMod 4) - (s : ZMod 4)).val % 2 == 0) = Nat.beq (r % 2) (s % 2)) := by
  decide +kernel

theorem beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem beq_div (x y : ℕ) : ((dec x).1 == (dec y).1) = Nat.beq (x / 16) (y / 16) := by
  simp only [dec]
  cases h : Nat.beq (x / 16) (y / 16)
  · simpa using Nat.ne_of_beq_eq_false h
  · simpa using Nat.eq_of_beq_eq_true h

theorem eqKM12_dec (x y : ℕ) : eqKM ((1 : ZMod 4), (2 : ZMod 4)) (dec x) (dec y) = eqKC 1 2 x y := by
  unfold eqKM eqKC
  rw [beq_div, bAnd_and]
  congr 1
  exact inKC12_aux _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num)) _
    (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num))

theorem eqKM10_dec (x y : ℕ) : eqKM ((1 : ZMod 4), (0 : ZMod 4)) (dec x) (dec y) = eqKC 1 0 x y := by
  unfold eqKM eqKC
  rw [beq_div, bAnd_and]
  congr 1
  exact inKC10_aux _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num)) _
    (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num))

theorem eqN2_dec (x y : ℕ) : eqN2 (dec x) (dec y) = eqN2C x y := by
  unfold eqN2 eqN2C
  rw [beq_div, bAnd_and]
  congr 1
  simp only [dec]
  rw [n2_aux _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num))]
  congr 1 <;> exact Nat.mod_mod_of_dvd _ (by norm_num)

theorem relsC_cons (E : ℕ → ℕ → Bool) (σ : ℕ → ℕ) (e : Tm × Tm) (l : List (Tm × Tm)) :
    relsC T E σ (e :: l) = (E (evalC T σ e.1) (evalC T σ e.2) && relsC T E σ l) :=
  bAnd_and _ _

theorem actC_cons (E : ℕ → ℕ → Bool) (σ : ℕ → ℕ) (i : ℕ) (e : ℕ × Tm) (l : List (ℕ × Tm)) :
    actC T A E σ i (e :: l) = (E (betaRepC A i (σ e.1)) (evalC T σ e.2) && actC T A E σ i l) :=
  bAnd_and _ _

theorem relsOK_eq (hT : T1Of T) (hb : boundsOK T A = true) {σ : ℕ → ℕ} (hσ : ∀ i, σ i < 1024)
    {eqf : MElt → MElt → Bool} {E : ℕ → ℕ → Bool} (hE : ∀ x y, eqf (dec x) (dec y) = E x y) :
    ∀ rels : List (Tm × Tm), relsOK eqf (fun i => dec (σ i)) rels = relsC T E σ rels
  | [] => rfl
  | e :: l => by
    have ih := relsOK_eq hT hb hσ hE l
    unfold relsOK at ih ⊢
    simp only [List.all_cons]
    rw [evalM_eq hT hb hσ, evalM_eq hT hb hσ, hE, ih, relsC_cons]

theorem actOK_eq (hT : T1Of T) (hA : AlOf A) (hb : boundsOK T A = true) {σ : ℕ → ℕ}
    (hσ : ∀ i, σ i < 1024) {eqf : MElt → MElt → Bool} {E : ℕ → ℕ → Bool}
    (hE : ∀ x y, eqf (dec x) (dec y) = E x y) {i : ℕ} (hi : i < 36) :
    ∀ rels : List (ℕ × Tm), actOK eqf (fun i => dec (σ i)) i rels = actC T A E σ i rels
  | [] => rfl
  | e :: l => by
    have ih := actOK_eq hT hA hb hσ hE hi l
    unfold actOK at ih ⊢
    simp only [List.all_cons]
    rw [← dec_betaRepC hA hi (hσ e.1), evalM_eq hT hb hσ, hE, ih, actC_cons]

theorem frC_lt (α i : ℕ) : frC α i < 1024 := by
  unfold frC
  cases Nat.beq i 0 <;> cases Nat.beq i 1 <;> cases Nat.beq i 2 <;> cases Nat.beq i 3 <;>
    cases Nat.beq i 4 <;> cases Nat.beq i 5 <;> cases Nat.beq α 0 <;> cases Nat.beq α 1 <;>
    cases Nat.beq α 2 <;> decide

theorem frM_eq {α : ℕ} (hα : α < 3) : frM α = fun i => dec (frC α i) := by
  funext i
  rcases i with _ | _ | _ | _ | _ | _ | i
  all_goals interval_cases α
  all_goals first
    | decide
    | (have h : ∀ k, k < 6 → Nat.beq (i + 6) k = false := fun k hk => beq_false (by omega)
       simp only [frM, frC, h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num),
         h 3 (by norm_num), h 4 (by norm_num), h 5 (by norm_num)]
       decide)

end CFSG.KC.L34W

end
