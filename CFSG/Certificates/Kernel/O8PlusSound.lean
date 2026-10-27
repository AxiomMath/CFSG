module

public import CFSG.Certificates.Kernel.O8EnumSound
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Lin

public section

namespace CFSG.KC.O8

open CFSG.EvenSmallLie.OmegaEight.Stage2

@[expose] noncomputable def powKK (a : ℕ) : ℕ → ℕ
  | 0 => ID12
  | n + 1 => mul12K (powKK a n) a

theorem powK_eq (a n : ℕ) : powK a n = powKK a n := by
  induction n with
  | zero => simp [powK, powKK, idK_eq]
  | succ n ih => simp [powK, powKK, ih, mulK_eq]

@[expose] noncomputable def fpowAuxK : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | f + 1, b, n, acc =>
    if n = 0 then acc else fpowAuxK f (mul12K b b) (n / 2) (if n % 2 = 1 then mul12K acc b else acc)

theorem fpowAux_eq (f b n acc : ℕ) : fpowAux f b n acc = fpowAuxK f b n acc := by
  induction f generalizing b n acc with
  | zero => simp [fpowAux, fpowAuxK]
  | succ f ih => simp [fpowAux, fpowAuxK, ih, mulK_eq]

theorem fpowK_eq (a n : ℕ) : fpowK a n = fpowAuxK 64 a n ID12 := by
  rw [fpowK, fpowAux_eq, idK_eq]

@[expose] noncomputable def stepKK (R : Array ℕ) (ins : ℕ × ℕ × ℕ) : Array ℕ :=
  R.push (if ins.1 = 0 then mul12K (R.getD ins.2.1 ID12) (R.getD ins.2.2 ID12)
    else powKK (R.getD ins.2.1 ID12) ins.2.2)

theorem stepK_eq : stepK = stepKK := by
  funext R ins
  simp only [stepK, stepKK, mulK_eq, powK_eq, idK_eq]

theorem runK_eq (gens : Array ℕ) (prog : List (ℕ × ℕ × ℕ)) :
    runK gens prog = prog.foldl stepKK gens := by
  rw [runK, stepK_eq]

@[expose] noncomputable def conPartK : List (ℕ × ℕ) → List (List ℕ) → ℕ → ℕ
  | c :: cs, q :: qs, m => linComb q (mul12K c.1 m ^^^ mul12K m c.2) ^^^ conPartK cs qs m
  | _, _, _ => 0

theorem conPart_eq : ∀ (cs : List (ℕ × ℕ)) (qs : List (List ℕ)) (m : ℕ),
    conPart cs qs m = conPartK cs qs m
  | c :: cs, q :: qs, m => by simp only [conPart, conPartK, mulK_eq, conPart_eq cs qs m]
  | [], _, _ => by simp [conPart, conPartK]
  | _ :: _, [], _ => by simp [conPart, conPartK]

theorem spanAll_of_chunks {qf : List ℕ} {d s : ℕ} {P : ℕ → Bool} (hs : s ≤ d)
    (h : ∀ k < 2 ^ (d - s), ((List.range (2 ^ s)).all fun c => P (linComb qf (k * 2 ^ s + c))) =
      true) : spanAll qf d P = true := by
  simp only [spanAll, List.all_eq_true, List.mem_range] at h ⊢
  intro c hc
  have h2 : 0 < 2 ^ s := by positivity
  have hd : 2 ^ d = 2 ^ (d - s) * 2 ^ s := by rw [← pow_add, Nat.sub_add_cancel hs]
  have hk : c / 2 ^ s < 2 ^ (d - s) := by
    rw [Nat.div_lt_iff_lt_mul h2, ← hd]
    exact hc
  have := h (c / 2 ^ s) hk (c % 2 ^ s) (Nat.mod_lt _ h2)
  rwa [Nat.div_add_mod' c (2 ^ s)] at this

end CFSG.KC.O8

end
