
module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsModel
public import Certificates.Data.ONanB2A6

@[expose] public section

namespace CFSG.OddStandard.ONanRec.A6C

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts

@[expose] def Ord4 (u : P10) : Prop := u ^ 4 = 1 ∧ u ^ 2 ≠ 1

@[expose] def PC (u r : P10) : Prop :=
  r ≠ 1 ∧ r ^ 3 = 1 ∧ u * r * u ^ 3 * r = r * (u * r * u ^ 3) ∧ u ^ 2 * r * u ^ 2 = r ^ 2

@[expose] def DC (u d : P10) : Prop := d ^ 2 = 1 ∧ d ≠ 1 ∧ d * u * d * u = 1

@[expose] def pEltP (u r0 : P10) (i j : ℕ) : P10 := r0 ^ i * (u * r0 * u ^ 3) ^ j

@[expose] def eOfP (u r : P10) : P10 := r * u ^ 2 * r ^ 2

@[expose] def conjP (b : P10) (k : ℕ) (x : P10) : P10 := b ^ k * x * (b ^ 119) ^ k

@[expose] def RelP (b d e : P10) : Prop :=
  conjP b 3 (e * d) * conjP b 2 (d * e) * conjP b 1 (e * d) * d = 1

@[expose] def BC (u d b : P10) : Prop :=
  b * u = u ^ 3 * b ∧ b * d = u * d * b ∧
    ∀ x ∈ pslGens, b ^ 2 * x = u ^ 2 * x * u ^ 2 * b ^ 2

theorem beq_code (x y : P10) : (code x == code y) = true ↔ x = y := by
  rw [beq_iff_eq]
  exact code_injective.eq_iff

theorem beq_code_cid (x : P10) : (code x == Core.cid) = true ↔ x = 1 := by
  rw [← code_one, beq_code]

theorem ord4_code (u : P10) : ord4 (code u) = true ↔ Ord4 u := by
  rw [ord4, Ord4, Bool.and_eq_true, Bool.not_eq_true', ← code_pow, ← code_pow, beq_code_cid,
    ← Bool.not_eq_true, beq_code_cid]

theorem pCond_code (u r : P10) : pCond (code u) (code r) = true ↔ PC u r := by
  simp only [pCond, PC, Bool.and_eq_true, Bool.not_eq_true', ← code_pow, ← code_mul]
  rw [← Bool.not_eq_true, beq_code_cid, beq_code_cid, beq_code, beq_code]
  tauto

theorem dCond_code (u d : P10) : dCond (code u) (code d) = true ↔ DC u d := by
  simp only [dCond, DC, Bool.and_eq_true, Bool.not_eq_true', ← code_pow, ← code_mul]
  rw [← Bool.not_eq_true, beq_code_cid, beq_code_cid, beq_code_cid]
  tauto

theorem pElt_code (u r0 : P10) (i j : ℕ) : pElt (code u) (code r0) i j = code (pEltP u r0 i j) := by
  simp only [pElt, pEltP, ← code_pow, ← code_mul]

theorem eOf_code (u r : P10) : eOf (code u) (code r) = code (eOfP u r) := by
  simp only [eOf, eOfP, ← code_pow, ← code_mul]

theorem conjPow_code (b : P10) (k : ℕ) (x : P10) :
    conjPow (code b) k (code x) = code (conjP b k x) := by
  simp only [conjPow, conjP, ← code_pow, ← code_mul]

theorem relG_code (b d e : P10) : relG (code b) (code d) (code e) = true ↔ RelP b d e := by
  simp only [relG, RelP, ← code_mul, conjPow_code, beq_code_cid]

theorem bCond_code (u d b : P10) : bCond (code u) (code d) (code b) = true ↔ BC u d b := by
  simp only [bCond, BC, Bool.and_eq_true, ← code_pow, ← code_mul, beq_code, List.all_eq_true]
  rw [← pslGens_code]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, h2, fun x hx => ?_⟩
    have := h3 (code x) (List.mem_map_of_mem hx)
    simpa only [← code_mul, beq_code] using this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, fun c hc => ?_⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
    simpa only [← code_mul, beq_code] using h3 x hx

theorem beq_code_cid_false (x : P10) : (code x == Core.cid) = false ↔ x ≠ 1 := by
  rw [← Bool.not_eq_true, beq_code_cid]

end CFSG.OddStandard.ONanRec.A6C
