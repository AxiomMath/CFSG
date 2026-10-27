module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Num

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

@[expose] def twoRankLow107 (lab : GLALabel) : ℕ :=
  match lab.tag with
  | .A => lab.n * ((lab.rank + 1) ^ 2 / 4)
  | .twA => lab.n * ((lab.rank + 1) / 2) ^ 2
  | .B => max (lab.n * (2 * lab.rank - 1)) (lab.n * (lab.rank * (lab.rank - 1) / 2))
  | .C => lab.n * (lab.rank * (lab.rank + 1) / 2)
  | .D => lab.n * (lab.rank * (lab.rank - 1) / 2)
  | .twD => max (lab.n * (2 * lab.rank - 2)) (lab.n * ((lab.rank - 1) * (lab.rank - 2) / 2))
  | .twB2 => lab.n
  | .triD4 => 5 * lab.n
  | .G2 => 3 * lab.n
  | .F4 => 7 * lab.n
  | .twF4 => 2 * lab.n
  | .E6 => 16 * lab.n
  | .E7 => 16 * lab.n
  | .E8 => 16 * lab.n
  | .twE6 => 9 * lab.n
  | _ => 0

@[expose] noncomputable def upA107 (lab : GLALabel) (p : ℕ) : ℕ :=
  rk2Mult lab (rk2Ord p lab.n) + (if p ∣ lab.n then 1 else 0) +
    (if p = 3 ∧ ((lab.tag = .D ∧ lab.rank = 4) ∨ lab.tag = .triD4) then 1 else 0)

@[expose] def exempt107 (lab : GLALabel) : Prop :=
  lab.n = 1 ∧ ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 3 ∨ lab.tag = .twA ∧ lab.rank = 3 ∨
    lab.tag = .twD ∧ lab.rank = 3 ∨ lab.tag = .D ∧ lab.rank = 4)

@[expose] def survivor107 (lab : GLALabel) : Prop :=
  (lab.n = 1 ∧ ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 3 ∨ lab.tag = .twA ∧ (lab.rank = 3 ∨ lab.rank = 4) ∨
    lab.tag = .twD ∧ lab.rank = 3 ∨ lab.tag = .D ∧ lab.rank = 4 ∨ lab.tag = .triD4)) ∨
  (lab.tag = .twA ∧ lab.rank = 2 ∧ lab.n = 3)

theorem m0_cases {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (rk2Ord p n = 1 ∧ p ∣ 2 ^ n - 1) ∨ (rk2Ord p n = 2 ∧ p ∣ 2 ^ n + 1) ∨ 3 ≤ rk2Ord p n := by
  have hpos := rk2Ord_pos hp hp2 n
  by_cases h1 : rk2Ord p n = 1
  · exact Or.inl ⟨h1, rk2Ord_eq_one_iff.1 h1⟩
  by_cases h2 : rk2Ord p n = 2
  · exact Or.inr (Or.inl ⟨h2, (rk2Ord_eq_two_iff hp hp2).1 h2⟩)
  exact Or.inr (Or.inr (by omega))

end CFSG.LocalAnalysis.GLTheoremA

end
