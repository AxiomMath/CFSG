module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abBKill

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

namespace MB

@[expose] def fdOf (p : ℕ × ℕ) : List MB := d3L.getD p.2 []

@[expose] def g0Q (p : ℕ × ℕ) : List MB :=
  compQ1 (fdOf p) (compQ1 (cQ p.1) (compQ1 (fdOf p) (fdOf p)))

@[expose] def H2elt (p : ℕ × ℕ) (s : MB) (a : Bool) : List MB :=
  compQ1 (conjQ1 s) (if a then cQ p.1 else gensQ1)

@[expose] def H4elt (p : ℕ × ℕ) (s : MB) (a b : Bool) : List MB :=
  compQ1 (H2elt p s a) (if b then g0Q p else gensQ1)

@[expose] def reps32 : List MB := (allBits 5).map (nfProd [w₂, u, w₁, v, t])

@[expose] def rep (s : MB) : MB := nfProd [w₂, u, w₁, v, t] [bit s 0, bit s 1, bit s 2, bit s 3,
  bit s 6]

@[expose] def H4T : List (MB × Bool × Bool) :=
  reps32.flatMap fun s => [(s, false, false), (s, false, true), (s, true, false), (s, true, true)]

@[expose] def liftSp : List (MB × Bool) := [(w₂, false), (u * w₁ * t, true), (w₁, false),
  (v, false), (1, false), (1, false), (w₂ * t, false), (1, false)]

theorem rep_mem (s : MB) : rep s ∈ reps32 :=
  List.mem_map.mpr ⟨_, mem_allBits [bit s 0, bit s 1, bit s 2, bit s 3, bit s 6], rfl⟩

theorem conjQ1_rep : ∀ s : MB, conjQ1 (rep s) = conjQ1 s := by decide +kernel

theorem mem_H4T {s : MB} (hs : s ∈ reps32) (a b : Bool) : (s, a, b) ∈ H4T := by
  simp only [H4T, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
  exact ⟨s, hs, by cases a <;> cases b <;> simp⟩

theorem goodIdx_fst : ∀ p ∈ goodIdx, p.1 < 4 := goodIdx_lt

theorem goodIdx_snd : ∀ p ∈ goodIdx, p.2 < 16 := by decide +kernel

theorem fdOf_mem_d3L {p : ℕ × ℕ} (hp : p ∈ goodIdx) : fdOf p ∈ d3L := by
  rw [fdOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
    (d3L_length ▸ goodIdx_snd p hp), Option.getD_some]
  exact List.getElem_mem _

theorem lift_sp : ∀ p ∈ goodIdx, ∀ i : Fin 8, compQ1 (g0Q p) (conjQ1 (gens.getD i 1)) =
    compQ1 (H2elt p (liftSp.getD i (1, false)).1 (liftSp.getD i (1, false)).2) (g0Q p) := by
  decide +kernel

theorem lift_c : ∀ p ∈ goodIdx, compQ1 (g0Q p) (cQ p.1) =
    compQ1 (H2elt p (w₂ * w₁) true) (g0Q p) := by decide +kernel

theorem lift_sq : ∀ p ∈ goodIdx, compQ1 (g0Q p) (g0Q p) = H2elt p w₂ false := by decide +kernel

theorem g0Q_k : ∀ p ∈ goodIdx, applyQ1 (g0Q p) k = y * k := by decide +kernel

theorem g0Q_mem : ∀ p ∈ goodIdx, ∀ x ∈ g0Q p, inQ1 x = true := by decide +kernel

theorem g0Q_length : ∀ p ∈ goodIdx, (g0Q p).length = 7 := by decide +kernel

theorem liftSp_length : liftSp.length = 8 := rfl

end MB

end Sec8

end CFSG.ComponentClassification.HSFLit
