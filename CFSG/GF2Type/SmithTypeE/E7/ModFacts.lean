module

public import CFSG.Assembly.LowTwoRankDefs
public import Certificates.Data.SmithD6Model

public section

namespace CFSG.GF2Type.SmithTypeE.E7

open CFSG.SmithD6 (wt adjW tvCols applyCols)

structure E7ModelFacts : Prop where
  wt_ne_zero : ∀ {i : Nat}, i < 75735 → wt i ≠ 0
  exists_adj : ∀ {i : Nat}, i < 75735 → ∃ j < 75735, adjW i j = true ∧ wt j ≠ wt i
  wt_ne_xor : ∀ {i j : Nat}, i < 75735 → j < 75735 → adjW i j = false →
    ∀ k < 75735, wt k ≠ wt i ^^^ wt j
  tv_wt : ∀ {k i : Nat}, k < 365211 → i < 75735 →
    ∃ j < 75735, wt j = applyCols (tvCols k) (wt i) ∧ adjW i j = true
  pair_rel_sym : ∀ {k l : Nat}, k < 365211 → l < 365211 → k ≠ l →
    (∀ c < 2 ^ 32, applyCols (tvCols k) (applyCols (tvCols l) c) =
      applyCols (tvCols l) (applyCols (tvCols k) c)) ∨
    (∀ c < 2 ^ 32, applyCols (tvCols k) (applyCols (tvCols l) (applyCols (tvCols k) c)) =
      applyCols (tvCols l) (applyCols (tvCols k) (applyCols (tvCols l) c))) ∨
    (∀ c < 2 ^ 32, applyCols (tvCols k) (applyCols (tvCols l) (applyCols (tvCols k)
        (applyCols (tvCols l) c))) =
      applyCols (tvCols l) (applyCols (tvCols k) (applyCols (tvCols l) (applyCols (tvCols k) c))))
  int_rel_sym : ∀ {k l : Nat}, k < 365211 → l < 365211 → k ≠ l → ∀ {c c' : Nat}, c < 2 ^ 32 →
    c' < 2 ^ 32 → applyCols (tvCols k) c ^^^ c = applyCols (tvCols l) c' ^^^ c' →
      applyCols (tvCols k) c ^^^ c = 0 ∨
        ((∀ e < 2 ^ 32, applyCols (tvCols k) (applyCols (tvCols l) e) =
          applyCols (tvCols l) (applyCols (tvCols k) e)) ∧
         ∃ j < 75735, wt j = applyCols (tvCols k) c ^^^ c)

end CFSG.GF2Type.SmithTypeE.E7
