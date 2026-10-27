module

public import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2.Model

structure FnFacts (n : ℕ) : Prop where
  centralizes_iff : ∀ g ∈ Fgrp n, (∀ q ∈ Fgrp n, q.1 = 1 → g * q = q * g) ↔
    Equiv.Perm.sign g.1 = 1
  card_C_q : ∀ q : Amb n, q ∈ Fgrp n → q.1 = 1 → q ≠ 1 → q ≠ x0 n →
    Nat.card ↥(Hgrp n q) = 2 * n.factorial
  card_C_inv : ∀ w : Amb n, w ∈ Fgrp n → w * w = 1 → Nat.card ↥(Hgrp n w) = 2 * n.factorial →
    w.1 = 1 ∧ w ≠ 1 ∧ w ≠ x0 n
  not_dvd : ¬ (2 * n.factorial ∣ 192 * (n - 4).factorial)

@[expose] def PatternFacts (G : Type) [Group G] (n : ℕ) : Prop :=
  (∀ w : G, orderOf w = 2 → Nat.card ↥(centralizer ({w} : Set G)) = 4 * n.factorial ∨
      Nat.card ↥(centralizer ({w} : Set G)) = 192 * (n - 4).factorial) ∧
    ∀ w w' : G, orderOf w = 2 → orderOf w' = 2 →
      Nat.card ↥(centralizer ({w} : Set G)) = 4 * n.factorial →
      Nat.card ↥(centralizer ({w'} : Set G)) = 4 * n.factorial → IsConj w w'

end CFSG.GH74.GLS.C3.Prop121
