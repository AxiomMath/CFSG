module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abBWord

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

namespace MB

@[expose] def d3L : List (List MB) := [
  [w₂ * w₁ * z * y, w₂, v, y, z * y, t, k],
  [w₂ * w₁ * z * y * k, w₂, v, y, z * y, t, k],
  [w₂ * w₁ * z * y, w₂ * k, v, y, z * y, t, k],
  [w₂ * w₁ * z * y * k, w₂ * k, v, y, z * y, t, k],
  [w₂ * w₁ * y, w₂ * y, v, y, z * y, t, k],
  [w₂ * w₁ * y * k, w₂ * y, v, y, z * y, t, k],
  [w₂ * w₁ * y, w₂ * y * k, v, y, z * y, t, k],
  [w₂ * w₁ * y * k, w₂ * y * k, v, y, z * y, t, k],
  [w₂ * w₁, w₂ * z, v, y, z * y, t, k],
  [w₂ * w₁ * k, w₂ * z, v, y, z * y, t, k],
  [w₂ * w₁, w₂ * z * k, v, y, z * y, t, k],
  [w₂ * w₁ * k, w₂ * z * k, v, y, z * y, t, k],
  [w₂ * w₁ * z, w₂ * z * y, v, y, z * y, t, k],
  [w₂ * w₁ * z * k, w₂ * z * y, v, y, z * y, t, k],
  [w₂ * w₁ * z, w₂ * z * y * k, v, y, z * y, t, k],
  [w₂ * w₁ * z * k, w₂ * z * y * k, v, y, z * y, t, k]]

@[expose] def kill0 : List (ℕ × List ℕ × List MB × MB) := [
  (0, [0, 2, 1, 2, 1, 2, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (1, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (3, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (4, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (5, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (6, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (7, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (8, [0, 2, 1, 2, 1, 2, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (9, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (11, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (12, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (13, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (14, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (15, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1)]

@[expose] def kill1 : List (ℕ × List ℕ × List MB × MB) := [
  (1, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (2, [0, 2, 1, 2, 1, 2, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (3, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (4, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (5, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (6, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (7, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (9, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (10, [0, 2, 1, 2, 1, 2, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (11, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (12, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (13, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (14, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (15, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1)]

@[expose] def kill2 : List (ℕ × List ℕ × List MB × MB) := [
  (0, [0, 2, 1, 2, 1, 2, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (1, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (3, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (4, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (5, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (6, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (7, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (8, [0, 2, 1, 2, 1, 2, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (9, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (11, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (12, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (13, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (14, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (15, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1)]

@[expose] def kill3 : List (ℕ × List ℕ × List MB × MB) := [
  (1, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (2, [0, 2, 1, 2, 1, 2, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (3, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (4, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (5, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (6, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (7, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (9, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (10, [0, 2, 1, 2, 1, 2, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (11, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (12, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (13, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (14, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (15, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1)]

@[expose] def kill4 : List (ℕ × List ℕ × List MB × MB) := [
  (0, [0, 2, 0, 2, 0, 2, 1, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (1, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (2, [0, 2, 1, 2, 0, 2, 0, 2, 0], [w₂ * w₁ * v * t, u, w₁, v, 1, 1, t, 1], 1),
  (3, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (4, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (5, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (6, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (7, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (8, [0, 2, 0, 2, 0, 2, 1, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (9, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (10, [0, 2, 1, 2, 0, 2, 0, 2, 0], [w₂ * w₁ * v * t, u, w₁, v, 1, 1, t, 1], 1),
  (11, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (12, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (13, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (14, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (15, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1)]

@[expose] def kill5 : List (ℕ × List ℕ × List MB × MB) := [
  (0, [0, 2, 1, 2, 0, 2, 0, 2, 0], [w₂ * w₁ * v * t, u, w₁, v, 1, 1, t, 1], 1),
  (1, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (2, [0, 2, 0, 2, 0, 2, 1, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (3, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (4, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (5, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (6, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (7, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (8, [0, 2, 1, 2, 0, 2, 0, 2, 0], [w₂ * w₁ * v * t, u, w₁, v, 1, 1, t, 1], 1),
  (9, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (10, [0, 2, 0, 2, 0, 2, 1, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (11, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (12, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (13, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (14, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (15, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1)]

@[expose] def kill6 : List (ℕ × List ℕ × List MB × MB) := [
  (0, [0, 2, 0, 2, 0, 2, 1, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (1, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (2, [0, 2, 1, 2, 0, 2, 0, 2, 0], [w₂ * w₁ * v * t, u, w₁, v, 1, 1, t, 1], 1),
  (3, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (4, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (5, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (6, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (7, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (8, [0, 2, 0, 2, 0, 2, 1, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (9, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (10, [0, 2, 1, 2, 0, 2, 0, 2, 0], [w₂ * w₁ * v * t, u, w₁, v, 1, 1, t, 1], 1),
  (11, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (12, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (13, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (14, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (15, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1)]

@[expose] def kill7 : List (ℕ × List ℕ × List MB × MB) := [
  (0, [0, 2, 1, 2, 0, 2, 0, 2, 0], [w₂ * w₁ * v * t, u, w₁, v, 1, 1, t, 1], 1),
  (1, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (2, [0, 2, 0, 2, 0, 2, 1, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (3, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (4, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (5, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (6, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (7, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (8, [0, 2, 1, 2, 0, 2, 0, 2, 0], [w₂ * w₁ * v * t, u, w₁, v, 1, 1, t, 1], 1),
  (9, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (10, [0, 2, 0, 2, 0, 2, 1, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (11, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (12, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (13, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (14, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1),
  (15, [0, 4, 1, 4, 0], [w₂, u, w₁, v, 1, 1, t, 1], 1)]

@[expose] def killOf : ℕ → List (ℕ × List ℕ × List MB × MB)
  | 0 => kill0
  | 1 => kill1
  | 2 => kill2
  | 3 => kill3
  | 4 => kill4
  | 5 => kill5
  | 6 => kill6
  | 7 => kill7
  | _ => []

@[expose] def goodIdx : List (ℕ × ℕ) :=
  [(0, 2), (0, 10), (1, 0), (1, 8), (2, 2), (2, 10), (3, 0), (3, 8)]

@[expose] def cQ (j : ℕ) : List MB := restrQ1 (r2Classes.getD j ([], 1)).1

theorem d3List_eq : d3List = d3L := by decide +kernel

theorem d3L_mem : ∀ f ∈ d3L, ∀ x ∈ f, inQ1 x = true := by decide +kernel

theorem d3L_order : ∀ f ∈ d3L, compQ1 f (compQ1 f f) = gensQ1 := by decide +kernel

theorem d3L_length : d3L.length = 16 := by decide +kernel

theorem cQ_mem : ∀ j < 8, ∀ x ∈ cQ j, inQ1 x = true := by decide +kernel

theorem goodIdx_lt : ∀ p ∈ goodIdx, p.1 < 4 := by decide +kernel

theorem kill_cover : ∀ j < 8, ∀ i < 16, (j, i) ∈ goodIdx ∨ ∃ e ∈ killOf j, e.1 = i := by
  decide +kernel

theorem kill0_ok :
    ∀ e ∈ kill0, KillOK (wordAct (d3L.getD e.1 []) (cQ 0) e.2.1) e.2.2.1 e.2.2.2 := by
  decide +kernel

theorem kill1_ok :
    ∀ e ∈ kill1, KillOK (wordAct (d3L.getD e.1 []) (cQ 1) e.2.1) e.2.2.1 e.2.2.2 := by
  decide +kernel

theorem kill2_ok :
    ∀ e ∈ kill2, KillOK (wordAct (d3L.getD e.1 []) (cQ 2) e.2.1) e.2.2.1 e.2.2.2 := by
  decide +kernel

theorem kill3_ok :
    ∀ e ∈ kill3, KillOK (wordAct (d3L.getD e.1 []) (cQ 3) e.2.1) e.2.2.1 e.2.2.2 := by
  decide +kernel

theorem kill4_ok :
    ∀ e ∈ kill4, KillOK (wordAct (d3L.getD e.1 []) (cQ 4) e.2.1) e.2.2.1 e.2.2.2 := by
  decide +kernel

theorem kill5_ok :
    ∀ e ∈ kill5, KillOK (wordAct (d3L.getD e.1 []) (cQ 5) e.2.1) e.2.2.1 e.2.2.2 := by
  decide +kernel

theorem kill6_ok :
    ∀ e ∈ kill6, KillOK (wordAct (d3L.getD e.1 []) (cQ 6) e.2.1) e.2.2.1 e.2.2.2 := by
  decide +kernel

theorem kill7_ok :
    ∀ e ∈ kill7, KillOK (wordAct (d3L.getD e.1 []) (cQ 7) e.2.1) e.2.2.1 e.2.2.2 := by
  decide +kernel

theorem applyMB_k (f : List MB) (hf : f.length = 8) : applyMB f k = f.getD 7 1 := by
  obtain ⟨-, -, -, -, -, -, -, h8⟩ := nfBits_gens
  match f, hf with
  | [a, b, c, d, e, f, g, h], _ => simp [applyMB, h8, nfProd]

theorem killOf_ok : ∀ j < 8, ∀ e ∈ killOf j,
    KillOK (wordAct (d3L.getD e.1 []) (cQ j) e.2.1) e.2.2.1 e.2.2.2 := by
  intro j hj
  interval_cases j
  exacts [kill0_ok, kill1_ok, kill2_ok, kill3_ok, kill4_ok, kill5_ok, kill6_ok, kill7_ok]

end MB

end Sec8

namespace KD8abB

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace BData

variable {B : BData S T₁}

theorem wordAct_mem {fd cQ : List MB} (hfd : ∀ x ∈ fd, MB.inQ1 x = true)
    (hcQ : ∀ x ∈ cQ, MB.inQ1 x = true) : ∀ w : List ℕ, ∀ x ∈ MB.wordAct fd cQ w, MB.inQ1 x = true
  | [] => fun x hx => MB.gensQ1_mem x hx
  | l :: _ => MB.compQ1_mem (letterAct_mem hfd hcQ l)

theorem good_of (R : B.R2Data) {δ : X} {f : List MB} (hf : f ∈ MB.d3List)
    (hδ : B.ActsQ1 δ f) : ∃ i, (R.j, i) ∈ MB.goodIdx ∧ MB.d3L.getD i [] = f := by
  rw [MB.d3List_eq] at hf
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hf
  have hget : MB.d3L.getD i [] = MB.d3L[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  rcases MB.kill_cover R.j R.hj i (MB.d3L_length ▸ hi) with hg | ⟨e, he, hei⟩
  · exact ⟨i, hg, hget⟩
  · exfalso
    have hfm := MB.d3L_mem _ hf
    have h3 := MB.d3L_order _ hf
    have hc : B.ActsQ1 R.c (MB.cQ R.j) := R.acts.actsQ1
    have hcQ := MB.cQ_mem R.j R.hj
    have hK := MB.killOf_ok R.j R.hj e he
    rw [hei, hget] at hK
    exact false_of_kill (actsQ1_wordElt hδ hfm h3 hc hcQ e.2.1)
      (wordAct_mem hfm hcQ e.2.1) hK

theorem c_conj_k (R : B.R2Data) : R.c * S.k * R.c⁻¹ = S.z * S.k := by
  obtain ⟨h7, hlen⟩ := MB.r2Classes_k R.j R.hj
  have h := R.acts MB.k
  rw [MB.applyMB_k _ hlen, h7, map_mul, B.ι_z, B.ι_k] at h
  exact h

end BData

end KD8abB

end CFSG.ComponentClassification.HSFLit
