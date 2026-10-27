module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cE16

public section

namespace CFSG.ComponentClassification.HSFLit.KD8c

@[expose] def d6 : Fin 12 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![0, 4, 5, 3, 1, 2, 6, 7], ![1, 0, 4, 5, 2, 3, 7, 6],
    ![1, 2, 3, 5, 0, 4, 7, 6], ![2, 1, 0, 4, 3, 5, 6, 7], ![2, 3, 5, 4, 1, 0, 6, 7],
    ![3, 2, 1, 0, 5, 4, 7, 6], ![3, 5, 4, 0, 2, 1, 7, 6], ![4, 0, 1, 2, 5, 3, 7, 6],
    ![4, 5, 3, 2, 0, 1, 7, 6], ![5, 3, 2, 1, 4, 0, 6, 7], ![5, 4, 0, 1, 3, 2, 6, 7]]

theorem d6_aux : ∀ a b c d : Fin 8, ((d = 6 ∨ d = 7) ∧ interCard a b = 8 ∧ interCard a c = 8 ∧
    interCard a d = 8 ∧ interCard b c = 4 ∧ interCard b d = 4 ∧ interCard c d = 4) →
    ∃ n : Fin 12, d6 n 0 = a ∧ d6 n 1 = b ∧ d6 n 4 = c ∧ d6 n 6 = d := by
  decide +kernel

theorem d6_uniq : ∀ n : Fin 12, ∀ i x : Fin 8, interCard x (d6 n 0) = interCard i 0 →
    interCard x (d6 n 1) = interCard i 1 → interCard x (d6 n 4) = interCard i 4 →
    interCard x (d6 n 6) = interCard i 6 → x = d6 n i := by
  decide +kernel

theorem d6_cases {p : Fin 8 → Fin 8} (hp : ∀ i j, interCard (p i) (p j) = interCard i j)
    (h6 : p 6 = 6 ∨ p 6 = 7) : ∃ n : Fin 12, ∀ i, p i = d6 n i := by
  obtain ⟨n, h0, h1, h4, h6'⟩ := d6_aux (p 0) (p 1) (p 4) (p 6) ⟨h6,
    (hp 0 1).trans (by decide), (hp 0 4).trans (by decide), (hp 0 6).trans (by decide),
    (hp 1 4).trans (by decide), (hp 1 6).trans (by decide), (hp 4 6).trans (by decide)⟩
  refine ⟨n, fun i => d6_uniq n i (p i) ?_ ?_ ?_ ?_⟩
  · rw [h0, hp]
  · rw [h1, hp]
  · rw [h4, hp]
  · rw [h6', hp]

@[expose] def wd (l : Fin 8 → Fin 8) : Fin 4 → Fin 8 → Fin 8
  | 0 => l
  | 1 => fun i => l (l i)
  | 2 => fun i => l (sig21 i)
  | _ => fun i => l (sig21 (l (sig21 i)))

theorem d6_three : ∀ n : Fin 12, d6 n 0 = 0 ∨ d6 n 0 = 3 ∨
    ∃ w : Fin 4, ∃ a : Fin 8, wd (d6 n) w a ≠ a ∧
      wd (d6 n) w (wd (d6 n) w (wd (d6 n) w a)) = a := by
  decide +kernel

theorem d6_antip : ∀ n : Fin 12, d6 n 0 = 3 →
    (∀ i, d6 n i = antip i) ∨ ∀ i, d6 n i = sig21 (antip i) := by
  decide +kernel

end CFSG.ComponentClassification.HSFLit.KD8c
