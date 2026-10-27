
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.HypOneBaseRu
public import Certificates.Certificate24370
public import Certificates.Certificate24371
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic

@[expose] public section

namespace CFSG.EvenSporadicStandard.TwoRu.HypOne

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Schreier
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 CFSG.Sporadic.RuSchreier
open CFSG.ComponentClassification.M12Cover CFSG.EvenSporadicStandard.HypOne
open CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Th (Rep)

theorem ruFourTest_iff {t : Array ℕ} {g : Equiv.Perm (Fin 4060)}
    (ht : CFSG.Monster.B.Co2.Rep 4060 t g) :
    ruFourTest t = true ↔ g ^ 4 = 1 ∧ g ^ 2 ≠ 1 := by
  have h1 : ∀ i : Fin 4060, t[(i : ℕ)]! = (g i : ℕ) := ht
  have h2 : ∀ i : Fin 4060, t[t[(i : ℕ)]!]! = ((g ^ 2) i : ℕ) := by
    intro i
    rw [h1 i, h1 (g i), pow_two]
    rfl
  have h4 : ∀ i : Fin 4060, t[t[t[t[(i : ℕ)]!]!]!]! = ((g ^ 4) i : ℕ) := by
    intro i
    rw [h2 i, h2 ((g ^ 2) i), show g ^ 4 = g ^ 2 * g ^ 2 by rw [← pow_add]]
    rfl
  have hall4 : (CFSG.Monster.B.Co2.Native.allLt 4060 fun i => t[t[t[t[i]!]!]!]! == i) = true ↔
      g ^ 4 = 1 := by
    rw [CFSG.Monster.B.Co2.allLt_iff]
    constructor
    · intro H
      ext i
      have := H i i.2
      rw [beq_iff_eq, h4 i] at this
      exact this
    · intro H i hi
      rw [beq_iff_eq, h4 ⟨i, hi⟩, H]
      rfl
  have hall2 : (CFSG.Monster.B.Co2.Native.allLt 4060 fun i => t[t[i]!]! == i) = true ↔
      g ^ 2 = 1 := by
    rw [CFSG.Monster.B.Co2.allLt_iff]
    constructor
    · intro H
      ext i
      have := H i i.2
      rw [beq_iff_eq, h2 i] at this
      exact this
    · intro H i hi
      rw [beq_iff_eq, h2 ⟨i, hi⟩, H]
      rfl
  rw [ruFourTest, Bool.and_eq_true, Bool.not_eq_true', hall4, Bool.eq_false_iff, ne_eq, hall2]

theorem getElem!_map_tblOfArr {A : Array (Array ℕ)} {l : ℕ} (hl : l < A.size) :
    (A.map tblOfArr)[l]! = tblOfArr A[l]! := by
  rw [getElem!_pos (A.map tblOfArr) l (by simpa using hl), getElem!_pos A l hl, Array.getElem_map]

theorem fourClassesLarge_ruC :
    FourClassesLarge ruC :=
  fourClassesLarge_ruC_of_base Certificates.certificate24370

theorem fourClassesLarge_ruL :
    FourClassesLarge ruL :=
  fourClassesLarge_ruL_of_base Certificates.certificate24371

end CFSG.EvenSporadicStandard.TwoRu.HypOne
