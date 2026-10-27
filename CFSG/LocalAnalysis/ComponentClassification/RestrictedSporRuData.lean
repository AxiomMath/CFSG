module

public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Schreier.RuArrays
public import CFSG.Sporadic.Th.TableSpec

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.RuSchreier

@[expose] def arrTable (t : Array ℕ) : Table := t.map UInt32.ofNat

theorem rep_arrTable {n : ℕ} (hn : n < 2 ^ 32) {t : Array ℕ} {g : Equiv.Perm (Fin n)}
    (h : CFSG.Monster.B.Co2.Rep n t g) : Rep n (arrTable t) g := by
  intro i hi
  rw [idx_of_lt _ hi]
  have hti := h ⟨i, hi⟩
  have hlt : t[i]! < 2 ^ 32 := by
    rw [hti]
    exact (g ⟨i, hi⟩).isLt.trans hn
  have hget : (arrTable t)[i]! = UInt32.ofNat t[i]! := by
    by_cases hs : i < t.size
    · rw [getElem!_pos (arrTable t) i (by simpa [arrTable] using hs), getElem!_pos t i hs]
      simp [arrTable]
    · rw [getElem!_neg (arrTable t) i (by simpa [arrTable] using hs), getElem!_neg t i hs]
      rfl
  rw [ap, hget, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlt, hti]
  rfl

@[expose] def ruCTab : Array Table := #[arrTable ruC0A, arrTable ruC1A]

@[expose] def ruCInvTab : Array Table := #[arrTable (ruInv ruC0A), arrTable (ruInv ruC1A)]

@[expose] def ruLetterTab (z : ℤ) : Table := if z = 1 then arrTable ruC0A else arrTable ruC1A

@[expose] def ruQWord : List ℤ :=
  [1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1,
    1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2]

@[expose] def ruYWord : List ℤ :=
  [2, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1,
    2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1]

@[expose] def ruQTab : Table := powT 4060 60 (wordT 4060 ruLetterTab ruQWord)

@[expose] def ruYTab : Table := powT 4060 2 (wordT 4060 ruLetterTab ruYWord)

end CFSG.ComponentClassification.RestrictedStd.Spor
