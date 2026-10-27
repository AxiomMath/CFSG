module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs123

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172B

open CFSG.Yardstones.Md0ec50421ce4

theorem not_catalogIs_isOmPA_of_lt_three (S : Type) [Group S] {n : ℕ} (q : ℕ) (hn : n < 3) :
    ¬ catalogIs S (isOmPA n q) := by
  rintro ⟨i, hi, -⟩
  rcases hi with h1 | ⟨h3, -⟩
  · cases i with
    | cyclic p hp => simp [isOmP, onLie] at h1
    | alternating m hm => simp [isOmP, onLie] at h1
    | sporadic s => simp [isOmP, onLie] at h1
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | D r qq =>
        have h1' : r = n ∧ qq.card = q := h1
        obtain ⟨hr, -⟩ := h1'
        have hrange := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
        simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hrange
        omega
      | _ => simp [isOmP, onLie] at h1
  · omega

theorem not_catalogIs_isUnA_two_two (S : Type) [Group S] : ¬ catalogIs S (isUnA 2 2) := by
  rintro ⟨i, hi, -⟩
  rcases hi with h1 | ⟨-, hi⟩
  · cases i with
    | cyclic p hp => simp [onLie] at h1
    | alternating m hm => simp [onLie] at h1
    | sporadic s => simp [onLie] at h1
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | twistedA r qq =>
        have h1' : r + 1 = 2 ∧ qq.card = 2 := h1
        obtain ⟨hr, -⟩ := h1'
        have hrange := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
        simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hrange
        obtain ⟨hr2, -⟩ := hrange
        omega
      | _ => simp [onLie, isLnEps] at h1
  · rcases hi with h2 | ⟨-, hq, -⟩ | ⟨-, h9, -⟩ | ⟨h3, -⟩ | ⟨h4, -⟩
    · cases i with
      | cyclic p hp => simp [onLie] at h2
      | alternating m hm => simp [onLie] at h2
      | sporadic s => simp [onLie] at h2
      | lie idx =>
        obtain ⟨d, hv⟩ := idx
        cases d with
        | A r qq =>
          have h2' : r + 1 = 2 ∧ qq.card = 2 := h2
          obtain ⟨hr, hq⟩ := h2'
          have hrange := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
          simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hrange
          have h4 : 4 ≤ qq.card := hrange.2 (by omega)
          omega
        | _ => simp [onLie, isLnEps] at h2
    · rcases hq with hq | hq <;> omega
    · omega
    · omega
    · omega

theorem not_catalogIs_isUnA_one (S : Type) [Group S] (q : ℕ) : ¬ catalogIs S (isUnA 1 q) := by
  rintro ⟨i, hi, -⟩
  rcases hi with h1 | ⟨h2, -⟩
  · cases i with
    | cyclic p hp => simp [onLie] at h1
    | alternating m hm => simp [onLie] at h1
    | sporadic s => simp [onLie] at h1
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | twistedA r qq =>
        have h1' : r + 1 = 1 ∧ qq.card = q := h1
        obtain ⟨hr, -⟩ := h1'
        have hrange := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
        simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hrange
        obtain ⟨hr2, -⟩ := hrange
        omega
      | _ => simp [onLie, isLnEps] at h1
  · omega

end CFSG.LocalAnalysis.GLTheoremA.S172B

end
