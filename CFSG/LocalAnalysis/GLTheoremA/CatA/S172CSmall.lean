module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs123

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172C

open CFSG.Yardstones.Md0ec50421ce4

theorem not_catalogIs_isUnA_zero (S : Type) [Group S] (q : ℕ) : ¬ catalogIs S (isUnA 0 q) := by
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
        have h1' : r + 1 = 0 ∧ qq.card = q := h1
        obtain ⟨hr, -⟩ := h1'
        have hrange := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
        simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hrange
        obtain ⟨hr2, -⟩ := hrange
        omega
      | _ => simp [onLie, isLnEps] at h1
  · omega

end CFSG.LocalAnalysis.GLTheoremA.S172C

end
