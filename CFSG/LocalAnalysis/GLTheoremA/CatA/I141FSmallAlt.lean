module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FSmallRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS07I67

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem i141f_autRank_alt5 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Type} [Group S] [Finite S]
    (h : catalogIs S (rsAlt 5)) {E : Subgroup (MulAut S)} (hE : IsElemAbelian p E)
    (h3 : p ^ 3 ≤ Nat.card E) : False := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | alternating m hm =>
    obtain rfl : m = 5 := hi
    exact no_alt5 hp hp2 e hE h3
  | _ => exact absurd hi (by simp [rsAlt])

theorem i141f_autRank_alt6 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Type} [Group S] [Finite S]
    (h : catalogIs S (rsAlt 6)) {E : Subgroup (MulAut S)} (hE : IsElemAbelian p E)
    (h3 : p ^ 3 ≤ Nat.card E) : False := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | alternating m hm =>
    obtain rfl : m = 6 := hi
    exact no_alt6 hp hp2 e hE h3
  | _ => exact absurd hi (by simp [rsAlt])

theorem i141f_autRank_alt8 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Type} [Group S] [Finite S]
    (h : catalogIs S (rsAlt 8)) {E : Subgroup (MulAut S)} (hE : IsElemAbelian p E)
    (h3 : p ^ 3 ≤ Nat.card E) : False := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | alternating m hm =>
    obtain rfl : m = 8 := hi
    exact no_alt8 hp hp2 e hE h3
  | _ => exact absurd hi (by simp [rsAlt])

end CFSG.LocalAnalysis.GLTheoremA.I141F
