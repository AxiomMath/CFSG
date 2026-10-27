module

public import Certificates.Certificate919008
public import Certificates.Data.Foote82InvolAutA6

public section

namespace CFSG.CGT.Foote82.InvolA6

theorem anyLt_iff {n : ℕ} {p : ℕ → Bool} : anyLt n p = true ↔ ∃ i < n, p i = true := by
  unfold anyLt
  rw [Nat.any_eq_finRange_any, List.any_eq_true]
  constructor
  · rintro ⟨⟨i, hi⟩, -, h⟩
    exact ⟨i, hi, h⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨⟨i, hi⟩, List.mem_finRange _, h⟩

end CFSG.CGT.Foote82.InvolA6

namespace CFSG.CGT.Foote82

theorem involAutA6Cases_holds : InvolAutA6Cases :=
  Certificates.certificate919008

end CFSG.CGT.Foote82
