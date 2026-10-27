module

public import Certificates.Data.Kernel.O8.SBCenF
public import CFSG.Certificates.Kernel.O8.SBCenSound

public section

namespace CFSG.KC.SBCenF

open CFSG.KC.Enum CFSG.KC.SB CFSG.KC.SBCen

theorem rowFN_eq (mul : ℕ → ℕ → ℕ) (NR : ℕ → ℕ) (W L : ℕ) :
    rowFN mul NR W L = rowF mul (nfEG NR) (nfAG NR) W L := by
  funext x
  unfold rowFN rowF nfEG nfAG
  cases Nat.blt x 65536
  · rfl
  · simp only [cen_strictN]

end CFSG.KC.SBCenF

end
