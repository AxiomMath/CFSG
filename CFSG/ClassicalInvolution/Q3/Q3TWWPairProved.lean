module

public import CFSG.ClassicalInvolution.Q3.Q3TWCollCert
public import CFSG.ClassicalInvolution.Q3.Q3TWWOddMapPair

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

theorem weakCT3OddMapPair_proved :
    ∀ N : ℕ, 5 ≤ N → WeakCT3OddMapPair N :=
  fun _ hN => weakCT3OddMapPair_of_collapse b3Collapse_proved (by omega)

end CFSG.ClassicalInvolution.Q3.Q3TW
