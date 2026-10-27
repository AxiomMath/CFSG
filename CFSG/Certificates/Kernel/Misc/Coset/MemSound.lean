module

public import CFSG.Certificates.Kernel.Misc.Coset.MemDefs
import CFSG.Certificates.Kernel.Misc.Coset.MemProved

public section

namespace CFSG.KC.MiscCoset.Mem

open CFSG.Certificates

theorem memOK_sound {G : Type*} [Group G] (gen : ℕ → G) {rels : List (List (ℕ × Bool))}
    (hrels : ∀ r ∈ rels, KB.sword gen r = 1)
    {inv L eps nLab nT N RW RM nR nS nW nF : ℕ} {F D Wd Wd2 R S : ℕ → ℕ} {amap m : ℕ}
    {words : List (List (ℕ × Bool))} {walk cov : List ℕ}
    (h : KB.tableOk inv L eps nLab nT N RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk cov =
      true) (hm : m < 128) (htop : KB.topOk amap m = true) {u : List (ℕ × Bool)}
    (hu : ∀ l ∈ u, l.1 < m) {refs : List ℕ} (hw : memOK F nF (u.map codeN) refs = true) :
    KB.sword gen u ∈ KB.wordSub gen words :=
  memOK_sound_proved gen hrels h hm htop hu hw

end CFSG.KC.MiscCoset.Mem

end
