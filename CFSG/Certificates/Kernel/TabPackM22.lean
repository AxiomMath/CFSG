module

public import CFSG.Certificates.Kernel.TabPackSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.TabCheck

public section

namespace CFSG.KTabPack.M22

open CFSG.EvenSporadicStandard.M22Std.TabCheck

theorem span_eq (gs : List (List Nat)) : span gs = spanT 22 gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => rw [span, spanT, ← ih]; rfl

theorem sylowOK_eq (gs : List (List Nat)) : sylowOK gs = sylowT 22 gs := by
  rw [sylowOK, sylowT, span_eq]; rfl

theorem elemAbOK_eq (L : List (List Nat)) (As : List (List (List Nat))) : elemAbOK L As = elemAbT 22 L As := rfl

theorem gens_W : ∀ g ∈ gensTab, W 22 g := by
  unfold W; decide +kernel

theorem elemTabs_W : ∀ A ∈ [elemTabs 0, elemTabs 1], ∀ y ∈ A, W 22 y := by
  unfold W; decide +kernel

theorem span_W : ∀ x ∈ span gensTab, W 22 x := by
  rw [span_eq]; exact spanT_W (by decide) gens_W

end CFSG.KTabPack.M22
