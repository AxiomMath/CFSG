module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5TtRowsAll

public section

set_option maxRecDepth 100000

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.TtK

theorem clsAll0 : (rowsT0.all fun r => decide (r.getD 2 0 < 51)) = true := by decide +kernel
theorem clsAll1 : (rowsT1.all fun r => decide (r.getD 2 0 < 51)) = true := by decide +kernel
theorem clsAll2 : (rowsT2.all fun r => decide (r.getD 2 0 < 51)) = true := by decide +kernel
theorem clsAll3 : (rowsT3.all fun r => decide (r.getD 2 0 < 51)) = true := by decide +kernel
theorem clsAll4 : (rowsT4.all fun r => decide (r.getD 2 0 < 51)) = true := by decide +kernel
theorem clsAll5 : (rowsT5.all fun r => decide (r.getD 2 0 < 51)) = true := by decide +kernel
theorem clsAll6 : (rowsT6.all fun r => decide (r.getD 2 0 < 51)) = true := by decide +kernel
theorem clsAll7 : (rowsT7.all fun r => decide (r.getD 2 0 < 51)) = true := by decide +kernel
theorem clsAll8 : (rowsT8.all fun r => decide (r.getD 2 0 < 51)) = true := by decide +kernel
theorem clsAll9 : (rowsT9.all fun r => decide (r.getD 2 0 < 51)) = true := by decide +kernel
theorem clsAll10 : (rowsT10.all fun r => decide (r.getD 2 0 < 51)) = true := by decide +kernel
theorem clsAll11 : (rowsT11.all fun r => decide (r.getD 2 0 < 51)) = true := by decide +kernel

theorem cls_lt : ∀ r ∈ rowsT, r.getD 2 0 < 51 := by
  intro r hr
  have h : ∀ (l : List (List ℕ)), (l.all fun r => decide (r.getD 2 0 < 51)) = true → r ∈ l →
      r.getD 2 0 < 51 := fun l hl hr => by
    simpa using List.all_eq_true.1 hl r hr
  simp only [rowsT, List.mem_append, or_assoc] at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr
  · exact h _ clsAll0 hr
  · exact h _ clsAll1 hr
  · exact h _ clsAll2 hr
  · exact h _ clsAll3 hr
  · exact h _ clsAll4 hr
  · exact h _ clsAll5 hr
  · exact h _ clsAll6 hr
  · exact h _ clsAll7 hr
  · exact h _ clsAll8 hr
  · exact h _ clsAll9 hr
  · exact h _ clsAll10 hr
  · exact h _ clsAll11 hr

theorem W1d_letters : ∀ k < 51, ∀ f ∈ (W1d.getD k ([], 0)).1, ∀ l ∈ f.1, l < 6 := by decide +kernel

theorem W2d_letters : ∀ k < 51, ∀ f ∈ (W2d.getD k ([], 0)).1, ∀ l ∈ f.1, l < 6 := by decide +kernel

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.TtK
