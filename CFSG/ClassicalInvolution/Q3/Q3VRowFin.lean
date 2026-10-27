module

public import CFSG.ClassicalInvolution.Q3.Q3VRow
public import CFSG.ClassicalInvolution.Q3.Q3VCtMainFrame

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V

theorem weakCT3SpHyp_of_collapse (hC : Q3Z.V6Collapse) {m : ℕ} (hm : 2 ≤ m) : WeakCT3SpHyp m := by
  refine weakCT3SpHyp_of_rankOne m ?_
  intro X _ U hcomm hpair hsp
  obtain ⟨Ψ, hker, -, -, -, hblk⟩ :=
    weakCT3_symplectic_subgroup hC (n := m + 1) (by omega) U hcomm hpair hsp
  exact ⟨Ψ, hker, hblk⟩

end CFSG.ClassicalInvolution.Q3.Q3V
