module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.LieType.Universal.SpecialLinear

public section

namespace CFSG.Open.StatedAPI

open CFSG.Assembly.LowTwoRank

theorem isQuasisimple_statedSL_of_two_le {m : ℕ} (hm : 2 ≤ m) (K : Type) [Field K] :
    CFSG.IsQuasisimple ↥(StatedSL (m + 1) K) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (specialLinearGroupEquivStatedSL (m + 1) K)
    (CFSG.LieType.Universal.SpecialLinear.isQuasisimple m K hm)

theorem isQuasisimple_statedSU_three_of_prime {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = p ^ 2) : CFSG.IsQuasisimple ↥(StatedSU 3 p K) := by
  have : Fact p.Prime := ⟨hp⟩
  have h := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := K) (p := p)
    (f := 1) (n := 3) (by simpa using hK) le_rfl (by intro h; simp at h; omega)
  have h1 := h.1
  rw [pow_one] at h1
  exact h1

end CFSG.Open.StatedAPI
