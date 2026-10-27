module

public import CFSG.ClassicalInvolution.Q3.AE.E29
public import CFSG.ClassicalInvolution.Q3.AE.Twins

public section

namespace CFSG.ClassicalInvolution.Q3.AE

variable {n : ℕ}

theorem eq_of_memBar_eq' (hn : 5 ≤ n) {α β : Finset (Fin n)} {h : α.card = 4} {h' : β.card = 4}
    {b c : Bool} (he : memBar α h b = memBar β h' c) : α = β := by
  have hmem : zBar α h ∈ memBar β h' c := he ▸ zBar_mem_memBar α h b
  rcases eq_of_mem_memBar_mul_self hn hmem (zBar_mul_self α h) with h1 | h1
  · exact absurd h1 (zBar_ne_one hn α h)
  · by_contra hne
    have hd : Disjoint α β :=
      disjoint_of_zBar_comm (h := h) (h' := h') (c := c) hne fun y hy => by
        rw [h1]
        exact zBar_comm_memBar β h' c y hy
    exact memBar_ne_of_disjoint hd b c he

end CFSG.ClassicalInvolution.Q3.AE
