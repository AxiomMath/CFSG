module

public import Certificates.Data.Kernel.LyDce.Conj
public import CFSG.Sporadic.Recognition.LyonsFinalDist2

public section

namespace CFSG.KC.LyDce

open CFSG.KC.LyReplay CFSG.Sporadic.Recognition.LyonsSims.LyFinal

variable {G : Type*} [Group G] {g : Fin 6 → G}

theorem conjOK_sound (hinv : ∀ i : Fin 6, i.val ≠ 1 → g i * g i = 1)
    {RL : List (List (Fin 6 × Bool))} {X : List Nat} {Gs : List (List Nat)}
    (h : conjOK RL X Gs = true) (hRL : ∀ r ∈ RL, FreeGroup.lift g (FreeGroup.mk r) = 1) :
    ∀ s ∈ Gs, ∃ z, isBWord z = true ∧
      FreeGroup.lift g (FreeGroup.mk (wordOf X)) * FreeGroup.lift g (FreeGroup.mk (wordOf s)) *
          (FreeGroup.lift g (FreeGroup.mk (wordOf X)))⁻¹ =
        (FreeGroup.lift g (FreeGroup.mk z))⁻¹ := by
  intro s hs
  obtain ⟨r, hr, hrs⟩ := List.any_eq_true.1 (List.all_eq_true.1 h s hs)
  rw [Bool.and_eq_true, beq_iff_eq] at hrs
  obtain ⟨htake, hz⟩ := hrs
  refine ⟨_, hz, ?_⟩
  have e : r = conjW X s ++ r.drop (conjW X s).length := by
    conv_lhs => rw [← List.take_append_drop (conjW X s).length r]
    rw [htake]
  have h1 := hRL r hr
  rw [e, lift_mk_append, conjW, lift_mk_append, lift_mk_append, lift_derivInv hinv] at h1
  exact eq_inv_of_mul_eq_one_left h1

end CFSG.KC.LyDce

end
