module

public import CFSG.FeitThompson.OddOrder.RankTwoKernelSmallerComplementPrimes

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

theorem pow_eq_one_of_iSup_eq_top {G : Type*} [Group G] [IsMulCommutative G] {p : ℕ}
    {ι : Type*} {E : ι → Subgroup G} (hsup : ⨆ i, E i = ⊤) (hE : ∀ i, Nat.card (E i) = p)
    (x : G) : x ^ p = 1 := by
  have _hab : IsMulCommutative ↥(⊤ : Subgroup G) :=
    ⟨⟨fun a b => Subtype.ext (IsMulCommutative.is_comm.comm (a : G) b)⟩⟩
  have hle : (⊤ : Subgroup G) ≤ powTorsion (⊤ : Subgroup G) p := by
    refine le_trans (le_of_eq hsup.symm) (iSup_le fun i => le_powTorsion le_top fun y hy => ?_)
    have h2 := pow_card_eq_one' (G := ↥(E i)) (x := (⟨y, hy⟩ : ↥(E i)))
    rw [hE i] at h2
    have h3 : ((⟨y, hy⟩ : ↥(E i)) : G) ^ p = ((1 : ↥(E i)) : G) := congrArg Subtype.val h2
    simpa using h3
  exact pow_eq_one_of_mem_powTorsion (hle (Subgroup.mem_top x))

end CFSG.FeitThompson
