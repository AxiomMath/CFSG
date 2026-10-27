module

public import CFSG.LieType.Ree.SuzukiOvoidAction
public import CFSG.LieType.Ree.SuzukiPerfect
public import CFSG.LieType.Simplicity.Primitive

public section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.LieType.Simplicity

variable {a : ℕ} {K : Type} [Field K]

theorem suzukiWElt_ne_one : suzukiWElt a K ≠ 1 := by
  intro h
  have h' := congrArg (fun g : suzukiGroup a K =>
    ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0) h
  simp [coe_suzukiWElt, suzukiW] at h'

theorem suzuki_simple
    (ha : 1 ≤ a) [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Finite (suzukiGroup a K) ∧ Nontrivial (suzukiGroup a K) ∧
      IsSimpleGroup (suzukiGroup a K) := by
  have hnt : Nontrivial (suzukiGroup a K) := ⟨⟨_, _, suzukiWElt_ne_one (a := a) (K := K)⟩⟩
  have : FaithfulSMul (suzukiGroup a K) (suzukiOmegaSub hK) := (suzuki_ovoid_faithful ha hK).2
  have : MulAction.IsPreprimitive (suzukiGroup a K) (suzukiOmegaSub hK) :=
    (suzuki_ovoid_double_transitivity hK).2.2.2.2
  have hstab := (suzuki_ovoid_stabilizer hK).2
  have hsolv : Group.IsSolvable (MulAction.stabilizer (suzukiGroup a K)
      (⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega a K⟩ : suzukiOmegaSub hK)) := by
    rw [hstab]
    exact (suzuki_borel_solvable hK).1
  exact ⟨inferInstance, hnt, isSimpleGroup_of_isPreprimitive_of_isSolvable_stabilizer
    (suzuki_perfect ha hK).2 _ hsolv⟩

end CFSG.LieType.Ree
