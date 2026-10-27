module

public import CFSG.ClassicalInvolution.Q3.TL4D1ML32B
public import CFSG.ClassicalInvolution.Q3.TL4D1MBaseB

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Q3.AE Matrix

theorem l32_normal {Q : Subgroup (Equiv.Perm (Fin 7))} (hQ : Q ≤ l32)
    (hQn : ∀ g ∈ l32, ∀ x ∈ Q, g * x * g⁻¹ ∈ Q) : Q = ⊥ ∨ Q = l32 := by
  have : (Q.subgroupOf l32).Normal :=
    ⟨fun x hx g => Subgroup.mem_subgroupOf.mpr (hQn g g.2 x (Subgroup.mem_subgroupOf.mp hx))⟩
  have hs := isSimpleGroup_l32
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Q.subgroupOf l32) with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hQ hx⟩ : ↥l32) ∈ Q.subgroupOf l32 := Subgroup.mem_subgroupOf.mpr hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  · right
    refine le_antisymm hQ fun x hx => ?_
    have : (⟨x, hx⟩ : ↥l32) ∈ Q.subgroupOf l32 := by rw [h]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this

@[expose] def det3 (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : ZMod 2 :=
  A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2 +
    A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0

theorem det_eq_det3 (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : A.det = det3 A := det_fin_three A

@[expose] def l32PairWit : Fin 7 → Fin 7 → Matrix (Fin 3) (Fin 3) (ZMod 2) × Fin 7
  | 0, 1 => (!![0, 1, 0; 0, 0, 1; 1, 0, 0], 5)
  | 0, 2 => (!![0, 0, 1; 0, 1, 0; 1, 0, 0], 1)
  | 0, 3 => (!![0, 1, 0; 0, 0, 1; 1, 1, 1], 5)
  | 0, 4 => (!![0, 0, 1; 0, 1, 1; 1, 0, 0], 1)
  | 0, 5 => (!![0, 0, 1; 0, 1, 1; 1, 0, 1], 1)
  | 0, 6 => (!![0, 0, 1; 0, 1, 0; 1, 0, 1], 1)
  | 1, 0 => (!![0, 0, 1; 1, 0, 0; 0, 1, 0], 5)
  | 1, 2 => (!![0, 1, 0; 0, 0, 1; 1, 0, 0], 5)
  | 1, 3 => (!![0, 0, 1; 0, 1, 0; 1, 1, 0], 6)
  | 1, 4 => (!![0, 1, 1; 0, 1, 0; 1, 0, 0], 6)
  | 1, 5 => (!![0, 1, 1; 0, 0, 1; 1, 0, 1], 4)
  | 1, 6 => (!![0, 1, 0; 0, 0, 1; 1, 1, 1], 5)
  | 2, 0 => (!![0, 0, 1; 0, 1, 0; 1, 0, 0], 1)
  | 2, 1 => (!![0, 0, 1; 1, 0, 0; 0, 1, 0], 5)
  | 2, 3 => (!![0, 0, 1; 1, 1, 0; 1, 0, 0], 1)
  | 2, 4 => (!![0, 1, 1; 1, 0, 0; 0, 0, 1], 3)
  | 2, 5 => (!![0, 1, 1; 1, 0, 1; 0, 0, 1], 3)
  | 2, 6 => (!![0, 1, 0; 1, 0, 1; 0, 0, 1], 3)
  | 3, 0 => (!![1, 0, 0; 1, 0, 1; 0, 1, 0], 4)
  | 3, 1 => (!![0, 1, 0; 1, 1, 0; 0, 0, 1], 2)
  | 3, 2 => (!![0, 0, 1; 0, 1, 1; 1, 0, 0], 1)
  | 3, 4 => (!![0, 0, 1; 0, 1, 0; 1, 0, 0], 1)
  | 3, 5 => (!![0, 0, 1; 0, 1, 0; 1, 0, 1], 1)
  | 3, 6 => (!![0, 0, 1; 0, 1, 1; 1, 0, 1], 1)
  | 4, 0 => (!![0, 0, 1; 1, 0, 0; 1, 1, 1], 5)
  | 4, 1 => (!![0, 0, 1; 0, 1, 0; 1, 1, 0], 6)
  | 4, 2 => (!![0, 1, 0; 0, 0, 1; 1, 1, 1], 5)
  | 4, 3 => (!![0, 0, 1; 0, 1, 0; 1, 0, 0], 1)
  | 4, 5 => (!![0, 1, 1; 0, 1, 0; 1, 0, 0], 6)
  | 4, 6 => (!![0, 1, 0; 0, 0, 1; 1, 0, 0], 5)
  | 5, 0 => (!![1, 0, 0; 1, 0, 1; 1, 1, 0], 3)
  | 5, 1 => (!![0, 1, 0; 0, 1, 1; 1, 1, 0], 3)
  | 5, 2 => (!![0, 0, 1; 0, 1, 1; 1, 0, 1], 1)
  | 5, 3 => (!![0, 1, 0; 1, 0, 0; 0, 1, 1], 2)
  | 5, 4 => (!![0, 0, 1; 0, 1, 0; 1, 0, 1], 1)
  | 5, 6 => (!![0, 0, 1; 0, 1, 1; 1, 0, 0], 1)
  | 6, 0 => (!![1, 0, 0; 0, 0, 1; 1, 1, 0], 4)
  | 6, 1 => (!![0, 1, 0; 0, 0, 1; 1, 1, 1], 5)
  | 6, 2 => (!![0, 0, 1; 0, 1, 0; 1, 0, 1], 1)
  | 6, 3 => (!![0, 1, 0; 0, 0, 1; 1, 0, 0], 5)
  | 6, 4 => (!![0, 0, 1; 0, 1, 1; 1, 0, 1], 1)
  | 6, 5 => (!![0, 0, 1; 0, 1, 1; 1, 0, 0], 1)
  | _, _ => (1, 0)

theorem l32PairWit_spec : ∀ j k : Fin 7, j ≠ k → det3 (l32PairWit j k).1 = 1 ∧
    (l32PairWit j k).2 ≠ k ∧
    fanoIdx ((l32PairWit j k).1 *ᵥ fanoVec (l32PairWit j k).2) = (l32PairWit j k).2 ∧
    fanoIdx ((l32PairWit j k).1 *ᵥ fanoVec k) = j := by
  decide

theorem l32_pairTrans : PairTrans l32 := by
  intro j k hjk
  obtain ⟨hdet, hik, hi, hk⟩ := l32PairWit_spec j k hjk
  let A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    ⟨(l32PairWit j k).1, by rw [det_eq_det3]; exact hdet⟩
  exact ⟨lpermHom A, lpermHom_mem_l32 A, (l32PairWit j k).2, hik, hi, hk⟩

theorem sl3Two_facts : det3 !![0, 1, 0; 0, 0, 1; 1, 0, 0] = 1 ∧
    det3 !![0, 0, 1; 0, 1, 0; 1, 0, 0] = 1 ∧
    (!![0, 1, 0; 0, 0, 1; 1, 0, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ 3 = 1 ∧
    (!![0, 1, 0; 0, 0, 1; 1, 0, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠ 1 ∧
    (!![0, 1, 0; 0, 0, 1; 1, 0, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        !![0, 0, 1; 0, 1, 0; 1, 0, 0] ≠
      !![0, 0, 1; 0, 1, 0; 1, 0, 0] * !![0, 1, 0; 0, 0, 1; 1, 0, 0] := by
  decide

end CFSG.ClassicalInvolution.Q3.TL4
