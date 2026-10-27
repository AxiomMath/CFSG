module

public import Certificates.Data.FzJ36

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzJ36

@[expose] def fz59e_baseGens : List Model :=
  [⟨(QuaternionGroup.a 1, 1, 1), 1⟩, ⟨(QuaternionGroup.xa 0, 1, 1), 1⟩,
    ⟨(1, QuaternionGroup.a 1, 1), 1⟩, ⟨(1, QuaternionGroup.xa 0, 1), 1⟩,
    ⟨(1, 1, QuaternionGroup.a 1), 1⟩, ⟨(1, 1, QuaternionGroup.xa 0), 1⟩]

private theorem fz59e_sq_comm_all : ∀ m : Model, KEq (m * m * (m * m)) 1 →
    fz59e_baseGens.all (fun g => decide (KEq (g * (m * m)) ((m * m) * g))) = true := by
  decide +kernel

theorem fz59e_sq_comm (m : Model) (hm : KEq (m * m * (m * m)) 1) :
    ∀ g ∈ fz59e_baseGens, KEq (g * (m * m)) ((m * m) * g) := fun g hg =>
  of_decide_eq_true (List.all_eq_true.mp (fz59e_sq_comm_all m hm) g hg)

theorem fz59e_base_of_comm (m : Model)
    (h₁ : KEq (m * ⟨(QuaternionGroup.a 2, 1, 1), 1⟩) (⟨(QuaternionGroup.a 2, 1, 1), 1⟩ * m))
    (h₂ : KEq (m * ⟨(1, QuaternionGroup.a 2, 1), 1⟩) (⟨(1, QuaternionGroup.a 2, 1), 1⟩ * m)) :
    m.right = 1 := by
  revert m
  decide +kernel

end CFSG.OddStandard.SmallF3.FritzII
