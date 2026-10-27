module

public import CFSG.GH74.GLS.Bg.TwoGroups.A44Phi
public import CFSG.GH74.GLS.Bg.TwoGroups.A44Data

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace A44

@[expose] def A'list : List M4 :=
  [dd, M4.mul dd iota, ⟨1, 0, 2, 1⟩, ⟨1, 2, 0, 1⟩, ⟨3, 2, 2, 3⟩]

theorem A'_isA0 : ∀ x ∈ A'list, x.IsA0 := by decide +kernel

theorem A'_cases : ∀ x ∈ A'list, x = dd ∨ x = M4.mul dd iota ∨
    ∃ vy : ZMod 4 × ZMod 4, vy ≠ 0 ∧ vy + vy = 0 ∧ x = M4.phiOf vy := by decide +kernel

theorem phiOf_mem_A' : ∀ vy : ZMod 4 × ZMod 4, vy ≠ 0 → vy + vy = 0 → M4.phiOf vy ∈ A'list := by
  decide +kernel

@[expose] def InvOnlyZ (x : M4) : Prop := ∀ w : ZMod 4 × ZMod 4, x.act w = -w → w + w = 0

instance (x : M4) : Decidable (InvOnlyZ x) := by unfold InvOnlyZ; infer_instance

theorem A'_char : ∀ x : M4, x.IsInv → x.IsA0 → x ≠ M4.one → (x ∈ A'list ↔ InvOnlyZ x) := by
  decide +kernel

theorem dd_iota_iota : M4.mul (M4.mul dd iota) iota = dd := by decide +kernel
end A44

end CFSG.GH74.GLS.Bg.TwoGroups
