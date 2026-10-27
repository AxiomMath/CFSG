module

public import CFSG.GH74.GLS.Bg.TwoGroups.A44Model

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace A44

namespace M4

theorem act_zero (x : M4) : x.act 0 = 0 := by
  simp [act]

theorem act_neg (x : M4) (v : ZMod 4 × ZMod 4) : x.act (-v) = -x.act v := by
  simp only [act, Prod.fst_neg, Prod.snd_neg]
  refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_neg, Prod.snd_neg] <;> ring

@[expose] def IsPhiM (x : M4) (vy : ZMod 4 × ZMod 4) : Prop :=
  (∀ u : ZMod 4 × ZMod 4, (∃ w : ZMod 4 × ZMod 4, u = x.act w - w) ↔ (u = 0 ∨ u = vy)) ∧
    ∀ v : ZMod 4 × ZMod 4, x.act v = v ↔ (v + v = 0 ∨ v + v = vy)

instance (x : M4) (vy : ZMod 4 × ZMod 4) : Decidable (IsPhiM x vy) := by
  unfold IsPhiM; infer_instance

@[expose] def phiOf (vy : ZMod 4 × ZMod 4) : M4 :=
  if vy = (0, 2) then ⟨1, 0, 2, 1⟩ else if vy = (2, 0) then ⟨1, 2, 0, 1⟩ else ⟨3, 2, 2, 3⟩

theorem phiOf_spec : ∀ vy : ZMod 4 × ZMod 4, vy ≠ 0 → vy + vy = 0 →
    (phiOf vy).IsInv ∧ IsPhiM (phiOf vy) vy := by decide +kernel

theorem phiOf_unique : ∀ vy : ZMod 4 × ZMod 4, vy ≠ 0 → vy + vy = 0 →
    ∀ x : M4, x.IsInv → IsPhiM x vy → x = phiOf vy := by decide +kernel

end M4

end A44

end CFSG.GH74.GLS.Bg.TwoGroups
