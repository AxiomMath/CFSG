module

public import CFSG.Certificates.Kernel.BabyMonster.TBind.Text0
public import CFSG.Certificates.Kernel.BabyMonster.TBind.Text1
public import CFSG.Certificates.Kernel.BabyMonster.TBind.Text2
public import CFSG.Certificates.Kernel.BabyMonster.TBind.Text3

public section

namespace CFSG.KD.TBind

@[expose] noncomputable def appP (L₁ L₂ : List (Nat × Nat)) : List (Nat × Nat) :=
  List.rec (motive := fun _ => List (Nat × Nat)) L₂ (fun x _ ih => List.cons x ih) L₁

@[expose] noncomputable def CH : List (Nat × Nat) := appP C0.CH (appP C1.CH (appP C2.CH C3.CH))

theorem appP_eq (L₁ L₂ : List (Nat × Nat)) : appP L₁ L₂ = L₁ ++ L₂ := by
  induction L₁ with
  | nil => rfl
  | cons x L ih =>
    rw [List.cons_append, ← ih]
    rfl

end CFSG.KD.TBind

end
