module

public import CFSG.CGT.PushingUpLit.A78G0.KData

public section

namespace CFSG.CGT.PushingUpLit.A78G0

open CFSG.CGT.PushingUpLit.A78 CFSG.Timmesfeld.ARS

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ : Subgroup G} {e : ℕ}

@[expose] def DualBase (h : G0Core G L₁ L₂ V W Z Z₂ e) : Prop :=
  ∃ K A I : Subgroup G, KData h K A ∧
    Nonempty (↥I ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)) ∧ Commuting K I ∧
    ∀ P : Subgroup G, P ≤ I → Nat.card P = 2 ^ e → P ∈ zClass Z

end CFSG.CGT.PushingUpLit.A78G0
