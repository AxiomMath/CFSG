module

public import CFSG.Timmesfeld.ARS.Defs

public section

namespace CFSG.CGT.PushingUpLit.A78

open CFSG.Timmesfeld.ARS

@[expose] def SylowOppositeSL2 : Prop :=
  ∀ {G : Type} [Group G] {K A B : Subgroup G} {e : ℕ}, 2 ≤ e →
    ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e) → A ≤ K → B ≤ K →
      Nat.card A = 2 ^ e → Nat.card B = 2 ^ e → A ≠ B → Opposite A B

@[expose] def SylowCountSL2 : Prop :=
  ∀ {G : Type} [Group G] {K : Subgroup G} {e : ℕ}, 2 ≤ e →
    ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e) →
      {P : Subgroup G | P ≤ K ∧ Nat.card P = 2 ^ e}.ncard = 2 ^ e + 1

end CFSG.CGT.PushingUpLit.A78
