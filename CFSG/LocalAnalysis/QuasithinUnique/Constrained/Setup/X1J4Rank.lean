module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4Wrap
public import CFSG.Sporadic.J4.QTRankProof

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Blueprint

theorem two_rank_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (hY : ∀ A : Subgroup Y, (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → (∀ x ∈ A, x * x = 1) →
      Nat.card A ≤ 2 ^ 17) (B : Subgroup X) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hsq : ∀ x ∈ B, x * x = 1) : Nat.card B ≤ 2 ^ 17 := by
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hc : ∀ x ∈ B.map e.toMonoidHom, ∀ y ∈ B.map e.toMonoidHom, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul e.toMonoidHom x y, ← map_mul e.toMonoidHom y x, hcomm x hx y hy]
  have hs : ∀ x ∈ B.map e.toMonoidHom, x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul e.toMonoidHom x x, hsq x hx, map_one]
  have h := hY _ hc hs
  rwa [Subgroup.card_map_of_injective hinj] at h

theorem j4TwoRank_aux
    : ∀ B : Subgroup NativeSporadic.J4,
    (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 17 := by
  intro B hcomm hsq
  have e : NativeSporadic.J4 ≃* CFSG.Sporadic.J4.J :=
    CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat
  exact @two_rank_of_mulEquiv NativeSporadic.J4 CFSG.Sporadic.J4.J inferInstance inferInstance e
    (fun A hc hs => CFSG.Sporadic.J4.QT.card_le_two_pow_seventeen CFSG.Sporadic.J4.j4Facts.mat
      CFSG.Sporadic.J4.j4Facts A hc hs) B hcomm hsq

theorem j4TwoRank
    : J4TwoRankProp := j4TwoRank_aux

end CFSG.QuasithinUnique.Setup.X1
