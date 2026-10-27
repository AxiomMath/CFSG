module

public import CFSG.GH74.GLS.Bg.TwoGroups.L23Models

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace L23

@[expose] def Invs (G : Type) [Group G] : Type := {t : G // t * t = 1 ∧ t ≠ 1}

theorem card_invs_congr {G G' : Type} [Group G] [Group G'] (e : G ≃* G') :
    Nat.card (Invs G) = Nat.card (Invs G') :=
  Nat.card_congr (e.toEquiv.subtypeEquiv (fun t => by
    show (t * t = 1 ∧ t ≠ 1) ↔ (e t * e t = 1 ∧ e t ≠ 1)
    rw [← map_mul, map_eq_one_iff e e.injective, e.injective.ne_iff' (map_one e)]))

theorem card_invs_Z4Z4 : Nat.card (Invs Z4Z4) = 3 := by
  show Nat.card {t : Z4Z4 // t * t = 1 ∧ t ≠ 1} = 3
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_invs_L : Nat.card (Invs (UT3 F4c)) = 27 := by
  show Nat.card {t : UT3 F4c // t * t = 1 ∧ t ≠ 1} = 27
  rw [Nat.card_eq_fintype_card]
  exact inv_count_L

theorem card_invs_S : Nat.card (Invs ↥sylSU3c) = 3 := by
  show Nat.card {t : ↥sylSU3c // t * t = 1 ∧ t ≠ 1} = 3
  rw [Nat.card_eq_fintype_card]
  exact inv_count_S

theorem classify_models {G : Type} [Group G] [Finite G] (hG : Nat.card G = 64)
    (D : ExtData PP QQ G) (hπ : (D.α, D.β, D.γ) ∈ S16) :
    (Nonempty (G ≃* SylSL3_4) ∧ Nat.card (Invs G) = 27) ∨
      (Nonempty (G ≃* SylSU3_4) ∧ Nat.card (Invs G) = 3) := by
  rcases S16_cover _ hπ with ⟨t, ht, h1⟩ | ⟨t, ht, h1⟩
  · left
    have hα : D.α = (dataL t ht).α := congrArg (fun p => p.1) h1.symm
    have hβ : D.β = (dataL t ht).β := congrArg (fun p => p.2.1) h1.symm
    have hγ : D.γ = (dataL t ht).γ := congrArg (fun p => p.2.2) h1.symm
    obtain ⟨e⟩ := ext_equiv D hG card_UT3c (dataL t ht) hdistPQ hα hβ hγ
    exact ⟨⟨e.trans sylLCongr.symm⟩, (card_invs_congr e).trans card_invs_L⟩
  · right
    have hα : D.α = (dataS t ht).α := congrArg (fun p => p.1) h1.symm
    have hβ : D.β = (dataS t ht).β := congrArg (fun p => p.2.1) h1.symm
    have hγ : D.γ = (dataS t ht).γ := congrArg (fun p => p.2.2) h1.symm
    obtain ⟨e⟩ := ext_equiv D hG card_sylSU3c (dataS t ht) hdistPQ hα hβ hγ
    exact ⟨⟨e.trans sylCongr.symm⟩, (card_invs_congr e).trans card_invs_S⟩

end L23

end CFSG.GH74.GLS.Bg.TwoGroups
