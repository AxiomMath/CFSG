module

public import CFSG.ClassicalInvolution.Asc77.WP3LayerPair

public section

namespace CFSG.ClassicalInvolution.Asc77.ExactLayer

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem lieSystemAt_exactFamily (hΩ : ConjInvariant Ω)
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hBelow : CITBelowU p f (Nat.card G)) (hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G)
    (hne : (tqMembers Ω c).Nonempty) : Nonempty (LocalLieSystemAt p f (exactFamily Ω c) c) :=
  (secData_exactFamily hΩ hcls hc2 hne).nonempty_lieSystem hBelow hnc

theorem lieDecomposition_exactFamily_comp (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hq : 5 ≤ p ^ f) (hΩ : ConjInvariant Ω)
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hne : (tqMembers Ω c).Nonempty) (D : LocalLieSystemAt p f (exactFamily Ω c) c) :
    ∃ D' : LieDecomposition (exactImages Ω c) (exactJoin Ω c),
      (∀ i, D'.Q i ∈ Set.range fun j : Fin D.card =>
        (secComponentHom (normalizesLayer_exactFamily hΩ) D j).range) ∧
      ((∀ j, p ^ D.exp j ≠ 3) → D'.Big) := by
  obtain ⟨D', hD'Q, hbig⟩ :=
    (secData_exactFamily hΩ hcls hc2 hne).lieDecomposition_comp hp2 h0 hA1 hq D
  exact ⟨D', hD'Q, hbig⟩

theorem localLieSystemAt_exactFamily_iff :
    Nonempty (LocalLieSystemAt p f (exactFamily Ω c) c) ↔ LieSystemMod p f (exactPair Ω c) := by
  have h : centralizingMembers (exactFamily Ω c) {c} = exactFamily Ω c :=
    centMembers_exactFamily Ω c
  constructor
  · rintro ⟨D⟩
    unfold LocalLieSystemAt at D
    rw [h] at D
    exact ⟨D⟩
  · intro ⟨D⟩
    unfold LocalLieSystemAt
    rw [h]
    exact ⟨D⟩

end CFSG.ClassicalInvolution.Asc77.ExactLayer
