module

public import CFSG.ClassicalInvolution.Q3.TL3CentStep

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

section Def

@[expose] def TightHasMember3LargeBelowQ8 : Prop :=
  ∀ n : ℕ, CIT3Below n → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
    Nat.card G < n → (∃ a b : genFittingFStar G, a * b ≠ b * a) →
    ¬ TwoSubgroupsFourGenerated (genFittingFStar G) →
    ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G), TightDatum R S t →
      Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2) →
      ∃ (z : G) (J : Subgroup G), IsClassicalMember3 J z

end Def

section Top

theorem tightHasMember3LargeBelowQ8_of_inductive₂ (hI : ∀ N, TightInductive N)
    (hE : ∀ n, TightLargeEdgeS n) : TightHasMember3LargeBelowQ8 := by
  intro n hn G _ _ _ hlt hnab hlarge R S t hd hq8
  obtain ⟨H, R', S', t', hd', hcls, hE2, hFs, hnabH, hlargeH, hmem⟩ :=
    tightTopRestrictS G hnab hlarge R S t hd hq8
  have hHn : Nat.card H < n :=
    lt_of_le_of_lt (Nat.card_le_card_of_injective _ H.subtype_injective) hlt
  have hbelow : TightBelow (Nat.card H) := fun Y _ _ hlt' R S t hd hc =>
    hI n hn Y (lt_trans hlt' hHn) R S t hd hc
  have hedge := hE (Nat.card H) (CIT3Below.mono hHn.le hn) hbelow H rfl hnabH R' S' t' hd' hcls
    hE2 hlargeH
  rcases hI n hn H hHn R' S' t' hd' hcls with
    (hex | ⟨hedgeless, -⟩ | ⟨hedgeless, -⟩ | h4) | hgood
  · exact absurd hex hE2
  · exact absurd hedgeless hedge
  · exact absurd hedgeless hedge
  ·
    have := hFs
    have hZ : Subgroup.center ↥H = ⊥ :=
      le_bot_iff.mp ((centralizer_fstar_eq_bot_and_oddCore_eq_bot hnabH).1 ▸
        Subgroup.center_le_centralizer _)
    exact absurd h4 (hd'.not_tightE4 hcls hE2 hZ)
  · obtain ⟨L, -, hL⟩ := tightHasLift_of_good hd' hgood
    exact hmem ⟨L, hL⟩

end Top

end CFSG.ClassicalInvolution.Q3.TA3
