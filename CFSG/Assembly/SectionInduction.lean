module

public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.Assembly

open CFSG.Blueprint CFSG.SectionRank

theorem card_section_lt {G : Type} [Group G] [Finite G] {K : Subgroup G} (hK : K ≠ ⊤)
    (L : Subgroup K) : Nat.card (K ⧸ L) < Nat.card G :=
  calc Nat.card (K ⧸ L)
      ≤ Nat.card K := Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    _ < Nat.card (⊤ : Subgroup G) := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.2 hK)
    _ = Nat.card G := Subgroup.card_top

theorem section_induction (C : GroupProp)
    (hK : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], KProper C G → C G)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] : C G := by
  suffices h : ∀ n, ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], Nat.card G = n → C G from
    h _ G rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ _ hn
    refine hK G fun K L hKtop _ _ _ _ => ?_
    exact ih _ (hn ▸ card_section_lt hKtop _) (K ⧸ L.subgroupOf K) rfl

@[expose] def IsKProperCat (X : Type) [Group X] : Prop :=
  ∀ H : Subgroup X, H ≠ ⊤ → IsKGroupCat H

end CFSG.Assembly
