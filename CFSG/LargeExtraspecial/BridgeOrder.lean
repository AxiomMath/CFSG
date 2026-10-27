module

public import CFSG.Sporadic.Co2
public import CFSG.Sporadic.Co1
public import CFSG.LargeExtraspecial.BridgeConclusion

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.Bridge

open Subgroup CFSG.Open

theorem card_Co2_eq
    : Nat.card CFSG.Blueprint.NativeSporadic.Co2 = timmesfeldOrderCo2 := by
  rw [CFSG.Sporadic.Co2.card_Co2]
  norm_num [timmesfeldOrderCo2]

theorem card_Co1_eq
    : Nat.card CFSG.Blueprint.NativeSporadic.Co1 = timmesfeldOrderCo1 := by
  rw [CFSG.Sporadic.Co1.card_Co1]
  norm_num [timmesfeldOrderCo1]

theorem isSimpleGroup_of_mulEquiv_Co2 {X : Type*} [Group X]
    (f : X ≃* CFSG.Blueprint.NativeSporadic.Co2) : IsSimpleGroup X :=
  @MulEquiv.isSimpleGroup X _ CFSG.Blueprint.NativeSporadic.Co2 _
    CFSG.Sporadic.Co2.isSimpleGroup_Co2 f

theorem isSimpleGroup_of_mulEquiv_Co1 {X : Type*} [Group X]
    (f : X ≃* CFSG.Blueprint.NativeSporadic.Co1) : IsSimpleGroup X :=
  @MulEquiv.isSimpleGroup X _ CFSG.Blueprint.NativeSporadic.Co1 _
    CFSG.Sporadic.Co1.isSimpleGroup_Co1 f

theorem card_of_mulEquiv_Co2
    {X : Type*} [Group X] (f : X ≃* CFSG.Blueprint.NativeSporadic.Co2) :
    Nat.card X = timmesfeldOrderCo2 := by
  rw [Nat.card_congr f.toEquiv, card_Co2_eq]

theorem card_of_mulEquiv_Co1
    {X : Type*} [Group X] (f : X ≃* CFSG.Blueprint.NativeSporadic.Co1) :
    Nat.card X = timmesfeldOrderCo1 := by
  rw [Nat.card_congr f.toEquiv, card_Co1_eq]

variable {G : Type*} [Group G] {Mbar : Type*} [Group Mbar] {w : ℕ}

theorem TimmesfeldConclusion.toOrder
    (h : TimmesfeldConclusion G w Mbar) :
    TimmesfeldOrderConclusion G w Mbar := by
  rw [timmesfeldConclusion_iff] at h
  rw [timmesfeldOrderConclusion_iff]
  rcases h with h | h | h | h | h | ⟨h11, ⟨f⟩⟩ | ⟨h12, ⟨f⟩⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨h11, isSimpleGroup_of_mulEquiv_Co2 f, card_of_mulEquiv_Co2 f⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨h12, isSimpleGroup_of_mulEquiv_Co1 f, card_of_mulEquiv_Co1 f⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

theorem orderMainFor_of_mainFor {G : Type} [Group G] (h : MainFor G) : OrderMainFor G :=
  fun hnonab z hz hext w hw Mbar _ hMbar => (h hnonab z hz hext w hw Mbar hMbar).toOrder

theorem order_of_mainStatement (h : MainStatement) (G : Type) [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (z : G) (hz : orderOf z = 2)
    (hext : timmesfeldIsExtraspecial (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))))
    (w : ℕ)
    (hw : Nat.card (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))) = 2 ^ (1 + 2 * w))
    (Mbar : Type) [Group Mbar]
    (hMbar : timmesfeldQuotientIso (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))) Mbar) :
    TimmesfeldOrderConclusion G w Mbar :=
  (h G hnonab z hz hext w hw Mbar hMbar).toOrder

end CFSG.LargeExtraspecial.Bridge
