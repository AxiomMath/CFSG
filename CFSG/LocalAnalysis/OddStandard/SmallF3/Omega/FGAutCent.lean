module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGAutCent6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGAutCentO5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGL281Model

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem fg_aut_cent :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (x : G) (X : Subgroup G),
    (IsOm6P L ∨ IsOm6M L ∨ IsOm5Q L ∨ (IsQuasisimple L ∧ IsL281 L)) → orderOf x = 2 →
    x ∈ normalizer (L : Set G) → IsComponentIn X (L ⊓ centralizer ({x} : Set G)) → InFStar X →
    (IsOm6P L → Hyp62At L) →
    ∀ R : Subgroup G, IsPGroup 2 R →
      R ≤ normalizer (L : Set G) ⊓ centralizer (X : Set G) →
        (centralizer (L : Set G)).relIndex R ≤ 2 ∨
          (IsL29 X ∧ IsOm6M L ∧
            QuotEquivTo R (R ⊓ centralizer (L : Set G))
              (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) ∨
          (IsU33 X ∧ IsOm6M L ∧
            QuotEquivTo R (R ⊓ centralizer (L : Set G)) (Multiplicative (ZMod 4))) ∨
          (IsL29 X ∧ IsOm6P L ∧
            QuotEquivTo R (R ⊓ centralizer (L : Set G)) (Multiplicative (ZMod 4))) := by
  intro G _ _ L x X hL hx hxN hX _ hH R _ hR
  rcases hL with hP | hM | h5 | ⟨hq, h81⟩
  · exact fg_aut_cent_om6 (Or.inl hP) hH hx hxN hX hR
  · exact fg_aut_cent_om6 (Or.inr hM) hH hx hxN hX hR
  · exact Or.inl (fg_aut_cent_om5 h5 hx hxN hX hR)
  · exact Or.inl (fg_aut_cent_l281 hq h81 (hX.le.trans inf_le_left) hX.isQuasisimple hR)

end CFSG.OddStandard.SmallF3.Omega
