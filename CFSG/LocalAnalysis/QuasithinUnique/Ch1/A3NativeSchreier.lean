module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic

public section

namespace CFSG.QuasithinUnique.Vol2Native

open CFSG.Quasithin CFSG.SectionRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem outSolvable_of_isSolvable_outer {X : Type} [Group X] (h : Group.IsSolvable (Outer X)) :
    OutSolvable X := by
  obtain ⟨n, hn⟩ := h.solvable
  refine ⟨n, fun x hx => ?_⟩
  have hmap := map_derivedSeries_eq (f := QuotientGroup.mk' (inner X))
    (QuotientGroup.mk'_surjective _) n
  have hx' : QuotientGroup.mk' (inner X) x ∈
      (derivedSeries (MulAut X) n).map (QuotientGroup.mk' (inner X)) := ⟨x, hx, rfl⟩
  rw [hmap, hn] at hx'
  have hxi : x ∈ inner X := (QuotientGroup.eq_one_iff x).mp (Subgroup.mem_bot.mp hx')
  exact hxi

theorem schreierFactCat_of_catalogueSchreier
    (hS : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
      CFSG.Blueprint.Catalog S → Group.IsSolvable (Outer S)) : SchreierFactCat := by
  intro X _ _ hqs hK
  have : Group.IsPerfect X := hqs.1
  have : IsSimpleGroup (X ⧸ Subgroup.center X) := hqs.2.1
  have hcat : CFSG.Blueprint.Catalog (X ⧸ Subgroup.center X) :=
    catalog_of_isKGroupCat_of_surjective hK ⊤
      ((QuotientGroup.mk' (Subgroup.center X)).comp (Subgroup.topEquiv (G := X)).toMonoidHom)
      ((QuotientGroup.mk'_surjective _).comp (Subgroup.topEquiv (G := X)).surjective)
  have : Group.IsSolvable (Outer (X ⧸ Subgroup.center X)) := hS _ hqs.2.2 hcat
  exact outSolvable_of_isSolvable_outer
    (CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient X)

theorem schreierFactListCat_of_simple
    (hS : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
      A23ListCat S → Group.IsSolvable (Outer S)) : SchreierFactListCat := by
  intro X _ _ hqs hlist
  have : Group.IsPerfect X := hqs.1
  have : IsSimpleGroup (X ⧸ Subgroup.center X) := hqs.2.1
  have : Group.IsSolvable (Outer (X ⧸ Subgroup.center X)) := hS _ hqs.2.2 hlist
  exact outSolvable_of_isSolvable_outer
    (CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient X)

end CFSG.QuasithinUnique.Vol2Native
