module

public import CFSG.GH74.NoComponent
public import CFSG.GH74.GLS.Statements

public section

namespace CFSG.GH74

open Blueprint

theorem catalog_of_c23List {G : Type} [Group G] (h : GLS.C23List G) : Catalog G := by
  rcases h with ⟨p, f, -, -, -, h⟩ | ⟨f, h⟩ | h | h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨-, h⟩ | h | h | ⟨-, h | h⟩ | h | ⟨-, ⟨-, h⟩ | ⟨-, h⟩⟩ <;>
      exact catalog_of_lieModel h
  · exact catalog_of_lieModel h
  · exact Or.inr (Or.inl ⟨7, by norm_num, h⟩)
  · exact Or.inr (Or.inl ⟨9, by norm_num, h⟩)
  · exact Or.inr (Or.inl ⟨10, by norm_num, h⟩)
  · exact Or.inr (Or.inl ⟨11, by norm_num, h⟩)
  · exact catalog_of_isSporadic h
  · exact catalog_of_lieModel h
  · exact catalog_of_isSporadic h
  · exact catalog_of_isSporadic h
  · exact catalog_of_isSporadic h
  · exact catalog_of_isSporadic h
  · exact catalog_of_isSporadic h

@[expose] def S_specialOdd : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    3 ≤ Open.twoRank G → Gen4 G → KGH G →
      (∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G)) →
      (∃ x : G, orderOf x = 2 ∧ layerBar x ≠ ⊥) → GLS.IsSpecialOddType G → GLS.C23List G

@[expose] def S_restrictedEven : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    3 ≤ Open.twoRank G → Gen4 G → KGH G →
      (∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G)) →
      (∃ x : G, orderOf x = 2 ∧ layerBar x ≠ ⊥) → GLS.IsRestrictedEvenType G → Catalog G

@[expose] def S_generic : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    3 ≤ Open.twoRank G → Gen4 G → KGH G →
      (∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G)) →
      (∃ x : G, orderOf x = 2 ∧ layerBar x ≠ ⊥) → GLS.L2Meets G GLS.InG2 → GH74Conclusion G

theorem gh74_of_routeH
    (hW : S_walterNative) (hQ : S_QTKE_Gen4) (hF : S_filter)
    (hRE : S_restrictedEven) (hGen : S_generic) (hSO : S_specialOdd) : GH74Statement := by
  suffices key : ∀ (n : ℕ) (G : Type) [Group G] [Finite G], Nat.card G = n → IsSimpleGroup G →
      (∃ a b : G, a * b ≠ b * a) → 3 ≤ Open.twoRank G → Gen4 G → GH74Conclusion G by
    intro G _ _ hs hnonab hrank hgen
    exact key _ G rfl hs hnonab hrank hgen
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hn hs hnonab hrank hgen
  have hK : KGH G := kgh_of_smaller hgen fun X _ _ hlt hsX hnX hrX hgX =>
    ih _ (hn ▸ hlt) X rfl hsX hnX hrX hgX
  by_cases habel : ∃ S : Sylow 2 G, IsMulCommutative (S : Subgroup G)
  · obtain ⟨S, hS⟩ := habel
    exact gh74Conclusion_of_abelian hW hnonab hrank hgen S hS
  have hnab := sylow_not_comm_of_not_comm habel
  by_cases hL : ∀ x : G, orderOf x = 2 → layerBar x = ⊥
  · exact noComponent_of_qtke hQ hF G hs hnonab hrank hgen hK hL
  have hLx : ∃ x : G, orderOf x = 2 ∧ layerBar x ≠ ⊥ := by
    push Not at hL
    exact hL
  by_cases hre : GLS.IsRestrictedEvenType G
  · exact hF G (hRE G hs hnonab hrank hgen hK hnab hLx hre) hnonab hrank hgen
  by_cases hg : GLS.L2Meets G GLS.InG2
  · exact hGen G hs hnonab hrank hgen hK hnab hLx hg
  · exact hF G (catalog_of_c23List (hSO G hs hnonab hrank hgen hK hnab hLx ⟨hre, hg⟩))
      hnonab hrank hgen

end CFSG.GH74
