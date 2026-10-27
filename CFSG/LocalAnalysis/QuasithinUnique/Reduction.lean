module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.Assembly.QuasithinDefs

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

@[expose] def LocalSQTK (G : Type) [Group G] : Prop :=
  ∀ P : Subgroup G, pCoreOf 2 P ≠ ⊥ → CFSG.SectionRank.IsSQTKCat P

@[expose] def QTKECore (G : Type) [Group G] [Finite G] : Prop :=
  LocalSQTK G ∧ CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G ∧ CFSG.Assembly.evenRank G ≤ 2

structure UniqueSetting (G : Type) [Group G] [Finite G] (T M : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  qtke : QTKECore G
  sylow : IsSylowTwoOf T ⊤
  maxLocal : CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal M
  le : T ≤ M
  unique : ∀ M' : Subgroup G, CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal M' → T ≤ M' → M' = M

@[expose] def BenderBranch : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), UniqueSetting G T M →
    (∀ D : Subgroup G, ¬ IsEscaping M D) → fusionIsBenderGroup G

@[expose] def ConstrainedBranch : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), UniqueSetting G T M →
    ¬ fusionIsBenderGroup G → ∀ H : Subgroup G, IsGamma0 M H → CharTwo H → UniqueSmallModel G

@[expose] def UnconstrainedBranch : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), UniqueSetting G T M →
    ¬ fusionIsBenderGroup G → ¬ UniqueSmallModel G →
    (∃ D : Subgroup G, IsEscaping M D) → (∀ H : Subgroup G, IsGamma0 M H → ¬ CharTwo H) → False

theorem theorem_2_1_1_of_branches (hB : BenderBranch) (hC : ConstrainedBranch)
    (hU : UnconstrainedBranch) {G : Type} [Group G] [Finite G] {T M : Subgroup G}
    (h : UniqueSetting G T M) : fusionIsBenderGroup G ∨ UniqueSmallModel G := by
  by_cases hbender : fusionIsBenderGroup G
  · exact Or.inl hbender
  by_cases hsmall : UniqueSmallModel G
  · exact Or.inr hsmall
  by_cases hδ : ∃ D : Subgroup G, IsEscaping M D
  · by_cases hΓ : ∃ H : Subgroup G, IsGamma0 M H ∧ CharTwo H
    · obtain ⟨H, hH, hc⟩ := hΓ
      exact Or.inr (hC G T M h hbender H hH hc)
    · exact (hU G T M h hbender hsmall hδ fun H hH hc => hΓ ⟨H, hH, hc⟩).elim
  · exact Or.inl (hB G T M h fun D hD => hδ ⟨D, hD⟩)

end CFSG.QuasithinUnique
