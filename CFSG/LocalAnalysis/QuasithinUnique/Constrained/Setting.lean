module

public import CFSG.LocalAnalysis.QuasithinUnique.Reduction
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.Quasithin.Background.Basic

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

variable {G : Type*} [Group G]

@[expose] def conjJoin (S L : Subgroup G) : Subgroup G :=
  ⨆ s : S, L.map (MulAut.conj (s : G)).toMonoidHom

@[expose] def IsMinimalParabolic (S H : Subgroup G) : Prop :=
  IsSylowTwoOf S H ∧ ¬ H ≤ Subgroup.normalizer (S : Set G) ∧
    ∃ K : Subgroup G, S ≤ K ∧ K < H ∧ ∀ X : Subgroup G, S ≤ X → X < H → X ≤ K

structure ConstrainedSetting (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) :
    Prop where
  setting : UniqueSetting G T M
  notBender : ¬ fusionIsBenderGroup G
  notSmall : ¬ UniqueSmallModel G
  gamma0 : IsGamma0 M H
  charTwo : CharTwo H
  sylow : IsSylowTwoOf S H
  sylow_inf : IsSylowTwoOf S (H ⊓ M)
  le_T : S ≤ T
  center_le : T ⊓ Subgroup.centralizer (T : Set G) ≤ S
  ne_T : S ≠ T
  witness : IsWitnessPair M S H
  block : IsChi0Block H L
  not_le : ¬ L ≤ M
  thompson : ⁅L, CFSG.Quasithin.thompsonJ S⁆ = L
  eq_join : H = conjJoin S L ⊔ S
  blocks : conjJoin S L = L ∨
    ∃ t ∈ S, L.map (MulAut.conj t).toMonoidHom ≠ L ∧
      conjJoin S L = L ⊔ L.map (MulAut.conj t).toMonoidHom ∧
      ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ = ⊥
  minParabolic : IsMinimalParabolic S H
  maxInf : ∀ X : Subgroup G, S ≤ X → X < H → X ≤ M

@[expose] def ConstrainedSetup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G), UniqueSetting G T M →
    ¬ fusionIsBenderGroup G → ¬ UniqueSmallModel G → IsGamma0 M H → CharTwo H →
    ∃ T' H' S L : Subgroup G, ConstrainedSetting G T' M H' S L

@[expose] def Lin2BlockExcluded : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    ∀ n : ℕ, 1 < n → ¬ IsLin2Type L n

@[expose] def A5BlockExcluded : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    ¬ IsAltType L 5

@[expose] def SingleA3Excluded : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    IsAltType L 3 → conjJoin S L = L → False

@[expose] def DoubleA3Excluded : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    IsAltType L 3 → conjJoin S L ≠ L → False

theorem constrainedBranch_of_parts (hsetup : ConstrainedSetup) (hlin : Lin2BlockExcluded)
    (ha5 : A5BlockExcluded) (ha3 : SingleA3Excluded) (ha33 : DoubleA3Excluded) :
    ConstrainedBranch := by
  intro G _ _ T M hset hnb H hH hc
  by_contra hns
  obtain ⟨T', H', S, L, hcs⟩ := hsetup G T M H hset hnb hns hH hc
  rcases hcs.block.2 with ⟨n, hn, hlin2⟩ | h3 | h5
  · exact hlin G T' M H' S L hcs n hn hlin2
  · by_cases hj : conjJoin S L = L
    · exact ha3 G T' M H' S L hcs h3 hj
    · exact ha33 G T' M H' S L hcs h3 hj
  · exact ha5 G T' M H' S L hcs h5

end CFSG.QuasithinUnique
