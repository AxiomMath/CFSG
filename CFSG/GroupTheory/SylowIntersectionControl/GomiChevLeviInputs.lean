module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevParabolicInputs

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Quasithin CFSG.ABGLocalTools Subgroup

structure IsGomiLeviData {G : Type} [Group G] (L U P D : Subgroup G) (𝒦 : Set (Subgroup G)) :
    Prop where
  pCoreOf_le : pCoreOf 2 P ≤ D
  le_inf_normalizer : D ≤ L ⊓ normalizer (U : Set G)
  not_two_dvd : ¬ 2 ∣ (pCoreOf 2 P).relIndex D
  commutator_le : ⁅D, P⁆ ≤ pCoreOf 2 P
  le_of_mem : ∀ K ∈ 𝒦, D ≤ K
  le_parabolic : ∀ K ∈ 𝒦, K ≤ P
  parabolic_le_normalizer : ∀ K ∈ 𝒦, P ≤ normalizer (K : Set G)
  two_dvd : ∀ K ∈ 𝒦, 2 ∣ D.relIndex K
  commutator_le_of_ne : ∀ K₁ ∈ 𝒦, ∀ K₂ ∈ 𝒦, K₁ ≠ K₂ → ⁅K₁, K₂⁆ ≤ D
  inf_sSup_le : ∀ K ∈ 𝒦, K ⊓ sSup (𝒦 \ {K}) ≤ D
  sylow_le : U ≤ sSup 𝒦
  le_sup : P ≤ L ⊓ normalizer (U : Set G) ⊔ sSup 𝒦
  map_conj : ∀ g ∈ normalizer (L : Set G) ⊓ normalizer (U : Set G) ⊓ normalizer (P : Set G),
    D.map (MulAut.conj g).toMonoidHom = D ∧ ∀ K ∈ 𝒦, K.map (MulAut.conj g).toMonoidHom ∈ 𝒦
  existsUnique_factor : ∀ A : Subgroup G, IsGomiAtom L U A → A ≤ P →
    ∃ K ∈ 𝒦, ¬ A ⊓ K ≤ L ⊓ normalizer (U : Set G) ∧
      ∀ K' ∈ 𝒦, ¬ A ⊓ K' ≤ L ⊓ normalizer (U : Set G) → K' = K
  factor : ∀ K ∈ 𝒦, ∀ [(D.subgroupOf K).Normal],
    IsGomiChevTwo (↥K ⧸ D.subgroupOf K) ∨
      Nonempty ((↥K ⧸ D.subgroupOf K) ≃* Equiv.Perm (Fin 6)) ∨
      ∀ Q : Subgroup G, L ⊓ normalizer (U : Set G) ⊓ K < Q → Q ≤ K → Q = K

@[expose] def GomiChevLeviDecomposition : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L U P : Subgroup G), IsGomiChevTwo ↥L → center ↥L = ⊥ →
    IsSylowOf 2 U L → L ⊓ normalizer (U : Set G) < P → P < L → ¬ IsGomiAtom L U P →
    ∃ (D : Subgroup G) (𝒦 : Set (Subgroup G)), IsGomiLeviData L U P D 𝒦

@[expose] def GomiChevRankOneOvergroups : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L Q : Subgroup G), IsSylowOf 2 T L → IsGomiChevTwo ↥L →
    (IsGomiL2 (↥L ⧸ center ↥L) ∨ IsGomiU3 (↥L ⧸ center ↥L) ∨ IsGomiSz (↥L ⧸ center ↥L)) →
    L ⊓ normalizer (T : Set G) ≤ Q → Q ≤ L → Q = L ⊓ normalizer (T : Set G) ∨ Q = L

end CFSG.GroupTheory
