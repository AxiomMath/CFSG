module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoLocalCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoModel

public section

namespace CFSG.ComponentClassification.CatalogueBLinearTwoLocal

noncomputable section

open CFSG.GorensteinWalter CatalogueSchreierLinearTwo

theorem normalizer_badSubgroup_eq_bot_of_coordinate_equiv {G K : Type*}
    [Group G] [Finite G] [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) (hsize : 5 ≤ Nat.card K)
    (H : Subgroup (Equiv.Perm (Omega K))) (hGH : coordinateG K ≤ H)
    (hHE : H ≤ coordinateE K) (hindex : (coordinateG K).relIndex H ≤ 2)
    (e : G ≃* H) (S : Subgroup G) (hne : S ≠ ⊥) (hS : IsPGroup 2 S) :
    TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥ := by
  have himageNe : S.map e.toMonoidHom ≠ ⊥ := by
    intro h
    exact hne ((Subgroup.map_eq_bot_iff_of_injective S e.injective).mp h)
  have hlocal := (linear_two_index_two_coordinate_local_B K hodd hsize H hGH hHE hindex).2
    (S.map e.toMonoidHom) himageNe (hS.map e.toMonoidHom)
  let r := CatalogueBAlternating.normalizerEquiv e S
  apply (Subgroup.map_eq_bot_iff_of_injective _ (f := r.toMonoidHom) r.injective).mp
  rw [BadComponents.equiv_invariant r]
  exact hlocal

theorem odd_rank_one_admissible_card (p f : ℕ) (hodd : Odd p)
    (hadmissible : Assembly.ComponentType.ClassicalTag.Admissible .PSL 2 p f) :
    5 ≤ p ^ f := by
  have hp := hadmissible.1
  have hf := hadmissible.2.1
  have hnot3 : p ^ f ≠ 3 := by
    intro h
    exact hadmissible.2.2.2 ⟨rfl, Or.inr h⟩
  have hpge : 3 ≤ p := by
    have hp2 := hp.two_le
    obtain ⟨n, hn⟩ := hodd
    omega
  have hbound : 3 ≤ p ^ f := hpge.trans (by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < p) hf)
  obtain ⟨n, hn⟩ := hodd.pow (n := f)
  omega

theorem generalizedFitting_normalizer_badSubgroup_eq_bot {G : Type}
    [Group G] [Finite G] [IsSimpleGroup (GeneralizedFitting.subgroup G)]
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (p f : ℕ) [Fact p.Prime] (hodd : Odd p)
    (hmodel : Assembly.ComponentType.ClassicalModel (GeneralizedFitting.subgroup G)
      .PSL 2 p f)
    (hindex : (GeneralizedFitting.subgroup G).index ≤ 2)
    (S : Subgroup G) (hne : S ≠ ⊥) (hS : IsPGroup 2 S) :
    TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥ := by
  let K := GaloisField p f
  have hf : f ≠ 0 := by
    have h := hmodel.1.2.1
    omega
  let : Finite K := Nat.finite_of_card_ne_zero (by
    rw [GaloisField.card p f hf]
    exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  obtain ⟨rho, hcard, hrho, hmap, _hindex⟩ :=
    CatalogueBLinearTwoModel.generalizedFitting_semilinear_model hnonab p f hmodel
  let action : G →* Equiv.Perm (Omega K) := (coordinateE K).subtype.comp rho
  have hinjective : Function.Injective action := (coordinateE K).subtype_injective.comp hrho
  let H := action.range
  have hactualMap : (GeneralizedFitting.subgroup G).map action = coordinateG K := by
    change (GeneralizedFitting.subgroup G).map ((coordinateE K).subtype.comp rho) = coordinateG K
    rw [← Subgroup.map_map]
    rw [hmap, Subgroup.map_subgroupOf_eq_of_le
      ((coordinateG_le_D K).trans (coordinateD_le_E K))]
  have hGH : coordinateG K ≤ H := by
    rw [← hactualMap]
    exact Subgroup.map_le_range action _
  have hHE : H ≤ coordinateE K := by
    rintro x ⟨g, rfl⟩
    exact (rho g).property
  have hactualIndex : (coordinateG K).relIndex H ≤ 2 := by
    rw [← hactualMap]
    have h := Subgroup.relIndex_map_map_of_injective (f := action)
      (GeneralizedFitting.subgroup G) ⊤ hinjective
    have heq : ((GeneralizedFitting.subgroup G).map action).relIndex H =
        (GeneralizedFitting.subgroup G).index := by
      simpa only [Subgroup.map_top, Subgroup.relIndex_top_right] using h
    exact heq.le.trans hindex
  have hoddK : Odd (Nat.card K) := by
    rw [hcard]
    exact hodd.pow
  have hsize : 5 ≤ Nat.card K := by
    rw [hcard]
    exact odd_rank_one_admissible_card p f hodd hmodel.1
  exact normalizer_badSubgroup_eq_bot_of_coordinate_equiv hoddK hsize H hGH hHE hactualIndex
    (MonoidHom.ofInjective hinjective) S hne hS

theorem generalizedFitting_B_inclusion {G : Type}
    [Group G] [Finite G] [IsSimpleGroup (GeneralizedFitting.subgroup G)]
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (p f : ℕ) [Fact p.Prime] (hodd : Odd p)
    (hmodel : Assembly.ComponentType.ClassicalModel (GeneralizedFitting.subgroup G)
      .PSL 2 p f) (hindex : (GeneralizedFitting.subgroup G).index ≤ 2) :
    CentralTwoBInclusion.Property G := by
  intro S hne hS
  rw [generalizedFitting_normalizer_badSubgroup_eq_bot hnonab p f hodd hmodel hindex S hne hS,
    Subgroup.map_bot]
  exact bot_le

theorem odd_linear_two_generalizedFitting_B_inclusion {G : Type}
    [Group G] [Finite G] [IsSimpleGroup (GeneralizedFitting.subgroup G)]
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (p f : ℕ) [Fact p.Prime] (hodd : Odd p)
    (hmodel : Assembly.ComponentType.ClassicalModel (GeneralizedFitting.subgroup G)
      .PSL 2 p f) (hindex : (GeneralizedFitting.subgroup G).index ≤ 2) :
    (∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
      TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥) ∧
      CentralTwoBInclusion.Property G :=
  ⟨generalizedFitting_normalizer_badSubgroup_eq_bot hnonab p f hodd hmodel hindex,
    generalizedFitting_B_inclusion hnonab p f hodd hmodel hindex⟩

end

end CFSG.ComponentClassification.CatalogueBLinearTwoLocal
