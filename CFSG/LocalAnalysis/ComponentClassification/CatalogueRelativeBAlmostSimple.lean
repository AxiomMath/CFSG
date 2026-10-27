module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBFixedComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSmallOrders
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting

public section

namespace CFSG.ComponentClassification.CatalogueRelativeB

theorem simple_self_centralizing_centralizer_eq_bot {G : Type*} [Group G]
    (N : Subgroup G) [IsSimpleGroup N]
    (hnonab : ∃ a b : N, a * b ≠ b * a)
    (hself : Subgroup.centralizer (N : Set G) ≤ N) :
    Subgroup.centralizer (N : Set G) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  let member : N := ⟨x, hself hx⟩
  have hcenter : member ∈ Subgroup.center N := by
    apply Subgroup.mem_center_iff.mpr
    intro other
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx other other.property)
  rw [Helpers.center_eq_bot N hnonab] at hcenter
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hcenter))

theorem simple_self_centralizing_center_eq_bot {G : Type*} [Group G]
    (N : Subgroup G) [IsSimpleGroup N]
    (hnonab : ∃ a b : N, a * b ≠ b * a)
    (hself : Subgroup.centralizer (N : Set G) ≤ N) : Subgroup.center G = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have hcentralizer : x ∈ Subgroup.centralizer (N : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro other _
    exact Subgroup.mem_center_iff.mp hx other
  rwa [simple_self_centralizing_centralizer_eq_bot N hnonab hself] at hcentralizer

theorem simple_generalizedFitting_centralizer_eq_bot {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup (GeneralizedFitting.subgroup G)]
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) :
    Subgroup.centralizer (GeneralizedFitting.subgroup G : Set G) = ⊥ :=
  simple_self_centralizing_centralizer_eq_bot _ hnonab (GeneralizedFitting.centralizer_le G)

theorem simple_generalizedFitting_center_eq_bot {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup (GeneralizedFitting.subgroup G)]
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) :
    Subgroup.center G = ⊥ :=
  simple_self_centralizing_center_eq_bot _ hnonab (GeneralizedFitting.centralizer_le G)

theorem quotient_solvable_of_index_le_two {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hindex : N.index ≤ 2) : Group.IsSolvable (G ⧸ N) := by
  apply CatalogueSchreierAlternating.solvable_of_card_le_four
  rw [← Subgroup.index_eq_card]
  omega

@[expose] def fixedSubgroupEquivalence {F M : Type*} [Group F] [Group M]
    (equivalence : F ≃* M) (automorphism : MulAut F) :
    FixedCommutingProduct.fixedSubgroup automorphism ≃*
      FixedCommutingProduct.fixedSubgroup (MulAut.congr equivalence automorphism) where
  toFun member := ⟨equivalence member, by
    change equivalence (automorphism (equivalence.symm (equivalence member))) = equivalence member
    rw [equivalence.symm_apply_apply]
    exact congrArg equivalence member.property⟩
  invFun member := ⟨equivalence.symm member, by
    apply equivalence.injective
    change equivalence (automorphism (equivalence.symm member)) =
      equivalence (equivalence.symm member)
    rw [equivalence.apply_symm_apply]
    exact member.property⟩
  left_inv member := Subtype.ext (equivalence.symm_apply_apply member)
  right_inv member := Subtype.ext (equivalence.apply_symm_apply member)
  map_mul' left right := Subtype.ext (equivalence.map_mul left right)

theorem normal_conjugation_involutive {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (t : G) (ht : orderOf t = 2) :
    Function.Involutive (MulAut.conjNormal (H := N) t) := by
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← ht]
    exact pow_orderOf_eq_one t
  have hautomorphism :
      (MulAut.conjNormal (H := N) t) * (MulAut.conjNormal (H := N) t) = 1 := by
    rw [← map_mul, ht2, map_one]
  intro member
  exact congrArg (fun automorphism : MulAut N => automorphism member) hautomorphism

theorem normal_fixed_components_of_model {G M : Type*} [Group G] [Finite G]
    [Group M] [Finite M] (N : Subgroup G) [N.Normal]
    (equivalence : N ≃* M)
    (hmodel : ∀ automorphism : MulAut M, Function.Involutive automorphism →
      ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup automorphism),
        TwoComponents.IsTwoComponent L → CFSG.Open.IsQuasisimple L)
    (t : G) (ht : orderOf t = 2)
    (L : Subgroup ((Subgroup.centralizer ({t} : Set G)).subgroupOf N))
    (hL : TwoComponents.IsTwoComponent L) : CFSG.Open.IsQuasisimple L := by
  let automorphism := MulAut.conjNormal (H := N) t
  let modelAutomorphism := MulAut.congr equivalence automorphism
  have hinvolutive : Function.Involutive modelAutomorphism := by
    intro member
    change equivalence (automorphism (equivalence.symm
      (equivalence (automorphism (equivalence.symm member))))) = member
    rw [equivalence.symm_apply_apply, normal_conjugation_involutive N t ht,
      equivalence.apply_symm_apply]
  let fixedEquivalence := (normalFixedEquivalence N t).symm.trans
    ((FixedNormalCentralizer.equivalence N t).trans
      (fixedSubgroupEquivalence equivalence automorphism))
  have htransport := (TwoComponentTransport.equiv_iff fixedEquivalence L).mpr hL
  have hquasisimple := hmodel modelAutomorphism hinvolutive _ htransport
  exact Components.quasisimple_of_equiv
    (L.equivMapOfInjective fixedEquivalence.toMonoidHom fixedEquivalence.injective)
    hquasisimple

theorem local_bad_eq_bot_of_simple_normal_model {G M : Type*}
    [Group G] [Finite G] [Group M] [Finite M]
    (N : Subgroup G) [N.Normal] [IsSimpleGroup N]
    (hnonab : ∃ a b : N, a * b ≠ b * a)
    (hself : Subgroup.centralizer (N : Set G) ≤ N) (hindex : N.index ≤ 2)
    (equivalence : N ≃* M)
    (hmodel : ∀ automorphism : MulAut M, Function.Involutive automorphism →
      ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup automorphism),
        TwoComponents.IsTwoComponent L → CFSG.Open.IsQuasisimple L)
    (hproper : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X)
    (S : Subgroup G) (hne : S ≠ ⊥) (htwo : IsPGroup 2 S) :
    TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥ := by
  let : Group.IsSolvable (G ⧸ N) := quotient_solvable_of_index_le_two N hindex
  have hoddCenter : Odd (Nat.card (Subgroup.center G)) := by
    rw [simple_self_centralizing_center_eq_bot N hnonab hself, Subgroup.card_bot]
    decide
  exact local_bad_eq_bot_of_normal_fixed_components N hoddCenter hproper
    (normal_fixed_components_of_model N equivalence hmodel) S hne htwo

theorem local_bad_eq_bot_of_simple_generalizedFitting_model {G M : Type*}
    [Group G] [Finite G] [Group M] [Finite M]
    [IsSimpleGroup (GeneralizedFitting.subgroup G)]
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hindex : (GeneralizedFitting.subgroup G).index ≤ 2)
    (equivalence : GeneralizedFitting.subgroup G ≃* M)
    (hmodel : ∀ automorphism : MulAut M, Function.Involutive automorphism →
      ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup automorphism),
        TwoComponents.IsTwoComponent L → CFSG.Open.IsQuasisimple L)
    (hproper : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X)
    (S : Subgroup G) (hne : S ≠ ⊥) (htwo : IsPGroup 2 S) :
    TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥ := by
  let : (GeneralizedFitting.subgroup G).Normal := GeneralizedFitting.normal G
  exact local_bad_eq_bot_of_simple_normal_model _ hnonab (GeneralizedFitting.centralizer_le G)
    hindex equivalence hmodel hproper S hne htwo

end CFSG.ComponentClassification.CatalogueRelativeB
