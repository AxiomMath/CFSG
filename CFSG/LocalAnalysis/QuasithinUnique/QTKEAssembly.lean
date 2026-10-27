module

public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore
public import CFSG.LocalAnalysis.ComponentClassification.SimpleEvenOrder

public section

namespace CFSG.QuasithinUnique

open CFSG.Assembly CFSG.Assembly.Quasithin

@[expose] def UniqueMaximalLocalOver (C : GroupProp) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    QTKEOver C G → ∀ T : Sylow 2 G,
    (∃! M : Subgroup G, quasithinIsMaxTwoLocal M ∧ (T : Subgroup G) ≤ M) → C G

@[expose] def FaithfulLocalEmptyOver (C : GroupProp) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    QTKEOver C G → ∀ T : Sylow 2 G,
    (∃ M₁ M₂ : Subgroup G, M₁ ≠ M₂ ∧ quasithinIsMaxTwoLocal M₁ ∧ quasithinIsMaxTwoLocal M₂ ∧
      (T : Subgroup G) ≤ M₁ ∧ (T : Subgroup G) ≤ M₂) →
    (∀ L : Subgroup G, ¬ quasithinIsFaithfulLocal (T : Subgroup G) L) → C G

@[expose] def FaithfulLocalNonemptyOver (C : GroupProp) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    QTKEOver C G → ∀ T : Sylow 2 G,
    (∃ L : Subgroup G, quasithinIsFaithfulLocal (T : Subgroup G) L) → C G

@[expose] def UniqueMaximalLocalCat : Prop :=
  UniqueMaximalLocalOver Blueprint.Catalog

@[expose] def FaithfulLocalEmptyCat : Prop :=
  FaithfulLocalEmptyOver Blueprint.Catalog

@[expose] def FaithfulLocalNonemptyCat : Prop :=
  FaithfulLocalNonemptyOver Blueprint.Catalog

theorem exists_maxTwoLocal_ge_sylow {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)
    (hT : (T : Subgroup G) ≠ ⊥) :
    ∃ M : Subgroup G, quasithinIsMaxTwoLocal M ∧ (T : Subgroup G) ≤ M := by
  let S := {H : Subgroup G | IsTwoLocal H ∧ (T : Subgroup G) ≤ H}
  have hN : Subgroup.normalizer ((T : Subgroup G) : Set G) ∈ S :=
    ⟨⟨T, hT, T.isPGroup', rfl⟩, Subgroup.le_normalizer⟩
  obtain ⟨M, -, hM⟩ := S.toFinite.exists_le_maximal hN
  exact ⟨M, ⟨hM.prop.1, fun H hH hMH => (hM.eq_of_le ⟨hH, hM.prop.2.trans hMH⟩ hMH).symm⟩,
    hM.prop.2⟩

theorem two_maxTwoLocal_of_not_unique {G : Type*} [Group G] {T M : Subgroup G}
    (hM : quasithinIsMaxTwoLocal M) (hTM : T ≤ M)
    (huniq : ¬ ∃! M : Subgroup G, quasithinIsMaxTwoLocal M ∧ T ≤ M) :
    ∃ M₁ M₂ : Subgroup G, M₁ ≠ M₂ ∧ quasithinIsMaxTwoLocal M₁ ∧ quasithinIsMaxTwoLocal M₂ ∧
      T ≤ M₁ ∧ T ≤ M₂ := by
  by_contra h
  refine huniq ⟨M, ⟨hM, hTM⟩, fun M' ⟨hM', hTM'⟩ => ?_⟩
  by_contra hne
  exact h ⟨M, M', Ne.symm hne, hM, hM', hTM, hTM'⟩

theorem qt_case_division {G : Type*} [Group G] [Finite G] {P : Prop}
    (heven : Even (Nat.card G))
    (hU : ∀ T : Sylow 2 G,
      (∃! M : Subgroup G, quasithinIsMaxTwoLocal M ∧ (T : Subgroup G) ≤ M) → P)
    (hE : ∀ T : Sylow 2 G, (∃ M₁ M₂ : Subgroup G, M₁ ≠ M₂ ∧ quasithinIsMaxTwoLocal M₁ ∧
      quasithinIsMaxTwoLocal M₂ ∧ (T : Subgroup G) ≤ M₁ ∧ (T : Subgroup G) ≤ M₂) →
      (∀ L : Subgroup G, ¬ quasithinIsFaithfulLocal (T : Subgroup G) L) → P)
    (hD : ∀ T : Sylow 2 G, (∃ L : Subgroup G, quasithinIsFaithfulLocal (T : Subgroup G) L) → P) :
    P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 2 G))
  obtain ⟨M, hM, hTM⟩ :=
    exists_maxTwoLocal_ge_sylow T (T.ne_bot_of_dvd_card (even_iff_two_dvd.mp heven))
  by_cases huniq : ∃! M : Subgroup G, quasithinIsMaxTwoLocal M ∧ (T : Subgroup G) ≤ M
  · exact hU T huniq
  by_cases hLf : ∃ L : Subgroup G, quasithinIsFaithfulLocal (T : Subgroup G) L
  · exact hD T hLf
  · exact hE T (two_maxTwoLocal_of_not_unique hM hTM huniq) fun L hL => hLf ⟨L, hL⟩

theorem qtke_classification_of_branches_over {C : GroupProp} (hU : UniqueMaximalLocalOver C)
    (hE : FaithfulLocalEmptyOver C) (hD : FaithfulLocalNonemptyOver C) (G : Type) [Group G]
    [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (hqtke : QTKEOver C G)
    (heven : Even (Nat.card G)) : C G :=
  qt_case_division heven (hU G hnonab hqtke) (hE G hnonab hqtke) (hD G hnonab hqtke)

theorem cls_qtke_classification_of_branches (hU : UniqueMaximalLocalCat)
    (hE : FaithfulLocalEmptyCat) (hD : FaithfulLocalNonemptyCat) (G : Type) [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (hqtke : quasithinIsQTKECat G) :
    Blueprint.Catalog G :=
  qtke_classification_of_branches_over hU hE hD G hnonab hqtke
    (ComponentClassification.SimpleEvenOrder.nonabelian_simple_even hnonab).1

end CFSG.QuasithinUnique
