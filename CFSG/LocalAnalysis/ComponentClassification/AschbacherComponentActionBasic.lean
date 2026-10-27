module

public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication

public noncomputable section

namespace CFSG.ComponentClassification.AschbacherComponentAction

open CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem perfect_three_subgroup_action (L X : Subgroup G) [Group.IsPerfect L]
    (h : ⁅⁅X, L⁆, L⁆ = ⊥) : ⁅X, L⁆ = ⊥ := by
  rw [Subgroup.commutator_comm X L] at h ⊢
  exact Quasisimple.perfect_double_commutator L X h

variable [Finite G]

theorem component_arbitrary_action (L X : Subgroup G)
    (hL : IsComponentOf L ⊤) : L ≤ ⁅L, X⁆ ∨ ⁅L, X⁆ = ⊥ := by
  let A := L ⊔ X
  let N := ⁅L, X⁆
  have hNA : N ≤ A := Subgroup.commutator_le_sup L X
  let : (N.subgroupOf A).Normal := inferInstance
  have hlocal := LocalComponents.normal_contains_or_commutes
    (L.subgroupOf A) (N.subgroupOf A) (LocalComponents.of_overgroup hL le_sup_left)
  rcases hlocal with hcontained | hcommutes
  · left
    intro l hl
    exact hcontained (show (⟨l, (le_sup_left : L ≤ A) hl⟩ : A) ∈ L.subgroupOf A from hl)
  · right
    have hmap := congrArg (Subgroup.map A.subtype) hcommutes
    have hdouble : ⁅L, N⁆ = ⊥ := by
      have hmapL : (L.subgroupOf A).map A.subtype = L :=
        Subgroup.map_subgroupOf_eq_of_le (le_sup_left : L ≤ A)
      have hmapN : (N.subgroupOf A).map A.subtype = N :=
        Subgroup.map_subgroupOf_eq_of_le hNA
      rw [Subgroup.map_commutator, hmapL, hmapN, Subgroup.map_bot] at hmap
      exact hmap
    let : Group.IsPerfect L := ⟨hL.2.2.1⟩
    exact Quasisimple.perfect_double_commutator L X
      (by rwa [Subgroup.commutator_comm N L])

theorem component_normalizing_action (L X : Subgroup G)
    (hL : IsComponentOf L ⊤) (hnormalize : L ≤ Subgroup.normalizer (X : Set G)) :
    (∃ _hLX : L ≤ X, IsComponentOf (L.subgroupOf X) ⊤ ∧
      L ≤ (Layer.subgroup X).map X.subtype ∧
      ((L.subgroupOf X).subgroupOf (Layer.subgroup X)).Normal) ∨ ⁅L, X⁆ = ⊥ := by
  rcases component_arbitrary_action L X hL with hcontained | htrivial
  · left
    have hLX : L ≤ X := hcontained.trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hnormalize)
    have hlocal := LocalComponents.of_overgroup hL hLX
    refine ⟨hLX, hlocal, ?_, Layer.normal_component hlocal⟩
    rw [← Subgroup.map_subgroupOf_eq_of_le hLX]
    exact Subgroup.map_mono (Layer.component_le hlocal)
  · exact Or.inr htrivial

@[expose] def actedComponents (X : Subgroup G) : Set (Subgroup G) :=
  {L | IsComponentOf L ⊤ ∧ ⁅L, X⁆ ≠ ⊥}

@[expose] def actedComponentProduct (X : Subgroup G) : Subgroup G :=
  sSup (actedComponents X)

theorem layer_normalizes_acted_product (X : Subgroup G) :
    Layer.subgroup G ≤ Subgroup.normalizer (actedComponentProduct X : Set G) := by
  have hnormalize : ∀ L : actedComponents X,
      Layer.subgroup G ≤ Subgroup.normalizer (L.val : Set G) := by
    intro L
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Layer.component_le L.property.1)).mp (Layer.normal_component L.property.1)
  change Layer.subgroup G ≤
    Subgroup.normalizer ((sSup (actedComponents X) : Subgroup G) : Set G)
  rw [sSup_eq_iSup']
  exact (le_iInf hnormalize).trans
    (Subgroup.iInf_normalizer_le_normalizer_iSup fun L : actedComponents X => L.val)

theorem actor_normalizes_acted_product (X : Subgroup G) :
    X ≤ Subgroup.normalizer (actedComponentProduct X : Set G) := by
  intro x hx
  let a := MulAut.conj x
  have hX : X.map a.toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (X.le_normalizer hx)
  have hpreserves : ∀ L ∈ actedComponents X, L.map a.toMonoidHom ∈ actedComponents X := by
    intro L hL
    refine ⟨(LocalComponents.equiv_iff a L).mpr hL.1, ?_⟩
    intro hbot
    have hmap : (⁅L, X⁆).map a.toMonoidHom = ⊥ := by
      rw [Subgroup.map_commutator, hX]
      exact hbot
    exact hL.2 ((Subgroup.map_eq_bot_iff_of_injective _ a.injective).mp hmap)
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  apply Subgroup.eq_of_le_of_card_ge
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply sSup_le
    intro L hL
    exact Subgroup.map_le_iff_le_comap.mp (le_sSup (hpreserves L hL))
  · rw [Subgroup.card_map_of_injective a.injective]

theorem layer_arbitrary_action (X : Subgroup G) :
    ⁅Layer.subgroup G, X⁆ = actedComponentProduct X := by
  let I := actedComponentProduct X
  have hEnormalizes := layer_normalizes_acted_product X
  have hXnormalizes := actor_normalizes_acted_product X
  have hE : Layer.subgroup G =
      ⨆ L : {L : Subgroup G // IsComponentOf L ⊤}, L.val := by
    exact sSup_eq_iSup' _
  apply le_antisymm
  · apply Subgroup.commutator_le.mpr
    intro e he x hx
    rw [hE] at he
    induction he using Subgroup.iSup_induction' with
    | hp L e he =>
      by_cases htrivial : ⁅L.val, X⁆ = ⊥
      · have hmem := Subgroup.commutator_mem_commutator he hx
        rw [htrivial, Subgroup.mem_bot] at hmem
        rw [hmem]
        exact I.one_mem
      · have hLI : L.val ≤ I := le_sSup ⟨L.property, htrivial⟩
        exact (Subgroup.le_normalizer_iff_commutator_le_left.mp hXnormalizes)
          ((Subgroup.commutator_mono hLI le_rfl)
            (Subgroup.commutator_mem_commutator he hx))
    | h1 =>
      rw [commutatorElement_one_left]
      exact I.one_mem
    | hmul e f he hf ihe ihf =>
      rw [commutatorElement_mul_left_eq_conj_mul]
      apply I.mul_mem
      · have heE : e ∈ Layer.subgroup G := hE.symm ▸ he
        exact (Subgroup.mem_normalizer_iff.mp (hEnormalizes heE) _).mp ihf
      · exact ihe
  · apply sSup_le
    intro L hL
    have hcontained := (component_arbitrary_action L X hL.1).resolve_right hL.2
    exact hcontained.trans (Subgroup.commutator_mono (Layer.component_le hL.1) le_rfl)

theorem layer_full_central_product :
    Layer.subgroup G = sSup {L : Subgroup G | IsComponentOf L ⊤} ∧
    (∀ L M : Subgroup G, IsComponentOf L ⊤ → IsComponentOf M ⊤ →
      L ≠ M → ⁅L, M⁆ = ⊥) ∧
    Function.Surjective (LayerMultiplication.multiplication G) ∧
    (LayerMultiplication.multiplication G).ker ≤
      Subgroup.center ((L : SemisimpleComponentStructure.ComponentIndex G) → L.val) ∧
    (∀ L : Subgroup G, IsComponentOf L ⊤ → (L.subgroupOf (Layer.subgroup G)).Normal) := by
  exact ⟨rfl, fun L M hL hM hne => LocalComponents.commute_of_ne L M hL hM hne,
    LayerMultiplication.surjective G, LayerMultiplication.kernel_le_center G,
    fun _ hL => Layer.normal_component hL⟩

theorem lemma_2_1 :
    (Layer.subgroup G = sSup {L : Subgroup G | IsComponentOf L ⊤} ∧
      (∀ L M : Subgroup G, IsComponentOf L ⊤ → IsComponentOf M ⊤ →
        L ≠ M → ⁅L, M⁆ = ⊥) ∧
      Function.Surjective (LayerMultiplication.multiplication G) ∧
      (LayerMultiplication.multiplication G).ker ≤
        Subgroup.center ((L : SemisimpleComponentStructure.ComponentIndex G) → L.val) ∧
      (∀ L : Subgroup G, IsComponentOf L ⊤ → (L.subgroupOf (Layer.subgroup G)).Normal)) ∧
    (∀ (L X : Subgroup G), IsComponentOf L ⊤ →
      (L ≤ ⁅L, X⁆ ∨ ⁅L, X⁆ = ⊥) ∧
      (L ≤ Subgroup.normalizer (X : Set G) →
        (∃ _hLX : L ≤ X, IsComponentOf (L.subgroupOf X) ⊤ ∧
          L ≤ (Layer.subgroup X).map X.subtype ∧
          ((L.subgroupOf X).subgroupOf (Layer.subgroup X)).Normal) ∨ ⁅L, X⁆ = ⊥)) ∧
    (∀ X : Subgroup G, ⁅Layer.subgroup G, X⁆ =
      sSup {L : Subgroup G | IsComponentOf L ⊤ ∧ ⁅L, X⁆ ≠ ⊥}) := by
  exact ⟨layer_full_central_product, fun L X hL =>
    ⟨component_arbitrary_action L X hL, component_normalizing_action L X hL⟩,
    layer_arbitrary_action⟩

end CFSG.ComponentClassification.AschbacherComponentAction
