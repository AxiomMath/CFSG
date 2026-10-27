module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.YComponents

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup CFSG.Open CFSG.ComponentClassification

theorem card_sup_of_commute_of_inf_eq_bot {Y : Type*} [Group Y] [Finite Y] {A B : Subgroup Y}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hdisj : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have hcomm' : ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) :=
    fun a b => hcomm a a.2 b b.2
  let φ : A × B →* Y := MonoidHom.noncommCoprod A.subtype B.subtype hcomm'
  have hrange : φ.range = A ⊔ B := by
    change (MonoidHom.noncommCoprod A.subtype B.subtype hcomm').range = A ⊔ B
    rw [MonoidHom.noncommCoprod_range A.subtype B.subtype hcomm', Subgroup.range_subtype,
      Subgroup.range_subtype]
  have hinj : Function.Injective φ := by
    change Function.Injective (MonoidHom.noncommCoprod A.subtype B.subtype hcomm')
    rw [MonoidHom.noncommCoprod_injective A.subtype B.subtype hcomm', Subgroup.range_subtype,
      Subgroup.range_subtype]
    exact ⟨A.subtype_injective, B.subtype_injective, disjoint_iff_inf_le.mpr (le_of_eq hdisj)⟩
  calc Nat.card ↥(A ⊔ B) = Nat.card ↥φ.range := by rw [hrange]
    _ = Nat.card (A × B) := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod _ _

theorem card_sup_pair {Y : Type*} [Group Y] [Finite Y] (hfree : SolvableRadical.Free Y)
    {A B : Subgroup Y} (hA : IsComponentOf A ⊤) (hB : IsComponentOf B ⊤) (hne : A ≠ B) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B :=
  card_sup_of_commute_of_inf_eq_bot (component_commute_of_ne hA hB hne)
    (component_inf_eq_bot hfree hA hB hne)

theorem card_sup_three {Y : Type*} [Group Y] [Finite Y] (hfree : SolvableRadical.Free Y)
    {A B C : Subgroup Y} (hA : IsComponentOf A ⊤) (hB : IsComponentOf B ⊤)
    (hC : IsComponentOf C ⊤) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    Nat.card ↥(A ⊔ B ⊔ C) = Nat.card A * Nat.card B * Nat.card C := by
  have hcommAC := component_commute_of_ne hA hC hAC
  have hcommBC := component_commute_of_ne hB hC hBC
  have hA_le : A ≤ Subgroup.centralizer (C : Set Y) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    exact fun c hc => (hcommAC a ha c hc).symm
  have hB_le : B ≤ Subgroup.centralizer (C : Set Y) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    exact fun c hc => (hcommBC b hb c hc).symm
  have hcommSup : ∀ x ∈ A ⊔ B, ∀ c ∈ C, x * c = c * x := by
    intro x hx c hc
    exact ((Subgroup.mem_centralizer_iff.mp ((sup_le hA_le hB_le) hx)) c hc).symm
  have hdisj : (A ⊔ B) ⊓ C = ⊥ := by
    rw [inf_comm]
    exact component_inf_sup_eq_bot hfree hC hA hB hAC.symm hBC.symm
  have h1 : Nat.card ↥((A ⊔ B) ⊔ C) = Nat.card ↥(A ⊔ B) * Nat.card C :=
    card_sup_of_commute_of_inf_eq_bot hcommSup hdisj
  rw [h1, card_sup_pair hfree hA hB hAB]

theorem isComponentOf_map_conj {Y : Type*} [Group Y] {C : Subgroup Y} (hC : IsComponentOf C ⊤)
    (y : Y) : IsComponentOf (C.map (MulAut.conj y).toMonoidHom) ⊤ :=
  (LocalComponents.equiv_iff (MulAut.conj y) C).mpr hC

theorem layer_eq_sup_of_two {Y : Type*} [Group Y] {T₁ T₂ : Subgroup Y}
    (hT₂ : IsComponentOf T₂ ⊤) (hT₁ : IsComponentOf T₁ ⊤)
    (hall : ∀ C : Subgroup Y, IsComponentOf C ⊤ → C = T₁ ∨ C = T₂) :
    Layer.subgroup Y = T₁ ⊔ T₂ := by
  have hset : {C : Subgroup Y | IsComponentOf C ⊤} = {T₁, T₂} := by
    ext C
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hC
      exact hall C hC
    · rintro (rfl | rfl)
      · exact hT₁
      · exact hT₂
  rw [Layer.subgroup.eq_sSup, hset, sSup_pair]

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
