module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34Small
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableDefs

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section M22Row


theorem sporadic_rows_m22 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .M22)
    {σ : MulAut S} (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range →
        SporadicInnerRow .M22 (Nat.card (D ⧸ center D))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        SporadicOuterRow .M22 (Nat.card (D ⧸ center D))) := by
  exact ⟨fun _ hc => SeitzReduction.SporadicRefine.m22_false_of_l34 hS hna e hσ hD hc,
    fun _ hc => SeitzReduction.SporadicRefine.m22_false_of_l34 hS hna e hσ hD hc⟩

end M22Row

section M23Row


theorem sporadic_rows_m23 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .M23)
    {σ : MulAut S} (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range →
        SporadicInnerRow .M23 (Nat.card (D ⧸ center D))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        SporadicOuterRow .M23 (Nat.card (D ⧸ center D))) := by
  exact ⟨fun _ hc => SeitzReduction.SporadicRefine.m23_false_of_l34 hS hna e hσ hD hc,
    fun _ hc => SeitzReduction.SporadicRefine.m23_false_of_l34 hS hna e hσ hD hc⟩

end M23Row

section M24Row


theorem sporadic_rows_m24 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .M24)
    {σ : MulAut S} (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range →
        SporadicInnerRow .M24 (Nat.card (D ⧸ center D))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        SporadicOuterRow .M24 (Nat.card (D ⧸ center D))) := by
  exact ⟨fun _ hc => SeitzReduction.SporadicRefine.m24_false_of_l34 hS hna e hσ hD hc,
    fun _ hc => SeitzReduction.SporadicRefine.m24_false_of_l34 hS hna e hσ hD hc⟩

end M24Row

section J2Row


theorem sporadic_rows_j2 {S : Type} [Group S] [Finite S] (_hS : IsSimpleGroup S)
    (_hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .J2)
    {σ : MulAut S} (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)}
    (_hD : IsComponent D) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range →
        SporadicInnerRow .J2 (Nat.card (D ⧸ center D))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        SporadicOuterRow .J2 (Nat.card (D ⧸ center D))) := by
  exact ⟨fun _ hc => SeitzReduction.SporadicRefine.j2_false_of_l34 e hσ hc,
    fun _ hc => SeitzReduction.SporadicRefine.j2_false_of_l34 e hσ hc⟩

end J2Row

section M11Row

theorem sporadic_rows_m11 {S : Type} [Group S] [Finite S] (_hS : IsSimpleGroup S)
    (_hna : ∃ a b : S, a * b ≠ b * a) (_e : S ≃* NativeSporadic.Carrier .M11)
    {σ : MulAut S} (_hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)}
    (_hD : IsComponent D) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range →
        SporadicInnerRow .M11 (Nat.card (D ⧸ center D))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        SporadicOuterRow .M11 (Nat.card (D ⧸ center D))) := by
  exact ⟨fun _ => trivial, fun _ => trivial⟩

end M11Row

section M12Row

theorem sporadic_rows_m12 {S : Type} [Group S] [Finite S] (_hS : IsSimpleGroup S)
    (_hna : ∃ a b : S, a * b ≠ b * a) (_e : S ≃* NativeSporadic.Carrier .M12)
    {σ : MulAut S} (_hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)}
    (_hD : IsComponent D) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range →
        SporadicInnerRow .M12 (Nat.card (D ⧸ center D))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        SporadicOuterRow .M12 (Nat.card (D ⧸ center D))) := by
  exact ⟨fun _ => trivial, fun _ => trivial⟩

end M12Row

section J1Row

theorem sporadic_rows_j1 {S : Type} [Group S] [Finite S] (_hS : IsSimpleGroup S)
    (_hna : ∃ a b : S, a * b ≠ b * a) (_e : S ≃* NativeSporadic.Carrier .J1)
    {σ : MulAut S} (_hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)}
    (_hD : IsComponent D) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range →
        SporadicInnerRow .J1 (Nat.card (D ⧸ center D))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        SporadicOuterRow .J1 (Nat.card (D ⧸ center D))) := by
  exact ⟨fun _ => trivial, fun _ => trivial⟩

end J1Row

section J3Row

theorem sporadic_rows_j3 {S : Type} [Group S] [Finite S] (_hS : IsSimpleGroup S)
    (_hna : ∃ a b : S, a * b ≠ b * a) (_e : S ≃* NativeSporadic.Carrier .J3)
    {σ : MulAut S} (_hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)}
    (_hD : IsComponent D) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range →
        SporadicInnerRow .J3 (Nat.card (D ⧸ center D))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        SporadicOuterRow .J3 (Nat.card (D ⧸ center D))) := by
  exact ⟨fun _ => trivial, fun _ => trivial⟩

end J3Row

end CFSG.ComponentClassification.CatFC
