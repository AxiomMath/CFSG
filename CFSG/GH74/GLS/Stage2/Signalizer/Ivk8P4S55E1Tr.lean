module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4QuadOdd
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup

@[expose] def E1Core (r : ℕ) (Y : Type) [Group Y] : Prop :=
  ∀ b : MulAut Y, b ≠ 1 → ¬ r ∣ orderOf b →
    (∀ E : Subgroup Y, IsPGroup r ↥E → (∀ x ∈ E, b x ∈ E) → ∀ x ∈ E, b x = x) →
    ∀ E : Subgroup Y, IsPGroup r ↥E → (∀ x ∈ E, b x ∈ E) → E = ⊥

theorem E1Core.of_mulEquiv {r : ℕ} {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : E1Core r Y') : E1Core r Y := by
  intro b hb1 hbr hHH E hE hinv
  set b' : MulAut Y' := MulAut.congr e b with hb'
  have hb'apply : ∀ y : Y', b' y = e (b (e.symm y)) := fun y => rfl
  have hb'1 : b' ≠ 1 := fun h1 => hb1 ((map_eq_one_iff _ (MulAut.congr e).injective).mp h1)
  have hbr' : ¬ r ∣ orderOf b' := by
    rw [hb', MulEquiv.orderOf_eq (MulAut.congr e) b]
    exact hbr
  have key : ∀ E' : Subgroup Y', IsPGroup r ↥E' → (∀ x ∈ E', b' x ∈ E') →
      ∀ x ∈ E', b' x = x := by
    intro E' hE' hinv' y' hy'
    have hE : IsPGroup r ↥(E'.map e.symm.toMonoidHom) := hE'.map _
    have hinvE : ∀ x ∈ E'.map e.symm.toMonoidHom, b x ∈ E'.map e.symm.toMonoidHom := by
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨b' z, hinv' z hz, ?_⟩
      simp [hb'apply]
    have := hHH _ hE hinvE (e.symm y') ⟨y', hy', rfl⟩
    rw [hb'apply, this]
    simp
  have hbot := h b' hb'1 hbr' key (E.map e.toMonoidHom) (hE.map _) (by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨b z, hinv z hz, by simp [hb'apply]⟩)
  exact (Subgroup.map_eq_bot_iff_of_injective E e.injective).mp hbot

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
