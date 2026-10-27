module

public import CFSG.Sporadic.Bridge.M11
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.EvenSporadicStandard.HNRecog.TwoHSData

open Subgroup

section Cert


theorem nonempty_mulEquiv_native_m11 {X : Type*} [Group X] {α β : X}
    (hcard : Nat.card X = 7920) (hgen : closure ({α, β} : Set X) = ⊤)
    (hrel : ∀ w ∈ TauCeti.Sporadic.m11Presentation.relatorLetters,
      CFSG.Sporadic.Bridge.wordProd (fun i => if i = 0 then α else if i = 1 then β else 1) w = 1) :
    Nonempty (X ≃* ↥CFSG.Blueprint.NativeSporadic.M11) := by
  obtain ⟨hfin, hcardP⟩ := CFSG.Sporadic.Bridge.M11.finite_card_le
  set img : ℕ → X := fun i => if i = 0 then α else if i = 1 then β else 1 with himg
  set φ : TauCeti.Sporadic.m11Presentation.Group →* X :=
    CFSG.Sporadic.Bridge.presHom _ img hrel with hφ
  have hsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, closure_le]
    intro x hx
    rcases Set.mem_insert_iff.1 hx with rfl | hx
    · refine ⟨CFSG.Sporadic.Bridge.presGen _ 0, ?_⟩
      rw [hφ, CFSG.Sporadic.Bridge.presHom_presGen _ img hrel
        (by rw [CFSG.Sporadic.Bridge.M11.generatorCount_eq]; decide)]
      simp [himg]
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      refine ⟨CFSG.Sporadic.Bridge.presGen _ 1, ?_⟩
      rw [hφ, CFSG.Sporadic.Bridge.presHom_presGen _ img hrel
        (by rw [CFSG.Sporadic.Bridge.M11.generatorCount_eq]; decide)]
      simp [himg]
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.nonempty_mulEquiv_of_surjective φ hsurj hcardP hcard.ge
  obtain ⟨e'⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  exact ⟨e.trans e'.symm⟩

end Cert

end CFSG.EvenSporadicStandard.HNRecog.TwoHSData
