module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RY0A

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

@[expose] def S16F1 (X : Type*) [Group X] : Prop :=
  ∀ r : MulAut X, r * r = 1 → ¬ IsInnerAut r →
    ∃ V0 : Subgroup X, V0 ≤ fixedSub r ∧ Nonempty (↥V0 ≃* DihedralGroup 8) ∧
      ∃ m : ℕ, Odd m ∧ Nat.card ↥(fixedSub r) = 16 * m

theorem S16F1.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (h : S16F1 X) :
    S16F1 Y := by
  intro r hr2 hrinn
  set r' : MulAut X := MulAut.congr e.symm r with hr'
  have hr'2 : r' * r' = 1 := by rw [hr', ← map_mul, hr2, map_one]
  have hrinn' : ¬ IsInnerAut r' := by
    intro hin
    apply hrinn
    have h1 := hin.congr e
    have e1 : MulAut.congr e (MulAut.congr e.symm r) = r := by
      ext w
      simp [MulAut.congr_apply]
    rwa [hr', e1] at h1
  obtain ⟨V0, hV0, ⟨eV⟩, m, hm, hcard⟩ := h r' hr'2 hrinn'
  have hfix : fixedSub r = (fixedSub r').map e.toMonoidHom := by
    rw [map_fixedSub_of_equiv, hr']
    have e1 : MulAut.congr e (MulAut.congr e.symm r) = r := by
      ext w
      simp [MulAut.congr_apply]
    rw [e1]
  refine ⟨V0.map e.toMonoidHom, ?_, ⟨(V0.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eV⟩,
    m, hm, ?_⟩
  · rw [hfix]
    exact Subgroup.map_mono hV0
  · rw [hfix, Subgroup.card_map_of_injective e.injective]
    exact hcard

end CFSG.EvenSporadicStandard.Fin76b
