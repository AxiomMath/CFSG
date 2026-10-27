module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Facts

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup

structure E32FactsX (Y : Type) [Group Y] (S : Subgroup (MulAut Y)) (F : Subgroup Y)
    (J : Subgroup (MulAut Y)) : Prop extends E32Facts Y S F J where
  exists_x : ∃ x ∈ J, x ∉ innerImage Y ⊤ ∧ Nat.card {v : Y // v ∈ F ∧ x v = v} = 4

variable {X Y : Type} [Group X] [Group Y]

theorem E32FactsX.map' (e : X ≃* Y) {S : Subgroup (MulAut X)} {F : Subgroup X}
    {J : Subgroup (MulAut X)} (h : E32FactsX X S F J) :
    E32FactsX Y (S.map (MulAut.congr e).toMonoidHom) (F.map e.toMonoidHom)
      (J.map (MulAut.congr e).toMonoidHom) := by
  refine ⟨h.toE32Facts.map' e (MulAut.congr e) (congr_conj e), ?_⟩
  obtain ⟨x, hxJ, hxin, hxc⟩ := h.exists_x
  refine ⟨MulAut.congr e x, ⟨x, hxJ, rfl⟩, ?_, ?_⟩
  · intro hin
    apply hxin
    have h1 : (MulAut.congr e) x ∈ (innerImage X ⊤).map (MulAut.congr e).toMonoidHom := by
      rw [innerImage_map' e (MulAut.congr e) (congr_conj e),
        Subgroup.map_top_of_surjective _ e.surjective]
      exact hin
    obtain ⟨α, hα, hαx⟩ := h1
    have : α = x := (MulAut.congr e).injective hαx
    rwa [this] at hα
  · rw [← hxc]
    refine (Nat.card_congr (e.toEquiv.subtypeEquiv fun v => ?_)).symm
    show (v ∈ F ∧ x v = v) ↔ (e v ∈ F.map e.toMonoidHom ∧ MulAut.congr e x (e v) = e v)
    rw [congr_apply_mk, e.injective.eq_iff, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem isoInv3_e32x :
    IsoInv3 (fun Y _ S F => ∃ J : Subgroup (MulAut Y), E32FactsX Y S F J) := by
  intro X Y _ _ e S F ⟨J, hJ⟩
  exact ⟨J.map (MulAut.congr e).toMonoidHom, hJ.map' e⟩

end CFSG.EvenSporadicStandard.M22Std
