module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Map
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Perm

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem y4a_conj_data {G : Type} [Group G] (g : G) {x w : G}
    (h5 : IsElemTwo 5 (Qz w ⊓ Gx x))
    (hM : CFSG.Open.pCoreOf 2 (derivedOf (Gxy x w)) = Qz w ⊓ Qz (x * w))
    (h4 : IsElemTwo 4 (Qz w ⊓ Qz (x * w))) :
    IsElemTwo 5 (Qz (g * w * g⁻¹) ⊓ Gx (g * x * g⁻¹)) ∧
      CFSG.Open.pCoreOf 2 (derivedOf (Gxy (g * x * g⁻¹) (g * w * g⁻¹))) =
        Qz (g * w * g⁻¹) ⊓ Qz (g * x * g⁻¹ * (g * w * g⁻¹)) ∧
      IsElemTwo 4 (Qz (g * w * g⁻¹) ⊓ Qz (g * x * g⁻¹ * (g * w * g⁻¹))) := by
  set f : G →* G := (MulAut.conj g).toMonoidHom with hf_def
  have hf : Function.Injective f := (MulAut.conj g).injective
  have hfc : ∀ c : G, f c = g * c * g⁻¹ := fun c => MulAut.conj_apply g c
  have hrange : f.range = ⊤ := MonoidHom.range_eq_top.mpr (MulAut.conj g).surjective
  have hGx : ∀ c : G, (Gx c).map f = Gx (g * c * g⁻¹) := by
    intro c
    rw [map_Gx_of_injective hf, hrange, inf_top_eq, hfc]
  have hQz : ∀ c : G, (Qz c).map f = Qz (g * c * g⁻¹) := by
    intro c
    show (CFSG.Open.pCoreOf 2 (Gx c)).map f = CFSG.Open.pCoreOf 2 (Gx (g * c * g⁻¹))
    rw [← pCoreOf_map_of_injective hf, hGx]
  have hGxy : (Gxy x w).map f = Gxy (g * x * g⁻¹) (g * w * g⁻¹) := by
    rw [Gxy_eq_inf, Gxy_eq_inf, Subgroup.map_inf_eq _ _ f hf, hGx, hGx]
  have hmul : g * x * g⁻¹ * (g * w * g⁻¹) = g * (x * w) * g⁻¹ := by group
  have hQ5 : (Qz w ⊓ Gx x).map f = Qz (g * w * g⁻¹) ⊓ Gx (g * x * g⁻¹) := by
    rw [Subgroup.map_inf_eq _ _ f hf, hQz, hGx]
  have hQ4 : (Qz w ⊓ Qz (x * w)).map f =
      Qz (g * w * g⁻¹) ⊓ Qz (g * x * g⁻¹ * (g * w * g⁻¹)) := by
    rw [Subgroup.map_inf_eq _ _ f hf, hQz, hQz, hmul]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hQ5]
    exact isElemTwo_map f hf h5
  · rw [← hGxy, derivedOf_map_of_injective hf, pCoreOf_map_of_injective hf, hM, hQ4]
  · rw [← hQ4]
    exact isElemTwo_map f hf h4

end CFSG.EvenSporadicStandard.HNRecog.Section3
