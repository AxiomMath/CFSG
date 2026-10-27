module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaMain
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDSetting

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup

structure HypC₂ {G : Type*} [Group G] (d : Data G) : Prop where
  C₂_pGroup : IsPGroup 2 d.C₂
  C₂_le : d.C₂ ≤ normalizer (d.withT d.A₂ : Set G)
  C₂_normal : normalizer (d.withT d.A₂ : Set G) ≤ normalizer (d.C₂ : Set G)
  C₂_le_cent : d.C₂ ≤ centralizer (d.A₂ : Set G)
  C₂_inf_H : d.C₂ ⊓ d.H = d.withT d.A₂
  C₂_conj : ∀ a ∈ d.A₂, ∃ c ∈ d.C₂, c⁻¹ * d.t * c = a * d.t
  C₂_max : normalizer (d.withT d.A₂ : Set G) ⊓ centralizer (d.A₂ : Set G) ≤ d.C₂

section Setting

theorem HypC₂.of_setting {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {D : ToddParabolic L} {t : G} (h : Yamada.Setting G L D t) {d : Data G} (ht : d.t = t)
    (hA : d.A₂ = Yamada.toddA D) (hC : d.C₂ = Yamada.yamadaC2 D t) : HypC₂ d := by
  have hE : d.withT d.A₂ = Yamada.toddE D t := by
    rw [Data.withT, hA, ht]
    rfl
  have hCeq := h.yamadaC2_eq h.omegaSet_eq
    (h.exists_mem_centralizer_toddA_not_comm h.omegaSet_eq)
  obtain ⟨-, hCH, -, -, -, hconj, -⟩ := h.yamada_4_3
  have htt : t * t = 1 := by rw [← sq, h.t_sq]
  refine
    { C₂_pGroup := hC ▸ Yamada.isPGroup_yamadaC2
      C₂_le := by rw [hC, hE]; exact Yamada.yamadaC2_le
      C₂_normal := by
        rw [hC, hE]
        exact fun x hx => mem_normalizer_of_conj_mem fun c hc => Yamada.conj_mem_yamadaC2 hx hc
      C₂_le_cent := by
        rw [hC, hA, hCeq]
        exact inf_le_right
      C₂_inf_H := by
        rw [hE, hC, inf_comm, Data.H, ht]
        exact hCH
      C₂_conj := by
        intro a ha
        rw [hA] at ha
        obtain ⟨c, hc, hct⟩ := hconj a ha
        refine ⟨c⁻¹, hC ▸ inv_mem hc, ?_⟩
        rw [ht, inv_inv]
        calc c * t * c⁻¹ = (c * t * c⁻¹ * t) * t := by rw [mul_assoc _ t t, htt, mul_one]
          _ = a * t := by rw [hct]
      C₂_max := by
        rw [hE, hA, hC, hCeq] }

end Setting

end CFSG.EvenSmallLie.UnitarySix.YamadaD
