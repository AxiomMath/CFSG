module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.TransportAbs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.OfMulEquiv
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.Facts

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open Subgroup CFSG.EvenSporadicStandard.TwoHS CFSG.EvenSporadicStandard.HNRecog.TwoHSData

variable {H K : Type} [Group H] [Group K]

theorem HaradaFacts.of_mulEquiv (e : H ≃* K) {E : Subgroup H} {E' : Subgroup K}
    (hE : E.map e.toMonoidHom = E') {a z b z₁ : H} {S T T' W0 : Subgroup H}
    {ι : Elem2 6 →* H} (h : HaradaFacts H E a z b z₁ S T T' W0 ι) :
    HaradaFacts K E' (e a) (e z) (e b) (e z₁) (S.map e.toMonoidHom) (T.map e.toMonoidHom)
      (T'.map e.toMonoidHom) (W0.map e.toMonoidHom) (e.toMonoidHom.comp ι) := by
  subst hE
  exact
    { toTwoHSFacts := TwoHSFacts.of_mulEquiv e h.toTwoHSFacts
      harCore := harCoreData_of_mulEquiv e h.harCore
      isPGroup_S := isPGroup_map_mulEquiv e h.isPGroup_S
      card_S := (card_map_mulEquiv e S).trans h.card_S
      injective_ι := e.injective.comp h.injective_ι
      ι_tv := by rw [MonoidHom.comp_apply, h.ι_tv]; rfl
      coords_z := by
        obtain ⟨v, hv, hl, hq⟩ := h.coords_z
        exact ⟨v, by rw [MonoidHom.comp_apply, hv]; rfl, hl, hq⟩
      coords_b := by
        obtain ⟨v, hv, hl, hq⟩ := h.coords_b
        exact ⟨v, by rw [MonoidHom.comp_apply, hv]; rfl, hl, hq⟩
      coords_z₁ := by
        obtain ⟨v, hv, hl, hq⟩ := h.coords_z₁
        exact ⟨v, by rw [MonoidHom.comp_apply, hv]; rfl, hl, hq⟩
      mem_E_iff := fun v => by
        rw [MonoidHom.comp_apply]
        exact (mem_map_iff e E _).trans (h.mem_E_iff v)
      conj_E64 := by
        rw [range_comp_mulEquiv]
        exact conj_E64_map e h.conj_E64
      centralizer_le := by
        rw [range_comp_mulEquiv]
        exact centralizer_map_le e h.centralizer_le
      card_normalizer := by
        rw [range_comp_mulEquiv, card_normalizer_map]
        exact h.card_normalizer
      fuse := fun v w hv0 hvt hw0 hwt hl hq => by
        obtain ⟨n, hn, hnvw⟩ := h.fuse v w hv0 hvt hw0 hwt hl hq
        rw [range_comp_mulEquiv]
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
        exact fuse_map e ι.range ⟨n, hn, hnvw⟩ }

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
