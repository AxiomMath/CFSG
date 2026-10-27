module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.Facts27
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.TransportFacts2

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.S25

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

theorem HaradaFacts27.of_mulEquiv {H K : Type} [Group H] [Group K] (e : H ≃* K)
    {E : Subgroup H} {E' : Subgroup K} (hE : E.map e.toMonoidHom = E') {a z b z₁ : H}
    {S T T' W0 : Subgroup H} {ι : Elem2 6 →* H} {zv : V6} {R0 F : Subgroup H}
    (h : HaradaFacts27 H E a z b z₁ S T T' W0 ι zv R0 F) :
    HaradaFacts27 K E' (e a) (e z) (e b) (e z₁) (S.map e.toMonoidHom) (T.map e.toMonoidHom)
      (T'.map e.toMonoidHom) (W0.map e.toMonoidHom) (e.toMonoidHom.comp ι) zv
      (R0.map e.toMonoidHom) (F.map e.toMonoidHom) := by
  refine { toHaradaFacts2 := HaradaModel.HaradaFacts2.of_mulEquiv e hE h.toHaradaFacts2
           C_hom := ?_ }
  obtain ⟨ψ, hψ, hker⟩ := h.C_hom
  refine ⟨ψ.comp (TwoHSData.centralizerMulEquiv e z).symm.toMonoidHom,
    hψ.comp (TwoHSData.centralizerMulEquiv e z).symm.surjective, ?_⟩
  ext c
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker,
    Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact Subgroup.mem_map_equiv.symm

end CFSG.EvenSporadicStandard.HNRecog.Harada.S25
