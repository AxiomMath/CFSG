module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.NoSL29Criterion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.InvolutionCentralizers

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan

open Subgroup CFSG.Blueprint.NativeSporadic

theorem noSL29_of_isSporadic_m22
    {N : Type} [Group N] [Finite N] (hN : IsSporadic N .M22)
    (K : Type) [Group K] [Finite K] (hK : commutator K = ⊤) (hZ : Nat.card (center K) = 2)
    (hA : Nonempty (K ⧸ center K ≃* alternatingGroup (Fin 6))) (f : K →* N)
    (hf : Function.Injective f) : False := by
  have hN' : NoPerfect720Centralizing N := by
    refine noPerfect720Centralizing_of_forall (fun z hz => Or.inl ?_)
    rw [card_centralizer_of_involution_of_isSporadic_m22 hN z hz]
    norm_num
  exact false_of_injective_of_noPerfect720Centralizing hN' K hK hZ hA f hf

theorem noSL29_of_isSporadic_m23
    {N : Type} [Group N] [Finite N] (hN : IsSporadic N .M23)
    (K : Type) [Group K] [Finite K] (hK : commutator K = ⊤) (hZ : Nat.card (center K) = 2)
    (hA : Nonempty (K ⧸ center K ≃* alternatingGroup (Fin 6))) (f : K →* N)
    (hf : Function.Injective f) : False := by
  have hN' : NoPerfect720Centralizing N := by
    refine noPerfect720Centralizing_of_forall (fun z hz => Or.inl ?_)
    rw [card_centralizer_of_involution_of_isSporadic_m23 hN z hz]
    norm_num
  exact false_of_injective_of_noPerfect720Centralizing hN' K hK hZ hA f hf

theorem noSL29_of_isSporadic_m24
    {N : Type} [Group N] [Finite N] (hN : IsSporadic N .M24)
    (K : Type) [Group K] [Finite K] (hK : commutator K = ⊤) (hZ : Nat.card (center K) = 2)
    (hA : Nonempty (K ⧸ center K ≃* alternatingGroup (Fin 6))) (f : K →* N)
    (hf : Function.Injective f) : False := by
  have hN' : NoPerfect720Centralizing N := by
    refine noPerfect720Centralizing_of_forall (fun z hz => Or.inl ?_)
    rcases card_centralizer_of_involution_of_isSporadic_m24 hN z hz with h | h <;>
      (rw [h]; norm_num)
  exact false_of_injective_of_noPerfect720Centralizing hN' K hK hZ hA f hf

theorem noSL29_of_isSporadic_j2
    {N : Type} [Group N] [Finite N] (hN : IsSporadic N .J2)
    (K : Type) [Group K] [Finite K] (hK : commutator K = ⊤) (hZ : Nat.card (center K) = 2)
    (hA : Nonempty (K ⧸ center K ≃* alternatingGroup (Fin 6))) (f : K →* N)
    (hf : Function.Injective f) : False := by
  have hN' : NoPerfect720Centralizing N := by
    refine noPerfect720Centralizing_of_forall (fun z hz => Or.inl ?_)
    rcases card_centralizer_of_involution_of_isSporadic_j2 hN z hz with h | h <;>
      (rw [h]; norm_num)
  exact false_of_injective_of_noPerfect720Centralizing hN' K hK hZ hA f hf

theorem noSL29_of_isSporadic_ru
    {N : Type} [Group N] [Finite N] (hN : IsSporadic N .Ru)
    (K : Type) [Group K] [Finite K] (hK : commutator K = ⊤) (hZ : Nat.card (center K) = 2)
    (hA : Nonempty (K ⧸ center K ≃* alternatingGroup (Fin 6))) (f : K →* N)
    (hf : Function.Injective f) : False := by
  have hN' : NoPerfect720Centralizing N := by
    refine noPerfect720Centralizing_of_forall (fun z hz => Or.inl ?_)
    rcases card_centralizer_of_involution_of_isSporadic_ru hN z hz with h | h <;>
      (rw [h]; norm_num)
  exact false_of_injective_of_noPerfect720Centralizing hN' K hK hZ hA f hf

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan
