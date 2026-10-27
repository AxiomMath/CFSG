module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.ModFacts
public import CFSG.Sporadic.Mathieu.M23
public import CFSG.Sporadic.Schreier.Outer
public import Certificates.Data.CFSGNative.SporadicSchreier.Count

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Wong77.Module

open CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

theorem exists_image_eq_of_card_eq
    (s t : Finset (Fin 23)) (hst : s.card = t.card) (hs : s.card ≤ 3) :
    ∃ g : NativeSporadic.Carrier .M23, s.image (permOf g) = t := by
  have h4 : MulAction.IsMultiplyPretransitive CFSG.M23.M23Group.H0 (Fin 23) 4 :=
    CFSG.M23.M23Group.four_pretransitive
  have hk : MulAction.IsMultiplyPretransitive CFSG.M23.M23Group.H0 (Fin 23) s.card :=
    MulAction.isMultiplyPretransitive_of_le (m := s.card) (n := 4) (by omega) (by simp)
  obtain ⟨g, hg⟩ := MulAction.isMultiplyPretransitive_iff.1 hk
    (s.orderEmbOfFin rfl).toEmbedding (t.orderEmbOfFin hst.symm).toEmbedding
  refine ⟨⟨g.1, by rw [CFSG.Sporadic.Mathieu.nativeM23_eq]; exact g.2⟩, ?_⟩
  rw [← Finset.coe_inj, Finset.coe_image, ← Finset.range_orderEmbOfFin s rfl,
    ← Finset.range_orderEmbOfFin t hst.symm, ← Set.range_comp]
  congr 1
  funext i
  exact congrArg (fun f : Fin s.card ↪ Fin 23 => f i) hg

end CFSG.EvenSporadicStandard.Wong77.Module
