module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUFieldDef
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftU38Map
public import Certificates.Certificate9690

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField

open CFSG.AGLEmbedding.ChevOuter CFSG.AGLEmbedding.ChevOuter.U38
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

theorem subfieldDiagGen_eight
    {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) (K₀ : Subfield K)
    (hK₀ : Nat.card K₀ = 4) : SubfieldDiagGen h K₀ := by
  intro H hH₀ hHd
  have hfin : Finite K := h.finite
  let _ : Fintype K := Fintype.ofFinite K
  obtain ⟨e⟩ : Nonempty (K ≃+* GF64) := ⟨FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, h.card, GF64.card_eq]
    norm_num)⟩
  refine eq_top_of_closure_eq_top (suMap h hU e.toRingHom) (suMap_injective h hU e.toRingHom)
    Certificates.certificate9690 ?_
  rintro s ⟨k, hk, hsk⟩
  refine ⟨suMap hU h e.symm.toRingHom s, ?_, suMap_suMap h hU e s⟩
  have hcoe : (((suMap hU h e.symm.toRingHom s : unitarySU 2 3 K 3) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = (toMat3 (Eight.z8Gen.gens.getD k #[])).map e.symm := by
    rw [coe_suMap, hsk]
    rfl
  have hk2 : k < 2 := hk
  interval_cases k
  · refine hH₀ _ fun i j => ?_
    rw [hcoe, Matrix.map_apply]
    refine mem_subfield_of_pow_four K₀ hK₀ ?_
    rw [← map_pow]
    congr 1
    fin_cases i <;> fin_cases j <;> decide +kernel
  · refine hHd _ ?_
    intro i j hij
    rw [hcoe, Matrix.map_apply]
    have h0 : toMat3 (Eight.z8Gen.gens.getD 1 #[]) i j = 0 := by
      fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide +kernel
    rw [h0, map_zero]

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField
