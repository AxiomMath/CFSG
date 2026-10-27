module

public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110m
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.OmegaFacts
import CFSG.LocalAnalysis.GLTheoremA.S3.Basic

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.GLTheoremB.MovingAround

theorem exists_not_isCyclic_of_statedClassicalModel_pOmegaPlus_four_two {W : Type} [Group W]
    (hW : CFSG.Open.StatedClassicalModel W .POmegaPlus 4 2 1) :
    ∃ E : Subgroup W, IsPGroup 3 E ∧ ¬ IsCyclic ↥E := by
  obtain ⟨e⟩ := Claims1110m.nonempty_equiv_omegaPlus_of_model_d4cls hW
  haveI : Finite W := Finite.of_injective e.toEquiv.toFun e.toEquiv.injective
  have hR : OmegaFacts.Rank2 (⊤ : Subgroup ↥(StatedOmega (StatedQuadPlus 4 (ZMod 2)))) :=
    OmegaFacts.rank2_top_of_subgroup (OmegaFacts.rank2_plus 3 (by norm_num))
  have hR' : OmegaFacts.Rank2 (⊤ : Subgroup W) :=
    OmegaFacts.Rank2.map e.symm.toMonoidHom e.symm.injective (fun _ _ => Subgroup.mem_top _) hR
  obtain ⟨E, k, hEel, hk, hk2⟩ := OmegaFacts.exists_elemAbelian_three_pow_of_rank2 hR'
  refine ⟨E, CFSG.Open.IsElemAbelian.isPGroup hEel, ?_⟩
  have hle : 3 ^ 2 ≤ Nat.card E := by rw [hk]; exact Nat.pow_le_pow_right (by norm_num) hk2
  exact CFSG.LocalAnalysis.GLTheoremA.S3.not_isCyclic_of_card Nat.prime_three hEel hle

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
