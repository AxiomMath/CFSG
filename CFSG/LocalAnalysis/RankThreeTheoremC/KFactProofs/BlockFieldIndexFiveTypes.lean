module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexTypes

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabPrime
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndex
open scoped commutatorElement

theorem div_three_le_pRank_of_alt {Y : Type} [Group Y] [Finite Y] {H : Subgroup Y} {N : ℕ}
    (ψ : ↥H ≃* alternatingGroup (Fin N)) : N / 3 ≤ Open.pRank 3 H := by
  obtain ⟨E, hEA, hE, hcard⟩ := exists_elem_alternatingGroup N
  have hEc := hE.1
  let f : ↥E →* Y := H.subtype.comp (ψ.symm.toMonoidHom.comp (Subgroup.inclusion hEA))
  have hf : Function.Injective f :=
    Subtype.val_injective.comp (ψ.symm.injective.comp (Subgroup.inclusion_injective hEA))
  refine CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num) (fun a b => mul_comm' a b)
    (fun a => Subtype.ext ?_) hcard f hf ?_
  · rw [Subgroup.coe_pow, hE.2 _ a.2]
    rfl
  · rintro _ ⟨x, rfl⟩
    exact (ψ.symm (Subgroup.inclusion hEA x)).2

variable {G : Type} [Group G] [Finite G]

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP
