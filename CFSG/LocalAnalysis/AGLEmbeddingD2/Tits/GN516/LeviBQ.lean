module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviQuasi
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviDecomp
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoNode
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParS

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open scoped Pointwise
open CFSG.Open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbedding.LeviBlock CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

section BQ

variable {K Y : Type} [Group K] [Finite K] [Group Y] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem pElement_map_parJ (h : BorelQuotient D n H π M) (J : Set (Fin D.rank)) :
    pElementSubgroup 2 ((parJ D H J).map π) = (unipJ D J).map π := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hx, k, hk⟩
    exact two_mem_map_unipJ h J hx (hk ▸ pow_orderOf_eq_one x)
  · have hU : unipJ D J ≤ parJ D H J := by rw [parJ_eq_sup]; exact le_sup_left
    exact (Subgroup.map_mono (unipJ_le_pElementSubgroup h hU)).trans
      (map_pElementSubgroup_le_pElementSubgroup_map π _)

omit [Finite K] [Finite Y] in
theorem unipJ_singleton (h : BorelQuotient D n H π M) (i : Fin D.rank) :
    unipJ D {i} = rankOne D.rootGroup i ⊔ posUnipotentExcept D i := by
  have hX : D.rootGroup (Pi.single i 1) ≤ rankOne D.rootGroup i := le_sup_left
  rw [unipJ, posUnipotent_eq_sup h.extras i]
  simp only [Set.mem_singleton_iff, iSup_iSup_eq_left]
  apply le_antisymm
  · exact sup_le (sup_le le_sup_right (hX.trans le_sup_left)) le_sup_left
  · exact sup_le le_sup_right (le_sup_of_le_left le_sup_left)

theorem leviAlt_map_parJ_singleton (h : BorelQuotient D n H π M) (i : Fin D.rank)
    (hnode : Group.IsSolvable ↥(rankOne D.rootGroup i) ∨
      Open.IsQuasisimple ↥(rankOne D.rootGroup i)) :
    LeviAlt ↥(pElementSubgroup 2 ((parJ D H {i}).map π)) := by
  rw [pElement_map_parJ h {i}, unipJ_singleton h i]
  set Lr : Subgroup K := rankOne D.rootGroup i with hLr
  set U' : Subgroup K := posUnipotentExcept D i with hU'
  set Λ : Subgroup K := Lr ⊔ U' with hΛ
  let ρ : ↥Λ →* ↥(Λ.map π) := (π.comp Λ.subtype).codRestrict _ (fun x => ⟨x.1, x.2, rfl⟩)
  have hρ : Function.Surjective ρ := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hLΛalt : LeviAlt ↥Λ := leviAlt_sup_of_normalizes_of_or
    (rankOne_le_normalizer_posUnipotentExcept h.ct h.extras i) (isPGroup_posUnipotentExcept h i)
    hnode
  have hkerρ : ρ.ker ≤ Subgroup.center ↥Λ := by
    intro x hx
    have hπx : π x.1 = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have hcent : (x : K) ∈ Subgroup.center K := h.ker_central _ (MonoidHom.mem_ker.2 hπx)
    exact Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_center_iff.1 hcent g.1)
  exact leviAlt_of_central_quotient ρ hρ hkerρ hLΛalt

end BQ

end CFSG.AGLEmbeddingD2.Tits.GN516
