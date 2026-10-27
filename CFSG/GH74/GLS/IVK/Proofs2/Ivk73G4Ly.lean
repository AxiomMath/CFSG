module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4CompTop
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvQuasi
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvSpor
public import CFSG.RankThree.PartOne.SPOR.OuterLy

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.Sporadic.Schreier CFSG.ClassicalInvolution
  CFSG.Sporadic.Ly
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem ivk73_ly :
    Ivk73Empty (fun X _ => NativeSporadic.IsSporadic X .Ly) := by
  obtain ⟨hkey, hq, -, -⟩ := LyProof.K_facts
  obtain ⟨hSp, hidx⟩ := LyProof.S_sylow
  obtain ⟨-, hcover⟩ := LyProof.S_facts
  have hperf : Group.IsPerfect ↥LyProof.KJ := Group.isPerfect_def.2 hq.1
  refine ivk73_empty_of_comp_top (P := fun X _ => NativeSporadic.IsSporadic X .Ly) ?_ ?_
  · intro L _ _ hL
    exact Nat.le_of_dvd two_pos (RankThree.PartOne.SPOR.outer_order_divides_two' hL).1
  · intro L _ _ hL y hy2 hy1
    obtain ⟨e⟩ := hL
    let e' : L ≃* ↥J := e.trans lyEquivJ
    have hy2' : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
    have hord : orderOf (e' y) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact hy2'
    have hSr : ∀ s ∈ LyProof.SJ, orderOf s = 2 → ∃ c ∈ (⊤ : Subgroup J), s = c * LyProof.zJ * c⁻¹ := by
      intro s hs hso
      have hss : s * s = 1 := by
        have := pow_orderOf_eq_one s
        rwa [hso, pow_two] at this
      have hs1 : s ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at hso
        exact absurd hso (by norm_num)
      obtain ⟨C, hC⟩ := hcover s hs hss hs1
      exact ⟨C, Subgroup.mem_top C, hC⟩
    obtain ⟨c, -, hc⟩ := cover_of_sylow (⊤ : Subgroup J) LyProof.SJ hSp hidx LyProof.zJ hSr (e' y)
      (Subgroup.mem_top _) hord
    refine ⟨↥LyProof.KJ, inferInstance, inferInstance, ?_, fun K hK => ?_⟩
    · exact (GHInv.centralizerEquivConj (J : Subgroup (GL (Fin 111) (ZMod 5))) e' y
        (t := ((LyProof.zJ : J) : GL (Fin 111) (ZMod 5))) (g := (c : GL (Fin 111) (ZMod 5))) c.2
        (by rw [hc]; simp)).trans
        ((GHInv.centralizerSubtypeEquiv J LyProof.zJ).symm.trans (MulEquiv.subgroupCongr hkey))
    · exact GHInv.isComponent_eq_top_of_perfect hperf (QuotientGroup.mk' (center ↥LyProof.KJ))
        (QuotientGroup.mk'_surjective _) hq.2 (by rw [QuotientGroup.ker_mk']) hK

end CFSG.GH74.GLS.IVK
