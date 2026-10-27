module

public import CFSG.LocalAnalysis.GLTheoremB.S7Facts
public import CFSG.LocalAnalysis.GL83PartI.I_27_9.GenAlt

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open Equiv Equiv.Perm GL83.PiGen GL83.CompFam CFSG.Open

variable {X : Type*} [Group X] {K A : Subgroup X}

theorem alternatingGroup_seven_le_closure_Y2 {R : Subgroup (Perm (Fin 7))}
    (hR : IsElemAbelian 3 R) : alternatingGroup (Fin 7) ≤ Subgroup.closure (Y2 3 R) := by
  have hpg : IsPGroup 3 R := GL83.CompFam.isPGroup_of_elem hR
  have hle : Nat.card R ≤ 9 := S7.card_le_nine hpg
  by_cases h3 : Nat.card R ≤ 3
  · exact alternatingGroup_le_closure_Y2_of_card_le (by simp) h3 0
  · obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hpg
    have h9 : Nat.card R = 9 := by
      have hk2 : k ≤ 2 := by
        by_contra hk3
        have : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      interval_cases k <;> simp_all
    have htop := S7.top_le_iSup_pCoreOf h9
    have hJ : (⨆ σ ∈ R, ⨆ (_ : σ ≠ 1), pCoreOf 2 (S7.cA σ)) ≤
        (Subgroup.closure (Y2 3 R)).subgroupOf S7.Alt7 := by
      refine iSup₂_le fun σ hσ => iSup_le fun hσ1 => ?_
      intro y hy
      refine Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure ?_)
      have hσ3 : σ ^ 3 = 1 := hR.2 σ hσ
      have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
      refine ⟨y.2, ?_, Subgroup.zpowers σ, (Subgroup.zpowers_le).2 hσ, ?_, ?_⟩
      · obtain ⟨j, hj⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (S7.cA σ)) ⟨y, hy⟩
        exact ⟨j, by simpa using congrArg (fun z => ((z : ↥(pCoreOf 2 (S7.cA σ))) : S7.Alt7).1) hj⟩
      · rw [Nat.card_zpowers, hord, h9]
      · intro g hg
        have hyσ : (y : Perm (Fin 7)) * σ = σ * y :=
          S7.mem_cA.1 (Subgroup.map_subtype_le _ hy)
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
        exact ((Commute.zpow_left (show Commute σ (y : Perm (Fin 7)) from hyσ.symm) m)).eq
    intro z hz
    exact Subgroup.mem_subgroupOf.1 (hJ (htop (Subgroup.mem_top ⟨z, hz⟩)))

theorem le_centGenI_of_seven [Group.IsPerfect K] (hA : A ≤ Subgroup.normalizer (K : Set X))
    (hAe : IsElemAbelian 3 A) (hodd : Odd (Nat.card (Subgroup.center K)))
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 7)) : K ≤ centGenI 3 A K :=
  le_centGenI_of_perm hA hodd (by norm_num) (by norm_num) e
    (alternatingGroup_seven_le_closure_Y2 (isElemAbelian_range hAe _))

end CFSG.LocalAnalysis.GLTheoremB
