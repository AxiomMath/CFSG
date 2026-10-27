module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2HermCover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2PocketCentral
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Pocket
public import CFSG.GH74.GLS.Stage1.Main.BrG2AutC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg CFSG.GH74.GLS.Stage1.Main
open scoped MatrixGroups

theorem isSL23Mod_rootSU2_herm : IsSL23Mod (rootSU2 F9 3 1 (by norm_num : 2 ≤ 4)) := by
  obtain ⟨e⟩ := (isClassicalSL2_rootSU2 (K := F9) (p := 3) (f := 1) natCard_F9 (by norm_num)
    (by norm_num : 2 ≤ 4)).nonempty_mulEquiv
  have hk : Nat.card (fixedSubfield F9 3 1) = 3 := by
    rw [card_fixedSubfield natCard_F9]
    norm_num
  haveI := Fintype.ofFinite (fixedSubfield F9 3 1)
  have hk' : Fintype.card (fixedSubfield F9 3 1) = 3 := by
    rw [← Nat.card_eq_fintype_card, hk]
  exact isSL23Mod_of_mulEquiv
    ((sl2EquivOfRingEquiv (ZMod.ringEquivOfPrime _ Nat.prime_three hk').symm).symm.trans e.symm)
    isSL23Mod_sl2f3

theorem isI4PlusIn_map_cover {X : Type} [Group X] (θ : Su F9 3 1 4 →* X)
    (hθ : Function.Surjective θ) (hker : θ.ker = Subgroup.zpowers hermNegSU) :
    IsI4PlusIn (⊤ : Subgroup X) (θ (rootInvSU F9 3 1 (by norm_num : 2 ≤ 4))) := by
  have hn : 2 ≤ 4 := by norm_num
  have hcl := isClassicalSL2_rootSU2 (K := F9) (p := 3) (f := 1) natCard_F9 (by norm_num) hn
  refine isI4PlusIn_map_of_chain θ hθ ?_ hcl.orderOf_eq_two hcl.mem le_rfl hcl.le_centralizer
    (fun h hh l hl => Subgroup.mul_mem _ (Subgroup.mul_mem _ hl hh) (Subgroup.inv_mem _ hl)) ?_
    isSL23Mod_rootSU2_herm ?_
  · intro m hm g
    rw [hker, mem_zpowers_hermNegSU] at hm
    rcases hm with rfl | rfl
    · rw [mul_one, one_mul]
    · exact Subgroup.mem_center_iff.mp hermNegSU_mem_center g
  · intro l hl c hc
    have hnorm := (isLongRootSU2_standard (K := F9) (p := 3) (f := 1) hn)
      |>.normal_subgroupOf_centralizer natCard_F9 (by norm_num)
    have h := hnorm.conj_mem ⟨l, hcl.le_centralizer hl⟩ (Subgroup.mem_subgroupOf.mpr hl) ⟨c, hc⟩
    exact Subgroup.mem_subgroupOf.mp h
  · rw [Subgroup.disjoint_def, hker]
    intro x hx hx'
    rcases mem_zpowers_hermNegSU.mp hx' with rfl | rfl
    · rfl
    · exact absurd hx hermNegSU_not_mem_rootSU2

end CFSG.OddStandard.SmallF3.Omega
