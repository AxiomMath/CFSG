module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_le_isSylowIn {V P Q : Subgroup G} (hP : IsSylowIn 2 V P) (hQ : IsPGroup 2 Q)
    (hQV : Q ≤ V) : ∃ h ∈ V, conjSub h Q ≤ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P' : Subgroup ↥V := P.subgroupOf V
  have hP'grp : IsPGroup 2 P' := hP.2.1.comap_subtype
  have hP'idx : ¬ 2 ∣ P'.index := by
    have h := Subgroup.relIndex_subgroupOf (H := P) (K := V) (L := V) le_rfl
    rw [Subgroup.subgroupOf_self, Subgroup.relIndex_top_right] at h
    rw [show P'.index = P.relIndex V from h]
    exact hP.2.2
  let P'' : Sylow 2 ↥V := hP'grp.toSylow hP'idx
  have hP''coe : (P'' : Subgroup ↥V) = P.subgroupOf V := IsPGroup.toSylow_coe _ _
  haveI : P''.FiniteIndex := inferInstance
  haveI : Finite (Sylow 2 ↥V) := Sylow.finite_of_finiteIndex P''
  have hQ'grp : IsPGroup 2 (Q.subgroupOf V) := hQ.comap_subtype
  obtain ⟨P₁, hP₁⟩ := hQ'grp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥V) P₁ P''
  refine ⟨(g : G), g.2, ?_⟩
  intro x hx
  rw [conjSub, Subgroup.mem_map] at hx
  obtain ⟨q, hq, rfl⟩ := hx
  have hqV : (⟨q, hQV hq⟩ : ↥V) ∈ P₁ := hP₁ (by rwa [Subgroup.mem_subgroupOf])
  have hmem : (MulAut.conj g) • (⟨q, hQV hq⟩ : ↥V) ∈ (P'' : Subgroup ↥V) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) (P₁ : Subgroup ↥V) hqV
  have hmemP : ((MulAut.conj g) • (⟨q, hQV hq⟩ : ↥V)).1 ∈ P := by
    rw [hP''coe] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  have hqeq : (MulAut.conj (g : G)).toMonoidHom q =
      ((MulAut.conj g) • (⟨q, hQV hq⟩ : ↥V)).1 := by
    change MulAut.conj (g : G) q = ((MulAut.conj g) • (⟨q, hQV hq⟩ : ↥V)).1
    simp [MulAut.conj_apply]
  rw [hqeq]
  exact hmemP

end CFSG.OddStandard.HigherRank.YamadaG23
