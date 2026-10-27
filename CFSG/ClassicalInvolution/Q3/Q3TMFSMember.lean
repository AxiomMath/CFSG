module

public import CFSG.ClassicalInvolution.Q3.Q3TMFSBasic
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerBlocks
public import CFSG.ClassicalInvolution.Q3.Q3SBasic

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T.MFS

open CFSG CFSG.Open CFSG.ClassicalInvolution
open scoped MatrixGroups

variable {Y : Type} [Group Y] [Finite Y]

theorem isClassicalMember3_inf_of_memberIndex_eq_one {z : Y} {L T : Subgroup Y} [hTn : T.Normal]
    (hz : IsClassicalMember3 L z) (hT : T ⊔ L = ⊤) (h1 : memberIndex L T = 1) :
    IsClassicalMember3 (L ⊓ T) z := by
  obtain ⟨ψ, hψs, hψk⟩ := hz.exists_hom
  let ι : ↥(L ⊓ T) →* ↥L := Subgroup.inclusion inf_le_left
  let ψ' : ↥(L ⊓ T) →* SL(2, ZMod 3) := ψ.comp ι
  have hN : T.subgroupOf L ⊔ classicalInvolutionOddCore L = ⊤ := Subgroup.index_eq_one.mp h1
  have hsurj : Function.Surjective ψ' := by
    intro s
    obtain ⟨g, rfl⟩ := hψs s
    have hg : g ∈ T.subgroupOf L ⊔ classicalInvolutionOddCore L := by
      rw [hN]; exact Subgroup.mem_top g
    obtain ⟨m, hm, o, ho, hmo⟩ := Subgroup.mem_sup_of_normal_right.mp hg
    refine ⟨⟨m, m.2, hm⟩, ?_⟩
    have hψo : ψ o = 1 := (hψk o).mpr ho
    change ψ m = ψ g
    rw [← hmo, map_mul, hψo, mul_one]
  have hodd : Odd (Nat.card ψ'.ker) := by
    have hle : ψ'.ker.map ι ≤ classicalInvolutionOddCore L := by
      rintro _ ⟨w, hw, rfl⟩
      exact (hψk (ι w)).mp hw
    have h1' : Nat.card (ψ'.ker.map ι) = Nat.card ψ'.ker :=
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective _)
    rw [← h1']
    exact hz.odd_card_oddCore.of_dvd_nat (Subgroup.card_dvd_of_le hle)
  have hOdd : Odd T.index := by
    rw [index_eq_mul_memberIndex hT, h1, mul_one]
    exact odd_relIndex_sup_oddCore
  have hzT : z ∈ T := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 (Subgroup.zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz.orderOf_eq_two]; norm_num)
    exact isPGroup_two_le_of_odd_index hOdd hp (Subgroup.mem_zpowers z)
  refine ⟨hz.orderOf_eq_two, ⟨hz.mem, hzT⟩, ?_, ?_⟩
  · refine IsSubnormal.step inf_le_left ⟨fun n hn g => ?_⟩ hz.subnormal
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact ⟨L.mul_mem (L.mul_mem g.2 hn.1) (L.inv_mem g.2), hTn.conj_mem _ hn.2 _⟩
  · exact ⟨(CFSG.ComponentClassification.OddKernel.coreQuotientEquiv ψ' hsurj hodd).trans
      ((QuotientGroup.quotientMulEquivOfEq componentOddCore_sl2Three).trans
        QuotientGroup.quotientBot)⟩

end CFSG.ClassicalInvolution.Q3.Q3T.MFS
