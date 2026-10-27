module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Local
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Field
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Data
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.Yardstones.Md0ec50421ce4

theorem i2015At_of_facts {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hodd : I2015OddCentreFact) (hlie : I2015LieModelFact) (hpar : I2015NoParabolicFact) :
    I2015At G p := by
  unfold I2015At
  intro X J I I₀ d h1 h2 h3 hI0 hcov hdp hR S hSJ hS2 hN
  haveI : Fact p.Prime := ⟨hp⟩
  have hJX : J ≤ X := by
    unfold GLAPComponent at h1
    exact h1.1
  obtain ⟨hdn, hfield⟩ := fieldAutOn_of_R2Prop hR
  have hδ : (conjAutOf J d hdn) ^ p = 1 := conjAutOf_pow_eq_one J d hdn hdp
  have hperf : commutator (ppQuot p ↥J) = ⊤ := commutator_ppQuot_of_component hJX h1
  have hIJ : I ≤ J := by
    unfold GLAPComponent at h3
    exact h3.1.trans inf_le_left
  have hI' : GLAPComponent p (fixSub (conjAutOf J d hdn)) (I.subgroupOf J) := by
    rw [fixSub_conjAutOf]
    exact glaPComponent_subgroupOf inf_le_left h3
  have hI0' : I₀.subgroupOf J ≤ I.subgroupOf J := Subgroup.subgroupOf_mono J hI0
  have hcov' := covering_subgroupOf hIJ hI0 hcov
  have hS' : IsPGroup 2 (S.subgroupOf J) := isPGroup_subgroupOf hS2 (J := J)
  have hN' : I₀.subgroupOf J ≤ Subgroup.normalizer (((S.subgroupOf J : Subgroup ↥J)) : Set ↥J) :=
    normalizer_le_subgroupOf hN (J := J)
  have hfin := local_reduction hp hp2 hodd hlie hpar hδ hperf h2 hfield hI' hI0' hcov' hS' hN'
  exact le_primeCoreOf_of_subgroupOf hSJ hfin

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
