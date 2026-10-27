module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428Core

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

theorem i1428_of_single_facts (hNorm : T1428NormFact) (hType : T1428TypeFact) (hNonInn : T1428NonInnFact)
    (hField : T1428FieldFact) (hChev : T1428ChevFact) (hYS08 : YS08) (hExc : T1428ExcFact)
    (hU6 : T1428U6Fact) (hD4 : T1428D4Fact) (G : Type) [Group G] [Finite G] : I1428At G := by
  intro p hp hp2 X K B hX hBmax hK hKchev hmark
  have hBX : B ≤ X := hBmax.1
  have hKX : K ≤ X := hK.1
  have hBmax' : GLAIsBmax p (B.subgroupOf X) := glaIsBmax_subgroupOf hBmax
  have hK' : GLAPComponent p ⊤ (K.subgroupOf X) := glaPComponent_top_of hp hK
  obtain ⟨eK⟩ := nonempty_pQuot_equiv_subgroupOf p hKX
  have hKchev' : IsChevSimple 2 (PSimple p (K.subgroupOf X)) := by
    obtain ⟨eS⟩ := nonempty_centerQuot_of_equiv eK
    exact (isChevSimple_congr eS).2 hKchev
  have hmark' : GLAMarking (PQuot p (K.subgroupOf X)) (fun lab _ _ _ _ _ => p ∣ lab.n) :=
    (glaMarking_congr_const eK.symm (fun lab => p ∣ lab.n)).1 hmark
  obtain ⟨hBK', hy⟩ := t1428Core_of_facts hNorm hType hNonInn hField hChev hYS08 hExc hU6 hD4 ↥X hX p hp hp2
    (B.subgroupOf X) (K.subgroupOf X) hBmax' hK' hKchev' hmark'
  refine ⟨(le_normalizer_subgroupOf_iff hBX hKX).1 hBK', ?_⟩
  intro y hyB hy1
  have hyX : y ∈ X := hBX hyB
  have hy' : (⟨y, hyX⟩ : ↥X) ∈ B.subgroupOf X := Subgroup.mem_subgroupOf.2 hyB
  have hy1' : (⟨y, hyX⟩ : ↥X) ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
  rcases hy _ hy' hy1' with hleft | ⟨hp3, m, hodd, hgt, hcatU, hcompL⟩
  · left
    intro M hM
    have hMX : M ≤ X := hM.1.trans (inf_le_left.trans hKX)
    have hM' := glaPComponent_inf_centralizer_subgroupOf hp hyX hKX hM
    exact (le_normalizer_subgroupOf_iff hBX hMX).1 (hleft _ hM')
  · right
    obtain ⟨eS⟩ := nonempty_pSimple_subgroupOf 3 hKX
    refine ⟨hp3, m, hodd, hgt, (catalogIs_congr eS).1 hcatU, ?_⟩
    intro M hM
    have hMX : M ≤ X := hM.1.trans (inf_le_left.trans hKX)
    have hM' := glaPComponent_inf_centralizer_subgroupOf Nat.prime_three hyX hKX hM
    obtain ⟨eM⟩ := nonempty_pSimple_subgroupOf 3 hMX
    exact (catalogIs_congr eM).1 (hcompL _ hM')

end CFSG.LocalAnalysis.GLTheoremA.T1428

end
