module

public import CFSG.CGT.PushingUpLit.SOLT.Block
public import CFSG.CGT.PushingUpLit.SolK.Inputs
public import CFSG.CGT.Timmesfeld75.SimpleCase
public import CFSG.CGT.Timmesfeld75.StdPair

public section

namespace CFSG.CGT.PushingUpLit.SOLT

open CFSG CFSG.CGT.Timmesfeld75 CFSG.CGT.PushingUpLit.SolK CFSG.RankThree.PartOne
open CFSG.Assembly (InCatalog KProper)

theorem t75Structural_of_list (hSCL : SimpleCaseListStmt) (hL : ListWCIdentification) :
    T75Structural := by
  intro G _ _ _ hsimple Q X n hn hel hTI hWC _ hXN hXnorm hQX _ hnat
  classical
  have := hsimple
  obtain ⟨B⟩ := natBlock_of_isNaturalAltModule hnat
  have hna := exists_noncomm_of_natBlock B hn
  have hUQ := shortU_subset_of_pCore_le hQX
  have h4 : 4 ≤ Nat.card Q := by
    have := card_gt_of_natBlock hn B hUQ
    omega
  have hTI' : ∀ g : G, Q ⊓ conjSubgroup g⁻¹ Q = ⊥ ∨ Q ⊓ conjSubgroup g⁻¹ Q = Q :=
    fun g => hTI g⁻¹
  have hWC' : ∀ g : G, conjSubgroup g⁻¹ Q ≤ Subgroup.normalizer (Q : Set G) →
      conjSubgroup g⁻¹ Q = Q := fun g h => hWC.2 g⁻¹ h
  have hwc : IsWC Q := isWC_of_corBHyp (corBHyp_of_ti_of_weaklyClosed hel hTI' hWC')
  have hlist := hSCL G hna Q hwc h4
  have hstd := hL G hlist Q hwc h4
  have hXN' : ∀ g ∈ Subgroup.normalizer (Q : Set G), ∀ x ∈ X, g * x * g⁻¹ ∈ X := by
    intro g hg x hx
    have h := hXnorm.conj_mem ⟨x, hXN hx⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨g, hg⟩
    exact Subgroup.mem_subgroupOf.1 h
  exact false_of_transitive_block hn hstd.transitive hXN' hQX hnat

end CFSG.CGT.PushingUpLit.SOLT
