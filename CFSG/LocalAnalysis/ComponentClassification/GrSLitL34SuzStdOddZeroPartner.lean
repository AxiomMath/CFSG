module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroPump
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroKill
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroCover

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G]

theorem isComponent_of_mem_of_l34PartnerConfig
    (hcat : L34CyclicProperFixedCatalog)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hG : L34BaseSetting G) (hhost : L34ZeroHostFree G) {V P Q : Subgroup G}
    (hcfg : L34PartnerConfig V P Q) {x : G} (hxQ : x ∈ Q)
    (hx : orderOf x = 2) :
    P ≤ centralizer ({x} : Set G) ∧ IsComponent (P.subgroupOf (centralizer ({x} : Set G))) := by
  have hcen : ∀ {g : G}, g ∈ centralizer (Q : Set G) → g ∈ centralizer ({x} : Set G) := fun hg =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hg x hxQ).symm
  have hPx : P ≤ centralizer ({x} : Set G) := fun p hp => hcen (hcfg.le_centralizer hp)
  have hV : V ≠ ⊥ := by
    intro h
    have h4 := hcfg.card_V
    rw [h, Subgroup.card_bot] at h4
    omega
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hu2 : orderOf u = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hcfg.mul_self u hu) hu1'
  obtain ⟨hPu, hcompu⟩ := hcfg.isComponent_left u hu hu1'
  obtain ⟨E, hE, -, hEab, hE16⟩ := exists_elemAbelian_sixteen_of_l34Odd hcfg.isQuasisimple_right
    hcfg.odd_card_center_right hcfg.isL34Type_right hxQ hx
  have hQP : Q ≤ centralizer (P : Set G) := le_centralizer_iff.mp hcfg.le_centralizer
  have hE8 : 8 ≤ Nat.card E := by omega
  rcases isComponent_or_swappedBar_of_l34 hcat hSch hU hheld hG hhost hu2 hx
      (hcen (hcfg.le_centralizer_right hu)) hPu hPx hcompu hcfg.odd_card_center_left
      hcfg.isL34Type_left ((hE.trans inf_le_left).trans hQP) (hE.trans inf_le_right) hEab hE8
      (hcfg.wGroup_right E (hE.trans inf_le_left) hEab hE8) with h | h
  · exact ⟨hPx, h⟩
  · exact (false_of_l34ZeroSwappedBar_of_four h hPx hcfg.le_centralizer_left
      (fun v hv => hcen (hcfg.le_centralizer_right hv)) hcfg.card_V hcfg.mul_self
      hcfg.isComponent_left).elim

end CFSG.ComponentClassification.GrSLit.L34Sec5S
