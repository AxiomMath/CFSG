module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.ECoreExtra
public import Certificates.Certificate24531
public import CFSG.Sporadic.Co1Block.TwoCCent

public section

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Sporadic.Co1.Cover CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.Blueprint
  CFSG.Monster.GMS

attribute [local irreducible] eps0 ga gb regCov rrCov epsRows

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem card_centralizer_epsA :
    Nat.card (Subgroup.centralizer ({epsMask eMaskA} : Set NativeSporadic.Co1)) = 89181388800 := by
  obtain ⟨-, h2⟩ := isCo1TwoA_epsA
  have hfix : (co1Fix (epsMask eMaskA)).ncard = 2 ^ 16 := (epsA_facts).2
  rw [hfix] at h2
  have h3 : 2 ^ 16 * Nat.card (Subgroup.centralizer ({epsMask eMaskA} : Set NativeSporadic.Co1)) =
      2 ^ 16 * 89181388800 := by
    rw [h2]
    norm_num
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h3

theorem card_centralizer_epsC :
    Nat.card (Subgroup.centralizer ({epsMask eMaskC} : Set NativeSporadic.Co1)) = 389283840 := by
  obtain ⟨-, hfixC⟩ := Certificates.certificate24531
  obtain ⟨g, hg⟩ : ∃ g : GA, g = co1MatEquiv (epsMask eMaskC) := ⟨_, rfl⟩
  have hg2 : orderOf g = 2 := by
    rw [hg, orderOf_co1MatEquiv]
    exact (epsC_facts).1
  have hrep : MRep (CFSG.Sporadic.Co1.CoverNative.eprodRows epsRows eMaskC) (g : GL24) := by
    unfold MRep
    rw [hg, co1MatEquiv_val]
    exact (matHom_epsMask eMaskC).symm
  have hfix : (xFix (g : GL24)).ncard = 264 := by
    rw [ncard_fix_certX hrep]
    exact hfixC
  have hgc : IsConj g cC := by
    obtain ⟨hcls, -, -, -⟩ := involution_classes
    rcases hcls g hg2 with h | h | h
    · exfalso
      have := not_isConj_of_ncard (x := g) (y := aC) (by rw [hfix, ncard_fix_aC]; norm_num)
      exact this h
    · exact h
    · exfalso
      have := not_isConj_of_ncard (x := g) (y := a₁) (by rw [hfix, ncard_fix_a₁]; norm_num)
      exact this h
  obtain ⟨x, hx⟩ := isConj_iff.1 hgc
  have h1 : Nat.card (Subgroup.centralizer ({epsMask eMaskC} : Set NativeSporadic.Co1)) =
      Nat.card (Subgroup.centralizer ({g} : Set GA)) := by
    rw [hg]
    exact card_centralizer_co1 _
  have h2 : Nat.card (Subgroup.centralizer ({g} : Set GA)) =
      Nat.card (Subgroup.centralizer ({cC} : Set GA)) := by
    rw [card_centralizer_equiv (MulAut.conj x) g, MulAut.conj_apply, hx]
  have h3 : Nat.card (Subgroup.centralizer ({cC} : Set GA)) = 389283840 := by
    rw [card_centralizer_GA, coe_cC]
    exact card_cent_cG
  rw [h1, h2, h3]

end CFSG.EvenSporadicStandard.TwoCo1
