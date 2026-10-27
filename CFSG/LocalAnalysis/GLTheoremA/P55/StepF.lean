module

public import CFSG.LocalAnalysis.GLTheoremA.P55.Inputs
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.LocalAnalysis.GLTheoremA.P55

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem eq_bot_of_le_centralizer_generalizedFitting {Q : Type} [Group Q] [Finite Q]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcore : CFSG.pPrimeCore p Q = ⊥)
    {T : Subgroup Q} (hT : IsPGroup 2 T)
    (hc : T ≤ Subgroup.centralizer (CFSG.generalizedFitting Q : Set Q)) : T = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : T ≤ CFSG.fittingSubgroup Q := by
    have h := CFSG.ComponentClassification.GeneralizedFitting.centralizer_le_fitting Q
    rw [← CFSG.generalizedFitting_eq_componentClassification] at h
    exact hc.trans h
  have hpT : IsPGroup p T :=
    (CFSG.pCore_isPGroup (p := p) (G := Q)).to_le (h1.trans (CFSG.Fitting_eq_pcore Q p hcore).le)
  exact disjoint_self.1 (IsPGroup.disjoint_of_ne 2 p hp2.symm T T hT hpT)

private theorem barX_oPPrimeP (p : ℕ) (X : Subgroup G) :
    barX p X (oPPrimeP p X) = CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X) := by
  have hJg : (oPPrimeP p X).subgroupOf X =
      (CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X)).comap (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  show ((oPPrimeP p X).subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) = _
  rw [hJg]
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

private theorem barX_le_centralizer_of_commutator {p : ℕ} {X S T : Subgroup G}
    (h : ∀ t ∈ T, ∀ s ∈ S, ⁅t, s⁆ ∈ GLAPPrimeCoreOf p X) :
    barX p X S ≤ Subgroup.centralizer (barX p X T : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
  refine barX_le_centralizer fun s hs t ht _ _ => ?_
  have h3 := Subgroup.inv_mem _ (h t ht s hs)
  rwa [commutatorElement_inv] at h3

theorem eq_bot_of_le_centModSubgroup_forall {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X S : Subgroup G} (hS2 : IsPGroup 2 S) (hSX : S ≤ X)
    (hodd : Odd (Nat.card (GLAPPrimeCoreOf p X)))
    (hQ : (⁅oPPrimeP p X, S⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p X)
    (hJ : ∀ J : Subgroup G, GLAPComponent p X J → S ≤ centModSubgroup p J) : S = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcore : CFSG.pPrimeCore p (↥X ⧸ GLAPPrimeCore p ↥X) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p
  have hS2' : IsPGroup 2 (barX p X S) :=
    (hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSX).symm).map _
  have hF : CFSG.generalizedFitting (↥X ⧸ GLAPPrimeCore p ↥X) ≤
      Subgroup.centralizer (barX p X S : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
    rw [CFSG.generalizedFitting.eq_sup]
    refine sup_le ?_ ?_
    · rw [CFSG.Fitting_eq_pcore _ p hcore, Subgroup.le_centralizer_iff, ← barX_oPPrimeP p X]
      exact barX_le_centralizer_of_commutator fun t ht s hs =>
        Subgroup.commutator_le.1 hQ t ht s hs
    · refine sSup_le fun K hK => ?_
      obtain ⟨L, hL, rfl⟩ := exists_glaPComponent_barX_eq X ((CFSG.isComponent_iff_open K).1 hK)
      rw [Subgroup.le_centralizer_iff]
      exact barX_le_centralizer_of_commutator fun l hl s hs =>
        glaPPrimeCoreOf_le_of_isSubnormal hp hL.2.1 ((hJ L hL hs).2 l hl)
  have hbot : barX p X S = ⊥ :=
    eq_bot_of_le_centralizer_generalizedFitting hp hp2 hcore hS2'
      (Subgroup.le_centralizer_iff.2 hF)
  have hSle : S ≤ GLAPPrimeCoreOf p X := by
    intro s hs
    have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨s, hSX hs⟩ ∈ barX p X S :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hs)
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨⟨s, hSX hs⟩, h1, rfl⟩
  rcases hS2.card_eq_or_dvd with h | h
  · exact Subgroup.card_eq_one.1 h
  · exfalso
    have h2 : 2 ∣ Nat.card (GLAPPrimeCoreOf p X) := h.trans (Subgroup.card_dvd_of_le hSle)
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)

end CFSG.LocalAnalysis.GLTheoremA.P55
