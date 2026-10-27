module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Gz9.SylowRed
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Gz9.Outer
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Gz9.CentQ
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Gz9.FreeP

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog
open scoped commutatorElement

theorem gz9_exists_involution (hC : CSideFacts) {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (hF3 : Vert Fusion3Facts a z) (hOrb : GzOrbitFacts a z)
    (hNo : GzNoFacts a z) :
    ∃ t : ↥(Gx z), t ∉ commutator ↥(Gx z) ∧ t ^ 2 = 1 ∧ ∀ T : Sylow 2 ↥(Gx z), t ∈ T →
      ∃ x ∈ CFSG.pCore 2 ↥(Gx z),
        (∀ s ∈ (T : Subgroup ↥(Gx z)) ⊓ commutator ↥(Gx z),
          ⁅x, s⁆ ∈ centerOf (CFSG.pCore 2 ↥(Gx z))) ∧
        ⁅t, x⁆ ∉ centerOf (CFSG.pCore 2 ↥(Gx z)) := by
  obtain ⟨a₁, ha₁z, ha₁Q, ha₁⟩ := hOrb.orbit_outA.1.nonempty
  have ha2 : a ^ 2 = 1 := by
    rw [← h.orderOf_a]
    exact pow_orderOf_eq_one a
  have ha₁2 : a₁ ^ 2 = 1 := by
    obtain ⟨c, rfl⟩ := isConj_iff.mp ha₁
    rw [conj_pow, ha2, mul_one, mul_inv_cancel]
  have ht2 : (⟨a₁, ha₁z⟩ : ↥(Gx z)) ^ 2 = 1 := Subtype.ext (by simpa using ha₁2)
  have hout := gz9_not_mem_commutator h hOrb hNo ha₁z ha₁Q ha₁
  refine ⟨⟨a₁, ha₁z⟩, hout, ht2, gz9_forall_sylow_of_exists _ ?_⟩
  exact hC.hyp3_of_free ↥(Gx z) (CFSG.pCore 2 ↥(Gx z))
    (isExtraspecialPlusByA5WrTwoWith_pCore h.cent_z) (cIrreducible_pCore h hOrb) ⟨a₁, ha₁z⟩ hout ht2
    ((gz9_card_P_le h hF3 ha₁z ha₁Q ha₁).trans
      (gz9_card_inf_centralizer_le h hOrb ha₁z ha₁Q ha₁))

end CFSG.EvenSporadicStandard.HNRecog.Section3
