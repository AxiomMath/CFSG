module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Branch54
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Level55Finkelstein
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Section56
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Shape54
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Layer54Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Constrained

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.TwoFi22
  CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

variable {G : Type} [Group G] [Finite G]

@[expose] def DS81Lemma54Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t z : G),
    Setting G L t → CentralPair G L t z → centralizer ({t} : Set G) = L → Psub z = zpowers z →
      centPair z t ≤ (CFSG.layer ↥(centZ z)).map (centZ z).subtype

section Certified


theorem ds81Lemma54_of_core (hI : HypothesisOne (Carrier .B))
    (h25 : Finkelstein77.Asc76Lemma25) (h210 : DS81Lemma210Two) (hCore : DS81Lemma54Core) :
    DS81Lemma54 := by
  intro G _ _ L t z hS hc
  obtain ⟨d⟩ := hS.exists_level55_of_finkelstein hc hI h25
  have hz2 : orderOf z = 2 := (Subgroup.orderOf_mk z hc.hz).symm.trans hc.loc.order_z
  have hodd := hS.std.oddCore z hz2
  rw [d.isTwoConstrained_iff_Psub_ne (by simpa using hodd)]
  intro hPz
  have := hS.std.simple
  obtain ⟨Q, hQC, hKQ, hZ, hsimp, hnonab⟩ := d.exists_quotient_simple_of_K_le_layer
    (by simpa using hodd) hPz
    (hCore G L t z hS hc (hS.centralizer_eq_of_finkelstein_B hI h25) hPz)
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have hQne : Q ≠ ⊤ := by
    intro hQ
    exact centralizer_ne_top_of_simple hS.std.nonabelian hz1 (top_unique (hQ ▸ hQC))
  have hzQ : z ∈ Q := hKQ (mem_centPair_iff.2 ⟨rfl, d.zt_comm.symm⟩)
  have hcat := hS.std.kProper Q (zpowers z) hQne (zpowers_le.2 hzQ) hsimp hnonab
  exact d.false_of_quotient_simple h210 hQC hKQ hnonab hcat

end Certified

end CFSG.EvenSporadicStandard.TwoB
