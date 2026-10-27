module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24AutRep
public import CFSG.Sporadic.Co1Block.TwoBD

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.G24Aut

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co1Block
  CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.Co1Schreier
open Subgroup

theorem gA_get : gA[0]! = xa ∧ gA[1]! = ya ∧ gA[2]! = sa := arr3_get xa ya sa

theorem gAi_get {j : ℕ} (hj : j < 3) : gAi[j]! = invCand nn gA[j]! := by
  unfold gAi
  rw [getElem!_map' gA (invCand nn) j (by simp [gA]; omega)]

theorem rep_xa : Rep nn xa xBar := by
  have h := strong_rep (j := 0) (by norm_num)
  rwa [strong0_eq] at h

theorem rep_ya : Rep nn ya yBar := by
  have h := strong_rep (j := 1) (by norm_num)
  rwa [strong1_eq] at h

@[expose] noncomputable def gGen (σ : PP) : ℕ → PP := fun j =>
  if j = 0 then xBar else if j = 1 then yBar else σ

theorem hg2 (hx : isInvA nn xa (invCand nn xa) = true) (hy : isInvA nn ya (invCand nn ya) = true)
    (σ : PP) : ∀ j < 2, Rep nn gA[j]! (gGen σ j) ∧ Rep nn gAi[j]! (gGen σ j)⁻¹ := by
  intro j hj
  interval_cases j
  · rw [gAi_get (by norm_num), gA_get.1]
    exact ⟨by simpa [gGen] using rep_xa, by simpa [gGen] using rep_inv_of_isInvA rep_xa hx⟩
  · rw [gAi_get (by norm_num), gA_get.2.1]
    exact ⟨by simpa [gGen] using rep_ya, by simpa [gGen] using rep_inv_of_isInvA rep_ya hy⟩

theorem mem_of_inD {g : Array ℕ} {G : PP} (hG : Rep nn g G) (h : inD g = true) : G ∈ twoBD :=
  mem_twoBD_of_sift hG h

theorem xa_inv : isInvA nn xa (invCand nn xa) = true :=
  isInvA_of_allPermsOK twoB_allPerms (j := 0) (by rw [twoBStrong_size]; norm_num)

theorem ya_inv : isInvA nn ya (invCand nn ya) = true :=
  isInvA_of_allPermsOK twoB_allPerms (j := 1) (by rw [twoBStrong_size]; norm_num)

end CFSG.EvenSporadicStandard.G24Aut
