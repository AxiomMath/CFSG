module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Glue
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverAct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5B5Geom
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5B5Abs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Sec5FactB5_of (hS : Asc82SchurU43) : Asc82Sec5FactB5 := by
  intro G _ _ L hL t ht ht2 r hr2 hα
  obtain ⟨α, V, i1, i2, i3, Q, hQ, e, x, hdim, hsgn, hind, y, hyx, _, s, hss, hst, hsy⟩ := hα
  letI := i1
  letI := i2
  letI := i3
  obtain ⟨φ, hcov, he⟩ := t5_cover_of_model hS hL hdim hsgn e
  have hx' : (QuotientGroup.mk (orthToSim Q s) : ProjSim Q) = x := by
    rw [← hyx, ← hsy, projOrthToProjSim_toProj]
  have hact : CoverAct L φ r (orthToSim Q s) :=
    t5_coverAct_of_inducesViaP hL hcov he hind hx'
  have hα' : ∀ l l' : ↥L, (l' : G) = r * l * r⁻¹ → φ l' = omegaConj hQ s (φ l) := by
    intro l l' hl
    apply Subtype.ext
    rw [coe_omegaConj]
    exact (hact.2 l l' hl).trans (simAct_orthToSim s _)
  have hs1 : invDim s = 1 := congrArg Prod.fst hst
  obtain ⟨K, Bb, hKP, hKn, hKq, hBP, hB, hgeom⟩ := t5_b5_geom hQ hdim hsgn hss hs1
  have htL : t ∈ L := by
    obtain ⟨w, _, hw⟩ := Subgroup.mem_map.mp ht
    rw [← hw]
    exact w.2
  have htz : (⟨t, htL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.mp ht
    have hwt : w = (⟨t, htL⟩ : ↥L) := Subtype.ext hwv
    rw [← hwt]
    exact hw
  obtain ⟨hπB, hBK, h, hπc⟩ := hgeom (φ ⟨t, htL⟩) (hcov.map_central hL ht ht2 htL)
  have hr2' : r * r = 1 := by
    rw [← pow_two, ← hr2]
    exact pow_orderOf_eq_one r
  exact t5_b5_lift φ (hcov.oddCentralCover hL) hr2' hind.1 (omegaConj hQ s) hα' htL ht2 htz K Bb
    hKP hKn hKq hBP hB hπB hBK hπc

end CFSG.OddStandard.SmallF3.Omega
