module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5FBDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5FBGeom
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5FBLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverAct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Tab5Cov

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Sec5FactB5z_of (hS : Asc82SchurU43) : Asc82Sec5FactB5z := by
  intro G _ _ L hL t ht ht2 z hz r hr2 hrz hα
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
  have htL : t ∈ L := by
    obtain ⟨w, _, hw⟩ := Subgroup.mem_map.mp ht
    rw [← hw]
    exact w.2
  have htz : (⟨t, htL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.mp ht
    have hwt : w = (⟨t, htL⟩ : ↥L) := Subtype.ext hwv
    rw [← hwt]
    exact hw
  have hzL : z ∈ L := by
    obtain ⟨_, K, hzK, hKle, _⟩ := hz
    exact (Subgroup.mem_inf.mp (hKle hzK)).1
  have hz2 : z * z = 1 := t5_mul_self_eq_one_of_orderOf_eq_two hz.1
  have hr2' : r * r = 1 := by
    rw [← pow_two, ← hr2]
    exact pow_orderOf_eq_one r
  have hutype := t5_phi_pocket_invType hcov hL hz hzL
  set u : OGroup Q := ((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q) with hudef
  have huu : u * u = 1 := by
    rw [hudef, ← Subgroup.coe_mul, ← map_mul, show (⟨z, hzL⟩ : ↥L) * ⟨z, hzL⟩ = 1 from
      Subtype.ext hz2, map_one]
    rfl
  have hsu : s * u = u * s := by
    have hzr : z = r * z * r⁻¹ := by
      rw [hrz, mul_assoc, mul_inv_cancel, mul_one]
    have h1 : φ ⟨z, hzL⟩ = omegaConj hQ s (φ ⟨z, hzL⟩) := hα' ⟨z, hzL⟩ ⟨z, hzL⟩ hzr
    have h2 : u = s * u * s⁻¹ := by
      have h3 := congrArg Subtype.val h1
      rw [coe_omegaConj] at h3
      exact h3
    calc s * u = (s * u * s⁻¹) * s := by group
      _ = u * s := by rw [← h2]
  obtain ⟨K, Bb, hKP, hKn, hKq, hBP, hB, hzBb, hgeom⟩ :=
    sec5fb_geom hQ hdim hsgn hss hs1 huu hsu hutype
  have hzB : φ ⟨z, hzL⟩ ∈ Bb := hzBb _ rfl
  obtain ⟨hπB, hBK, h, hπc⟩ := hgeom (φ ⟨t, htL⟩) (hcov.map_central hL ht ht2 htL)
  exact sec5fb_lift φ (hcov.oddCentralCover hL) hr2' hind.1 (omegaConj hQ s) hα' htL ht2 htz
    hzL hz2 hrz K Bb hKP hKn hKq hBP hB hπB hzB hBK hπc

end CFSG.OddStandard.SmallF3.Omega
