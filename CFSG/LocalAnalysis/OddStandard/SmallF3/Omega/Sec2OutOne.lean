module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutComp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrSix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Layer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem exists_conj_of_type (hQ : Q.Nondegenerate) (h3 : 3 ≤ Module.finrank (ZMod 3) V)
    {x : OGroup Q} (hx : x * x = 1) (w : ↥(omegaGroup hQ))
    (hwx : (w : OGroup Q) * x = x * (w : OGroup Q)) (hww : (w : OGroup Q) * w = 1)
    (hty : invType ((w : OGroup Q) * x) = invType x ∨
      invType ((w : OGroup Q) * x) = invType (piOrth Q * x)) :
    ∃ a : ↥(omegaProj hQ), a⁻¹ * projAut hQ x a = omegaToProj hQ w := by
  have ht : ((w : OGroup Q) * x) * ((w : OGroup Q) * x) = 1 := by
    calc ((w : OGroup Q) * x) * ((w : OGroup Q) * x)
        = (w : OGroup Q) * (x * (w : OGroup Q)) * x := by group
      _ = (w : OGroup Q) * ((w : OGroup Q) * x) * x := by rw [hwx]
      _ = ((w : OGroup Q) * w) * (x * x) := by group
      _ = 1 := by rw [hww, hx]; group
  have hc : ∃ c ∈ omegaGroup hQ, toProj Q c * toProj Q x * (toProj Q c)⁻¹ =
      toProj Q (w : OGroup Q) * toProj Q x := by
    rcases hty with h | h
    · obtain ⟨c, hc, hcx⟩ := exists_mem_omegaGroup_conj hQ h3 hx ht h.symm
      refine ⟨c, hc, ?_⟩
      have h1 : toProj Q (c * x * c⁻¹) = toProj Q c * toProj Q x * (toProj Q c)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      rw [← h1, hcx, map_mul]
    · obtain ⟨c, hc, hcx⟩ := exists_mem_omegaGroup_conj hQ h3 (piOrth_mul_mul_self hx) ht h.symm
      refine ⟨c, hc, ?_⟩
      have h1 : toProj Q c * toProj Q (piOrth Q * x) * (toProj Q c)⁻¹ =
          toProj Q ((w : OGroup Q) * x) := by
        rw [← hcx]
        simp only [map_mul, map_inv]
      rw [map_mul, toProj_piOrth, one_mul] at h1
      rw [h1, map_mul]
  obtain ⟨c, hcΩ, hcw⟩ := hc
  refine ⟨(omegaToProj hQ ⟨c, hcΩ⟩)⁻¹, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_mul, inv_inv, coe_projAut, Subgroup.coe_inv]
  change toProj Q c * (toProj Q x * (toProj Q c)⁻¹ * (toProj Q x)⁻¹) = toProj Q (w : OGroup Q)
  calc toProj Q c * (toProj Q x * (toProj Q c)⁻¹ * (toProj Q x)⁻¹)
      = (toProj Q c * toProj Q x * (toProj Q c)⁻¹) * (toProj Q x)⁻¹ := by group
    _ = (toProj Q (w : OGroup Q) * toProj Q x) * (toProj Q x)⁻¹ := by rw [hcw]
    _ = toProj Q (w : OGroup Q) := by group

theorem isComponentIn_omegaProjInr (hQ : Q.Nondegenerate) {x : OGroup Q} (hx : x * x = 1)
    (hU : 2 ≤ Module.finrank (ZMod 3) (commSp x))
    (hW : 0 < Module.finrank (ZMod 3) (fixSp x))
    (hq : CFSG.IsQuasisimple (omegaGroup (nondegenerate_restrict_commSp hQ hx))) :
    IsComponentIn (omegaProjInr hQ hx hU).range (fixSub (projAut hQ x)) := by
  have hinj := omegaProjInr_injective hQ hx hU hW
  let φ : omegaGroup (nondegenerate_restrict_commSp hQ hx) ≃* (omegaProjInr hQ hx hU).range :=
    MonoidHom.ofInjective hinj
  have hquasi : CFSG.IsQuasisimple ↥(omegaProjInr hQ hx hU).range :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv φ hq
  have hKle : (omegaInr hQ hx hU).range ≤ cOmega hQ x := by
    rintro _ ⟨b, rfl⟩
    rw [mem_cOmega_iff, coe_omegaInr]
    exact (Subgroup.mem_centralizer_singleton_iff.mp (blockInr_mem_centralizer hQ hx _))
  have hKn : ∀ g ∈ cOmega hQ x, ∀ k ∈ (omegaInr hQ hx hU).range,
      g * k * g⁻¹ ∈ (omegaInr hQ hx hU).range := by
    intro g hg k hk
    obtain ⟨b, rfl⟩ := hk
    have hgc : (g : OGroup Q) ∈ Subgroup.centralizer ({x} : Set (OGroup Q)) := hg
    obtain ⟨c₂, hc₂⟩ := blockInr_conj hQ hx hgc (b : OGroup _)
    have hmem : c₂ * (b : OGroup _) * c₂⁻¹ ∈ omegaGroup (nondegenerate_restrict_commSp hQ hx) :=
      (omegaGroup_normal _).conj_mem _ b.2 c₂
    refine ⟨⟨c₂ * (b : OGroup _) * c₂⁻¹, hmem⟩, ?_⟩
    exact Subtype.ext hc₂.symm
  have hmap : (omegaInr hQ hx hU).range.map (omegaToProj hQ) = (omegaProjInr hQ hx hU).range :=
    MonoidHom.map_range _ _
  rw [← hmap]
  exact isComponentIn_fix hQ hx hKle hKn (by rw [hmap]; exact hquasi)

theorem omegaProjInr_mem_layer (hQ : Q.Nondegenerate) {x : OGroup Q} (hx : x * x = 1)
    (hU : 2 ≤ Module.finrank (ZMod 3) (commSp x))
    (hW : 0 < Module.finrank (ZMod 3) (fixSp x))
    (hq : CFSG.IsQuasisimple (omegaGroup (nondegenerate_restrict_commSp hQ hx)))
    (u : omegaGroup (nondegenerate_restrict_commSp hQ hx)) :
    omegaProjInr hQ hx hU u ∈ CFSG.inSubgroup CFSG.layer (fixSub (projAut hQ x)) :=
  (isComponentIn_omegaProjInr hQ hx hU hW hq).le_layer ⟨u, rfl⟩

theorem outerData_of_block (hQ : Q.Nondegenerate) (h3 : 3 ≤ Module.finrank (ZMod 3) V)
    {x : OGroup Q} (hx : x * x = 1) (hU : 2 ≤ Module.finrank (ZMod 3) (commSp x))
    (hW : 0 < Module.finrank (ZMod 3) (fixSp x))
    (hq : CFSG.IsQuasisimple (omegaGroup (nondegenerate_restrict_commSp hQ hx)))
    {u : omegaGroup (nondegenerate_restrict_commSp hQ hx)}
    (huu : (u : OGroup (Q.restrict (commSp x))) * u = 1) (hu1 : u ≠ 1)
    (hty : invType (blockInr hx (u : OGroup (Q.restrict (commSp x))) * x) = invType x ∨
      invType (blockInr hx (u : OGroup (Q.restrict (commSp x))) * x) = invType (piOrth Q * x)) :
    OuterData ↥(omegaProj hQ) (projAut hQ x) := by
  have hinj := omegaProjInr_injective hQ hx hU hW
  set w : ↥(omegaGroup hQ) := omegaInr hQ hx hU u with hwdef
  have hwx : (w : OGroup Q) * x = x * (w : OGroup Q) := by
    rw [hwdef, coe_omegaInr]
    exact (Subgroup.mem_centralizer_singleton_iff.mp (blockInr_mem_centralizer hQ hx _))
  have hww : (w : OGroup Q) * w = 1 := by
    rw [hwdef, coe_omegaInr, ← map_mul, huu, map_one]
  obtain ⟨a, ha⟩ := exists_conj_of_type hQ h3 hx w hwx hww (by rw [hwdef, coe_omegaInr]; exact hty)
  have huP : omegaProjInr hQ hx hU u = omegaToProj hQ w := rfl
  refine ⟨a, omegaToProj hQ w, ?_, ?_, ?_, ha⟩
  · rw [← map_mul, show w * w = 1 from Subtype.ext hww, map_one]
  · intro h1
    rw [← huP] at h1
    exact hu1 (hinj (h1.trans (map_one _).symm))
  · rw [← huP]
    exact omegaProjInr_mem_layer hQ hx hU hW hq u

end CFSG.OddStandard.SmallF3.Omega
