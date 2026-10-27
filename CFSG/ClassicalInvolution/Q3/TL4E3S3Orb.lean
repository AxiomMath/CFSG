module

public import CFSG.ClassicalInvolution.Q3.TL4E3Rank1O
public import CFSG.ClassicalInvolution.Q3.TL4VtxFam

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)
open scoped commutatorElement

section Cit3

section Std

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.secInO2_of_normal (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hK : (secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd)).Normal) :
    SecInO2 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) z := by
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  set q := QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω (z * t))) with hqdef
  have h := TightLargeHypR.typeRFam hs.large
  have hzY := mem_layerY_of_isUniqueInvolution h hs.xMem_K hs.hz
  have hzb := isUniqueInvolution_secImg h hs.xMem_K hs.hz
  set zb : SecQuot Ω (z * t) := q ⟨z, hzY⟩ with hzbdef
  have hcen : ∀ g : SecQuot Ω (z * t), g * zb * g⁻¹ = zb := by
    intro g
    have hm := hK.conj_mem zb hzb.mem g
    have hsq : (g * zb * g⁻¹) * (g * zb * g⁻¹) = 1 := by
      calc (g * zb * g⁻¹) * (g * zb * g⁻¹) = g * (zb * zb) * g⁻¹ := by group
        _ = 1 := by rw [hzb.sq]; group
    rcases hzb.unique _ hm hsq with h1 | h1
    · exfalso
      apply hzb.ne_one
      calc zb = g⁻¹ * (g * zb * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    · exact h1
  have hcyc : ∀ c ∈ secCyc Ω (z * t) z, ∃ m : ℤ, c = zb ^ m := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : (w : Y) ∈ Subgroup.zpowers z := Subgroup.mem_subgroupOf.mp hw
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hw'
    refine ⟨m, ?_⟩
    have hwm : w = (⟨z, hzY⟩ : ↥(layerY Ω (z * t))) ^ m := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow, ← hm]
    rw [hwm, map_zpow]
  refine ⟨(secCyc Ω (z * t) z).subgroupOf (secOrb Ω (tightCore Rd) (z * t)),
    ⟨fun c hc d => ?_⟩, fun c => ?_, fun c hc => Subgroup.mem_subgroupOf.mpr hc⟩
  · rw [Subgroup.mem_subgroupOf] at hc ⊢
    obtain ⟨m, hm⟩ := hcyc _ hc
    have e : ((d * c * d⁻¹ : ↥(secOrb Ω (tightCore Rd) (z * t))) : SecQuot Ω (z * t)) =
        (c : SecQuot Ω (z * t)) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hm, ← conj_zpow, hcen]
    rw [e]
    exact hc
  · obtain ⟨m, hm⟩ := hcyc _ (Subgroup.mem_subgroupOf.mp c.2)
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    have h2 : ((c : ↥(secOrb Ω (tightCore Rd) (z * t))) : SecQuot Ω (z * t)) ^ 2 = 1 := by
      calc ((c : ↥(secOrb Ω (tightCore Rd) (z * t))) : SecQuot Ω (z * t)) ^ 2 =
          zb ^ m * zb ^ m := by rw [hm, sq]
        _ = (zb * zb) ^ m := ((Commute.refl zb).mul_zpow m).symm
        _ = 1 := by rw [hzb.sq, one_zpow]
    simpa using h2

end Std

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y}

theorem E3Frame.oddCoreOf_orbGen_le_centralizer (hF : E3Frame n R S t J u) {L : Subgroup Y}
    (hLπ : L ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R)) :
    oddCoreOf (E3.orbGen (CoreAssembly.conjClass (tightCore R)) L J) ≤
      Subgroup.centralizer ({u} : Set Y) := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hd := hF.large.datum
  have hc : ConjInvariant Ω := hd.hypOmegaGen.conjInvariant
  have hK₀Ω : tightCore R ∈ Ω := CoreAssembly.mem_conjClass_self _
  have hJn : J ∈ omegaNbr Ω (tightCore R) := hF.maxAdj.1.2
  obtain ⟨gs, Sd, S', R', T, W, hgJ, hu, hs⟩ := hF.exists_std8
  have hcore : tightCore (conjSub gs R) = J := by rw [← conjSub_tightCore, hgJ]
  obtain ⟨x, hx, hxL⟩ := hLπ
  have hxC : x ∈ Subgroup.centralizer ({u} : Set Y) := hF.nbrGen_le_centralizer hx
  have hxJ : conjSub x J = J := by
    have h1 := hs.large.datum.le_normalizer_core hxC
    rw [hcore] at h1
    exact mem_normalizer_iff_conjSub_eq.mp h1
  have hX : E3.orbGen Ω L J = conjSub x (E3.orbGen Ω (tightCore R) J) := by
    rw [← hxL, ← E3.orbGen_conj hc hK₀Ω x, hxJ]
  have h1 : oddCoreOf (E3.orbGen Ω (tightCore R) J) ≤ Subgroup.centralizer ({u} : Set Y) :=
    hF.oddCoreOf_orbGen_core_le.trans (E3.oddCore_le_centralizer_of_alpha
      (hF.alpha J hJn u hF.inv) hd.isUniqueInvolution_core.ne_one)
  rw [hX]
  calc oddCoreOf (conjSub x (E3.orbGen Ω (tightCore R) J))
      = conjSub x (oddCoreOf (E3.orbGen Ω (tightCore R) J)) :=
        Vtx.oddCoreOf_map_of_inj (MulAut.conj x).toMonoidHom (MulAut.conj x).injective _
    _ ≤ conjSub x (Subgroup.centralizer ({u} : Set Y)) := conjSub_mono h1
    _ = Subgroup.centralizer ({u} : Set Y) := conjSub_eq_self_of_mem hxC

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
