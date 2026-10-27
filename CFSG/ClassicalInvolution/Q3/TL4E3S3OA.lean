module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OFix2
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OFr

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)

namespace E3S3O

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {L Rd : Subgroup Y} {Sd : Sylow 2 Rd} {S' : Sylow 2 Y}
  {R' T W : Subgroup Y}

namespace Ctx

variable (h : Ctx n R S t J u L Rd Sd S' R' T W)
include h

theorem secAct_fix_J {s : Y} (hs : IsUniqueInvolution L s) :
    ∀ m ∈ secImg (CoreAssembly.conjClass (tightCore Rd)) (u * t) (tightCore Rd),
      secAct (conjInvariant_conjClass (tightCore Rd)) (h.mem_centralizer_a hs) m = m :=
  secAct_eq_of_le_centralizer _ (h.mem_centralizer_a hs)
    (h.le_centralizer_of_mem hs (by rw [h.core]; exact h.J_mem_nbr))

theorem map_orbW_eq {s : Y} (hs : IsUniqueInvolution L s) :
    (orbW Rd (u * t)).map (secAct (conjInvariant_conjClass (tightCore Rd))
      (h.mem_centralizer_a hs)).toMonoidHom = orbW Rd (u * t) := by
  set σ := secAct (conjInvariant_conjClass (tightCore Rd)) (h.mem_centralizer_a hs) with hσ
  have hJmap := map_eq_of_forall_eq σ (h.secAct_fix_J hs)
  have hle : (orbW Rd (u * t)).map σ.toMonoidHom ≤ orbW Rd (u * t) := by
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup_le fun g => ?_
    rw [← Subgroup.map_le_iff_le_comap, AscQuot.map_conjSub, hJmap]
    have hg : ∀ y, y ∈ omegaGen (secFam (CoreAssembly.conjClass (tightCore Rd)) (u * t)) := by
      intro y
      rw [omegaGen_secFam]
      exact Subgroup.mem_top _
    exact Vtx.conjSub_le_orbGrp _ ⟨σ g, hg _⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have e := Subgroup.card_map_of_injective (K := orbW Rd (u * t)) (f := σ.toMonoidHom)
    (fun a b hab => σ.injective hab)
  exact e.symm.le

end Ctx

theorem stepA_proved {n : ℕ} : StepA n := by
  intro Y _ _ R S t J u L Rd Sd S' R' T W h
  have hΩ' := TightLargeHypR.typeRFam h.std.large
  have hcl := hΩ'.hyp.conjInvariant
  obtain ⟨s, hs⟩ := Sec6Gen.exists_uniqueInvolution h.frame.large.datum.hypOmegaGen h.star.1
  have hsa := h.mem_centralizer_a hs
  have hW := h.map_orbW_eq hs
  set σ := secAct (conjInvariant_conjClass (tightCore Rd)) hsa with hσ
  refine ⟨s, hs, hsa, hW, ?_, ?_, fun x hx => Subtype.ext (h.secAct_fix_J hs _
    (Subgroup.mem_subgroupOf.mp hx))⟩
  · rintro _ ⟨M', hM', hM'W, rfl⟩
    obtain ⟨M₁, hM₁, rfl⟩ := mem_secFam_iff.mp hM'
    refine ⟨(secImg (CoreAssembly.conjClass (tightCore Rd)) (u * t) M₁).map σ.toMonoidHom, ?_,
      (Subgroup.map_mono hM'W).trans hW.le, ?_⟩
    · rw [← secImg_conjSub_eq_map]
      exact secImg_mem (XMem.conj' hcl hM₁ hsa)
    · ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact Subgroup.mem_subgroupOf.mpr ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
      · intro hy
        obtain ⟨m, hm, hmy⟩ := Subgroup.mem_subgroupOf.mp hy
        exact ⟨⟨m, hM'W hm⟩, Subgroup.mem_subgroupOf.mpr hm, Subtype.ext hmy⟩
  · have hσσ : σ * σ = 1 := by
      show s26Act _ _ * s26Act _ _ = 1
      rw [← map_mul]
      convert map_one (s26Act (layerY (CoreAssembly.conjClass (tightCore Rd)) (u * t)))
      exact Subtype.ext hs.sq
    refine MulEquiv.ext fun x => Subtype.ext ?_
    exact congrArg (fun γ : MulAut (SecQuot (CoreAssembly.conjClass (tightCore Rd)) (u * t)) =>
      γ (x : SecQuot (CoreAssembly.conjClass (tightCore Rd)) (u * t))) hσσ

end Cit3

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
