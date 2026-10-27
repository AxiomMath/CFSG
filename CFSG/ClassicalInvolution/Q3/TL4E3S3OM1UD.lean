module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Cover
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1UB

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.LieType.Multipliers.U43
open CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.ComponentClassification.HarrisLit.P1.U43
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3.TL4.E4A
open CFSG.ClassicalInvolution.Q3.TL4.E4C


theorem K1_ne_K0 : K1 ≠ K0 := by
  intro h
  have hv : v1P ∈ K0 := h ▸ v1_mem_K1
  exact rel_facts.2.2.2.2.2.2.2.2.1 (commute_d2_K0 v1P hv)

theorem exists_conj_K0
    {K : Subgroup (Equiv.Perm (Fin 820))} {r : Equiv.Perm (Fin 820)}
    (hd : Vtx.AmbientQuatDatum P K r) : ∃ g ∈ P, g * r * g⁻¹ = r0P ∧ conjSub g K = K0 := by
  obtain ⟨c, hcP, hc⟩ := inner_involutions_conj mem_P.1 (hd.le hd.inv.mem) rel_facts.2.1
    hd.inv.sq rel_facts.1 hd.inv.ne_one
  have hg : c⁻¹ ∈ P := P.inv_mem hcP
  have hgr : c⁻¹ * r * c⁻¹⁻¹ = r0P := by
    rw [hc]
    group
  have hd' := hd.conj hg
  rw [hgr] at hd'
  rcases ident hd' with h | h
  · exact ⟨c⁻¹, hg, hgr, h⟩
  · refine ⟨s01P * c⁻¹, P.mul_mem mem_P.2.2.2.2.2.1 hg, ?_, ?_⟩
    · calc s01P * c⁻¹ * r * (s01P * c⁻¹)⁻¹ = s01P * (c⁻¹ * r * c⁻¹⁻¹) * s01P⁻¹ := by group
        _ = r0P := by
          rw [hgr, rel_facts.2.2.2.2.2.2.2.2.2.2.1]
          group
    · rw [conjSub_mul, h, conjSub_s01]

theorem twin_eq_K1 (hd0 : Vtx.AmbientQuatDatum P K0 r0P) {q : Equiv.Perm (Fin 820)}
    (hq : q ∈ P) (hqr : q * r0P = r0P * q) (hne : conjSub q K0 ≠ K0) : conjSub q K0 = K1 := by
  have hd' := hd0.conj hq
  have h1 : q * r0P * q⁻¹ = r0P := by
    rw [hqr]
    group
  rw [h1] at hd'
  exact (ident hd').resolve_left hne

end CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M
