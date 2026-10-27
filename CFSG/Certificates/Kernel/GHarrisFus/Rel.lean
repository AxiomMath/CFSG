module

public import Certificates.Data.Kernel.GHarrisFus.RelDefs
public import CFSG.Certificates.Kernel.GHarrisFus.Sound

public section

namespace CFSG.KC.GHFus

open CFSG.ComponentClassification.GHarris.SCert

theorem testB_spec {A : Fus.Data} {t : Test} (h : testB A t = true) : TestRel A t := by
  obtain ⟨p, s, r⟩ := t
  unfold testB at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true, or_assoc] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem relB_spec {A : Fus.Data} {D : FusT} (h : relB A D = true) : FusRel A D := by
  obtain ⟨v, P, ⟨t1, t2, t3⟩, IK, BP, EW, zw, uE, uF⟩ := D
  unfold relB at h
  simp only [Bool.and_eq_true, and_assoc, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hv, hP, h1, h2, h3, hIK, hBP, hEW, hzw, huE, huF⟩ := h
  refine ⟨hv, hP, testB_spec h1, testB_spec h2, testB_spec h3, hIK, ?_, hEW, hzw, huE, huF⟩
  intro i hi j hj hb
  have hc := hBP i hi j hj
  rw [hb, Bool.not_true, Bool.false_or] at hc
  simpa using hc

end CFSG.KC.GHFus
