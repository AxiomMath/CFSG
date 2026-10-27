module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import Certificates.Certificate23230

public section

namespace CFSG.ComponentClassification.Foote5.L34Unitary

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

theorem tabRep_tpow {t : Tab} {g : Equiv.Perm (Fin 42)} (ht : TabRep t g) (n : ℕ) :
    TabRep (tpow t n) (g ^ n) := by
  induction n with
  | zero => exact TabRep.idTab
  | succ n ih =>
    rw [pow_succ]
    exact ih.comp ht

theorem tabRep_wTab {xt st : Tab} {x s : Equiv.Perm (Fin 42)} (hx : TabRep xt x)
    (hs : TabRep st s) (hx945 : x ^ 945 = 1) (hs8 : s ^ 8 = 1) :
    TabRep (wTab xt st) (x⁻¹ * (s⁻¹ * x * s * x⁻¹) * x * (s⁻¹ * x * s * x⁻¹)⁻¹) := by
  have hxi : x ^ 944 = x⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]
    exact hx945
  have hsi : s ^ 7 = s⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]
    exact hs8
  have h := (((tabRep_tpow hx 944).comp ((((tabRep_tpow hs 7).comp hx).comp hs).comp
    (tabRep_tpow hx 944))).comp hx).comp ((((hx.comp (tabRep_tpow hs 7)).comp
      (tabRep_tpow hx 944))).comp hs)
  rw [hxi, hsi] at h
  unfold wTab tTab tInvTab
  convert h using 1
  group

theorem exists_w_not_mem
    {x : Equiv.Perm (Fin 42)} (hxR : x ∈ R) (hxr : x * r₄ = r₄ * x) (hxS : x ∉ S)
    (hx : x ^ 945 = 1) :
    ∃ s ∈ C₄, s ^ 8 = 1 ∧
      x⁻¹ * (s⁻¹ * x * s * x⁻¹) * x * (s⁻¹ * x * s * x⁻¹)⁻¹ ∉ ambientDerived C₄ 2 := by
  have hc := Certificates.certificate23230
  rw [unitaryCheck, Array.all_eq_true'] at hc
  obtain ⟨xt, hxt, hrep⟩ := enumerates_R.complete x hxR
  have h := hc xt (Array.mem_toList_iff.mp hxt)
  simp only [unitaryAt, Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne,
    Array.any_eq_true', Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ((h | h) | h) | ⟨st, hst, hs8, hw⟩
  · exact absurd ((hrep.comp tabRep_r₄).tab_eq (hxr ▸ tabRep_r₄.comp hrep)) h
  · obtain ⟨g, hg, hgr⟩ := enumerates_C₄.sound xt
      (Array.mem_toList_iff.mpr (Array.contains_iff_mem.mp h))
    rw [hrep.perm_eq hgr] at hxS
    exact absurd hg.2 hxS
  · exact absurd ((tabRep_tpow hrep 945).tab_eq (hx ▸ TabRep.idTab)) h
  · obtain ⟨s, hs, hsr⟩ := enumerates_C₄.sound st (Array.mem_toList_iff.mpr hst)
    have hs8' : s ^ 8 = 1 := ((tabRep_tpow hsr 8).eq_iff TabRep.idTab).mp hs8
    refine ⟨s, hs, hs8', fun hmem => ?_⟩
    obtain ⟨dt, hdt, hdr⟩ := enumerates_derived₂.complete _ hmem
    have he := (tabRep_wTab hrep hsr hx hs8').tab_eq hdr
    rw [he] at hw
    change derived₂.1.contains dt = false at hw
    rw [Array.contains_iff_mem.mpr (Array.mem_toList_iff.mp hdt)] at hw
    exact absurd hw (by decide)

end CFSG.ComponentClassification.Foote5.L34Unitary
