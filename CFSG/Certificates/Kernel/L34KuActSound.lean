module

public import Certificates.Data.Kernel.L34KuAct
public import CFSG.Certificates.Kernel.L34ScanSound
public import Certificates.Data.GrSLitL34Sec5SKuActCheck
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.L34Scan

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34KSnd
open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts.KuAct
open CFSG.KLie.CT (andB orB notB)

theorem pow32Tab_unpack {x : Nat} (hx : canonK 42 6 (mask 6) (42 * 6) x = true) :
    pow32Tab (unpack 42 6 x) = unpack 42 6 (pow2K 42 6 5 x) := by
  rw [pow2K_unpack hx]
  rfl

theorem kuAct_of {N m r : Nat} {T CP : Nat → Nat}
    (hT : ∀ i < N, canonK 42 6 (mask 6) (42 * 6) (T i) = true)
    (hc : ∀ c < m, canonK 42 6 (mask 6) (42 * 6) (CP c) = true)
    (hr : canonK 42 6 (mask 6) (42 * 6) r = true)
    (h : ∀ i < N, kuK 42 6 r m CP (pidn 42 6) (T i) = true) :
    ((centTabs 42 (pts 42 6 N T) (unpack 42 6 r)).all fun ρ =>
      !(((pts 42 6 m CP).map fun s => comp 42 s s).all fun q => comp 42 ρ q == comp 42 q ρ) ||
        pow32Tab ρ == idTab 42) = true := by
  unfold centTabs
  rw [Array.all_eq_true_iff_forall_mem]
  intro ρ hρ
  rw [Array.mem_filter] at hρ
  obtain ⟨hmem, hcomm⟩ := hρ
  unfold pts at hmem
  rw [Array.mem_ofFn] at hmem
  obtain ⟨⟨i, hi⟩, rfl⟩ := hmem
  have hx := hT i hi
  have hcp : commPt 42 6 (T i) r = true := (commPt_iff hx hr).2 (beq_iff_eq.1 hcomm)
  have eall : (((pts 42 6 m CP).map fun s => comp 42 s s).all fun q =>
      comp 42 (unpack 42 6 (T i)) q == comp 42 q (unpack 42 6 (T i))) =
      allN m fun c => commPt 42 6 (T i) (pcomp 42 6 (mask 6) (CP c) (CP c)) := by
    rw [Bool.eq_iff_iff, Array.all_eq_true_iff_forall_mem, CFSG.KS.Raw.Orb.allN_iff]
    constructor
    · intro H c hcm
      have cc := canonK_pcomp (hc c hcm) (hc c hcm)
      have h2 := H (comp 42 (unpack 42 6 (CP c)) (unpack 42 6 (CP c))) (by
        rw [Array.mem_map]
        refine ⟨unpack 42 6 (CP c), ?_, rfl⟩
        unfold pts
        rw [Array.mem_ofFn]
        exact ⟨⟨c, hcm⟩, rfl⟩)
      rw [comp_unpack' (hc c hcm) (hc c hcm), beq_iff_eq] at h2
      exact (commPt_iff hx cc).2 h2
    · intro H q hq
      rw [Array.mem_map] at hq
      obtain ⟨s, hs, rfl⟩ := hq
      unfold pts at hs
      rw [Array.mem_ofFn] at hs
      obtain ⟨⟨c, hcm⟩, rfl⟩ := hs
      have cc := canonK_pcomp (hc c hcm) (hc c hcm)
      rw [comp_unpack' (hc c hcm) (hc c hcm), beq_iff_eq]
      exact (commPt_iff hx cc).1 (H c hcm)
  rw [eall, pow32Tab_unpack hx, idTab_unpack' hsz42,
    beq_unpack (pow2K_canon hx 5) (canon_pidn hsz42)]
  have h' := h i hi
  unfold kuK at h'
  rw [hcp] at h'
  simpa only [orB_eq, notB_eq, Bool.not_true, Bool.false_or] using h'

end CFSG.KC.L34Scan

end
