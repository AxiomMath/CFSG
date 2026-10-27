module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWIsoModelBase

public import Certificates.Certificate22235
public import Certificates.Certificate22236
public import Certificates.Certificate22237

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit

theorem wIsoD1Parts : WIsoD1Parts :=
  ⟨Certificates.certificate22235⟩

theorem wIsoDParts : WIsoDParts :=
  ⟨Certificates.certificate22236⟩

theorem dCase_spec {kb : List Bool} (hkb : kb ∈ kbList)
    {t i : ℕ} (ht : t < 64) (hi : i < 36) (hS : repInS.contains i = false)
    (h2 : wordPerm (tg t) * repPerm i * (wordPerm (tg t) * repPerm i) = 1)
    (hl : liftsKB kb i = true) {k : ℕ} (hk : k ∈ kVals t i) :
    (∃ x ∈ fixInvs kb t i, eqKB kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x) = true ∧ x.1 ≠ 0 ∧
        x.1 ≠ k) ∨
      (∃ a ∈ (fixInvs kb t i).filter (fun x => eqKB kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x)),
        ∃ b ∈ (fixInvs kb t i).filter (fun x => eqKB kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x)),
        ∃ c ∈ (fixInvs kb t i).filter (fun x => eqKB kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x)),
        ∃ d ∈ (fixInvs kb t i).filter (fun x => eqKB kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x)),
        eqKB kb b a = false ∧ eqKB kb c a = false ∧ eqKB kb c b = false ∧
          eqKB kb d a = false ∧ eqKB kb d b = false ∧ eqKB kb d c = false) ∨
      (k ≠ 0 ∧ typeOf t i = expType kb ∧ (kbZero kb = true ∨ kbCyc kb = true) ∧
        (kbFull kb = true ∨
          ∃ a ∈ (fixInvs kb t i).filter (fun x =>
            eqKB kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x)),
          ∃ b ∈ (fixInvs kb t i).filter (fun x =>
            eqKB kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x)),
          ∃ c ∈ (fixInvs kb t i).filter (fun x =>
            eqKB kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x)),
          eqKB kb b a = false ∧ eqKB kb c a = false ∧ eqKB kb c b = false)) := by
  simp only [kVals, List.mem_filter, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    Bool.and_eq_true] at hk
  have mem : ∀ {x : MElt}, (x ∈ allM ∧ fixKB kb t i x = true ∧ isInvKB kb x = true ∧
      eqKB kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x) = true) →
      x ∈ (fixInvs kb t i).filter (fun x => eqKB kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x)) :=
    fun ⟨h1, h2, h3, h4⟩ => List.mem_filter.2 ⟨mem_fixInvs.2 ⟨h1, h2, h3⟩, h4⟩
  rcases wIsoDParts.d kb hkb t ht i hi hS h2 hl k hk.1 hk.2 with
    ⟨x, ⟨h1, h2, h3, h4⟩, hx0, hxk⟩ | ⟨a, b, c, d, hm, h⟩ | ⟨hk0, hty, hz, hf | ⟨a, b, c, hm, h⟩⟩
  · exact Or.inl ⟨x, mem_fixInvs.2 ⟨h1, h2, h3⟩, h4, hx0, hxk⟩
  · exact Or.inr (Or.inl ⟨a, mem (hm a (by simp)), b, mem (hm b (by simp)), c,
      mem (hm c (by simp)), d, mem (hm d (by simp)), h⟩)
  · exact Or.inr (Or.inr ⟨hk0, hty, hz, Or.inl hf⟩)
  · exact Or.inr (Or.inr ⟨hk0, hty, hz, Or.inr ⟨a, mem (hm a (by simp)), b, mem (hm b (by simp)),
      c, mem (hm c (by simp)), h⟩⟩)

theorem wIsoTypeParts : WIsoTypeParts := by
  obtain ⟨h0, h1, h2, h3⟩ := Certificates.certificate22237
  exact ⟨h0, h1, h2, h3⟩

theorem typeOf_spec {t i lab : ℕ} (h : typeOf t i = lab)
    (hlab : lab < 3) : ∃ t' < 64, ∃ j < 36, yPerm t' j * yPerm t i * (yPerm t' j)⁻¹ = rhoPerm lab :=
  h ▸ wIsoTypeParts.types t i (h ▸ hlab)

theorem typeOf_ne {t i t' i' : ℕ} (ht : t < 64) (hi : i < 36)
    (ht' : t' < 64) (hi' : i' < 36) (hS : repInS.contains i = false)
    (hS' : repInS.contains i' = false) (h2 : yPerm t i * yPerm t i = 1)
    (h2' : yPerm t' i' * yPerm t' i' = 1) (hc : yPerm t i * yPerm t' i' = yPerm t' i' * yPerm t i)
    (hn : yPerm t i * yPerm t' i' ∉ S) : typeOf t i ≠ typeOf t' i' :=
  wIsoTypeParts.pairs t ht i hi t' ht' i' hi' hS hS' h2 h2' hc hn

end CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso
