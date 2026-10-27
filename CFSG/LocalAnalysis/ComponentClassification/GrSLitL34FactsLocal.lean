
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsLocalBase

public import Certificates.Certificate22202
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverAutBase

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four Subgroup
open scoped Pointwise

theorem localParts : LocalParts := by
  have h := Certificates.certificate22202
  simp only [localOK, Bool.and_eq_true] at h
  exact ⟨h.1, h.2⟩

theorem quat_relations :
    qt₁ * qt₁ = qc ∧ qt₂ * qt₂ = qc ∧ qc * qc = 1 ∧ qc ≠ 1 ∧ qt₁ * qt₂ = qt₂ * qc * qt₁ ∧
      qt₂ ≠ 1 ∧ qt₂ ≠ qt₁ ∧ qt₂ ≠ qc ∧ qt₂ ≠ qc * qt₁ := by
  have h := localParts.quat
  simp only [quatOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne,
    ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  have r1 := tabRep_tgT 35
  have r2 := tabRep_tgT 38
  have r4 := tabRep_tgT 4
  refine ⟨((r1.comp r1).eq_iff r4).1 h1, ((r2.comp r2).eq_iff r4).1 h2,
    ((r4.comp r4).eq_iff TabRep.idTab).1 h3, fun e => h4 ((r4.eq_iff TabRep.idTab).2 e),
    ((r1.comp r2).eq_iff ((r2.comp r4).comp r1)).1 h5,
    fun e => h6 ((r2.eq_iff TabRep.idTab).2 e), fun e => h7 ((r2.eq_iff r1).2 e),
    fun e => h8 ((r2.eq_iff r4).2 e), fun e => h9 ((r2.eq_iff (r4.comp r1)).2 e)⟩

theorem exists_conj_T0_of_r4
    {s : Equiv.Perm (Fin 42)} (hs : s ∈ S)
    (hr : ∀ t ∈ T0, s⁻¹ * (r₄ * (s * t * s⁻¹) * r₄⁻¹) * s ∈ T0) :
    ∃ c ∈ S, c * r₄ = r₄ * c ∧ ∀ t, s⁻¹ * t * s ∈ T0 ↔ c⁻¹ * t * c ∈ T0 := by
  obtain ⟨k, hk, hb⟩ := exists_rep hs
  obtain ⟨b, hbB, rfl⟩ : ∃ b ∈ B0, s = wordPerm (wReps.getD k []) * b := ⟨_, hb, by group⟩
  have hz := conj_normalizes_aux (B0_le_normalizer hbB) hr
  have hr4 : r₄⁻¹ = r₄ := inv_eq_of_mul_eq_one_right r₄_mul_self
  have hsyl := localParts.syl
  simp only [sylWitOK, allBelow_eq_true] at hsyl
  rcases Bool.or_eq_true _ _ ▸ hsyl k hk with hnot | hwit
  · exfalso
    simp only [r4NotNormalizes, anyBelow_eq_true] at hnot
    obtain ⟨i, hi, hni⟩ := hnot
    have hi' : i < wT₀.length := by rwa [size_wordTabs] at hi
    have hzrep := tabRep_r4Conj hk
    have hzinv : TabRep (r4Conj (wordTab (wReps.getD k [])))
        ((wordPerm (wReps.getD k []))⁻¹ * r₄ * wordPerm (wReps.getD k []))⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, _root_.inv_inv, hr4, ← mul_assoc]
      exact hzrep
    have hrep := hzrep.conjTab (tabRep_wordTabs wT₀ hi') hzinv
    exact not_mem_of_notInOK enumerates_T0 hni hrep
      (hz _ (Subgroup.subset_closure ⟨wT₀[i], List.getElem_mem hi', rfl⟩))
  · obtain ⟨e, -, hcond⟩ := List.any_eq_true.mp hwit
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    obtain ⟨⟨⟨-, hcomm⟩, hinv⟩, hfound⟩ := hcond
    have hcrep := tabRep_wordTab e.2
    have hci := tabRep_invTab_of_invOK hinv hcrep
    refine ⟨wordPerm e.2, wordPerm_mem _,
      ((hcrep.comp tabRep_r₄).eq_iff (tabRep_r₄.comp hcrep)).1 hcomm,
      conj_iff_aux (B0_le_normalizer (B0.mul_mem ?_ hbB))⟩
    exact mem_of_found_enum enumerates_B0 (hci.comp (tabRep_wordTab _)) hfound

end CFSG.ComponentClassification.GrSLit.L34Facts
