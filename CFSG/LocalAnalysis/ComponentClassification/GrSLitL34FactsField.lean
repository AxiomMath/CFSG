module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCentralFourModel
public import Certificates.Certificate22209

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four Subgroup
open scoped Pointwise

structure FieldParts : Prop where
  syl : syl2WitOK = true
  free : fieldFreeOK = true

theorem fieldParts : FieldParts := by
  have h := Certificates.certificate22209
  simp only [fieldOK, Bool.and_eq_true] at h
  exact ⟨h.1, h.2⟩

theorem tabRep_r2Conj {k : ℕ} (hk : k < wReps.length) :
    TabRep (r2Conj (wordTab (wReps.getD k [])))
      ((wordPerm (wReps.getD k []))⁻¹ * r₂ * wordPerm (wReps.getD k [])) := by
  have hy : TabRep (wordTab (wReps.getD k [])) ((wordPerm (wReps.getD k []))⁻¹)⁻¹ := by
    rw [_root_.inv_inv]
    exact tabRep_wordTab _
  have h := (tabRep_rep_inv hk).conjTab tabRep_r₂ hy
  rw [_root_.inv_inv] at h
  exact h

theorem exists_conj_T0_of_r2
    {s : Equiv.Perm (Fin 42)} (hs : s ∈ S)
    (hr : ∀ t ∈ T0, s⁻¹ * (r₂ * (s * t * s⁻¹) * r₂⁻¹) * s ∈ T0) :
    ∃ c ∈ S, c * r₂ = r₂ * c ∧ ∀ t, s⁻¹ * t * s ∈ T0 ↔ c⁻¹ * t * c ∈ T0 := by
  obtain ⟨k, hk, hb⟩ := exists_rep hs
  obtain ⟨b, hbB, rfl⟩ : ∃ b ∈ B0, s = wordPerm (wReps.getD k []) * b := ⟨_, hb, by group⟩
  have hz := conj_normalizes_aux (B0_le_normalizer hbB) hr
  have hr2 : r₂⁻¹ = r₂ := inv_eq_of_mul_eq_one_right r₂_mul_self
  have hsyl := fieldParts.syl
  simp only [syl2WitOK, allBelow_eq_true] at hsyl
  rcases Bool.or_eq_true _ _ ▸ hsyl k hk with hnot | hwit
  · exfalso
    simp only [r2NotNormalizes, anyBelow_eq_true] at hnot
    obtain ⟨i, hi, hni⟩ := hnot
    have hi' : i < wT₀.length := by rwa [size_wordTabs] at hi
    have hzrep := tabRep_r2Conj hk
    have hzinv : TabRep (r2Conj (wordTab (wReps.getD k [])))
        ((wordPerm (wReps.getD k []))⁻¹ * r₂ * wordPerm (wReps.getD k []))⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, _root_.inv_inv, hr2, ← mul_assoc]
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
      ((hcrep.comp tabRep_r₂).eq_iff (tabRep_r₂.comp hcrep)).1 hcomm,
      conj_iff_aux (B0_le_normalizer (B0.mul_mem ?_ hbB))⟩
    exact mem_of_found_enum enumerates_B0 (hci.comp (tabRep_wordTab _)) hfound

theorem field_free
    {t : Equiv.Perm (Fin 42)}
    (ht : t ∈ T0) (hinv : r₂ * t * r₂ * t = 1) :
    ∃ u ∈ T0, ∃ d ∈ Z0, t = u * r₂ * u⁻¹ * r₂ * d := by
  obtain ⟨k, hk, rfl⟩ := exists_tg ht
  have h := fieldParts.free
  simp only [fieldFreeOK, allBelow_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    anyBelow_eq_true, Bool.and_eq_true, List.any_eq_true] at h
  rcases h k hk with h' | ⟨m, hm, hinvm, z, hz, hzeq⟩
  · exfalso
    have h1 : (comp 42 (comp 42 (comp 42 r₂T (tgT k)) r₂T) (tgT k) == idTab 42) = true :=
      ((((tabRep_r₂.comp (tabRep_tgT k)).comp tabRep_r₂).comp (tabRep_tgT k)).beq_iff
        TabRep.idTab).2 hinv
    rw [h1] at h'
    exact Bool.noConfusion h'
  · have hmi := tabRep_invTab_of_invOK hinvm (tabRep_tgT m)
    have hrep := (((((tabRep_tgT m).comp tabRep_r₂).comp hmi).comp tabRep_r₂).comp (tabRep_tgT z))
    have hz64 : z < 64 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      omega
    refine ⟨wordPerm (tg m), tg_mem_T0 m hm, wordPerm (tg z), mem_Z0.2 ⟨z, hz, rfl⟩, ?_⟩
    exact ((tabRep_tgT k).eq_iff hrep).1 (beq_iff_eq.mp hzeq)

end CFSG.ComponentClassification.GrSLit.L34Facts
