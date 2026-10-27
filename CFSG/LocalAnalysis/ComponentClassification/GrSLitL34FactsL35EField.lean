module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverAut
public import Certificates.Certificate22234

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable

structure FieldZParts : Prop where
  specs : ∀ s ∈ fieldZSpecs, cv s.1 = cv (zword s.2.1 s.2.2.1 s.2.2.2)
  r3 : ∀ k ∈ r3Idx, comp 42 (wordTab (tg k)) r₃T = comp 42 r₃T (wordTab (tg k))

theorem fieldZParts : FieldZParts := by
  obtain ⟨h1, h2⟩ := Certificates.certificate22234
  simp only [List.all_eq_true, beq_iff_eq] at h2
  exact ⟨h1, h2⟩

theorem cv_fieldSpec
    {s : List (Fin 2 × Bool) × ℕ × ℕ × ℕ} (hs : s ∈ fieldZSpecs) :
    cv s.1 = cv (zword s.2.1 s.2.2.1 s.2.2.2) :=
  fieldZParts.specs s hs

theorem alphaF_z₁ :
    cv (alphaF zOne) = z₁ := by
  have h := cv_fieldSpec (s := (alphaF zOne, 1, 0, 0)) (by simp [fieldZSpecs])
  rw [cv_zword] at h
  simpa using h

theorem alphaF_z₂ :
    cv (alphaF zTwo) = z₁ ^ 3 * z₂ ^ 3 := by
  have h := cv_fieldSpec (s := (alphaF zTwo, 3, 3, 0)) (by simp [fieldZSpecs])
  rw [cv_zword] at h
  simpa using h

theorem exists_fieldLift :
    ∃ α : Cover →* Cover, (∀ w, α (cv w) = cv (alphaF w)) ∧
      ∀ c, sigma (α c) = r₂ * sigma c * r₂⁻¹ :=
  exists_autLift r₂ (abPerm_conj_of tabRep_r₂ r₂_mul_self tabRep_aS coverParts.autF.1)
    (abPerm_conj_of tabRep_r₂ r₂_mul_self tabRep_bS coverParts.autF.2)

theorem tg_mem_C₃ {k : ℕ} (hk : k ∈ r3Idx) :
    wordPerm (tg k) ∈ centralizer {r₃} ⊓ S := by
  have h2 : TabRep (comp 42 (wordTab (tg k)) r₃T) (r₃ * wordPerm (tg k)) := by
    rw [fieldZParts.r3 k hk]
    exact tabRep_r₃.comp (tabRep_wordTab (tg k))
  exact mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr
    (((tabRep_wordTab (tg k)).comp tabRep_r₃).perm_eq h2), wordPerm_mem _⟩

end CFSG.ComponentClassification.GrSLit.L34Facts
