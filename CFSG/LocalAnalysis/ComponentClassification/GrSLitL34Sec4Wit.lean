module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCover
public import Certificates.Certificate22900
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverAutBase

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit.L34Facts

structure WitParts : Prop where
  specs : ∀ s ∈ witSpecs, cv s.1 = cv (zword s.2.1 s.2.2.1 s.2.2.2)
  syl : syl3WitOK = true

theorem witParts : WitParts :=
  ⟨Certificates.certificate22900.1, Certificates.certificate22900.2⟩

theorem cv_witSpec
    {s : List (Fin 2 × Bool) × ℕ × ℕ × ℕ} (hs : s ∈ witSpecs) :
    cv s.1 = cv (zword s.2.1 s.2.2.1 s.2.2.2) :=
  witParts.specs s hs

theorem sigma_witF : sigma (cv witF) = wordPerm (tg 28) :=
  sigma_tw 28 (by norm_num)

theorem sigma_witG : sigma (cv witG) = wordPerm (tg 8) := by
  rw [witG, cv_append, map_mul, sigma_tw 8 (by norm_num), sigma_cv,
    show abPerm zOne = abPerm (zword 1 0 0) by simp [zword, wpow], abPerm_zword, mul_one]

theorem sigma_witU : sigma (cv witU) = wordPerm (tg 4) := by
  rw [witU, cv_append, cv_append, map_mul, map_mul, sigma_tw 4 (by norm_num), sigma_cv,
    sigma_cv, show abPerm zOne = abPerm (zword 1 0 0) by simp [zword, wpow], abPerm_zword,
    show abPerm zTwo = abPerm (zword 0 1 0) by simp [zword, wpow], abPerm_zword, mul_one,
    mul_one]

private theorem tabRep_rep_inv' {k : ℕ} (hk : k < wReps.length) :
    TabRep (invTab 42 (wordTab (wReps.getD k []))) (wordPerm (wReps.getD k []))⁻¹ := by
  have hk' : k < (wordTabs wReps).size := by rw [size_wordTabs]; exact hk
  have hrep := tabRep_wordTabs wReps hk
  rw [← List.getD_eq_getElem _ [] hk] at hrep
  have h := invsOK_spec parabolicParts.invs hk' hrep
  have he : ((wordTabs wReps).map (invTab 42))[k]! = invTab 42 (wordTab (wReps.getD k [])) := by
    rw [getElem!_pos _ k (by simpa using hk'), Array.getElem_map,
      ← getElem!_pos (wordTabs wReps) k hk', wordTabs_getElem! wReps hk,
      List.getD_eq_getElem _ [] hk]
  rwa [he] at h

private theorem tabRep_invTab_of_invOK3 {x : Tab} {g : Equiv.Perm (Fin 42)}
    (h : invOK3 x = true) (hx : TabRep x g) : TabRep (invTab 42 x) g⁻¹ := by
  simp only [invOK3, Bool.and_eq_true, beq_iff_eq] at h
  exact hx.inv h.1 h.2

private theorem tabRep_r3Conj {k : ℕ} (hk : k < wReps.length) :
    TabRep (r3Conj (wordTab (wReps.getD k [])))
      ((wordPerm (wReps.getD k []))⁻¹ * r₃ * wordPerm (wReps.getD k [])) := by
  have hy : TabRep (wordTab (wReps.getD k [])) ((wordPerm (wReps.getD k []))⁻¹)⁻¹ := by
    rw [_root_.inv_inv]
    exact tabRep_wordTab _
  have h := (tabRep_rep_inv' hk).conjTab tabRep_r₃ hy
  rw [_root_.inv_inv] at h
  exact h

private theorem conj_normalizes_aux' {X : Type*} [Group X] {T : Subgroup X} {y b r : X}
    (hbN : b ∈ normalizer (T : Set X))
    (hr : ∀ t ∈ T, (y * b)⁻¹ * (r * (y * b * t * (y * b)⁻¹) * r⁻¹) * (y * b) ∈ T) :
    ∀ t ∈ T, y⁻¹ * r * y * t * (y⁻¹ * r * y)⁻¹ ∈ T := by
  intro t ht
  have h1 := hr _ ((mem_normalizer_iff''.mp hbN t).mp ht)
  refine (mem_normalizer_iff''.mp hbN _).mpr ?_
  have e : b⁻¹ * (y⁻¹ * r * y * t * (y⁻¹ * r * y)⁻¹) * b =
      (y * b)⁻¹ * (r * (y * b * (b⁻¹ * t * b) * (y * b)⁻¹) * r⁻¹) * (y * b) := by group
  rw [e]
  exact h1

private theorem conj_iff_aux' {X : Type*} [Group X] {T : Subgroup X} {c y b : X}
    (hd : c⁻¹ * y * b ∈ normalizer (T : Set X)) (t : X) :
    (y * b)⁻¹ * t * (y * b) ∈ T ↔ c⁻¹ * t * c ∈ T := by
  rw [mem_normalizer_iff''.mp hd (c⁻¹ * t * c)]
  have e : (c⁻¹ * y * b)⁻¹ * (c⁻¹ * t * c) * (c⁻¹ * y * b) = (y * b)⁻¹ * t * (y * b) := by group
  rw [e]

theorem exists_conj_T0_of_r3
    {s : Equiv.Perm (Fin 42)} (hs : s ∈ S)
    (hr : ∀ t ∈ T0, s⁻¹ * (r₃ * (s * t * s⁻¹) * r₃⁻¹) * s ∈ T0) :
    ∃ c ∈ S, c * r₃ = r₃ * c ∧ ∀ t, s⁻¹ * t * s ∈ T0 ↔ c⁻¹ * t * c ∈ T0 := by
  obtain ⟨k, hk, hb⟩ := exists_rep hs
  obtain ⟨b, hbB, rfl⟩ : ∃ b ∈ B0, s = wordPerm (wReps.getD k []) * b := ⟨_, hb, by group⟩
  have hz := conj_normalizes_aux' (B0_le_normalizer hbB) hr
  have hr3 : r₃⁻¹ = r₃ := inv_eq_of_mul_eq_one_right r₃_mul_self
  have hsyl := witParts.syl
  simp only [syl3WitOK, allBelow_eq_true] at hsyl
  rcases Bool.or_eq_true _ _ ▸ hsyl k hk with hnot | hwit
  · exfalso
    simp only [r3NotNormalizes, anyBelow_eq_true] at hnot
    obtain ⟨i, hi, hni⟩ := hnot
    have hi' : i < wT₀.length := by rwa [size_wordTabs] at hi
    have hzrep := tabRep_r3Conj hk
    have hzinv : TabRep (r3Conj (wordTab (wReps.getD k [])))
        ((wordPerm (wReps.getD k []))⁻¹ * r₃ * wordPerm (wReps.getD k []))⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, _root_.inv_inv, hr3, ← mul_assoc]
      exact hzrep
    have hrep := hzrep.conjTab (tabRep_wordTabs wT₀ hi') hzinv
    exact not_mem_of_notInOK enumerates_T0 hni hrep
      (hz _ (Subgroup.subset_closure ⟨wT₀[i], List.getElem_mem hi', rfl⟩))
  · obtain ⟨e, -, hcond⟩ := List.any_eq_true.mp hwit
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    obtain ⟨⟨⟨-, hcomm⟩, hinv⟩, hfound⟩ := hcond
    have hcrep := tabRep_wordTab e.2
    have hci := tabRep_invTab_of_invOK3 hinv hcrep
    refine ⟨wordPerm e.2, wordPerm_mem _,
      ((hcrep.comp tabRep_r₃).eq_iff (tabRep_r₃.comp hcrep)).1 hcomm,
      conj_iff_aux' (B0_le_normalizer (B0.mul_mem ?_ hbB))⟩
    exact mem_of_found_enum enumerates_B0 (hci.comp (tabRep_wordTab _)) hfound

end CFSG.ComponentClassification.GrSLit.GrS4
