module

public import Certificates.Certificate6147
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverBase

public section

namespace CFSG.OddStandard.ONanRec.IdCert

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable Subgroup
open CFSG.ComponentClassification.GrSLit.L34Facts

structure IdCertParts : Prop where
  sigma : sigmaOK = true
  cent : centOK = true
  specs : ∀ s ∈ idSpecs, cv s.1 = cv (zword s.2.1 s.2.2.1 s.2.2.2)

theorem idCertParts : IdCertParts :=
  ⟨Certificates.certificate6147.1, Certificates.certificate6147.2.1,
    Certificates.certificate6147.2.2⟩

theorem tabRep_tgT (k : ℕ) : TabRep (tgT k) (wordPerm (tg k)) := tabRep_wordTab (tg k)

theorem comT_iff {x y : Tab} {a b : Equiv.Perm (Fin 42)} (hx : TabRep x a) (hy : TabRep y b) :
    comT x y = true ↔ a * b = b * a :=
  (hx.comp hy).beq_iff (hy.comp hx)

theorem exists_conj_r4 {k : ℕ} (hk : k < 64)
    {ν : Equiv.Perm (Fin 42)} (hν : ν = r₂ ∨ ν = r₃ ∨ ν = r₄)
    (h2 : wordPerm (tg k) * ν * (wordPerm (tg k) * ν) = 1) {m₁ m₂ : ℕ} (hm₁ : m₁ < 64)
    (hm₂ : m₂ < 64)
    (h1 : wordPerm (tg m₁) * (wordPerm (tg k) * ν) = wordPerm (tg k) * ν * wordPerm (tg m₁))
    (h1' : wordPerm (tg m₂) * (wordPerm (tg k) * ν) = wordPerm (tg k) * ν * wordPerm (tg m₂))
    (hsq : wordPerm (tg m₁) * wordPerm (tg m₁) ≠ 1)
    (hsq' : wordPerm (tg m₁) * wordPerm (tg m₁) = wordPerm (tg m₂) * wordPerm (tg m₂))
    (hnc : wordPerm (tg m₁) * wordPerm (tg m₂) ≠ wordPerm (tg m₂) * wordPerm (tg m₁)) :
    ∃ m < 64, wordPerm (tg m) * (wordPerm (tg k) * ν) = r₄ * wordPerm (tg m) := by
  have hs := idCertParts.sigma
  simp only [sigmaOK, List.all_eq_true, List.mem_range] at hs
  obtain ⟨vT, hvT, hrep⟩ : ∃ vT ∈ [r₂T, r₃T, r₄T], TabRep vT ν := by
    rcases hν with rfl | rfl | rfl
    · exact ⟨r₂T, by simp, tabRep_r₂⟩
    · exact ⟨r₃T, by simp, tabRep_r₃⟩
    · exact ⟨r₄T, by simp, tabRep_r₄⟩
  have hρ : TabRep (comp 42 (tgT k) vT) (wordPerm (tg k) * ν) := (tabRep_tgT k).comp hrep
  have hc := hs k hk vT hvT
  simp only [sigmaCase, Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true,
    List.mem_range] at hc
  rcases hc with (hc | hc) | hc
  ·
    have : (comp 42 (comp 42 (tgT k) vT) (comp 42 (tgT k) vT) == idTab 42) = true :=
      ((hρ.comp hρ).beq_iff TabRep.idTab).2 h2
    rw [this] at hc
    exact absurd hc (by decide)
  ·
    exfalso
    have hq : ∃ x, x < 64 ∧ ∃ y, y < 64 ∧ q8PairT (comp 42 (tgT k) vT) x y = true := by
      refine ⟨m₁, hm₁, m₂, hm₂, ?_⟩
      simp only [q8PairT, Bool.and_eq_true, Bool.not_eq_true']
      refine ⟨⟨⟨⟨(comT_iff (tabRep_tgT m₁) hρ).2 h1, (comT_iff (tabRep_tgT m₂) hρ).2 h1'⟩,
        ?_⟩, ((tabRep_tgT m₁ |>.comp (tabRep_tgT m₁)).beq_iff
          (tabRep_tgT m₂ |>.comp (tabRep_tgT m₂))).2 hsq'⟩, ?_⟩
      · rw [← Bool.not_eq_true, ((tabRep_tgT m₁).comp (tabRep_tgT m₁)).beq_iff TabRep.idTab]
        exact hsq
      · rw [← Bool.not_eq_true, comT_iff (tabRep_tgT m₁) (tabRep_tgT m₂)]
        exact hnc
    obtain ⟨x, hx, y, hy, hxy⟩ := hq
    have hany : ((List.range 64).any fun m₁ => (List.range 64).any fun m₂ =>
        q8PairT (comp 42 (tgT k) vT) m₁ m₂) = true :=
      List.any_eq_true.2 ⟨x, List.mem_range.2 hx, List.any_eq_true.2 ⟨y, List.mem_range.2 hy, hxy⟩⟩
    rw [hany] at hc
    exact absurd hc (by decide)
  · obtain ⟨m, hm, hmc⟩ := hc
    exact ⟨m, hm, ((tabRep_tgT m).comp hρ |>.beq_iff (tabRep_r₄.comp (tabRep_tgT m))).1 hmc⟩

theorem comm_tg_iff {d : ℕ × List ℕ} (hd : d ∈ aCent) {m : ℕ}
    (hm : m < 64) :
    wordPerm (tg m) * wordPerm (tg d.1) = wordPerm (tg d.1) * wordPerm (tg m) ↔ m ∈ d.2 := by
  have hc := idCertParts.cent
  simp only [centOK, List.all_eq_true, List.mem_range, beq_iff_eq] at hc
  rw [← comT_iff (tabRep_tgT m) (tabRep_tgT d.1), hc d hd m hm, List.contains_iff_mem]

theorem cv_specId
    {s : List (Fin 2 × Bool) × ℕ × ℕ × ℕ} (hs : s ∈ idSpecs) :
    cv s.1 = cv (zword s.2.1 s.2.2.1 s.2.2.2) :=
  idCertParts.specs s hs

theorem comm_id_spec
    {d : ℕ × ℕ × ℕ × ℕ × ℕ} (hd : d ∈ idCommData) :
    cv (tw d.1) * cv (tw d.2.1) * (cv (tw d.1))⁻¹ * (cv (tw d.2.1))⁻¹ =
      z₁ ^ d.2.2.1 * z₂ ^ d.2.2.2.1 * z₃ ^ d.2.2.2.2 := by
  have hs : (commWord (tw d.1) (tw d.2.1), d.2.2.1, d.2.2.2.1, d.2.2.2.2) ∈ idSpecs :=
    List.mem_map_of_mem (f := fun d : ℕ × ℕ × ℕ × ℕ × ℕ =>
      (commWord (tw d.1) (tw d.2.1), d.2.2.1, d.2.2.2.1, d.2.2.2.2)) hd
  have h := cv_specId hs
  rw [commWord, cv_append, cv_append, cv_append, cv_invRev, cv_invRev, cv_zword] at h
  exact h

end CFSG.OddStandard.ONanRec.IdCert
