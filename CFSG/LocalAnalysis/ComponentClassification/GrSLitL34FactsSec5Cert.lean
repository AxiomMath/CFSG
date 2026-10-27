module

public import Certificates.Certificate22211
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCentralFourModel

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

structure Sec5Parts : Prop where
  h0 : h0OK = true
  z0 : z0CommOK = true
  unit : unitZ0OK = true
  bit : bit12OK = true
  cent : centROK = true

theorem sec5Parts : Sec5Parts := by
  have h := Certificates.certificate22211
  unfold sec5OK at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

noncomputable abbrev h0 : Equiv.Perm (Fin 42) := wordPerm h0w

theorem h0_mem_B0 : h0 ∈ B0 := subset_closure ⟨h0w, by decide, rfl⟩

theorem h0_cube : h0 * h0 * h0 = 1 := by
  have h := sec5Parts.h0
  unfold h0OK at h
  rw [Bool.and_eq_true] at h
  exact ((((tabRep_wordTab _).comp (tabRep_wordTab _)).comp (tabRep_wordTab _)).beq_iff
    TabRep.idTab).1 h.1

theorem h0_moves {k : ℕ} (hk : k < 16) (hk0 : k ≠ 0) :
    h0 * wordPerm (tg k) ≠ wordPerm (tg k) * h0 ∧
      h0 * wordPerm (tg (4 * k)) ≠ wordPerm (tg (4 * k)) * h0 := by
  have h := sec5Parts.h0
  unfold h0OK at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  have h1 := h.2 k (List.mem_range.2 hk)
  rw [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true'] at h1
  rcases h1 with h1 | ⟨h1, h2⟩
  · exact absurd h1 hk0
  · refine ⟨fun he => ?_, fun he => ?_⟩
    · have := ((((tabRep_wordTab _).comp (tabRep_wordTab _)).beq_iff
        ((tabRep_wordTab _).comp (tabRep_wordTab _))).2 he)
      rw [h1] at this
      exact Bool.false_ne_true this
    · have := ((((tabRep_wordTab _).comp (tabRep_wordTab _)).beq_iff
        ((tabRep_wordTab _).comp (tabRep_wordTab _))).2 he)
      rw [h2] at this
      exact Bool.false_ne_true this

theorem tg4_comm :
    wordPerm (tg 1) * wordPerm (tg 16) = wordPerm (tg 4) * wordPerm (tg 16) * wordPerm (tg 1) := by
  have h := sec5Parts.z0
  unfold z0CommOK at h
  rw [Bool.and_eq_true] at h
  exact (((tabRep_wordTab _).comp (tabRep_wordTab _)).beq_iff
    (((tabRep_wordTab _).comp (tabRep_wordTab _)).comp (tabRep_wordTab _))).1 h.1

theorem tg8_comm :
    wordPerm (tg 1) * wordPerm (tg 24) = wordPerm (tg 8) * wordPerm (tg 24) * wordPerm (tg 1) := by
  have h := sec5Parts.z0
  unfold z0CommOK at h
  rw [Bool.and_eq_true] at h
  exact (((tabRep_wordTab _).comp (tabRep_wordTab _)).beq_iff
    (((tabRep_wordTab _).comp (tabRep_wordTab _)).comp (tabRep_wordTab _))).1 h.2

theorem unit_parts :
    r₄ * wordPerm (tg 4) = wordPerm (tg 4) * r₄ ∧
      r₄ * wordPerm (tg 8) ≠ wordPerm (tg 8) * r₄ ∧
      r₄ * wordPerm (tg 12) ≠ wordPerm (tg 12) * r₄ ∧
      r₄ * wordPerm (tg 8) = wordPerm (tg 8) * wordPerm (tg 4) * r₄ := by
  have h := sec5Parts.unit
  unfold unitZ0OK at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h4, h8⟩, h12⟩, h48⟩ := h
  have hc : ∀ k, (comp 42 r₄T (wordTab (tg k)) == comp 42 (wordTab (tg k)) r₄T) = true ↔
      r₄ * wordPerm (tg k) = wordPerm (tg k) * r₄ := fun k =>
    (tabRep_r₄.comp (tabRep_wordTab _)).beq_iff ((tabRep_wordTab _).comp tabRep_r₄)
  refine ⟨(hc 4).1 h4, fun he => ?_, fun he => ?_,
    ((tabRep_r₄.comp (tabRep_wordTab _)).beq_iff
      (((tabRep_wordTab _).comp (tabRep_wordTab _)).comp tabRep_r₄)).1 h48⟩
  · have := (hc 8).2 he
    rw [h8] at this
    exact Bool.false_ne_true this
  · have := (hc 12).2 he
    rw [h12] at this
    exact Bool.false_ne_true this

theorem mem_zpowers_of_comm_r4
    {t : Equiv.Perm (Fin 42)}
    (ht : t ∈ Z0) (hc : r₄ * t = t * r₄) : t ∈ zpowers (wordPerm (tg 4)) := by
  obtain ⟨k, hk, rfl⟩ := mem_Z0.1 ht
  obtain ⟨-, h8, h12, -⟩ := unit_parts
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact mem_zpowers _
  · exact absurd hc h8
  · exact absurd hc h12

theorem mem_Z0_of_comm_T0
    {r : Equiv.Perm (Fin 42)} (hrR : r ∈ R) (hc : ∀ t ∈ T0, r * t = t * r) : r ∈ Z0 := by
  obtain ⟨t, ht, hrep⟩ := enumerates_R.complete r hrR
  have h := List.all_eq_true.mp sec5Parts.cent t ht
  rw [Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h with h | h
  · exfalso
    have hall : ((wordTabs wT₀).toList.all fun g => comp 42 t g == comp 42 g t) = true := by
      rw [List.all_eq_true]
      intro g hg
      simp only [wordTabs, List.toList_toArray, List.mem_map] at hg
      obtain ⟨w, hw, rfl⟩ := hg
      exact (hrep.comp (tabRep_wordTab w)).beq_iff ((tabRep_wordTab w).comp hrep) |>.2
        (hc _ (subset_closure ⟨w, hw, rfl⟩))
    rw [h] at hall
    exact Bool.false_ne_true hall
  · obtain ⟨k, hk, hkt⟩ := List.any_eq_true.mp h
    rw [hrep.beq_iff (tabRep_wordTab _)] at hkt
    rw [hkt]
    exact mem_Z0.2 ⟨k, hk, rfl⟩

end CFSG.ComponentClassification.GrSLit.L34Facts
