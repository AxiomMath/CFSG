module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsS0b

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.M22Std

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.FusionCheck
  CFSG.EvenSporadicStandard.M22Std.OutCheck CFSG.Blueprint.NativeSporadic


theorem mem_s0Inner_iff {l : Tab} : l ∈ s0Inner ↔ ∃ z ∈ sylowS, tab z = l := by
  have hS := (Certificates.certificate24781).1
  rw [s0Inner, ← tab_sylowGens, ← tab_spanE]
  constructor
  · intro h
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 h
    exact ⟨z, (mem_sylowS_iff hS z).2 hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact List.mem_map_of_mem ((mem_sylowS_iff hS z).1 hz)

theorem mem_s0_outer_iff (s : MulAut (Carrier .M22)) :
    (s ∈ s0 ∧ s ∉ innerImage (Carrier .M22) ⊤) ↔ autTab s ∈ s0Outer := by
  have hsplit : ∀ l, l ∈ s0Tabs ↔ l ∈ s0Inner ∨ l ∈ s0Outer := fun l => by
    rw [s0Tabs_eq]
    exact List.mem_append
  constructor
  · rintro ⟨hs, hni⟩
    rcases (hsplit _).1 ((mem_s0_iff s).1 hs) with h | h
    · exfalso
      obtain ⟨z, -, hz⟩ := mem_s0Inner_iff.1 h
      apply hni
      have : s = MulAut.conj z := autTab_injective (by rw [autTab_conj, hz])
      rw [this]
      exact ⟨z, Subgroup.mem_top _, rfl⟩
    · exact h
  · intro h
    refine ⟨(mem_s0_iff s).2 ((hsplit _).2 (Or.inr h)), fun hin => ?_⟩
    obtain ⟨l, hl, hls⟩ := List.mem_map.1 h
    obtain ⟨z, -, hz⟩ := mem_s0Inner_iff.1 hl
    have hs : s = betaAut * MulAut.conj z :=
      autTab_injective (by rw [autTab_mul, autTab_betaAut, autTab_conj, hz, ← hls])
    apply betaAut_not_inner
    have : betaAut = s * (MulAut.conj z)⁻¹ := by rw [hs]; group
    rw [this]
    exact Subgroup.mul_mem _ hin (Subgroup.inv_mem _ ⟨z, Subgroup.mem_top _, rfl⟩)

theorem s0_outer_inv : ∃ s ∈ s0, s ∉ innerImage (Carrier .M22) ⊤ ∧ s * s = 1 := by
  refine ⟨betaAut, betaAut_mem_s0, betaAut_not_inner, autTab_injective ?_⟩
  rw [autTab_mul, autTab_betaAut, autTab_one]
  exact (s0Check_spec).2.1

theorem nodup_s0Outer : s0Outer.Nodup := by
  have := (s0Check_spec).1.2.1
  rw [s0Tabs_eq] at this
  exact (List.nodup_append.1 this).2.1

theorem exists_of_mem_s0Outer {l : Tab} (hl : l ∈ s0Outer) : ∃ a, autTab a = l := by
  have : l ∈ s0Tabs := by
    rw [s0Tabs_eq]
    exact List.mem_append_right _ hl
  obtain ⟨x, -, hx⟩ := isTabsOf_s0.exists_mem l this
  exact ⟨x, hx⟩

theorem ncard_outer_sq (q : Tab) :
    {s : MulAut (Carrier .M22) | s ∈ s0 ∧ s ∉ innerImage (Carrier .M22) ⊤ ∧
      autTab (s * s) = q}.ncard = (s0Outer.filter fun l => decide (tmul l l = q)).length := by
  have hset : {s : MulAut (Carrier .M22) | s ∈ s0 ∧ s ∉ innerImage (Carrier .M22) ⊤ ∧
      autTab (s * s) = q} =
      {s | autTab s ∈ s0Outer.filter fun l => decide (tmul l l = q)} := by
    ext s
    simp only [Set.mem_ofPred_eq, List.mem_filter, decide_eq_true_eq, autTab_mul]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨(mem_s0_outer_iff s).1 ⟨h1, h2⟩, h3⟩
    · rintro ⟨h1, h3⟩
      obtain ⟨h1, h2⟩ := (mem_s0_outer_iff s).2 h1
      exact ⟨h1, h2, h3⟩
  rw [hset, ncard_preimage_mem_tabs autTab autTab_injective _ (nodup_s0Outer.filter _)]
  intro l hl
  exact exists_of_mem_s0Outer (List.mem_filter.1 hl).1

theorem s0_count_ne :
    {s : MulAut (Carrier .M22) | s ∈ s0 ∧ s ∉ innerImage (Carrier .M22) ⊤ ∧ s * s = 1}.ncard ≠
      {s : MulAut (Carrier .M22) | s ∈ s0 ∧ s ∉ innerImage (Carrier .M22) ⊤ ∧
        s * s = MulAut.conj tEl}.ncard := by
  have h1 : {s : MulAut (Carrier .M22) | s ∈ s0 ∧ s ∉ innerImage (Carrier .M22) ⊤ ∧
      s * s = 1} = {s | s ∈ s0 ∧ s ∉ innerImage (Carrier .M22) ⊤ ∧ autTab (s * s) = idTab} := by
    ext s
    simp only [Set.mem_ofPred_eq]
    refine and_congr_right fun _ => and_congr_right fun _ => ?_
    rw [← autTab_one]
    exact autTab_injective.eq_iff.symm
  have h2 : {s : MulAut (Carrier .M22) | s ∈ s0 ∧ s ∉ innerImage (Carrier .M22) ⊤ ∧
      s * s = MulAut.conj tEl} =
      {s | s ∈ s0 ∧ s ∉ innerImage (Carrier .M22) ⊤ ∧ autTab (s * s) = tTab} := by
    ext s
    simp only [Set.mem_ofPred_eq]
    refine and_congr_right fun _ => and_congr_right fun _ => ?_
    rw [← autTab_conj_tEl]
    exact autTab_injective.eq_iff.symm
  rw [h1, h2, ncard_outer_sq, ncard_outer_sq, (s0Check_spec).2.2.2.2.2.1,
    (s0Check_spec).2.2.2.2.2.2]
  norm_num

theorem innerImage_le_s0 {F : Subgroup (Carrier .M22)} (hFS : F ≤ sylowS) :
    innerImage (Carrier .M22) F ≤ s0 := by
  rintro _ ⟨f, hf, rfl⟩
  rw [mem_s0_iff, autTab_conj, s0Tabs_eq]
  refine List.mem_append_left _ ?_
  rw [mem_s0Inner_iff]
  exact ⟨f, hFS hf, rfl⟩

end CFSG.EvenSporadicStandard.M22Std
