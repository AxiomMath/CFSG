module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagFinCheck

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint.Chevalley CFSG.LieType.SeitzGeneration.ExcHighThree

theorem rfCovSet_spec (j : ℕ) : ∀ (Hs : List ℕ) (acc t : ℕ),
    Nat.testBit (rfCovSet j Hs acc) t = true ↔
      Nat.testBit acc t = true ∨ ∃ H ∈ Hs, Nat.testBit H j = true ∧ Nat.testBit H t = true
  | [], acc, t => by simp [rfCovSet]
  | H :: rest, acc, t => by
    rw [rfCovSet, rfCovSet_spec j rest _ t]
    have hstep : Nat.testBit (if Nat.testBit H j then acc ||| H else acc) t = true ↔
        Nat.testBit acc t = true ∨ (Nat.testBit H j = true ∧ Nat.testBit H t = true) := by
      by_cases hj : Nat.testBit H j = true
      · simp [hj, Nat.testBit_or]
      · simp [hj]
    rw [hstep]
    constructor
    · rintro ((h | ⟨h1, h2⟩) | ⟨H', hH', h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨H, List.mem_cons_self, h1, h2⟩
      · exact Or.inr ⟨H', List.mem_cons_of_mem _ hH', h1, h2⟩
    · rintro (h | ⟨H', hH', h1, h2⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.1 hH' with rfl | hH'
        · exact Or.inl (Or.inr ⟨h1, h2⟩)
        · exact Or.inr ⟨H', hH', h1, h2⟩

theorem rfCover_sound {K₁ K₂ : List ℕ} (h₁ : K₁.length = 6) (h₂ : K₂.length = 6)
    (h₁3 : ∀ x ∈ K₁, x < 3) (h₂3 : ∀ x ∈ K₂, x < 3)
    (hreg : ∀ a ∈ posRoots e6ArtifactRoots, ¬ (rootDot a K₁ % 3 = 0 ∧ rootDot a K₂ % 3 = 0)) :
    ∃ p ∈ rfPlaneBases, planeBits p.1 p.2 = planeBits K₁ K₂ := by
  have hc := rfCover_true
  unfold rfCover at hc
  rw [List.all_eq_true] at hc
  have hmem1 : (vecIdx K₁, K₁) ∈ rfIdxVecs := by
    unfold rfIdxVecs
    rw [List.mem_map]
    exact ⟨K₁, mem_allVecs 6 K₁ h₁ h₁3, rfl⟩
  have hmem2 : (vecIdx K₂, K₂) ∈ rfIdxVecs := by
    unfold rfIdxVecs
    rw [List.mem_map]
    exact ⟨K₂, mem_allVecs 6 K₂ h₂ h₂3, rfl⟩
  have hkill : Nat.testBit (rfCovSet (vecIdx K₁) ((posRoots e6ArtifactRoots).map hyperBits) 0)
      (vecIdx K₂) = false := by
    by_contra hne
    have hne' : Nat.testBit (rfCovSet (vecIdx K₁) ((posRoots e6ArtifactRoots).map hyperBits) 0)
        (vecIdx K₂) = true := by simpa using hne
    rw [rfCovSet_spec] at hne'
    rcases hne' with h0 | ⟨H, hH, hb1, hb2⟩
    · simp at h0
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hH
      have hal : a.length = 6 := length_of_mem_artifactRoots (τ := Tag.E6)
        (List.mem_filter.1 ha).1
      exact hreg a ha ⟨(hyperBits_spec a (h₁.trans hal.symm) h₁3).1 hb1,
        (hyperBits_spec a (h₂.trans hal.symm) h₂3).1 hb2⟩
  have h1 := hc _ hmem1
  simp only [Bool.or_eq_true, beq_iff_eq] at h1
  rcases h1 with hU | hin
  · exfalso
    have hlt : vecIdx K₂ < 3 ^ 6 := by
      have := vecIdx_lt K₂ h₂3
      rwa [h₂] at this
    have hb : Nat.testBit (rfCovSet (vecIdx K₁) ((posRoots e6ArtifactRoots).map hyperBits) 0)
        (vecIdx K₂) = true := by
      rw [hU, Nat.testBit_two_pow_sub_one]
      simpa using hlt
    rw [hkill] at hb
    exact Bool.false_ne_true hb
  · have h2 := List.all_eq_true.1 hin _ hmem2
    simp only [Bool.or_eq_true] at h2
    rcases h2 with hb | hcont
    · rw [hkill] at hb
      exact absurd hb Bool.false_ne_true
    · have hmem := List.contains_iff_mem.1 hcont
      unfold rfPlaneSets at hmem
      obtain ⟨p, hp, hpe⟩ := List.mem_map.1 hmem
      exact ⟨p, hp, hpe⟩

end CFSG.LieType.SeitzGeneration.ExcWideThree
