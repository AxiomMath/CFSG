module

public import CFSG.GH74.Uniqueness.SU.SU2Types

public section

open Subgroup Pointwise

namespace CFSG.GH74.Uniqueness.SU.SU2

section Struct

variable {X : Type} [Group X] (V : Type) [Group V] [MulDistribMulAction X V]

@[expose] def omegaA (Y : Subgroup X) : Set (Subgroup V) :=
  {W | W ∈ omega V Y ∧ W ≠ fixSub V Y ∧ W ≤ commSub V Y}

@[expose] def omegaB (Y : Subgroup X) : Set (Subgroup V) :=
  {W | W ∈ omega V Y ∧ W ≠ fixSub V Y ∧ ¬ W ≤ commSub V Y}

variable {V}

theorem mem_omegaA_iff {Y : Subgroup X} {W : Subgroup V} :
    W ∈ omegaA V Y ↔ W ∈ omega V Y ∧ W ≠ fixSub V Y ∧ W ≤ commSub V Y := Iff.rfl

theorem mem_omegaB_iff {Y : Subgroup X} {W : Subgroup V} :
    W ∈ omegaB V Y ↔ W ∈ omega V Y ∧ W ≠ fixSub V Y ∧ ¬ W ≤ commSub V Y := Iff.rfl

theorem omega_eq (Y : Subgroup X) :
    omega V Y = insert (fixSub V Y) (omegaA V Y ∪ omegaB V Y) := by
  ext W
  simp only [Set.mem_insert_iff, Set.mem_union, mem_omegaA_iff, mem_omegaB_iff]
  constructor
  · intro hW
    by_cases h0 : W = fixSub V Y
    · exact Or.inl h0
    · by_cases h1 : W ≤ commSub V Y
      · exact Or.inr (Or.inl ⟨hW, h0, h1⟩)
      · exact Or.inr (Or.inr ⟨hW, h0, h1⟩)
  · rintro (rfl | ⟨hW, -, -⟩ | ⟨hW, -, -⟩)
    · exact fixSub_mem_omega Y
    · exact hW
    · exact hW

theorem disjoint_omegaA_omegaB (Y : Subgroup X) : Disjoint (omegaA V Y) (omegaB V Y) := by
  rw [Set.disjoint_left]
  intro W hA hB
  exact hB.2.2 hA.2.2

theorem fixSub_notMem_omegaAB (Y : Subgroup X) :
    fixSub V Y ∉ omegaA V Y ∪ omegaB V Y := by
  rintro (h | h) <;> exact h.2.1 rfl

omit [MulDistribMulAction X V] in
theorem le_or_le_of_subset_union {G : Type*} [Group G] {T A B : Subgroup G}
    (h : (T : Set G) ⊆ (A : Set G) ∪ B) : T ≤ A ∨ T ≤ B := by
  by_contra hcon
  obtain ⟨hTA, hTB⟩ := not_or.1 hcon
  obtain ⟨a, haT, haA⟩ := IsConcreteLE.not_le_iff_exists.1 hTA
  obtain ⟨b, hbT, hbB⟩ := IsConcreteLE.not_le_iff_exists.1 hTB
  have haB : a ∈ B := (h haT).resolve_left haA
  have hbA : b ∈ A := (h hbT).resolve_right hbB
  rcases h (T.mul_mem haT hbT) with hab | hab
  · apply haA
    have := A.mul_mem hab (A.inv_mem hbA)
    simpa using this
  · apply hbB
    have := B.mul_mem (B.inv_mem haB) hab
    simpa using this

theorem smul_fixSub_of_mem {Y : Subgroup X} {y : X} (hy : y ∈ Y) :
    y • fixSub V Y = fixSub V Y := by
  ext m
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [hs y hy]
    exact hs
  · intro hm
    exact ⟨m, hm, hm y hy⟩

namespace GOPair

variable {Y : Subgroup X}

theorem smul_mem_omegaA (hGO : GOPair V Y) {x : X} (hx : x • fixSub V Y = fixSub V Y)
    {W : Subgroup V} (hW : W ∈ omegaA V Y) : x • W ∈ omegaA V Y := by
  obtain ⟨hWΩ, hW0, hWV⟩ := hW
  refine ⟨smul_mem_omega hWΩ x, ?_, ?_⟩
  · intro h
    apply hW0
    have h1 : x⁻¹ • fixSub V Y = fixSub V Y := by rw [inv_smul_eq_iff]; exact hx.symm
    calc W = x⁻¹ • (x • W) := by rw [inv_smul_smul]
      _ = fixSub V Y := by rw [h, h1]
  · intro m hm
    obtain ⟨w, hw, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hm
    exact hGO.smul_commSub_of_stab hx (hWV hw)

theorem smul_mem_omegaB (hGO : GOPair V Y) {x : X} (hx : x • fixSub V Y = fixSub V Y)
    {W : Subgroup V} (hW : W ∈ omegaB V Y) : x • W ∈ omegaB V Y := by
  obtain ⟨hWΩ, hW0, hWV⟩ := hW
  have h1 : x⁻¹ • fixSub V Y = fixSub V Y := by rw [inv_smul_eq_iff]; exact hx.symm
  refine ⟨smul_mem_omega hWΩ x, ?_, ?_⟩
  · intro h
    apply hW0
    calc W = x⁻¹ • (x • W) := by rw [inv_smul_smul]
      _ = fixSub V Y := by rw [h, h1]
  · intro hle
    apply hWV
    intro m hm
    have hxm : x • m ∈ commSub V Y := hle (Subgroup.smul_mem_pointwise_smul m x W hm)
    have := hGO.smul_commSub_of_stab h1 hxm
    rwa [inv_smul_smul] at this

theorem omegaA_eq_orbit [Finite X] (hGO : GOPair V Y) {W : Subgroup V} (hW : W ∈ omegaA V Y) :
    omegaA V Y = MulAction.orbit ↥Y W := by
  ext A
  constructor
  · intro hA
    obtain ⟨y, hy, rfl⟩ := hGO.typeA_conj hW.1 hW.2.2 hA.1 hA.2.2
    exact ⟨⟨y, hy⟩, rfl⟩
  · rintro ⟨⟨y, hy⟩, rfl⟩
    exact hGO.smul_mem_omegaA (smul_fixSub_of_mem hy) hW

theorem omegaB_eq_orbit [Finite X] [Finite V] (hGO : GOPair V Y) {W : Subgroup V}
    (hW : W ∈ omegaB V Y) : omegaB V Y = MulAction.orbit ↥Y W := by
  ext A
  constructor
  · intro hA
    obtain ⟨y, hy, rfl⟩ := hGO.typeB_conj hW.1 hW.2.1 hW.2.2 hA.1 hA.2.1 hA.2.2
    exact ⟨⟨y, hy⟩, rfl⟩
  · rintro ⟨⟨y, hy⟩, rfl⟩
    exact hGO.smul_mem_omegaB (smul_fixSub_of_mem hy) hW

omit [MulDistribMulAction X V] in
theorem ncard_orbit_dvd {G : Type*} [Group G] {α : Type*} [MulAction G α] (a : α) :
    (MulAction.orbit G a).ncard ∣ Nat.card G := by
  rw [← MulAction.index_stabilizer]
  exact Subgroup.index_dvd_card _

theorem odd_ncard_omegaA [Finite X] (hGO : GOPair V Y) {W : Subgroup V} (hW : W ∈ omegaA V Y) :
    Odd (omegaA V Y).ncard := by
  rw [hGO.omegaA_eq_orbit hW]
  exact hGO.odd_card.of_dvd_nat (ncard_orbit_dvd W)

theorem odd_ncard_omegaB [Finite X] [Finite V] (hGO : GOPair V Y) {W : Subgroup V}
    (hW : W ∈ omegaB V Y) : Odd (omegaB V Y).ncard := by
  rw [hGO.omegaB_eq_orbit hW]
  exact hGO.odd_card.of_dvd_nat (ncard_orbit_dvd W)

theorem ncard_omega [Finite V] (Y : Subgroup X) :
    (omega V Y).ncard = (omegaA V Y).ncard + (omegaB V Y).ncard + 1 := by
  rw [omega_eq, Set.ncard_insert_of_notMem (fixSub_notMem_omegaAB Y) (Set.toFinite _),
    Set.ncard_union_eq (disjoint_omegaA_omegaB Y) (Set.toFinite _) (Set.toFinite _)]

end GOPair

end Struct

end CFSG.GH74.Uniqueness.SU.SU2
