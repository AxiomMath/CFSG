module

public import CFSG.FeitThompson.Representations.DadeTransporterCountsInsertedElement
import CFSG.FeitThompson.Representations.DadeCosetConjugatesDisjoint
import CFSG.FeitThompson.Representations.TISetDadeData

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise

section Sets

variable {α : Type*} {s : Set α} {x : α}

theorem symmDiff_singleton_eq_sdiff (h : x ∈ s) : symmDiff s ({x} : Set α) = s \ {x} := by
  ext y
  simp only [Set.mem_symmDiff, Set.mem_sdiff, Set.mem_singleton_iff]
  refine ⟨?_, fun ⟨h1, h2⟩ => Or.inl ⟨h1, h2⟩⟩
  rintro (⟨h1, h2⟩ | ⟨rfl, h2⟩)
  · exact ⟨h1, h2⟩
  · exact absurd h h2

theorem symmDiff_singleton_eq_insert (h : x ∉ s) : symmDiff s ({x} : Set α) = insert x s := by
  ext y
  simp only [Set.mem_symmDiff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (⟨h1, -⟩ | ⟨rfl, -⟩)
    · exact Or.inr h1
    · exact Or.inl rfl
  · rintro (rfl | h1)
    · exact Or.inr ⟨rfl, h⟩
    · exact Or.inl ⟨h1, fun he => h (he ▸ h1)⟩

theorem symmDiff_symmDiff_singleton (s : Set α) (x : α) :
    symmDiff (symmDiff s ({x} : Set α)) ({x} : Set α) = s := by simp

theorem symmDiff_singleton_ne (s : Set α) (x : α) : symmDiff s ({x} : Set α) ≠ s := fun h => by
  simpa using (symmDiff_eq_left.1 h : ({x} : Set α) = ⊥)

theorem symmDiff_singleton_ne_singleton (hs : s.Nonempty) :
    symmDiff s ({x} : Set α) ≠ ({x} : Set α) := by
  intro h
  refine absurd ?_ (Set.nonempty_iff_ne_empty.1 hs)
  have h2 := symmDiff_symmDiff_singleton s x
  rw [h] at h2
  simpa using h2.symm

end Sets

variable {G : Type*} [Group G] {L : Subgroup G} {A B : Set G} {H : G → Subgroup G} {a g : G}

theorem mem_normalizer_insert (h : a ∈ Subgroup.normalizer B) :
    a ∈ Subgroup.normalizer (insert a B) := by
  rw [Subgroup.mem_normalizer_iff_conj_image_eq] at h ⊢
  rw [Set.image_insert_eq, h]
  simp

theorem mem_normalizer_sdiff_singleton (h : a ∈ Subgroup.normalizer B) :
    a ∈ Subgroup.normalizer (B \ {a}) := by
  rw [Subgroup.mem_normalizer_iff_conj_image_eq] at h ⊢
  rw [Set.image_sdiff (MulAut.conj a).injective, h]
  simp

theorem mem_normalizer_symmDiff_singleton (h : a ∈ Subgroup.normalizer B) :
    a ∈ Subgroup.normalizer (symmDiff B ({a} : Set G)) := by
  by_cases hB : a ∈ B
  · rw [symmDiff_singleton_eq_sdiff hB]; exact mem_normalizer_sdiff_singleton h
  · rw [symmDiff_singleton_eq_insert hB]; exact mem_normalizer_insert h

def dadeInvariantSubsets (A : Set G) (a : G) : Set (Set G) :=
  {B : Set G | B.Nonempty ∧ B ⊆ A ∧ a ∈ Subgroup.normalizer B}

theorem mem_dadeInvariantSubsets_iff :
    B ∈ dadeInvariantSubsets A a ↔ B.Nonempty ∧ B ⊆ A ∧ a ∈ Subgroup.normalizer B := Iff.rfl

theorem mem_dadeInvariantSubsets_iff_conjInv_image_eq :
    B ∈ dadeInvariantSubsets A a ↔ B.Nonempty ∧ B ⊆ A ∧ (fun x => a⁻¹ * x * a) '' B = B := by
  rw [mem_dadeInvariantSubsets_iff, mem_normalizer_iff_conjInv_image_eq]

theorem dadeInvariantSubsets_eq_setOf_conjInv_image_eq (A : Set G) (a : G) :
    dadeInvariantSubsets A a
      = {B : Set G | B.Nonempty ∧ B ⊆ A ∧ (fun x => a⁻¹ * x * a) '' B = B} :=
  Set.ext fun _ => mem_dadeInvariantSubsets_iff_conjInv_image_eq

theorem nonempty_of_mem_dadeInvariantSubsets (hB : B ∈ dadeInvariantSubsets A a) : B.Nonempty :=
  hB.1

theorem subset_of_mem_dadeInvariantSubsets (hB : B ∈ dadeInvariantSubsets A a) : B ⊆ A := hB.2.1

theorem mem_normalizer_of_mem_dadeInvariantSubsets (hB : B ∈ dadeInvariantSubsets A a) :
    a ∈ Subgroup.normalizer B := hB.2.2

theorem singleton_mem_dadeInvariantSubsets (ha : a ∈ A) :
    ({a} : Set G) ∈ dadeInvariantSubsets A a :=
  ⟨Set.singleton_nonempty a, Set.singleton_subset_iff.2 ha, by
    rw [Subgroup.mem_normalizer_iff_conj_image_eq]; simp⟩

theorem insert_mem_dadeInvariantSubsets (ha : a ∈ A) (hB : B ∈ dadeInvariantSubsets A a) :
    insert a B ∈ dadeInvariantSubsets A a :=
  ⟨Set.insert_nonempty _ _, Set.insert_subset ha hB.2.1, mem_normalizer_insert hB.2.2⟩

theorem sdiff_singleton_mem_dadeInvariantSubsets (hB : B ∈ dadeInvariantSubsets A a)
    (haB : a ∈ B) (hne : B ≠ {a}) : B \ {a} ∈ dadeInvariantSubsets A a := by
  refine ⟨?_, Set.sdiff_subset.trans hB.2.1, mem_normalizer_sdiff_singleton hB.2.2⟩
  rw [Set.nonempty_iff_ne_empty]
  intro h
  refine hne ?_
  rw [← Set.insert_sdiff_self_of_mem haB, h]
  simp

theorem symmDiff_singleton_mem_dadeInvariantSubsets (ha : a ∈ A)
    (hB : B ∈ dadeInvariantSubsets A a) (hne : B ≠ {a}) :
    symmDiff B ({a} : Set G) ∈ dadeInvariantSubsets A a := by
  by_cases h : a ∈ B
  · rw [symmDiff_singleton_eq_sdiff h]
    exact sdiff_singleton_mem_dadeInvariantSubsets hB h hne
  · rw [symmDiff_singleton_eq_insert h]
    exact insert_mem_dadeInvariantSubsets ha hB

theorem dadeCoset_eq_coe_mul_singleton (H : G → Subgroup G) (a : G) :
    dadeCoset H a = (H a : Set G) * {a} :=
  (dadeCoset_eq_image H a).trans Set.mul_singleton.symm

theorem dadeTransporter_singleton_eq (H : G → Subgroup G) (g a : G) :
    dadeTransporter H {a} g a = conjTransporter (dadeCoset H a) g := by
  rw [dadeTransporter_eq_conjTransporter, dadeInter_singleton, dadeCoset_eq_coe_mul_singleton]

theorem exists_conj_mem_dadeCoset_of_mem_dadeSupport (hg : g ∈ dadeSupport H a) :
    ∃ x : G, x⁻¹ * g * x ∈ dadeCoset H a := by
  obtain ⟨y, hy, hc⟩ := mem_dadeSupport_iff.1 hg
  obtain ⟨c, hc⟩ := _root_.isConj_iff.1 hc
  refine ⟨c, ?_⟩
  have hy' : c⁻¹ * g * c = y := by rw [← hc]; group
  rw [hy']
  exact hy

noncomputable def dadeAlternatingTerm (H : G → Subgroup G) (g a : G) (B : Set G) : ℚ :=
  (-1) ^ B.ncard * Nat.card (dadeTransporter H B g a) / Nat.card (dadeInter H B)

theorem dadeAlternatingTerm_eq_mul_div (H : G → Subgroup G) (g a : G) (B : Set G) :
    dadeAlternatingTerm H g a B =
      (-1) ^ B.ncard * ((Nat.card (dadeTransporter H B g a) : ℚ) / Nat.card (dadeInter H B)) := by
  rw [dadeAlternatingTerm, mul_div_assoc]

namespace IsDadeData

variable [Finite G]

theorem dadeTransporter_singleton_eq_smul (hD : IsDadeData L A H) (ha : a ∈ A) {x₀ : G}
    (hx₀ : x₀⁻¹ * g * x₀ ∈ dadeCoset H a) :
    dadeTransporter H {a} g a = x₀ • (Subgroup.centralizer ({a} : Set G) : Set G) := by
  ext x
  rw [dadeTransporter_singleton_eq, mem_conjTransporter_iff, Set.mem_smul_set_iff_inv_smul_mem,
    smul_eq_mul, SetLike.mem_coe]
  have hkey : x⁻¹ * g * x = (x₀⁻¹ * x)⁻¹ * (x₀⁻¹ * g * x₀) * (x₀⁻¹ * x) := by group
  set c := x₀⁻¹ * x with hc
  have hmem : c⁻¹ * (x₀⁻¹ * g * x₀) * c ∈ (fun y => c⁻¹ * y * c) '' dadeCoset H a := ⟨_, hx₀, rfl⟩
  constructor
  · intro hx
    rw [hkey] at hx
    rcases hD.conjInv_image_dadeCoset_eq_or_disjoint ha c with h | h
    · exact (hD.conjInv_image_dadeCoset_eq_iff_mem_centralizer ha).1 h
    · exact absurd hmem (Set.disjoint_left.1 h hx)
  · intro hx
    rw [hkey]
    rwa [hD.conjInv_image_dadeCoset_eq ha hx] at hmem

theorem natCard_dadeTransporter_singleton (hD : IsDadeData L A H) (ha : a ∈ A)
    (hg : g ∈ dadeSupport H a) :
    Nat.card (dadeTransporter H {a} g a)
      = Nat.card (H a) * Nat.card (L ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) := by
  obtain ⟨x₀, hx₀⟩ := exists_conj_mem_dadeCoset_of_mem_dadeSupport hg
  rw [hD.dadeTransporter_singleton_eq_smul ha hx₀, Set.natCard_smul_set, hD.card_mul_card ha]
  rfl

theorem dadeAlternatingTerm_singleton (hD : IsDadeData L A H) (ha : a ∈ A)
    (hg : g ∈ dadeSupport H a) :
    dadeAlternatingTerm H g a {a}
      = -(Nat.card (L ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : ℚ) := by
  have hHpos : (0 : ℚ) < Nat.card (H a) := by
    exact_mod_cast Nat.card_pos (α := (H a : Subgroup G))
  rw [dadeAlternatingTerm, dadeInter_singleton, hD.natCard_dadeTransporter_singleton ha hg,
    Set.ncard_singleton]
  push_cast
  field_simp

theorem dadeAlternatingTerm_insert_add (hD : IsDadeData L A H) (ha : a ∈ A)
    (hB : B ∈ dadeInvariantSubsets A a) (haB : a ∉ B) (g : G) :
    dadeAlternatingTerm H g a (insert a B) + dadeAlternatingTerm H g a B = 0 := by
  obtain ⟨hne, hBA, hnB⟩ := hB
  have hcard : (insert a B).ncard = B.ncard + 1 := Set.ncard_insert_of_notMem haB
  have hratio := hD.natCard_dadeTransporter_div_natCard_dadeInter ha hBA hne hnB g
  rw [dadeAlternatingTerm, dadeAlternatingTerm, hcard, mul_div_assoc, mul_div_assoc, ← hratio,
    pow_succ]
  ring

theorem dadeAlternatingTerm_add_symmDiff_singleton (hD : IsDadeData L A H) (ha : a ∈ A)
    (hB : B ∈ dadeInvariantSubsets A a) (hne : B ≠ {a}) (g : G) :
    dadeAlternatingTerm H g a B + dadeAlternatingTerm H g a (symmDiff B ({a} : Set G)) = 0 := by
  by_cases h : a ∈ B
  · have hB' := sdiff_singleton_mem_dadeInvariantSubsets hB h hne
    have hkey := hD.dadeAlternatingTerm_insert_add ha hB' (by simp) g
    rw [Set.insert_sdiff_self_of_mem h] at hkey
    rwa [symmDiff_singleton_eq_sdiff h]
  · rw [symmDiff_singleton_eq_insert h, add_comm]
    exact hD.dadeAlternatingTerm_insert_add ha hB h g

theorem finsum_dadeAlternatingTerm (hD : IsDadeData L A H) (ha : a ∈ A)
    (hg : g ∈ dadeSupport H a) :
    ∑ᶠ B ∈ dadeInvariantSubsets A a, dadeAlternatingTerm H g a B
      = -(Nat.card (L ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : ℚ) := by
  classical
  have hfin : (dadeInvariantSubsets A a).Finite := Set.toFinite _
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hmem : ({a} : Set G) ∈ hfin.toFinset :=
    hfin.mem_toFinset.2 (singleton_mem_dadeInvariantSubsets ha)
  rw [← Finset.add_sum_erase _ _ hmem, hD.dadeAlternatingTerm_singleton ha hg]
  have hzero : ∑ B ∈ hfin.toFinset.erase ({a} : Set G), dadeAlternatingTerm H g a B = 0 := by
    refine Finset.sum_involution (fun B _ => symmDiff B ({a} : Set G)) ?_ ?_ ?_ ?_
    · intro B hB
      obtain ⟨hne, hB'⟩ := Finset.mem_erase.1 hB
      exact hD.dadeAlternatingTerm_add_symmDiff_singleton ha (hfin.mem_toFinset.1 hB') hne g
    · intro B _ _
      exact symmDiff_singleton_ne B a
    · intro B hB
      obtain ⟨hne, hB'⟩ := Finset.mem_erase.1 hB
      have hB'' := hfin.mem_toFinset.1 hB'
      refine Finset.mem_erase.2 ⟨symmDiff_singleton_ne_singleton hB''.1, ?_⟩
      exact hfin.mem_toFinset.2 (symmDiff_singleton_mem_dadeInvariantSubsets ha hB'' hne)
    · intro B _
      exact symmDiff_symmDiff_singleton B a
  rw [hzero, add_zero]

theorem finsum_alternating_natCard_dadeTransporter_div_natCard_dadeInter (hD : IsDadeData L A H)
    (ha : a ∈ A) (hg : g ∈ dadeSupport H a) :
    ∑ᶠ B ∈ {B : Set G | B.Nonempty ∧ B ⊆ A ∧ (fun x => a⁻¹ * x * a) '' B = B},
        (-1 : ℚ) ^ B.ncard * Nat.card (dadeTransporter H B g a) / Nat.card (dadeInter H B)
      = -(Nat.card (L ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : ℚ) := by
  rw [← dadeInvariantSubsets_eq_setOf_conjInv_image_eq]
  exact hD.finsum_dadeAlternatingTerm ha hg

end IsDadeData

end CFSG.FeitThompson
