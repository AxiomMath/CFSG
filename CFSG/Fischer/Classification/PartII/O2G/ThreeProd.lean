module

public import CFSG.Fischer.Classification.PartII.Twins.Basic

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer LocalU O2Twin

namespace O2G

variable {G : Type} [Group G]

open Classical

noncomputable def sprod (S : Set G) (hS : S.Pairwise Commute) (X : Finset G) : G :=
  (X.filter (· ∈ S)).noncommProd id fun _ ha _ hb hab =>
    hS (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2 hab

variable {S : Set G} (hS : S.Pairwise Commute)

theorem sprod_empty : sprod S hS ∅ = 1 := by
  simp [sprod]

theorem sprod_insert {a : G} {X : Finset G} (ha : a ∈ S) (haX : a ∉ X) :
    sprod S hS (insert a X) = a * sprod S hS X := by
  unfold sprod
  simp only [Finset.filter_insert, ha, ↓reduceIte]
  rw [Finset.noncommProd_insert_of_notMem _ _ _ _ fun h => haX (Finset.mem_filter.1 h).1]
  rfl

theorem sprod_singleton {a : G} (ha : a ∈ S) : sprod S hS {a} = a := by
  rw [← Finset.insert_empty, sprod_insert hS ha (Finset.notMem_empty a), sprod_empty, mul_one]

theorem sprod_eq_sprod {S' : Set G} (hS' : S'.Pairwise Commute) {X : Finset G}
    (hX : (X : Set G) ⊆ S) (hX' : (X : Set G) ⊆ S') : sprod S hS X = sprod S' hS' X := by
  induction X using Finset.induction_on with
  | empty => rw [sprod_empty, sprod_empty]
  | insert a X haX ih =>
    have hXS : (X : Set G) ⊆ S := fun y hy => hX (Finset.mem_insert_of_mem hy)
    have hXS' : (X : Set G) ⊆ S' := fun y hy => hX' (Finset.mem_insert_of_mem hy)
    rw [sprod_insert hS (hX (Finset.mem_insert_self a X)) haX,
      sprod_insert hS' (hX' (Finset.mem_insert_self a X)) haX, ih hXS hXS']

theorem commute_sprod {z : G} (hz : ∀ a ∈ S, Commute z a) (X : Finset G) :
    Commute z (sprod S hS X) :=
  Finset.noncommProd_commute _ _ _ _ fun x hx => hz x (Finset.mem_filter.1 hx).2

theorem sprod_mem_closure (X : Finset G) : sprod S hS X ∈ Subgroup.closure S :=
  Finset.noncommProd_induction _ _ _ (· ∈ Subgroup.closure S) (fun _ _ => Subgroup.mul_mem _)
    (Subgroup.one_mem _) fun _ hx => Subgroup.subset_closure (Finset.mem_filter.1 hx).2

theorem conj_sprod {S' : Set G} (hS' : S'.Pairwise Commute) (q : G)
    (hq : ∀ a ∈ S, q * a * q⁻¹ ∈ S') {X : Finset G} (hX : (X : Set G) ⊆ S) :
    q * sprod S hS X * q⁻¹ = sprod S' hS' (X.image fun a => q * a * q⁻¹) := by
  induction X using Finset.induction_on with
  | empty => rw [sprod_empty, Finset.image_empty, sprod_empty, mul_one, mul_inv_cancel]
  | insert a X haX ih =>
    have hXS : (X : Set G) ⊆ S := fun y hy => hX (Finset.mem_insert_of_mem hy)
    have haS : a ∈ S := hX (Finset.mem_insert_self a X)
    have hnot : q * a * q⁻¹ ∉ X.image fun a => q * a * q⁻¹ := by
      rintro h
      obtain ⟨b, hb, hba⟩ := Finset.mem_image.1 h
      exact haX (by rwa [mul_left_inj, mul_right_inj] at hba ▸ hb)
    rw [Finset.image_insert, sprod_insert hS haS haX, sprod_insert hS' (hq a haS) hnot, ← ih hXS]
    group

variable (hinv : ∀ a ∈ S, a * a = 1)
include hinv

theorem sprod_mul_self (X : Finset G) : sprod S hS X * sprod S hS X = 1 := by
  induction X using Finset.induction_on with
  | empty => rw [sprod_empty, mul_one]
  | insert a X haX ih =>
    by_cases haS : a ∈ S
    · rw [sprod_insert hS haS haX]
      have hc := commute_sprod hS (fun b hb => (by
        by_cases hab : a = b
        · rw [hab]
        · exact hS haS hb hab) : ∀ b ∈ S, Commute a b) X
      calc a * sprod S hS X * (a * sprod S hS X)
          = a * a * (sprod S hS X * sprod S hS X) := by
            rw [mul_assoc a, ← mul_assoc (sprod S hS X) a, ← hc.eq]; group
        _ = 1 := by rw [hinv a haS, ih, one_mul]
    · have : sprod S hS (insert a X) = sprod S hS X := by
        unfold sprod
        simp only [Finset.filter_insert, haS, ↓reduceIte]
      rw [this, ih]

theorem sprod_mul_sprod {X Y : Finset G} (hX : (X : Set G) ⊆ S) (hY : (Y : Set G) ⊆ S) :
    sprod S hS X * sprod S hS Y = sprod S hS (symmDiff X Y) := by
  induction X using Finset.induction_on with
  | empty =>
    rw [sprod_empty, one_mul]
    congr 1
    ext y
    simp [Finset.mem_symmDiff]
  | insert a X haX ih =>
    have hXS : (X : Set G) ⊆ S := fun y hy => hX (Finset.mem_insert_of_mem hy)
    have haS : a ∈ S := hX (Finset.mem_insert_self a X)
    have hXY : ((symmDiff X Y : Finset G) : Set G) ⊆ S := by
      intro y hy
      rcases Finset.mem_symmDiff.1 hy with h | h
      · exact hXS h.1
      · exact hY h.1
    rw [sprod_insert hS haS haX, mul_assoc, ih hXS]
    by_cases haY : a ∈ Y
    ·
      have hmem : a ∈ symmDiff X Y := Finset.mem_symmDiff.2 (Or.inr ⟨haY, haX⟩)
      have heq : symmDiff (insert a X) Y = (symmDiff X Y).erase a := by
        ext y
        simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_erase]
        by_cases hy : y = a
        · subst hy; tauto
        · tauto
      have hsplit : sprod S hS (symmDiff X Y) = a * sprod S hS ((symmDiff X Y).erase a) := by
        conv_lhs => rw [← Finset.insert_erase hmem]
        exact sprod_insert hS haS (Finset.notMem_erase a _)
      rw [heq, hsplit, ← mul_assoc, hinv a haS, one_mul]
    · have hnot : a ∉ symmDiff X Y := by
        simp only [Finset.mem_symmDiff, not_or, not_and, not_not]
        exact ⟨fun h => absurd h haX, fun h => absurd h haY⟩
      have heq : symmDiff (insert a X) Y = insert a (symmDiff X Y) := by
        ext y
        simp only [Finset.mem_symmDiff, Finset.mem_insert]
        by_cases hy : y = a
        · subst hy; tauto
        · tauto
      rw [heq, sprod_insert hS haS hnot]

theorem exists_eq_sprod {g : G} (hg : g ∈ Subgroup.closure S) :
    ∃ X : Finset G, (X : Set G) ⊆ S ∧ sprod S hS X = g := by
  induction hg using Subgroup.closure_induction with
  | mem a ha => exact ⟨{a}, by simpa using ha, sprod_singleton hS ha⟩
  | one => exact ⟨∅, by simp, sprod_empty hS⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨X, hX, rfl⟩ := ihx
    obtain ⟨Y, hY, rfl⟩ := ihy
    refine ⟨symmDiff X Y, fun z hz => ?_, (sprod_mul_sprod hS hinv hX hY).symm⟩
    rcases Finset.mem_symmDiff.1 hz with h | h
    · exact hX h.1
    · exact hY h.1
  | inv x _ ihx =>
    obtain ⟨X, hX, rfl⟩ := ihx
    exact ⟨X, hX, (inv_eq_of_mul_eq_one_right (sprod_mul_self hS hinv X)).symm⟩

omit hinv

variable {D : Set G}

theorem pairwise_commute_twinClass (A : Set G) (a : G) : (twinClass A a).Pairwise Commute :=
  fun _ hx _ hy _ => (isTwin_of_mem hx hy).2.2.1

end O2G

end CFSG.Fischer.Classification
