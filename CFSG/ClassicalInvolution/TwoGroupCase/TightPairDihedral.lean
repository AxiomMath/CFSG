module

public import CFSG.ClassicalInvolution.TwoGroupCase.TightPair
public import CFSG.ClassicalInvolution.TwoGroupCase.FourGroupCentralizer

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open

universe u

namespace PairData

variable {G : Type u} [Group G] [Finite G] {K : Subgroup G} {g : G} {R S : Subgroup G}
  (d : PairData K g R S)
include d

theorem exists_fourCentralizer (hR1 : R ≠ ⊥) (hR2 : Nat.card R = 2) :
    ∃ r z : S, FourCentralizer S r z := by
  classical
  obtain ⟨-, h4, -, hcen, z, hz, hz1, hzc, hS₁⟩ := d.card_two_structure hR1 hR2
  obtain ⟨⟨r, hrR⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR1
  have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
  have hrS : r ∈ S := d.le hrR
  have hzS : z ∈ S := hz.1.1
  have hrr : r * r = 1 := mul_self_eq_one_of_natCard_eq_two hR2 r hrR
  obtain ⟨w, -, hw⟩ := (Nat.card_eq_two_iff' (1 : R)).mp hR2
  have hRel : ∀ y ∈ R, y = 1 ∨ y = r := by
    intro y hy
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    · right
      have h1 := hw ⟨y, hy⟩ (fun h => hy1 (congrArg Subtype.val h))
      have h2 := hw ⟨r, hrR⟩ hr1
      exact congrArg Subtype.val (h1.trans h2.symm)
  have hzz : z * z = 1 := by
    rcases hS₁ (z * z) ((S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G)).mul_mem hz hz)
      with h | h
    · exact h
    · exfalso
      apply hz1
      exact mul_left_cancel (a := z) (by rw [h, mul_one])
  have hrz : r ≠ z := by
    intro h
    have hmem : r ∈ S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) ⊓ R := ⟨h ▸ hz, hrR⟩
    rw [d.S₁_inf_R, Subgroup.mem_bot] at hmem
    exact hr1' hmem
  have hrV : r ∈ S ⊓ Subgroup.normalizer (R : Set G) := ⟨hrS, Subgroup.le_normalizer hrR⟩
  have hzV : z ∈ S ⊓ Subgroup.normalizer (R : Set G) := ⟨hzS, hz.2⟩
  have hrzV : r * z ∈ S ⊓ Subgroup.normalizer (R : Set G) :=
    (S ⊓ Subgroup.normalizer (R : Set G)).mul_mem hrV hzV
  have hrz1 : r * z ≠ 1 := fun h =>
    hrz ((eq_inv_of_mul_eq_one_left h).trans (inv_eq_of_mul_eq_one_right hzz))
  have hV : ∀ x ∈ S ⊓ Subgroup.normalizer (R : Set G),
      x = 1 ∨ x = r ∨ x = z ∨ x = r * z := by
    have hn1 : (1 : G) ∉ ({r, z, r * z} : Finset G) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hr1'.symm, hz1.symm, hrz1.symm⟩
    have hn2 : r ∉ ({z, r * z} : Finset G) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hrz, fun h => hz1 (by simpa using h.symm)⟩
    have hn3 : z ∉ ({r * z} : Finset G) := by
      simp only [Finset.mem_singleton]
      intro h
      exact hr1' (by simpa using h.symm)
    have hT : ({1, r, z, r * z} : Finset G).card = 4 := by
      rw [Finset.card_insert_of_notMem hn1, Finset.card_insert_of_notMem hn2,
        Finset.card_insert_of_notMem hn3, Finset.card_singleton]
    have hsub : (({1, r, z, r * z} : Finset G) : Set G) ⊆
        ((S ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) : Set G) := by
      intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact hrV
      · exact hzV
      · exact hrzV
    have heq := Set.eq_of_subset_of_ncard_le hsub (by
      rw [Set.ncard_coe_finset, hT, ← Nat.card_coe_set_eq]; exact h4.le) (Set.toFinite _)
    intro x hx
    have hx' : x ∈ (({1, r, z, r * z} : Finset G) : Set G) := heq ▸ hx
    simpa using hx'
  refine ⟨⟨r, hrS⟩, ⟨z, hzS⟩, d.S_two, Subtype.ext hrr, fun h => hr1' (congrArg Subtype.val h),
    Subtype.ext hzz, fun h => hz1 (congrArg Subtype.val h),
    fun h => hrz (congrArg Subtype.val h), fun s => Subtype.ext (hzc s s.2).symm, fun x => ?_⟩
  constructor
  · intro hx
    have hxG : (x : G) * r = r * x := congrArg Subtype.val hx
    have hxC : (x : G) ∈ Subgroup.centralizer (R : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rcases hRel y hy with rfl | rfl
      · simp
      · exact hxG.symm
    have hxV : (x : G) ∈ S ⊓ Subgroup.normalizer (R : Set G) := by
      rw [← hcen]
      exact ⟨x.2, hxC⟩
    rcases hV x hxV with h | h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))
  · rintro (rfl | rfl | rfl | rfl)
    · simp
    · rfl
    · exact Subtype.ext (hzc r hrS)
    · apply Subtype.ext
      show (r * z) * r = r * (r * z)
      calc (r * z) * r = r * (z * r) := mul_assoc _ _ _
        _ = r * (r * z) := by rw [hzc r hrS]

theorem isDihedral_or_semidihedral_of_card_two (hR1 : R ≠ ⊥) (hR2 : Nat.card R = 2) :
    Nat.card S = 4 ∨ ∃ m' : ℕ, Nat.card S = 2 ^ (m' + 3) ∧
      (Nonempty (S ≃* DihedralGroup (2 ^ (m' + 2))) ∨
        (1 ≤ m' ∧ Nonempty (S ≃* SemidihedralGroup (m' + 3)))) := by
  obtain ⟨r, z, h⟩ := d.exists_fourCentralizer hR1 hR2
  exact h.classification

end PairData

end CFSG.ClassicalInvolution
