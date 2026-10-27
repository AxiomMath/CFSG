module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301

open CFSG.Open

variable {G : Type} [Group G]

theorem isElemAbelian_closure_four {a b c e : G} (hab : Commute a b) (hac : Commute a c)
    (hae : Commute a e) (hbc : Commute b c) (hbe : Commute b e) (hce : Commute c e)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hc : c ^ 3 = 1) (he : e ^ 3 = 1)
    (hind : ∀ i j k l : ℕ, i < 3 → j < 3 → k < 3 → l < 3 → a ^ i * b ^ j * c ^ k * e ^ l = 1 →
      i = 0 ∧ j = 0 ∧ k = 0 ∧ l = 0) :
    IsElemAbelian 3 (Subgroup.closure {a, b, c, e}) ∧
      Nat.card (Subgroup.closure {a, b, c, e}) = 3 ^ 4 := by
  have hmul : ∀ i j k l i' j' k' l' : ℕ,
      a ^ i * b ^ j * c ^ k * e ^ l * (a ^ i' * b ^ j' * c ^ k' * e ^ l') =
        a ^ (i + i') * b ^ (j + j') * c ^ (k + k') * e ^ (l + l') := by
    intro i j k l i' j' k' l'
    simp only [pow_add, mul_assoc]
    rw [((hae.pow_pow i' l).symm).left_comm, ((hac.pow_pow i' k).symm).left_comm,
      ((hab.pow_pow i' j).symm).left_comm, ((hbe.pow_pow j' l).symm).left_comm,
      ((hbc.pow_pow j' k).symm).left_comm, ((hce.pow_pow k' l).symm).left_comm]
  have hone : ∀ i j k l : ℕ, a ^ (3 * i) * b ^ (3 * j) * c ^ (3 * k) * e ^ (3 * l) = 1 := by
    intro i j k l
    simp [pow_mul, ha, hb, hc, he]
  have hred : ∀ i j k l : ℕ, a ^ i * b ^ j * c ^ k * e ^ l =
      a ^ (i % 3) * b ^ (j % 3) * c ^ (k % 3) * e ^ (l % 3) := by
    intro i j k l
    rw [pow_eq_pow_mod i ha, pow_eq_pow_mod j hb, pow_eq_pow_mod k hc, pow_eq_pow_mod l he]
  have hrep : ∀ g ∈ Subgroup.closure ({a, b, c, e} : Set G),
      ∃ i j k l : ℕ, g = a ^ i * b ^ j * c ^ k * e ^ l := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨1, 0, 0, 0, by simp⟩
      · exact ⟨0, 1, 0, 0, by simp⟩
      · exact ⟨0, 0, 1, 0, by simp⟩
      · exact ⟨0, 0, 0, 1, by simp⟩
    | one => exact ⟨0, 0, 0, 0, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨i, j, k, l, rfl⟩ := hx
      obtain ⟨i', j', k', l', rfl⟩ := hy
      exact ⟨i + i', j + j', k + k', l + l', hmul i j k l i' j' k' l'⟩
    | inv x _ hx =>
      obtain ⟨i, j, k, l, rfl⟩ := hx
      refine ⟨2 * i, 2 * j, 2 * k, 2 * l, inv_eq_of_mul_eq_one_right ?_⟩
      rw [hmul, show i + 2 * i = 3 * i by ring, show j + 2 * j = 3 * j by ring,
        show k + 2 * k = 3 * k by ring, show l + 2 * l = 3 * l by ring, hone]
  have hcomm : ∀ x ∈ Subgroup.closure ({a, b, c, e} : Set G),
      ∀ y ∈ Subgroup.closure ({a, b, c, e} : Set G), x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, j, k, l, rfl⟩ := hrep x hx
    obtain ⟨i', j', k', l', rfl⟩ := hrep y hy
    rw [hmul, hmul, Nat.add_comm i, Nat.add_comm j, Nat.add_comm k, Nat.add_comm l]
  refine ⟨⟨isMulCommutative_iff.2 fun x y => Subtype.ext (hcomm x.1 x.2 y.1 y.2), ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨i, j, k, l, rfl⟩ := hrep x hx
    rw [pow_three, hmul, hmul, show i + (i + i) = 3 * i by ring,
      show j + (j + j) = 3 * j by ring, show k + (k + k) = 3 * k by ring,
      show l + (l + l) = 3 * l by ring, hone]
  · have hmem : ∀ i j k l : ℕ,
        a ^ i * b ^ j * c ^ k * e ^ l ∈ Subgroup.closure ({a, b, c, e} : Set G) := by
      intro i j k l
      have ha' : a ∈ Subgroup.closure ({a, b, c, e} : Set G) := Subgroup.subset_closure (by simp)
      have hb' : b ∈ Subgroup.closure ({a, b, c, e} : Set G) := Subgroup.subset_closure (by simp)
      have hc' : c ∈ Subgroup.closure ({a, b, c, e} : Set G) := Subgroup.subset_closure (by simp)
      have he' : e ∈ Subgroup.closure ({a, b, c, e} : Set G) := Subgroup.subset_closure (by simp)
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ ha' i)
        (Subgroup.pow_mem _ hb' j)) (Subgroup.pow_mem _ hc' k)) (Subgroup.pow_mem _ he' l)
    let f : Fin 3 × Fin 3 × Fin 3 × Fin 3 → Subgroup.closure ({a, b, c, e} : Set G) :=
      fun t => ⟨a ^ (t.1 : ℕ) * b ^ (t.2.1 : ℕ) * c ^ (t.2.2.1 : ℕ) * e ^ (t.2.2.2 : ℕ),
        hmem _ _ _ _⟩
    have hinj : Function.Injective f := by
      rintro ⟨i, j, k, l⟩ ⟨i', j', k', l'⟩ h
      have h' : a ^ (i : ℕ) * b ^ (j : ℕ) * c ^ (k : ℕ) * e ^ (l : ℕ) =
          a ^ (i' : ℕ) * b ^ (j' : ℕ) * c ^ (k' : ℕ) * e ^ (l' : ℕ) := congrArg Subtype.val h
      have h1 : a ^ (((i : ℕ) + 2 * i') % 3) * b ^ (((j : ℕ) + 2 * j') % 3) *
          c ^ (((k : ℕ) + 2 * k') % 3) * e ^ (((l : ℕ) + 2 * l') % 3) = 1 := by
        rw [← hred, ← hmul, h', hmul, show (i' : ℕ) + 2 * i' = 3 * i' by ring,
          show (j' : ℕ) + 2 * j' = 3 * j' by ring, show (k' : ℕ) + 2 * k' = 3 * k' by ring,
          show (l' : ℕ) + 2 * l' = 3 * l' by ring, hone]
      obtain ⟨hi, hj, hk, hl⟩ := hind _ _ _ _ (Nat.mod_lt _ (by norm_num))
        (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h1
      have := i.isLt; have := i'.isLt; have := j.isLt; have := j'.isLt
      have := k.isLt; have := k'.isLt; have := l.isLt; have := l'.isLt
      have hi' : (i : ℕ) = i' := by omega
      have hj' : (j : ℕ) = j' := by omega
      have hk' : (k : ℕ) = k' := by omega
      have hl' : (l : ℕ) = l' := by omega
      simp only [Prod.mk.injEq]
      exact ⟨Fin.ext hi', Fin.ext hj', Fin.ext hk', Fin.ext hl'⟩
    have hsurj : Function.Surjective f := by
      rintro ⟨g, hg⟩
      obtain ⟨i, j, k, l, rfl⟩ := hrep g hg
      refine ⟨(⟨i % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 3, Nat.mod_lt _ (by norm_num)⟩,
        ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨l % 3, Nat.mod_lt _ (by norm_num)⟩),
        Subtype.ext ?_⟩
      exact (hred i j k l).symm
    rw [← Nat.card_eq_of_bijective f ⟨hinj, hsurj⟩]
    simp [Nat.card_eq_fintype_card]

end CFSG.LocalAnalysis.GLTheoremA.H301
