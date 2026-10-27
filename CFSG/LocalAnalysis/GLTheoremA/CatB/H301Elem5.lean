module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301

theorem isElemAbelian_closure_five {G : Type} [Group G] {a b c e f : G}
    (hab : Commute a b) (hac : Commute a c) (hae : Commute a e) (haf : Commute a f)
    (hbc : Commute b c) (hbe : Commute b e) (hbf : Commute b f) (hce : Commute c e)
    (hcf : Commute c f) (hef : Commute e f)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hc : c ^ 3 = 1) (he : e ^ 3 = 1) (hf : f ^ 3 = 1)
    (hind : ∀ i j k l m : ℕ, i < 3 → j < 3 → k < 3 → l < 3 → m < 3 →
      a ^ i * b ^ j * c ^ k * e ^ l * f ^ m = 1 → i = 0 ∧ j = 0 ∧ k = 0 ∧ l = 0 ∧ m = 0) :
    CFSG.Open.IsElemAbelian 3 (Subgroup.closure {a, b, c, e, f}) ∧
      Nat.card (Subgroup.closure {a, b, c, e, f}) = 3 ^ 5 := by
  have hmul : ∀ i j k l m i' j' k' l' m' : ℕ,
      a ^ i * b ^ j * c ^ k * e ^ l * f ^ m * (a ^ i' * b ^ j' * c ^ k' * e ^ l' * f ^ m') =
        a ^ (i + i') * b ^ (j + j') * c ^ (k + k') * e ^ (l + l') * f ^ (m + m') := by
    intro i j k l m i' j' k' l' m'
    simp only [pow_add, mul_assoc]
    rw [((haf.pow_pow i' m).symm).left_comm, ((hae.pow_pow i' l).symm).left_comm,
      ((hac.pow_pow i' k).symm).left_comm, ((hab.pow_pow i' j).symm).left_comm,
      ((hbf.pow_pow j' m).symm).left_comm, ((hbe.pow_pow j' l).symm).left_comm,
      ((hbc.pow_pow j' k).symm).left_comm, ((hcf.pow_pow k' m).symm).left_comm,
      ((hce.pow_pow k' l).symm).left_comm, ((hef.pow_pow l' m).symm).left_comm]
  have hone : ∀ i j k l m : ℕ,
      a ^ (3 * i) * b ^ (3 * j) * c ^ (3 * k) * e ^ (3 * l) * f ^ (3 * m) = 1 := by
    intro i j k l m
    simp [pow_mul, ha, hb, hc, he, hf]
  have hred : ∀ i j k l m : ℕ, a ^ i * b ^ j * c ^ k * e ^ l * f ^ m =
      a ^ (i % 3) * b ^ (j % 3) * c ^ (k % 3) * e ^ (l % 3) * f ^ (m % 3) := by
    intro i j k l m
    rw [pow_eq_pow_mod i ha, pow_eq_pow_mod j hb, pow_eq_pow_mod k hc, pow_eq_pow_mod l he,
      pow_eq_pow_mod m hf]
  have hrep : ∀ g ∈ Subgroup.closure ({a, b, c, e, f} : Set G),
      ∃ i j k l m : ℕ, g = a ^ i * b ^ j * c ^ k * e ^ l * f ^ m := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact ⟨1, 0, 0, 0, 0, by simp⟩
      · exact ⟨0, 1, 0, 0, 0, by simp⟩
      · exact ⟨0, 0, 1, 0, 0, by simp⟩
      · exact ⟨0, 0, 0, 1, 0, by simp⟩
      · exact ⟨0, 0, 0, 0, 1, by simp⟩
    | one => exact ⟨0, 0, 0, 0, 0, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨i, j, k, l, m, rfl⟩ := hx
      obtain ⟨i', j', k', l', m', rfl⟩ := hy
      exact ⟨i + i', j + j', k + k', l + l', m + m', hmul i j k l m i' j' k' l' m'⟩
    | inv x _ hx =>
      obtain ⟨i, j, k, l, m, rfl⟩ := hx
      refine ⟨2 * i, 2 * j, 2 * k, 2 * l, 2 * m, inv_eq_of_mul_eq_one_right ?_⟩
      rw [hmul, show i + 2 * i = 3 * i by ring, show j + 2 * j = 3 * j by ring,
        show k + 2 * k = 3 * k by ring, show l + 2 * l = 3 * l by ring,
        show m + 2 * m = 3 * m by ring, hone]
  have hcomm : ∀ x ∈ Subgroup.closure ({a, b, c, e, f} : Set G),
      ∀ y ∈ Subgroup.closure ({a, b, c, e, f} : Set G), x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, j, k, l, m, rfl⟩ := hrep x hx
    obtain ⟨i', j', k', l', m', rfl⟩ := hrep y hy
    rw [hmul, hmul, Nat.add_comm i, Nat.add_comm j, Nat.add_comm k, Nat.add_comm l,
      Nat.add_comm m]
  refine ⟨⟨isMulCommutative_iff.2 fun x y => Subtype.ext (hcomm x.1 x.2 y.1 y.2), ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨i, j, k, l, m, rfl⟩ := hrep x hx
    rw [pow_three, hmul, hmul, show i + (i + i) = 3 * i by ring,
      show j + (j + j) = 3 * j by ring, show k + (k + k) = 3 * k by ring,
      show l + (l + l) = 3 * l by ring, show m + (m + m) = 3 * m by ring, hone]
  · have hmem : ∀ i j k l m : ℕ,
        a ^ i * b ^ j * c ^ k * e ^ l * f ^ m ∈ Subgroup.closure ({a, b, c, e, f} : Set G) := by
      intro i j k l m
      have ha' : a ∈ Subgroup.closure ({a, b, c, e, f} : Set G) :=
        Subgroup.subset_closure (by simp)
      have hb' : b ∈ Subgroup.closure ({a, b, c, e, f} : Set G) :=
        Subgroup.subset_closure (by simp)
      have hc' : c ∈ Subgroup.closure ({a, b, c, e, f} : Set G) :=
        Subgroup.subset_closure (by simp)
      have he' : e ∈ Subgroup.closure ({a, b, c, e, f} : Set G) :=
        Subgroup.subset_closure (by simp)
      have hf' : f ∈ Subgroup.closure ({a, b, c, e, f} : Set G) :=
        Subgroup.subset_closure (by simp)
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.pow_mem _ ha' i) (Subgroup.pow_mem _ hb' j)) (Subgroup.pow_mem _ hc' k))
        (Subgroup.pow_mem _ he' l)) (Subgroup.pow_mem _ hf' m)
    let φ : Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 3 →
        Subgroup.closure ({a, b, c, e, f} : Set G) :=
      fun t => ⟨a ^ (t.1 : ℕ) * b ^ (t.2.1 : ℕ) * c ^ (t.2.2.1 : ℕ) * e ^ (t.2.2.2.1 : ℕ) *
        f ^ (t.2.2.2.2 : ℕ), hmem _ _ _ _ _⟩
    have hinj : Function.Injective φ := by
      rintro ⟨i, j, k, l, m⟩ ⟨i', j', k', l', m'⟩ h
      have h' : a ^ (i : ℕ) * b ^ (j : ℕ) * c ^ (k : ℕ) * e ^ (l : ℕ) * f ^ (m : ℕ) =
          a ^ (i' : ℕ) * b ^ (j' : ℕ) * c ^ (k' : ℕ) * e ^ (l' : ℕ) * f ^ (m' : ℕ) :=
        congrArg Subtype.val h
      have h1 : a ^ (((i : ℕ) + 2 * i') % 3) * b ^ (((j : ℕ) + 2 * j') % 3) *
          c ^ (((k : ℕ) + 2 * k') % 3) * e ^ (((l : ℕ) + 2 * l') % 3) *
          f ^ (((m : ℕ) + 2 * m') % 3) = 1 := by
        rw [← hred, ← hmul, h', hmul, show (i' : ℕ) + 2 * i' = 3 * i' by ring,
          show (j' : ℕ) + 2 * j' = 3 * j' by ring, show (k' : ℕ) + 2 * k' = 3 * k' by ring,
          show (l' : ℕ) + 2 * l' = 3 * l' by ring, show (m' : ℕ) + 2 * m' = 3 * m' by ring,
          hone]
      obtain ⟨hi, hj, hk, hl, hm⟩ := hind _ _ _ _ _ (Nat.mod_lt _ (by norm_num))
        (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
        (Nat.mod_lt _ (by norm_num)) h1
      have := i.isLt; have := i'.isLt; have := j.isLt; have := j'.isLt; have := k.isLt
      have := k'.isLt; have := l.isLt; have := l'.isLt; have := m.isLt; have := m'.isLt
      have hi' : (i : ℕ) = i' := by omega
      have hj' : (j : ℕ) = j' := by omega
      have hk' : (k : ℕ) = k' := by omega
      have hl' : (l : ℕ) = l' := by omega
      have hm' : (m : ℕ) = m' := by omega
      simp only [Prod.mk.injEq]
      exact ⟨Fin.ext hi', Fin.ext hj', Fin.ext hk', Fin.ext hl', Fin.ext hm'⟩
    have hsurj : Function.Surjective φ := by
      rintro ⟨g, hg⟩
      obtain ⟨i, j, k, l, m, rfl⟩ := hrep g hg
      refine ⟨(⟨i % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 3, Nat.mod_lt _ (by norm_num)⟩,
        ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨l % 3, Nat.mod_lt _ (by norm_num)⟩,
        ⟨m % 3, Nat.mod_lt _ (by norm_num)⟩), Subtype.ext ?_⟩
      exact (hred i j k l m).symm
    rw [← Nat.card_eq_of_bijective φ ⟨hinj, hsurj⟩]
    simp [Nat.card_eq_fintype_card]

end CFSG.LocalAnalysis.GLTheoremA.H301
