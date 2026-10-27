module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.QuasithinUnique.Bridge.J2Excl

@[expose] def conjF (mulF : ℕ → ℕ → ℕ) (invF : ℕ → ℕ) (s i : ℕ) : ℕ := mulF (mulF s i) (invF s)

@[expose] def inFgF (mulF : ℕ → ℕ → ℕ) (a b u : ℕ) : Bool := u == a || u == b || u == mulF a b

@[expose] def goodPairF (N : ℕ) (mulF : ℕ → ℕ → ℕ) (invF : ℕ → ℕ) (reps : List (ℕ × ℕ))
    (i j : ℕ) : Bool :=
  reps.any fun ab => (List.range N).any fun s =>
    conjF mulF invF s i != conjF mulF invF s j && inFgF mulF ab.1 ab.2 (conjF mulF invF s i) &&
      inFgF mulF ab.1 ab.2 (conjF mulF invF s j)

@[expose] def isInvF (mulF : ℕ → ℕ → ℕ) (k : ℕ) : Bool := k != 0 && mulF k k == 0

@[expose] def goodTblF (N : ℕ) (mulF : ℕ → ℕ → ℕ) (invF : ℕ → ℕ) (reps : List (ℕ × ℕ)) :
    Array Bool :=
  ((List.range (N * N)).map fun k =>
    isInvF mulF (k / N) && isInvF mulF (k % N) && mulF (k / N) (k % N) == mulF (k % N) (k / N) &&
      goodPairF N mulF invF reps (k / N) (k % N)).toArray

@[expose] def tripleOKF (N : ℕ) (mulF : ℕ → ℕ → ℕ) (good : ℕ → ℕ → Bool) : Bool :=
  let inv := (List.range N).filter (isInvF mulF)
  inv.all fun i => inv.all fun j => inv.all fun k =>
    !(i != j && i != k && i != mulF j k && j != k && mulF i j == mulF j i &&
      mulF i k == mulF k i && mulF j k == mulF k j) || good i j || good i k || good j k

theorem isInvF_iff {mulF : ℕ → ℕ → ℕ} {k : ℕ} : isInvF mulF k = true ↔ k ≠ 0 ∧ mulF k k = 0 := by
  simp [isInvF]

section Spec

variable {G : Type*} [Group G] {N : ℕ} {E : ℕ → G} {mulF : ℕ → ℕ → ℕ} {invF : ℕ → ℕ}

theorem conjF_spec (hmul : ∀ i < N, ∀ j < N, mulF i j < N ∧ E (mulF i j) = E i * E j)
    (hinv : ∀ s < N, invF s < N ∧ E (invF s) = (E s)⁻¹) {s i : ℕ} (hs : s < N) (hi : i < N) :
    conjF mulF invF s i < N ∧ E (conjF mulF invF s i) = E s * E i * (E s)⁻¹ := by
  obtain ⟨h1, h2⟩ := hmul s hs i hi
  obtain ⟨h3, h4⟩ := hinv s hs
  obtain ⟨h5, h6⟩ := hmul _ h1 _ h3
  exact ⟨h5, by rw [conjF, h6, h2, h4]⟩

theorem goodPairF_spec (hmul : ∀ i < N, ∀ j < N, mulF i j < N ∧ E (mulF i j) = E i * E j)
    (hinv : ∀ s < N, invF s < N ∧ E (invF s) = (E s)⁻¹)
    (hinj : ∀ i < N, ∀ j < N, E i = E j → i = j) {reps : List (ℕ × ℕ)}
    (hreps : ∀ ab ∈ reps, ab.1 < N ∧ ab.2 < N) {i j : ℕ} (hi : i < N) (hj : j < N)
    (h : goodPairF N mulF invF reps i j = true) :
    ∃ ab ∈ reps, ∃ s < N, E s * E i * (E s)⁻¹ ≠ E s * E j * (E s)⁻¹ ∧
      (E s * E i * (E s)⁻¹ = E ab.1 ∨ E s * E i * (E s)⁻¹ = E ab.2 ∨
        E s * E i * (E s)⁻¹ = E ab.1 * E ab.2) ∧
      (E s * E j * (E s)⁻¹ = E ab.1 ∨ E s * E j * (E s)⁻¹ = E ab.2 ∨
        E s * E j * (E s)⁻¹ = E ab.1 * E ab.2) := by
  simp only [goodPairF, List.any_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq]
    at h
  obtain ⟨ab, hab, s, hs, ⟨hne, hu⟩, hv⟩ := h
  obtain ⟨hu1, hu2⟩ := conjF_spec hmul hinv hs hi
  obtain ⟨hv1, hv2⟩ := conjF_spec hmul hinv hs hj
  obtain ⟨ha1, ha2⟩ := hreps ab hab
  have hab' := hmul ab.1 ha1 ab.2 ha2
  have hfg : ∀ u : ℕ, u < N → inFgF mulF ab.1 ab.2 u = true →
      E u = E ab.1 ∨ E u = E ab.2 ∨ E u = E ab.1 * E ab.2 := by
    intro u hu0 hh
    simp only [inFgF, Bool.or_eq_true, beq_iff_eq] at hh
    rcases hh with (h1 | h1) | h1
    · exact Or.inl (by rw [h1])
    · exact Or.inr (Or.inl (by rw [h1]))
    · exact Or.inr (Or.inr (by rw [h1, hab'.2]))
  refine ⟨ab, hab, s, hs, ?_, ?_, ?_⟩
  · rw [← hu2, ← hv2]
    intro heq
    exact hne (hinj _ hu1 _ hv1 heq)
  · rw [← hu2]
    exact hfg _ hu1 (by simpa using hu)
  · rw [← hv2]
    exact hfg _ hv1 (by simpa using hv)

theorem goodTblF_spec {reps : List (ℕ × ℕ)} {i j : ℕ} (hi : i < N) (hj : j < N)
    (h : (goodTblF N mulF invF reps).getD (i * N + j) false = true) :
    goodPairF N mulF invF reps i j = true := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hi
  have hk : i * N + j < N * N := by
    calc i * N + j < i * N + N := by omega
      _ = (i + 1) * N := by ring
      _ ≤ N * N := Nat.mul_le_mul_right N hi
  have hdiv : (i * N + j) / N = i := by
    rw [Nat.mul_comm i N, Nat.mul_add_div hN, Nat.div_eq_of_lt hj, Nat.add_zero]
  have hmod : (i * N + j) % N = j := by
    rw [Nat.mul_comm i N, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  simp only [goodTblF, hk, hdiv, hmod, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_map, List.getElem?_range, Option.map_some, Option.getD_some,
    Bool.and_eq_true] at h
  exact h.2

theorem tripleOKF_spec {good : ℕ → ℕ → Bool} (h : tripleOKF N mulF good = true) {i j k : ℕ}
    (hi : i < N) (hj : j < N) (hk : k < N) (hii : isInvF mulF i = true)
    (hjj : isInvF mulF j = true) (hkk : isInvF mulF k = true) (hij : i ≠ j) (hik : i ≠ k)
    (hijk : i ≠ mulF j k) (hjk : j ≠ k) (hcij : mulF i j = mulF j i) (hcik : mulF i k = mulF k i)
    (hcjk : mulF j k = mulF k j) : good i j = true ∨ good i k = true ∨ good j k = true := by
  simp only [tripleOKF, List.all_eq_true, List.mem_filter, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  have h1 := h i ⟨hi, hii⟩ j ⟨hj, hjj⟩ k ⟨hk, hkk⟩
  have hg : (i != j && i != k && i != mulF j k && j != k && mulF i j == mulF j i &&
      mulF i k == mulF k i && mulF j k == mulF k j) = true := by
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
    exact ⟨⟨⟨⟨⟨⟨hij, hik⟩, hijk⟩, hjk⟩, hcij⟩, hcik⟩, hcjk⟩
  rcases h1 with ((h1 | h1) | h1) | h1
  · rw [hg] at h1
    exact absurd h1 (by simp)
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)

end Spec

end CFSG.QuasithinUnique.Bridge.J2Excl
