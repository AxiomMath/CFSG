module

public import CFSG.LieType.Steinberg.Basic
public import CFSG.LieType.Steinberg.Collection
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public noncomputable section

namespace CFSG.LieType.Steinberg

open scoped commutatorElement

section Height

variable {ι : Type*} [Fintype ι]

theorem ht_add (v w : ι → ℤ) : ht (v + w) = ht v + ht w := by
  simp [ht, Finset.sum_add_distrib]

theorem ht_neg (v : ι → ℤ) : ht (-v) = -ht v := by
  simp [ht]

theorem ht_nsmul (n : ℕ) (v : ι → ℤ) : ht (n • v) = n * ht v := by
  simp [ht, Finset.mul_sum]

theorem ht_two_smul (v : ι → ℤ) : ht (2 • v) = 2 * ht v := by
  simp [ht, Finset.mul_sum]

theorem ht_single [DecidableEq ι] (i : ι) : ht (Pi.single i 1 : ι → ℤ) = 1 := by
  simp [ht, Finset.sum_pi_single']

end Height

section Pair

variable {ι : Type*}

theorem exists_apply_ne_zero {γ : ι → ℤ} (hγ : γ ≠ 0) : ∃ j, γ j ≠ 0 := by
  by_contra h
  push Not at h
  exact hγ (funext h)

theorem not_isNegMultiple_self {γ : ι → ℤ} (hγ : γ ≠ 0) : ¬ IsNegMultiple γ γ := by
  rintro ⟨c, hc, h⟩
  obtain ⟨j, hj⟩ := exists_apply_ne_zero hγ
  have hj' : (γ j : ℝ) ≠ 0 := by exact_mod_cast hj
  have : c = 1 := mul_right_cancel₀ hj' (by rw [one_mul]; exact (h j).symm)
  linarith

theorem not_isNegMultiple_two_smul {γ : ι → ℤ} (hγ : γ ≠ 0) : ¬ IsNegMultiple γ (2 • γ) := by
  rintro ⟨c, hc, h⟩
  obtain ⟨j, hj⟩ := exists_apply_ne_zero hγ
  have hj' : (γ j : ℝ) ≠ 0 := by exact_mod_cast hj
  have h2 := h j
  simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat, Int.cast_mul, Int.cast_ofNat] at h2
  have : c = 2 := mul_right_cancel₀ hj' h2.symm
  linarith

theorem LinIndepPair.ne_zero_left {γ δ : ι → ℤ} (h : LinIndepPair γ δ) : γ ≠ 0 := by
  rintro rfl
  exact one_ne_zero (h 1 0 (by simp)).1

theorem LinIndepPair.not_isNegMultiple {γ δ : ι → ℤ} (h : LinIndepPair γ δ) :
    ¬ IsNegMultiple γ δ := by
  rintro ⟨c, -, hc⟩
  obtain ⟨j, hj⟩ := exists_apply_ne_zero h.ne_zero_left
  refine hj (h (-(δ j)) (γ j) ?_).2
  funext k
  have e : ((-(δ j) * γ k + γ j * δ k : ℤ) : ℝ) = 0 := by
    push_cast
    rw [hc j, hc k]
    ring
  have e' : -(δ j) * γ k + γ j * δ k = 0 := by exact_mod_cast e
  simpa using e'

theorem LinIndepPair.of_neg {α β : ι → ℤ} (h : LinIndepPair (-α) (-β)) : LinIndepPair α β := by
  intro a b hab
  exact h a b (by rw [zsmul_neg, zsmul_neg, ← neg_add, hab, neg_zero])

theorem mem_cone_left {Ψ : Set (ι → ℤ)} {α : ι → ℤ} (β : ι → ℤ) (hα : α ∈ Ψ) :
    α ∈ cone Ψ α β :=
  ⟨hα, 1, 0, by simp⟩

theorem mem_cone_right {Ψ : Set (ι → ℤ)} (α : ι → ℤ) {β : ι → ℤ} (hβ : β ∈ Ψ) :
    β ∈ cone Ψ α β :=
  ⟨hβ, 0, 1, by simp⟩

theorem openCone_subset_cone (Ψ : Set (ι → ℤ)) (α β : ι → ℤ) : openCone Ψ α β ⊆ cone Ψ α β :=
  fun _ ⟨h, a, b, _, _, e⟩ => ⟨h, a, b, e⟩

end Pair

section Word

variable {ι : Type*} (s : ι → (ι → ℤ) →+ (ι → ℤ))

@[simp] theorem wordAct_nil (v : ι → ℤ) : wordAct s [] v = v := rfl

@[simp] theorem wordAct_cons (i : ι) (w : List ι) (v : ι → ℤ) :
    wordAct s (i :: w) v = s i (wordAct s w v) := rfl

theorem wordAct_append (w₁ w₂ : List ι) (v : ι → ℤ) :
    wordAct s (w₁ ++ w₂) v = wordAct s w₁ (wordAct s w₂ v) := by
  induction w₁ with
  | nil => rfl
  | cons i w ih => simp [ih]

theorem wordAct_neg (w : List ι) (v : ι → ℤ) : wordAct s w (-v) = -wordAct s w v := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [ih]

theorem wordAct_nsmul (w : List ι) (n : ℕ) (v : ι → ℤ) :
    wordAct s w (n • v) = n • wordAct s w v := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [wordAct_cons, wordAct_cons, ih, map_nsmul]

theorem exists_split_wordAct {P : (ι → ℤ) → Prop} {v₀ : ι → ℤ} (h0 : P v₀) :
    ∀ w : List ι, ¬ P (wordAct s w v₀) →
      ∃ p a v, w = p ++ a :: v ∧ P (wordAct s v v₀) ∧ ¬ P (s a (wordAct s v v₀))
  | [], h => absurd h0 h
  | r :: w, h => by
    by_cases hw : P (wordAct s w v₀)
    · exact ⟨[], r, w, rfl, hw, h⟩
    · obtain ⟨p, a, v, rfl, h1, h2⟩ := exists_split_wordAct h0 w hw
      exact ⟨r :: p, a, v, rfl, h1, h2⟩

end Word

namespace RootSystem

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (Φ : RootSystem ι)

theorem ne_zero_of_mem {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) : γ ≠ 0 :=
  fun h => Φ.zero_notMem (h ▸ hγ)

theorem nonneg_of_mem_pos {γ : ι → ℤ} (hγ : γ ∈ Φ.pos) (j : ι) : 0 ≤ γ j := by
  rcases Φ.sign γ hγ.1 with h | h
  · exact h j
  · exact absurd hγ.2 (not_lt.2 (Finset.sum_nonpos fun k _ => h k))

theorem mem_pos_of_pos {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) {j : ι} (hj : 0 < γ j) : γ ∈ Φ.pos := by
  rcases Φ.sign γ hγ with h | h
  · exact ⟨hγ, hj.trans_le (Finset.single_le_sum (fun k _ => h k) (Finset.mem_univ j))⟩
  · exact absurd (h j) (not_le.2 hj)

theorem neg_mem_pos_iff {γ : ι → ℤ} : -γ ∈ Φ.pos ↔ γ ∈ Φ.neg := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by simpa using Φ.neg_mem _ h1, by rw [ht_neg] at h2; linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Φ.neg_mem _ h1, by rw [ht_neg]; linarith⟩

theorem neg_mem_neg_iff {γ : ι → ℤ} : -γ ∈ Φ.neg ↔ γ ∈ Φ.pos := by
  rw [← neg_mem_pos_iff, neg_neg]

theorem mem_neg_of_neg {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) {j : ι} (hj : γ j < 0) : γ ∈ Φ.neg :=
  Φ.neg_mem_pos_iff.1 (Φ.mem_pos_of_pos (Φ.neg_mem γ hγ) (j := j) (by simpa using hj))

theorem mem_pos_or_mem_neg {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) : γ ∈ Φ.pos ∨ γ ∈ Φ.neg := by
  obtain ⟨j, hj⟩ := exists_apply_ne_zero (Φ.ne_zero_of_mem hγ)
  rcases hj.lt_or_gt with h | h
  · exact Or.inr (Φ.mem_neg_of_neg hγ h)
  · exact Or.inl (Φ.mem_pos_of_pos hγ h)

theorem notMem_neg_of_mem_pos {γ : ι → ℤ} (hγ : γ ∈ Φ.pos) : γ ∉ Φ.neg :=
  fun h => absurd hγ.2 (not_lt.2 h.2.le)

theorem isIndiv_neg {γ : ι → ℤ} : Φ.IsIndiv (-γ) ↔ Φ.IsIndiv γ := by
  constructor
  · intro h δ hδ hγδ
    exact h (-δ) (Φ.neg_mem δ hδ) (by rw [hγδ, neg_nsmul])
  · intro h δ hδ hγδ
    exact h (-δ) (Φ.neg_mem δ hδ) (by rw [← neg_neg γ, hγδ, neg_nsmul])

theorem isIndiv_single (i : ι) : Φ.IsIndiv (Pi.single i 1) := by
  intro δ _ h
  have := congrFun h i
  simp at this
  omega

theorem single_mem_pos (i : ι) : (Pi.single i 1 : ι → ℤ) ∈ Φ.pos :=
  ⟨Φ.single_mem i, by rw [ht_single]; exact one_pos⟩

theorem neg_single_mem_neg (i : ι) : -(Pi.single i 1 : ι → ℤ) ∈ Φ.neg :=
  Φ.neg_mem_neg_iff.2 (Φ.single_mem_pos i)

theorem isIndiv_of_two_smul_mem {δ : ι → ℤ} (h2 : 2 • δ ∈ Φ.roots) : Φ.IsIndiv δ := by
  intro ζ hζ hδζ
  subst hδζ
  apply Φ.ne_zero_of_mem hζ
  have hdep : ¬ LinIndepPair (2 • 2 • ζ) ζ := by
    intro h
    have := h 1 (-4) (by funext j; simp; ring)
    exact one_ne_zero this.1
  rcases Φ.proportional _ h2 ζ hζ hdep with h | h | h | h | h | h <;>
    funext j <;> have := congrFun h j <;> simp at this <;> simp <;> omega

theorem exists_eq_two_smul {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) (h : ¬ Φ.IsIndiv γ) :
    ∃ δ ∈ Φ.roots, Φ.IsIndiv δ ∧ γ = 2 • δ := by
  simp only [IsIndiv, not_forall, not_not, exists_prop] at h
  obtain ⟨δ, hδ, rfl⟩ := h
  exact ⟨δ, hδ, Φ.isIndiv_of_two_smul_mem hγ, rfl⟩

theorem linIndepPair_of_mem_pos {γ δ : ι → ℤ} (hγ : γ ∈ Φ.pos) (hγ' : Φ.IsIndiv γ)
    (hδ : δ ∈ Φ.pos) (hδ' : Φ.IsIndiv δ) (hne : γ ≠ δ) : LinIndepPair γ δ := by
  by_contra h
  have h1 := hγ.2
  have h2 := hδ.2
  rcases Φ.proportional γ hγ.1 δ hδ.1 h with h | h | h | h | h | h
  · exact hne h
  · rw [h, ht_neg] at h1; linarith
  · exact hγ' δ hδ.1 h
  · rw [h, ht_neg, ht_two_smul] at h1; linarith
  · exact hδ' γ hγ.1 h
  · rw [h, ht_neg, ht_two_smul] at h2; linarith

theorem linIndepPair_of_mem_neg {γ δ : ι → ℤ} (hγ : γ ∈ Φ.neg) (hγ' : Φ.IsIndiv γ)
    (hδ : δ ∈ Φ.neg) (hδ' : Φ.IsIndiv δ) (hne : γ ≠ δ) : LinIndepPair γ δ :=
  LinIndepPair.of_neg (Φ.linIndepPair_of_mem_pos (Φ.neg_mem_pos_iff.2 hγ) (Φ.isIndiv_neg.2 hγ')
    (Φ.neg_mem_pos_iff.2 hδ) (Φ.isIndiv_neg.2 hδ') (neg_injective.ne hne))

theorem min_lt_ht_of_two_smul {a b δ : ι → ℤ} (ha : a ∈ Φ.pos) (ha' : Φ.IsIndiv a)
    (hb : b ∈ Φ.pos) (hb' : Φ.IsIndiv b) (hab : a ≠ b) (hδ : δ ∈ Φ.roots) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (h : m • a + n • b = 2 • δ) : min (ht a) (ht b) < ht δ := by
  have hht : (m : ℤ) * ht a + n * ht b = 2 * ht δ := by
    rw [← ht_nsmul, ← ht_nsmul, ← ht_add, h, ht_two_smul]
  have ha0 := ha.2
  have hb0 := hb.2
  by_contra hle
  rw [not_lt, le_min_iff] at hle
  obtain ⟨h1, h2⟩ := hle
  have hm1 : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have p1 : 0 ≤ ((m : ℤ) - 1) * ht a := mul_nonneg (by linarith) ha0.le
  have p2 : 0 ≤ ((n : ℤ) - 1) * ht b := mul_nonneg (by linarith) hb0.le
  have e1 : ((m : ℤ) - 1) * ht a = 0 := le_antisymm (by linarith) p1
  have e2 : ((n : ℤ) - 1) * ht b = 0 := le_antisymm (by linarith) p2
  have hm' : m = 1 := by
    rcases mul_eq_zero.1 e1 with e | e
    · omega
    · omega
  have hn' : n = 1 := by
    rcases mul_eq_zero.1 e2 with e | e
    · omega
    · omega
  subst hm' hn'
  have hab' : ht a = ht b := by push_cast at hht; linarith
  rw [one_nsmul, one_nsmul] at h
  exact Φ.sum_ne_two_smul a ha.1 b hb.1 δ hδ ha0 hab' hab ha' hb' h

theorem exists_of_mem_openCone_pos {a b ε : ι → ℤ} (ha : a ∈ Φ.pos) (ha' : Φ.IsIndiv a)
    (hb : b ∈ Φ.pos) (hb' : Φ.IsIndiv b) (hab : a ≠ b) (hε : ε ∈ openCone Φ.roots a b) :
    ∃ c, (c ∈ Φ.pos ∧ Φ.IsIndiv c) ∧ min (ht a) (ht b) < ht c ∧ (c = ε ∨ ε = 2 • c) := by
  obtain ⟨hεr, m, n, hm, hn, rfl⟩ := hε
  have ha0 := ha.2
  have hb0 := hb.2
  have hm1 : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have hge : ht a + ht b ≤ ht (m • a + n • b) := by
    rw [ht_add, ht_nsmul, ht_nsmul]
    nlinarith
  have hmin : min (ht a) (ht b) < ht (m • a + n • b) :=
    lt_of_lt_of_le (lt_of_le_of_lt (min_le_left _ _) (by linarith)) hge
  by_cases hind : Φ.IsIndiv (m • a + n • b)
  · exact ⟨_, ⟨⟨hεr, by linarith⟩, hind⟩, hmin, Or.inl rfl⟩
  · obtain ⟨δ, hδ, hδ', hεδ⟩ := Φ.exists_eq_two_smul hεr hind
    have h2 := ht_two_smul δ
    rw [← hεδ] at h2
    exact ⟨δ, ⟨⟨hδ, by linarith⟩, hδ'⟩,
      Φ.min_lt_ht_of_two_smul ha ha' hb hb' hab hδ hm hn hεδ, Or.inr hεδ⟩

theorem exists_of_mem_openCone_neg {a b ε : ι → ℤ} (ha : a ∈ Φ.neg) (ha' : Φ.IsIndiv a)
    (hb : b ∈ Φ.neg) (hb' : Φ.IsIndiv b) (hab : a ≠ b) (hε : ε ∈ openCone Φ.roots a b) :
    ∃ c, (c ∈ Φ.neg ∧ Φ.IsIndiv c) ∧ min (-ht a) (-ht b) < -ht c ∧ (c = ε ∨ ε = 2 • c) := by
  have hε' : -ε ∈ openCone Φ.roots (-a) (-b) := by
    obtain ⟨hεr, m, n, hm, hn, rfl⟩ := hε
    exact ⟨Φ.neg_mem _ hεr, m, n, hm, hn, by rw [neg_add, neg_nsmul, neg_nsmul]⟩
  obtain ⟨c, ⟨hc, hc'⟩, hlt, hcε⟩ := Φ.exists_of_mem_openCone_pos (Φ.neg_mem_pos_iff.2 ha)
    (Φ.isIndiv_neg.2 ha') (Φ.neg_mem_pos_iff.2 hb) (Φ.isIndiv_neg.2 hb') (neg_injective.ne hab) hε'
  refine ⟨-c, ⟨Φ.neg_mem_neg_iff.2 hc, Φ.isIndiv_neg.2 hc'⟩, ?_, ?_⟩
  · rw [ht_neg, neg_neg]
    rwa [ht_neg, ht_neg] at hlt
  · rcases hcε with rfl | h
    · exact Or.inl (neg_neg ε)
    · right
      rw [neg_nsmul, ← h, neg_neg]

@[expose] def posExcept (i : ι) : Set (ι → ℤ) := Φ.pos \ {Pi.single i 1, 2 • Pi.single i 1}

@[expose] def negExcept (i : ι) : Set (ι → ℤ) :=
  Φ.neg \ {-Pi.single i 1, -(2 • Pi.single i 1)}

theorem posExcept_subset_pos (i : ι) : Φ.posExcept i ⊆ Φ.pos := Set.sdiff_subset

theorem negExcept_subset_neg (i : ι) : Φ.negExcept i ⊆ Φ.neg := Set.sdiff_subset

theorem neg_mem_posExcept_iff {i : ι} {γ : ι → ℤ} : -γ ∈ Φ.posExcept i ↔ γ ∈ Φ.negExcept i := by
  simp only [posExcept, negExcept, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff,
    neg_mem_pos_iff, neg_eq_iff_eq_neg]

theorem mem_posExcept_of_pos {i j : ι} {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) (hji : j ≠ i)
    (hj : 0 < γ j) : γ ∈ Φ.posExcept i := by
  refine ⟨Φ.mem_pos_of_pos hγ hj, ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro (rfl | rfl) <;> simp [hji] at hj

theorem mem_negExcept_of_neg {i j : ι} {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) (hji : j ≠ i)
    (hj : γ j < 0) : γ ∈ Φ.negExcept i :=
  Φ.neg_mem_posExcept_iff.1 (Φ.mem_posExcept_of_pos (Φ.neg_mem γ hγ) hji (by simpa using hj))

theorem exists_pos_of_mem_posExcept {i : ι} {γ : ι → ℤ} (hγ : γ ∈ Φ.posExcept i) :
    ∃ j, j ≠ i ∧ 0 < γ j := by
  obtain ⟨hγp, hγne⟩ := hγ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hγne
  by_contra hcon
  push Not at hcon
  have hzero : ∀ j, j ≠ i → γ j = 0 := fun j hj =>
    le_antisymm (hcon j hj) (Φ.nonneg_of_mem_pos hγp j)
  have hdep : ¬ LinIndepPair γ (Pi.single i 1) := by
    intro h
    have := h 1 (-(γ i)) (by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [hj, hzero j hj])
    exact one_ne_zero this.1
  have hi := Φ.nonneg_of_mem_pos hγp i
  rcases Φ.proportional γ hγp.1 _ (Φ.single_mem i) hdep with h | h | h | h | h | h
  · exact hγne.1 h
  · have := congrFun h i
    simp at this
    omega
  · exact hγne.2 h
  · have := congrFun h i
    simp at this
    omega
  · have := congrFun h i
    simp at this
    omega
  · have := congrFun h i
    simp at this
    omega

theorem exists_neg_of_mem_negExcept {i : ι} {γ : ι → ℤ} (hγ : γ ∈ Φ.negExcept i) :
    ∃ j, j ≠ i ∧ γ j < 0 := by
  obtain ⟨j, hji, hj⟩ := Φ.exists_pos_of_mem_posExcept (Φ.neg_mem_posExcept_iff.2 hγ)
  exact ⟨j, hji, by simpa using hj⟩

theorem refl_mem_posExcept {i : ι} {γ : ι → ℤ} (hγ : γ ∈ Φ.posExcept i) :
    Φ.refl i γ ∈ Φ.posExcept i := by
  obtain ⟨j, hji, hj⟩ := Φ.exists_pos_of_mem_posExcept hγ
  exact Φ.mem_posExcept_of_pos (Φ.refl_mem i γ hγ.1.1) hji
    (by rwa [Φ.refl_apply_of_ne i γ j hji])

theorem refl_mem_negExcept {i : ι} {γ : ι → ℤ} (hγ : γ ∈ Φ.negExcept i) :
    Φ.refl i γ ∈ Φ.negExcept i := by
  obtain ⟨j, hji, hj⟩ := Φ.exists_neg_of_mem_negExcept hγ
  exact Φ.mem_negExcept_of_neg (Φ.refl_mem i γ hγ.1.1) hji
    (by rwa [Φ.refl_apply_of_ne i γ j hji])

omit [Fintype ι] in
theorem apply_eq_zero_of_eq_single {i j : ι} {s : ι → ℤ}
    (hs : s = Pi.single i 1 ∨ s = -Pi.single i 1) (hji : j ≠ i) : s j = 0 := by
  rcases hs with rfl | rfl <;> simp [hji]

theorem openCone_subset_posExcept {i : ι} {s γ : ι → ℤ}
    (hs : s = Pi.single i 1 ∨ s = -Pi.single i 1) (hγ : γ ∈ Φ.posExcept i) :
    openCone Φ.roots s γ ⊆ Φ.posExcept i := by
  obtain ⟨j, hji, hj⟩ := Φ.exists_pos_of_mem_posExcept hγ
  rintro ε ⟨hε, a, b, -, hb, rfl⟩
  refine Φ.mem_posExcept_of_pos hε hji ?_
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, apply_eq_zero_of_eq_single hs hji, smul_zero,
    zero_add, nsmul_eq_mul]
  exact mul_pos (Int.natCast_pos.2 hb) hj

theorem openCone_subset_negExcept {i : ι} {s γ : ι → ℤ}
    (hs : s = Pi.single i 1 ∨ s = -Pi.single i 1) (hγ : γ ∈ Φ.negExcept i) :
    openCone Φ.roots s γ ⊆ Φ.negExcept i := by
  obtain ⟨j, hji, hj⟩ := Φ.exists_neg_of_mem_negExcept hγ
  rintro ε ⟨hε, a, b, -, hb, rfl⟩
  refine Φ.mem_negExcept_of_neg hε hji ?_
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, apply_eq_zero_of_eq_single hs hji, smul_zero,
    zero_add, nsmul_eq_mul]
  exact mul_neg_of_pos_of_neg (Int.natCast_pos.2 hb) hj

omit [Fintype ι] in
theorem linIndepPair_of_apply_ne_zero {i j : ι} {s γ : ι → ℤ}
    (hs : s = Pi.single i 1 ∨ s = -Pi.single i 1) (hji : j ≠ i) (hj : γ j ≠ 0) :
    LinIndepPair s γ := by
  intro a b hab
  have h1 := congrFun hab j
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, apply_eq_zero_of_eq_single hs hji, smul_zero,
    zero_add, smul_eq_mul, Pi.zero_apply, mul_eq_zero] at h1
  have hb : b = 0 := h1.resolve_right hj
  subst hb
  have h2 := congrFun hab i
  rcases hs with rfl | rfl <;> simp at h2 <;> exact ⟨h2, rfl⟩

theorem linIndepPair_of_mem_posExcept {i : ι} {s γ : ι → ℤ}
    (hs : s = Pi.single i 1 ∨ s = -Pi.single i 1) (hγ : γ ∈ Φ.posExcept i) :
    LinIndepPair s γ := by
  obtain ⟨j, hji, hj⟩ := Φ.exists_pos_of_mem_posExcept hγ
  exact linIndepPair_of_apply_ne_zero hs hji hj.ne'

theorem linIndepPair_of_mem_negExcept {i : ι} {s γ : ι → ℤ}
    (hs : s = Pi.single i 1 ∨ s = -Pi.single i 1) (hγ : γ ∈ Φ.negExcept i) :
    LinIndepPair s γ := by
  obtain ⟨j, hji, hj⟩ := Φ.exists_neg_of_mem_negExcept hγ
  exact linIndepPair_of_apply_ne_zero hs hji hj.ne

theorem mem_cases (i : ι) {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) :
    (γ = Pi.single i 1 ∨ γ = -Pi.single i 1 ∨ γ = 2 • Pi.single i 1 ∨
      γ = -(2 • Pi.single i 1)) ∨ γ ∈ Φ.posExcept i ∨ γ ∈ Φ.negExcept i := by
  by_cases h1 : γ = Pi.single i 1
  · exact Or.inl (Or.inl h1)
  by_cases h2 : γ = -Pi.single i 1
  · exact Or.inl (Or.inr (Or.inl h2))
  by_cases h3 : γ = 2 • Pi.single i 1
  · exact Or.inl (Or.inr (Or.inr (Or.inl h3)))
  by_cases h4 : γ = -(2 • Pi.single i 1)
  · exact Or.inl (Or.inr (Or.inr (Or.inr h4)))
  right
  rcases Φ.mem_pos_or_mem_neg hγ with h | h
  · refine Or.inl ⟨h, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h1, h3⟩
  · refine Or.inr ⟨h, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h2, h4⟩

theorem refl_neg_single (i : ι) : Φ.refl i (-Pi.single i 1) = Pi.single i 1 := by
  rw [map_neg, Φ.refl_single, neg_neg]

theorem refl_two_smul_single (i : ι) :
    Φ.refl i (2 • Pi.single i 1) = -(2 • Pi.single i 1) := by
  rw [map_nsmul, Φ.refl_single, neg_nsmul]

theorem refl_neg_two_smul_single (i : ι) :
    Φ.refl i (-(2 • Pi.single i 1)) = 2 • Pi.single i 1 := by
  rw [map_neg, refl_two_smul_single, neg_neg]

theorem wordAct_mem (w : List ι) {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) :
    wordAct Φ.refl w γ ∈ Φ.roots := by
  induction w with
  | nil => exact hγ
  | cons i w ih => exact Φ.refl_mem i _ ih

theorem wordAct_reverse (w : List ι) (v : ι → ℤ) :
    wordAct Φ.refl w.reverse (wordAct Φ.refl w v) = v := by
  induction w generalizing v with
  | nil => rfl
  | cons i w ih => rw [List.reverse_cons, wordAct_append, wordAct_cons, wordAct_cons,
      wordAct_nil, Φ.refl_refl, ih]

theorem isIndiv_wordAct (w : List ι) {γ : ι → ℤ} (hγ : Φ.IsIndiv γ) :
    Φ.IsIndiv (wordAct Φ.refl w γ) := by
  intro ζ hζ h
  apply hγ (wordAct Φ.refl w.reverse ζ) (Φ.wordAct_mem _ hζ)
  rw [← Φ.wordAct_reverse w γ, h, wordAct_nsmul]

end RootSystem

namespace RootGroupData

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : RootSystem ι} {K : Type*} [Group K]
variable (D : RootGroupData Φ K)

@[expose] def stSub (Ψ : Set (ι → ℤ)) : Subgroup (StGroup Φ D.X) :=
  (freeSub Φ D.X Ψ).map (QuotientGroup.mk' (relN Φ D.X))

@[expose] def stRoot (γ : ι → ℤ) : Subgroup (StGroup Φ D.X) := D.stSub {γ}

theorem stPi_mk (w : FreeSt Φ D.X) :
    stPi Φ D.X (QuotientGroup.mk' (relN Φ D.X) w) = piF Φ D.X w :=
  QuotientGroup.lift_mk' _ _ _

theorem piF_of (s : Symbol Φ D.X) : piF Φ D.X (FreeGroup.of s) = s.1.2 :=
  FreeGroup.lift_apply_of

theorem stPi_comp_mk : (stPi Φ D.X).comp (QuotientGroup.mk' (relN Φ D.X)) = piF Φ D.X :=
  MonoidHom.ext D.stPi_mk

theorem freeSub_mono {Ψ Ψ' : Set (ι → ℤ)} (h : Ψ ⊆ Ψ') : freeSub Φ D.X Ψ ≤ freeSub Φ D.X Ψ' :=
  Subgroup.closure_mono (Set.image_mono fun _ hs => h hs)

theorem stSub_mono {Ψ Ψ' : Set (ι → ℤ)} (h : Ψ ⊆ Ψ') : D.stSub Ψ ≤ D.stSub Ψ' :=
  Subgroup.map_mono (D.freeSub_mono h)

theorem stRoot_le_stSub {γ : ι → ℤ} {Ψ : Set (ι → ℤ)} (h : γ ∈ Ψ) : D.stRoot γ ≤ D.stSub Ψ :=
  D.stSub_mono (Set.singleton_subset_iff.2 h)

theorem mk_of_mem_stRoot (s : Symbol Φ D.X) :
    QuotientGroup.mk' (relN Φ D.X) (FreeGroup.of s) ∈ D.stRoot s.1.1 :=
  Subgroup.mem_map_of_mem _ (Subgroup.subset_closure ⟨s, rfl, rfl⟩)

theorem stSub_eq_iSup (Ψ : Set (ι → ℤ)) : D.stSub Ψ = ⨆ γ ∈ Ψ, D.stRoot γ := by
  refine le_antisymm ?_ (iSup₂_le fun γ hγ => D.stRoot_le_stSub hγ)
  rw [stSub, freeSub, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
  exact (le_iSup₂ (f := fun γ (_ : γ ∈ Ψ) => D.stRoot γ) s.1.1 hs) (D.mk_of_mem_stRoot s)

theorem map_stSub {Ψ : Set (ι → ℤ)} (hΨ : Ψ ⊆ Φ.roots) :
    (D.stSub Ψ).map (stPi Φ D.X) = ⨆ γ ∈ Ψ, D.X γ := by
  rw [stSub, Subgroup.map_map, stPi_comp_mk, freeSub, MonoidHom.map_closure]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    rw [piF_of]
    exact (le_iSup₂ (f := fun γ (_ : γ ∈ Ψ) => D.X γ) s.1.1 hs) s.2.2
  · refine iSup₂_le fun γ hγ x hx => Subgroup.subset_closure ⟨FreeGroup.of ⟨(γ, x), hΨ hγ, hx⟩,
      ⟨_, hγ, rfl⟩, D.piF_of _⟩

theorem map_stRoot {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) : (D.stRoot γ).map (stPi Φ D.X) = D.X γ := by
  rw [stRoot, D.map_stSub (Set.singleton_subset_iff.2 hγ), iSup_singleton]

theorem stPi_mem_X {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) {x : StGroup Φ D.X} (hx : x ∈ D.stRoot γ) :
    stPi Φ D.X x ∈ D.X γ := by
  rw [← D.map_stRoot hγ]
  exact Subgroup.mem_map_of_mem _ hx

theorem exists_mem_stRoot {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) {x : K} (hx : x ∈ D.X γ) :
    ∃ y ∈ D.stRoot γ, stPi Φ D.X y = x := by
  rw [← D.map_stRoot hγ] at hx
  exact hx

theorem stSub_roots : D.stSub Φ.roots = ⊤ := by
  have : freeSub Φ D.X Φ.roots = ⊤ := by
    rw [freeSub, eq_top_iff, ← FreeGroup.closure_range_of]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨s, rfl⟩
    exact ⟨s, s.2.1, rfl⟩
  rw [stSub, this, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem injOn_stSub {Ψ : Set (ι → ℤ)}
    (h : ∀ w ∈ freeSub Φ D.X Ψ, piF Φ D.X w = 1 → w ∈ relN Φ D.X) :
    Set.InjOn (stPi Φ D.X) (D.stSub Ψ) := by
  refine injOn_of_eq_one ?_
  rintro _ ⟨w, hw, rfl⟩ h1
  rw [D.stPi_mk] at h1
  exact (QuotientGroup.eq_one_iff w).2 (h w hw h1)

theorem injOn_stSub_of_subset_cone {α β : ι → ℤ} (hα : α ∈ Φ.roots) (hβ : β ∈ Φ.roots)
    (hαβ : ¬ IsNegMultiple α β) {Ψ : Set (ι → ℤ)} (hΨ : Ψ ⊆ cone Φ.roots α β) :
    Set.InjOn (stPi Φ D.X) (D.stSub Ψ) :=
  D.injOn_stSub fun _ hw h1 => Subgroup.subset_normalClosure
    (Or.inl ⟨α, hα, β, hβ, hαβ, D.freeSub_mono hΨ hw, h1⟩)

theorem injOn_stRoot {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) :
    Set.InjOn (stPi Φ D.X) (D.stRoot γ) :=
  D.injOn_stSub_of_subset_cone hγ hγ (not_isNegMultiple_self (Φ.ne_zero_of_mem hγ))
    (Set.singleton_subset_iff.2 (mem_cone_left γ hγ))

@[expose] def stRankOne (i : ι) : Subgroup (StGroup Φ D.X) :=
  D.stRoot (Pi.single i 1) ⊔ D.stRoot (-Pi.single i 1)

theorem stRankOne_eq_stSub (i : ι) :
    D.stRankOne i = D.stSub {Pi.single i 1, -Pi.single i 1} := by
  rw [stSub_eq_iSup, iSup_pair, stRankOne]

theorem stRoot_single_le_stRankOne (i : ι) : D.stRoot (Pi.single i 1) ≤ D.stRankOne i :=
  le_sup_left

theorem stRoot_neg_single_le_stRankOne (i : ι) : D.stRoot (-Pi.single i 1) ≤ D.stRankOne i :=
  le_sup_right

theorem injOn_stRankOne (i : ι) : Set.InjOn (stPi Φ D.X) (D.stRankOne i) := by
  rw [stRankOne_eq_stSub]
  exact D.injOn_stSub fun _ hw h1 => Subgroup.subset_normalClosure (Or.inr ⟨i, hw, h1⟩)

theorem map_stRankOne (i : ι) : (D.stRankOne i).map (stPi Φ D.X) = D.rankOne i := by
  rw [stRankOne, Subgroup.map_sup, D.map_stRoot (Φ.single_mem i),
    D.map_stRoot (Φ.neg_mem _ (Φ.single_mem i)), rankOne]

open scoped _root_.Classical in
@[expose] def stn (i : ι) : StGroup Φ D.X :=
  if h : ∃ g ∈ D.stRankOne i, stPi Φ D.X g = D.n i then h.choose else 1

@[expose] def stnw (w : List ι) : StGroup Φ D.X := (w.map D.stn).prod

@[simp] theorem stnw_nil : D.stnw [] = 1 := rfl

theorem stnw_cons (i : ι) (w : List ι) : D.stnw (i :: w) = D.stn i * D.stnw w := by
  simp [stnw]

theorem stnw_append (w₁ w₂ : List ι) : D.stnw (w₁ ++ w₂) = D.stnw w₁ * D.stnw w₂ := by
  simp [stnw]

theorem stnw_singleton (i : ι) : D.stnw [i] = D.stn i := by
  simp [stnw]

variable {D}

namespace IsSteinberg

variable (hD : D.IsSteinberg)
include hD

theorem stn_spec (i : ι) : D.stn i ∈ D.stRankOne i ∧ stPi Φ D.X (D.stn i) = D.n i := by
  have h : ∃ g ∈ D.stRankOne i, stPi Φ D.X g = D.n i := by
    have := hD.n_mem i
    rw [← D.map_stRankOne] at this
    exact this
  rw [stn, dite_eq_left h]
  exact h.choose_spec

theorem stn_mem (i : ι) : D.stn i ∈ D.stRankOne i := (hD.stn_spec i).1

theorem stPi_stn (i : ι) : stPi Φ D.X (D.stn i) = D.n i := (hD.stn_spec i).2

theorem stRoot_two_smul_le {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) (h2 : 2 • γ ∈ Φ.roots) :
    D.stRoot (2 • γ) ≤ D.stRoot γ := by
  have hcone : ({γ, 2 • γ} : Set (ι → ℤ)) ⊆ cone Φ.roots γ (2 • γ) := by
    rintro _ (rfl | rfl)
    · exact mem_cone_left _ hγ
    · exact mem_cone_right _ h2
  refine le_of_injOn (D.injOn_stSub_of_subset_cone hγ h2
    (not_isNegMultiple_two_smul (Φ.ne_zero_of_mem hγ)) hcone) (D.stRoot_le_stSub (by simp))
    (D.stRoot_le_stSub (by simp)) ?_
  rw [D.map_stRoot h2, D.map_stRoot hγ]
  exact hD.two_smul_le γ hγ h2

theorem commutator_mem_stSub {γ δ : ι → ℤ} (hγ : γ ∈ Φ.roots) (hδ : δ ∈ Φ.roots)
    (hγδ : LinIndepPair γ δ) {x y : StGroup Φ D.X} (hx : x ∈ D.stRoot γ) (hy : y ∈ D.stRoot δ) :
    ⁅x, y⁆ ∈ D.stSub (openCone Φ.roots γ δ) := by
  set M := D.stSub (cone Φ.roots γ δ)
  have hM := D.injOn_stSub_of_subset_cone hγ hδ hγδ.not_isNegMultiple (subset_refl _)
  have hxM : x ∈ M := D.stRoot_le_stSub (mem_cone_left δ hγ) hx
  have hyM : y ∈ M := D.stRoot_le_stSub (mem_cone_right γ hδ) hy
  have hxyM : ⁅x, y⁆ ∈ M := by
    rw [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem hxM hyM) (M.inv_mem hxM)) (M.inv_mem hyM)
  refine mem_of_injOn hM (D.stSub_mono (openCone_subset_cone _ _ _)) hxyM ?_
  rw [D.map_stSub (fun ε hε => hε.1), map_commutatorElement]
  exact hD.commutator_mem γ hγ δ hδ hγδ _ (D.stPi_mem_X hγ hx) _ (D.stPi_mem_X hδ hy)

end IsSteinberg

end RootGroupData

end CFSG.LieType.Steinberg
