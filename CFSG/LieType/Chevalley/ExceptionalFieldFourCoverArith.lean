module

public import CFSG.LieType.Chevalley.ExceptionalFieldFourCoverEdge
public import CFSG.LieType.Chevalley.ExceptionalLargeEvenCoverTorus

public section

namespace CFSG.LieType.Chevalley.ExceptionalCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag}

@[expose] def CrossCoord (v w : Fin τ.rank → ℤ) : Prop :=
  ∀ i < 2, ∀ j < 2, ∃ k, ¬ (3 : ℤ) ∣ 2 ^ i * cartanCoord v k + 2 ^ j * cartanCoord w k

instance (v w : Fin τ.rank → ℤ) : Decidable (CrossCoord v w) := by
  unfold CrossCoord
  infer_instance

variable (τ) in
@[expose] def CrossCheck (n n' : ℕ) : Prop :=
  0 < height (τ.rootCertificate.root n) → 0 < height (τ.rootCertificate.root n') →
    τ.rootCertificate.root n ≠ τ.rootCertificate.root n' →
      CrossCoord (τ.rootCertificate.root n) (τ.rootCertificate.root n')

instance (n n' : ℕ) : Decidable (CrossCheck τ n n') := by
  unfold CrossCheck
  infer_instance

@[expose] def resid (v : Fin τ.rank → ℤ) : List ℤ :=
  List.ofFn fun k => cartanCoord v k % 3

@[expose] def residNeg (v : Fin τ.rank → ℤ) : List ℤ :=
  List.ofFn fun k => (-cartanCoord v k) % 3

@[expose] def enc (l : List ℤ) : ℤ :=
  l.foldr (fun x acc => x + 3 * acc) 0

@[expose] def key (v : Fin τ.rank → ℤ) : ℤ :=
  min (enc (resid v)) (enc (residNeg v))

variable (τ) in
@[expose] def keys : List ℤ :=
  ((List.range τ.rootCertificate.roots.length).filter
    fun n => decide (0 < height (τ.rootCertificate.root n))).map
      fun n => key (τ.rootCertificate.root n)

theorem resid_eq_or_neg_of_dvd {v w : Fin τ.rank → ℤ} {i j : ℕ} (hi : i < 2) (hj : j < 2)
    (h : ∀ k, (3 : ℤ) ∣ 2 ^ i * cartanCoord v k + 2 ^ j * cartanCoord w k) :
    (resid v = resid w ∧ residNeg v = residNeg w) ∨
      (resid v = residNeg w ∧ residNeg v = resid w) := by
  unfold resid residNeg
  obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  all_goals obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
  all_goals simp only [pow_zero, pow_one, one_mul] at h
  · exact Or.inr ⟨congrArg List.ofFn (funext fun k => by have := h k; omega),
      congrArg List.ofFn (funext fun k => by have := h k; omega)⟩
  · exact Or.inl ⟨congrArg List.ofFn (funext fun k => by have := h k; omega),
      congrArg List.ofFn (funext fun k => by have := h k; omega)⟩
  · exact Or.inl ⟨congrArg List.ofFn (funext fun k => by have := h k; omega),
      congrArg List.ofFn (funext fun k => by have := h k; omega)⟩
  · exact Or.inr ⟨congrArg List.ofFn (funext fun k => by have := h k; omega),
      congrArg List.ofFn (funext fun k => by have := h k; omega)⟩

theorem key_eq_of_dvd {v w : Fin τ.rank → ℤ} {i j : ℕ} (hi : i < 2) (hj : j < 2)
    (h : ∀ k, (3 : ℤ) ∣ 2 ^ i * cartanCoord v k + 2 ^ j * cartanCoord w k) :
    key v = key w := by
  unfold key
  rcases resid_eq_or_neg_of_dvd hi hj h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, min_comm]

theorem crossCheck_of_keys_nodup (hk : (keys τ).Nodup) :
    ∀ n < τ.rootCertificate.roots.length, ∀ n' < τ.rootCertificate.roots.length,
      CrossCheck τ n n' := by
  intro n hn n' hn' hp hp' hne
  by_contra hc
  unfold CrossCoord at hc
  push Not at hc
  obtain ⟨i, hi, j, hj, h⟩ := hc
  unfold keys at hk
  have hmem : ∀ m < τ.rootCertificate.roots.length, 0 < height (τ.rootCertificate.root m) →
      m ∈ (List.range τ.rootCertificate.roots.length).filter
        fun n => decide (0 < height (τ.rootCertificate.root n)) := fun m hm hmp =>
    List.mem_filter.2 ⟨List.mem_range.2 hm, decide_eq_true hmp⟩
  exact hne (congrArg τ.rootCertificate.root (List.inj_on_of_nodup_map hk (hmem n hn hp)
    (hmem n' hn' hp') (key_eq_of_dvd hi hj h)))

theorem keys_nodup_E6 : (keys .E6).Nodup := by
  decide +kernel

theorem keys_nodup_E7 : (keys .E7).Nodup := by
  decide +kernel

theorem keys_nodup_E8 : (keys .E8).Nodup := by
  decide +kernel

theorem crossCheck_F4 : ∀ n < Tag.F4.rootCertificate.roots.length,
    ∀ n' < Tag.F4.rootCertificate.roots.length, CrossCheck .F4 n n' := by
  decide +kernel

theorem crossCheck_E6 : ∀ n < Tag.E6.rootCertificate.roots.length,
    ∀ n' < Tag.E6.rootCertificate.roots.length, CrossCheck .E6 n n' :=
  crossCheck_of_keys_nodup keys_nodup_E6

theorem crossCheck_E7 : ∀ n < Tag.E7.rootCertificate.roots.length,
    ∀ n' < Tag.E7.rootCertificate.roots.length, CrossCheck .E7 n n' :=
  crossCheck_of_keys_nodup keys_nodup_E7

theorem crossCheck_E8 : ∀ n < Tag.E8.rootCertificate.roots.length,
    ∀ n' < Tag.E8.rootCertificate.roots.length, CrossCheck .E8 n n' :=
  crossCheck_of_keys_nodup keys_nodup_E8

@[expose] def EdgeSupport (v : Fin τ.rank → ℤ) (i j : Fin τ.rank) : Prop :=
  (∀ l, l ≠ i → l ≠ j → v l = 0) → 1 ≤ v i → 1 ≤ v j → v i = 1 ∧ v j = 1

instance (v : Fin τ.rank → ℤ) (i j : Fin τ.rank) : Decidable (EdgeSupport v i j) := by
  unfold EdgeSupport
  infer_instance

@[expose] def EdgeCond (v : Fin τ.rank → ℤ) (i j : Fin τ.rank) : Prop :=
  τ.cartan i j = -1 → τ.cartan j i = -1 → EdgeSupport v i j

instance (v : Fin τ.rank → ℤ) (i j : Fin τ.rank) : Decidable (EdgeCond v i j) := by
  unfold EdgeCond
  infer_instance

variable (τ) in
@[expose] def EdgeCheck (n : ℕ) : Prop :=
  ∀ i j : Fin τ.rank, EdgeCond (τ.rootCertificate.root n) i j

instance (n : ℕ) : Decidable (EdgeCheck τ n) := by
  unfold EdgeCheck
  infer_instance

theorem edgeCheck_F4 : ∀ n < Tag.F4.rootCertificate.roots.length, EdgeCheck .F4 n := by
  decide +kernel

theorem edgeCheck_E6 : ∀ n < Tag.E6.rootCertificate.roots.length, EdgeCheck .E6 n := by
  decide +kernel

theorem edgeCheck_E7 : ∀ n < Tag.E7.rootCertificate.roots.length, EdgeCheck .E7 n := by
  decide +kernel

theorem edgeCheck_E8 : ∀ n < Tag.E8.rootCertificate.roots.length, EdgeCheck .E8 n := by
  decide +kernel

theorem checks_four_of_tag (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    (∀ n < τ.rootCertificate.roots.length, ∀ n' < τ.rootCertificate.roots.length,
      CrossCheck τ n n') ∧ (∀ n < τ.rootCertificate.roots.length, EdgeCheck τ n) ∧
      ∀ j : Fin τ.rank, HasEdgeNeighbor τ j := by
  rcases hτ with rfl | rfl | rfl | rfl
  · exact ⟨crossCheck_F4, edgeCheck_F4, neighbor_F4⟩
  · exact ⟨crossCheck_E6, edgeCheck_E6, neighbor_E6⟩
  · exact ⟨crossCheck_E7, edgeCheck_E7, neighbor_E7⟩
  · exact ⟨crossCheck_E8, edgeCheck_E8, neighbor_E8⟩

theorem cross_not_dvd
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {α β : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hαp : 0 < height α) (hβ : IsRoot τ β) (hβp : 0 < height β)
    (hne : α ≠ β) (i j : ℕ) (hi : i < 2) (hj : j < 2) :
    ¬ ∀ k, (2 ^ 2 - 1 : ℤ) ∣ 2 ^ i * cartanCoord α k + 2 ^ j * cartanCoord β k := by
  obtain ⟨n, hn, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check τ)).1 hα
  obtain ⟨n', hn', rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check τ)).1 hβ
  obtain ⟨k, hk⟩ := (checks_four_of_tag hτ).1 n hn n' hn' hαp hβp hne i hi j hj
  exact fun h => hk (by simpa using h k)

theorem not_isRoot_edge
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {i j : Fin τ.rank}
    (hij : τ.cartan i j = -1) (hji : τ.cartan j i = -1) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ¬ IsRoot τ (a • Pi.single i 1 + b • (Pi.single i 1 + Pi.single j 1)) := by
  have hne : i ≠ j := fun h => by
    subst h
    rw [τ.cartan_self] at hij
    exact absurd hij (by decide)
  intro hr
  obtain ⟨n, hn, hn'⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check τ)).1 hr
  have h := (checks_four_of_tag hτ).2.1 n hn i j hij hji
  rw [hn'] at h
  have hvi : (a • Pi.single i 1 + b • (Pi.single i 1 + Pi.single j 1) : Fin τ.rank → ℤ) i =
      a + b := by
    simp [hne]
  have hvj : (a • Pi.single i 1 + b • (Pi.single i 1 + Pi.single j 1) : Fin τ.rank → ℤ) j =
      b := by
    simp [hne.symm]
  have hv0 : ∀ l, l ≠ i → l ≠ j →
      (a • Pi.single i 1 + b • (Pi.single i 1 + Pi.single j 1) : Fin τ.rank → ℤ) l = 0 := by
    intro l hli hlj
    simp [hli, hlj]
  obtain ⟨h1, -⟩ := h hv0 (by rw [hvi]; omega) (by rw [hvj]; omega)
  rw [hvi] at h1
  omega

theorem not_isRoot_edge'
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {i j : Fin τ.rank}
    (hij : τ.cartan i j = -1) (hji : τ.cartan j i = -1) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ¬ IsRoot τ (a • Pi.single j 1 + b • (Pi.single i 1 + Pi.single j 1)) := by
  rw [add_comm (Pi.single i 1)]
  exact not_isRoot_edge hτ hji hij ha hb

end CFSG.LieType.Chevalley.ExceptionalCover
