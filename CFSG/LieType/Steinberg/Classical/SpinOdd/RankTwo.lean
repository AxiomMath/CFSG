module

public import CFSG.LieType.Steinberg.Classical.SpinOdd.Commutator
public import CFSG.LieType.Steinberg.Classical.SpinOdd.Unipotent

public noncomputable section

namespace CFSG.LieType.Steinberg.SpinOdd

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg.SpinFrame
  CFSG.LieType.RootSystem

variable {n : ℕ} {K : Type} [Field K]

theorem x_injective {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanB n) ∅) :
    Function.Injective (x n K γ) :=
  ((isParametrization (n := n) (K := K)) γ hγ).2.2

theorem eq_of_x_mul_x_eq {a b : Fin n → ℤ} (ha : a ∈ roots (isFiniteType_cartanB n) ∅)
    (hb : b ∈ roots (isFiniteType_cartanB n) ∅) (hab : a ≠ b) (μ : (Fin n → ℤ) →+ ℤ)
    (hμa : 0 < μ a) (hμb : 0 < μ b) (hle : μ a ≤ μ b) {u v u' v' : K}
    (h : x n K a u * x n K b v = x n K a u' * x n K b v') : u = u' ∧ v = v' := by
  classical
  have key := prodInjective (K := K) μ [a, b] (by simp [hab])
    (fun γ hγ => by
      rcases List.mem_pair.mp hγ with rfl | rfl
      · exact ⟨ha, hμa⟩
      · exact ⟨hb, hμb⟩)
    (List.pairwise_pair.mpr hle)
  let g : (Fin n → ℤ) → spinGroup (quadOdd n K) := fun γ => if γ = a then x n K a u else x n K b v
  let g' : (Fin n → ℤ) → spinGroup (quadOdd n K) := fun γ =>
    if γ = a then x n K a u' else x n K b v'
  have hmem : ∀ (w w' : K), ∀ γ ∈ [a, b],
      (if γ = a then x n K a w else x n K b w') ∈ oddRootGroup n K γ := by
    intro w w' γ hγ
    rcases List.mem_pair.mp hγ with rfl | rfl
    · rw [ite_eq_left rfl]
      exact x_mem ha w
    · rw [ite_eq_right (Ne.symm hab)]
      exact x_mem hb w'
  have hgg := key g g' (hmem u v) (hmem u' v') (by
    simp only [g, g', List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      ite_true, ite_eq_right (Ne.symm hab)]
    exact h)
  have h1 := hgg a (by simp)
  have h2 := hgg b (by simp)
  simp only [g, g', ite_true, ite_eq_right (Ne.symm hab)] at h1 h2
  exact ⟨x_injective ha h1, x_injective hb h2⟩

@[expose] def signedCoord (i : Fin n) (s : Bool) : (Fin n → ℤ) →+ ℤ :=
  boolSign s • (Pi.evalAddMonoidHom (fun _ => ℤ) i).comp (Orthogonal.toStdBHom n)

theorem signedCoord_apply (i : Fin n) (s : Bool) (v : Fin n → ℤ) :
    signedCoord i s v = boolSign s * toStdB n v i := rfl

theorem roots_of_isRootVec {γ : Fin n → ℤ} (h : IsRootVec (toStdB n γ)) :
    γ ∈ roots (isFiniteType_cartanB n) ∅ :=
  mem_roots_iff.mpr h

theorem cast_eq_commC {O : CommOrder (Φ n K)} {C : (Fin n → ℤ) → (Fin n → ℤ) → ℕ × ℕ → ℤ}
    (hC : CommutatorFormula (x n K) O C) {α β : Fin n → ℤ}
    (hα : α ∈ roots (isFiniteType_cartanB n) ∅) (hβ : β ∈ roots (isFiniteType_cartanB n) ∅)
    (hαβ : α + β ≠ 0) {p : ℕ × ℕ} (hp : p ∈ expPairs (Φ n K) α β) :
    (C α β p : K) = commC α β p := by
  have heq := (hC α hα β hβ hαβ 1 1).symm.trans (commutatorFormula O α hα β hβ hαβ 1 1)
  simp only [one_pow, mul_one] at heq
  have he : IsRootVec (toStdB n α) := mem_roots_iff.mp hα
  have hf : IsRootVec (toStdB n β) := mem_roots_iff.mp hβ
  have hef : toStdB n α + toStdB n β ≠ 0 := fun h =>
    hαβ (toStdB_injective n (by rw [toStdB_add, h, toStdB_zero]))
  have hmem := mem_list_iff O hα hβ hαβ
  have hpL : p ∈ O.list α β := (O.mem_iff α hα β hβ hαβ p).mpr hp
  have h11' : toStdB n (1 • α + 1 • β) = toStdB n α + toStdB n β := by
    rw [toStdB_comb, one_smul, one_smul]
  have h12' : toStdB n (1 • α + 2 • β) = toStdB n α + 2 • toStdB n β := by
    rw [toStdB_comb, one_smul]
  have h21' : toStdB n (2 • α + 1 • β) = 2 • toStdB n α + toStdB n β := by
    rw [toStdB_comb, one_smul]
  rcases classify (oddFrame n K) he hf hef with ⟨-, -, hl, h12, h21⟩ |
    ⟨⟨q, hq⟩, h12, h21⟩ | ⟨⟨q, hq⟩, h21⟩ | ⟨⟨q, hq⟩, h12⟩ | ⟨h11, h12, h21, -⟩
  ·
    have hL := fun q' => (hmem q').trans (iff_of_one_one (Or.inl hl) h12 h21 q')
    rw [prod_map_of_mem_iff_eq (O.nodup α β) hL, prod_map_of_mem_iff_eq (O.nodup α β) hL] at heq
    obtain rfl := (hL p).mp hpL
    exact x_injective (roots_of_isRootVec (by rw [h11']; exact Or.inl hl)) heq
  ·
    have hL := fun q' => (hmem q').trans (iff_of_one_one (Or.inl hq.isLong_add) h12 h21 q')
    rw [prod_map_of_mem_iff_eq (O.nodup α β) hL, prod_map_of_mem_iff_eq (O.nodup α β) hL] at heq
    obtain rfl := (hL p).mp hpL
    exact x_injective (roots_of_isRootVec (by rw [h11']; exact Or.inl hq.isLong_add)) heq
  ·
    have hL := fun q' => (hmem q').trans
      (iff_of_one_two (Or.inr hq.isShort_add) (Or.inl hq.isLong_add_two_nsmul) h21 q')
    have hcomm : ∀ u v : K, Commute (x n K (1 • α + 1 • β) u) (x n K (1 • α + 2 • β) v) := by
      intro u v
      rw [x, x, h11', h12', elt_of_isShort _ hq.isShort_add,
        elt_of_isLong _ hq.isLong_add_two_nsmul]
      exact commute_shortElt_rootElt_of_isMixedRep _ hq u v
    rw [prod_map_of_mem_iff_eq_or_eq (O.nodup α β) (a := (1, 1)) (b := (1, 2)) (by decide) hL
        (fun p => x n K (p.1 • α + p.2 • β) (C α β p : K)) (hcomm _ _),
      prod_map_of_mem_iff_eq_or_eq (O.nodup α β) (a := (1, 1)) (b := (1, 2)) (by decide) hL
        (fun p => x n K (p.1 • α + p.2 • β) (commC α β p : K)) (hcomm _ _)] at heq
    have ha : toStdB n (1 • α + 1 • β) = Pi.single q.i (boolSign q.s) := by
      rw [h11', hq.add_eq]
    have hb : toStdB n (1 • α + 2 • β) =
        Pi.single q.i (boolSign q.s) + Pi.single q.j (boolSign (!q.t)) := by
      rw [h12', hq.add_two_nsmul_eq]
    have hμa : signedCoord q.i q.s (1 • α + 1 • β) = 1 := by
      rw [signedCoord_apply, ha, Pi.single_eq_same, boolSign_mul_self]
    have hμb : signedCoord q.i q.s (1 • α + 2 • β) = 1 := by
      rw [signedCoord_apply, hb, single_add_single_apply_left hq.1, boolSign_mul_self]
    have hra : 1 • α + 1 • β ∈ roots (isFiniteType_cartanB n) ∅ := by
      refine roots_of_isRootVec ?_
      rw [ha]
      exact Or.inr (isShort_single _ _)
    have hrb : 1 • α + 2 • β ∈ roots (isFiniteType_cartanB n) ∅ := by
      refine roots_of_isRootVec ?_
      rw [hb]
      exact Or.inl (isLong_single_add_single hq.1 _ _)
    have hab : 1 • α + 1 • β ≠ 1 • α + 2 • β := fun h => by
      have h' := congrArg (toStdB n) h
      rw [ha, hb] at h'
      refine (isShort_single q.i q.s).not_isLong ?_
      rw [h']
      exact isLong_single_add_single hq.1 _ _
    obtain ⟨e1, e2⟩ := eq_of_x_mul_x_eq hra hrb hab (signedCoord q.i q.s)
      (by rw [hμa]; exact one_pos) (by rw [hμb]; exact one_pos) (by rw [hμa, hμb]) heq
    rcases (hL p).mp hpL with rfl | rfl
    · exact e1
    · exact e2
  ·
    have h11r : IsRootVec (toStdB n α + toStdB n β) := by
      rw [add_comm]
      exact Or.inr hq.isShort_add
    have h21r : IsRootVec (2 • toStdB n α + toStdB n β) := by
      rw [add_comm]
      exact Or.inl hq.isLong_add_two_nsmul
    have hL := fun q' => (hmem q').trans (iff_of_two_one h11r h12 h21r q')
    have ha : toStdB n (1 • α + 1 • β) = Pi.single q.i (boolSign q.s) := by
      rw [h11', add_comm, hq.add_eq]
    have hb : toStdB n (2 • α + 1 • β) =
        Pi.single q.i (boolSign q.s) + Pi.single q.j (boolSign (!q.t)) := by
      rw [h21', add_comm, hq.add_two_nsmul_eq]
    have hcomm : ∀ u v : K, Commute (x n K (1 • α + 1 • β) u) (x n K (2 • α + 1 • β) v) := by
      intro u v
      rw [x, x, ha, hb, elt_of_isShort _ (isShort_single _ _),
        elt_of_isLong _ (isLong_single_add_single hq.1 _ _), ← hq.add_two_nsmul_eq,
        ← hq.add_eq]
      exact commute_shortElt_rootElt_of_isMixedRep _ hq u v
    rw [prod_map_of_mem_iff_eq_or_eq (O.nodup α β) (a := (1, 1)) (b := (2, 1)) (by decide) hL
        (fun p => x n K (p.1 • α + p.2 • β) (C α β p : K)) (hcomm _ _),
      prod_map_of_mem_iff_eq_or_eq (O.nodup α β) (a := (1, 1)) (b := (2, 1)) (by decide) hL
        (fun p => x n K (p.1 • α + p.2 • β) (commC α β p : K)) (hcomm _ _)] at heq
    have hμa : signedCoord q.i q.s (1 • α + 1 • β) = 1 := by
      rw [signedCoord_apply, ha, Pi.single_eq_same, boolSign_mul_self]
    have hμb : signedCoord q.i q.s (2 • α + 1 • β) = 1 := by
      rw [signedCoord_apply, hb, single_add_single_apply_left hq.1, boolSign_mul_self]
    have hra : 1 • α + 1 • β ∈ roots (isFiniteType_cartanB n) ∅ := by
      refine roots_of_isRootVec ?_
      rw [ha]
      exact Or.inr (isShort_single _ _)
    have hrb : 2 • α + 1 • β ∈ roots (isFiniteType_cartanB n) ∅ := by
      refine roots_of_isRootVec ?_
      rw [hb]
      exact Or.inl (isLong_single_add_single hq.1 _ _)
    have hab : 1 • α + 1 • β ≠ 2 • α + 1 • β := fun h => by
      have h' := congrArg (toStdB n) h
      rw [ha, hb] at h'
      refine (isShort_single q.i q.s).not_isLong ?_
      rw [h']
      exact isLong_single_add_single hq.1 _ _
    obtain ⟨e1, e2⟩ := eq_of_x_mul_x_eq hra hrb hab (signedCoord q.i q.s)
      (by rw [hμa]; exact one_pos) (by rw [hμb]; exact one_pos) (by rw [hμa, hμb]) heq
    rcases (hL p).mp hpL with rfl | rfl
    · exact e1
    · exact e2
  ·
    exfalso
    rcases (hmem p).mp hpL with ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩
    · exact h11 h'
    · exact h12 h'
    · exact h21 h'

private theorem isUnit_of_sign {z : ℤ} (h : z = 1 ∨ z = -1) : IsUnit (z : K) := by
  rcases h with rfl | rfl
  · simp
  · simp

theorem rankTwo (hn : 2 ≤ n) {O : CommOrder (Φ n K)}
    {C : (Fin n → ℤ) → (Fin n → ℤ) → ℕ × ℕ → ℤ} (hC : CommutatorFormula (x n K) O C)
    (i : Fin n) :
    ∃ δ ∈ roots (isFiniteType_cartanB n) ∅, ∃ γ ∈ roots (isFiniteType_cartanB n) ∅, δ + γ ≠ 0 ∧
      ∃ j : ℕ, (j = 1 ∨ j = 2) ∧ (Pi.single i 1 : Fin n → ℤ) = δ + j • γ ∧
        IsUnit (C δ γ (1, j) : K) := by
  have hsingle : (Pi.single i 1 : Fin n → ℤ) ≠ 0 := fun h => by
    simpa using congrFun h i
  by_cases hk : i.val + 1 < n
  ·
    set i' : Fin n := ⟨i.val + 1, hk⟩
    have hii' : i ≠ i' := Fin.ne_of_val_ne (by simp [i'])
    set δ := ofStdB n (Pi.single i (boolSign true) + Pi.single i' (boolSign true))
    set γ := ofStdB n (Pi.single i' (boolSign false))
    have hrep : (⟨i, i', true, true⟩ : PairRep n).IsMixedRep (toStdB n δ) (toStdB n γ) :=
      ⟨hii', toStdB_ofStdB n _, toStdB_ofStdB n _⟩
    have hδ : δ ∈ roots (isFiniteType_cartanB n) ∅ := roots_of_isRootVec (Or.inl hrep.isLong)
    have hγ : γ ∈ roots (isFiniteType_cartanB n) ∅ := roots_of_isRootVec (Or.inr hrep.isShort)
    have hsum : δ + 2 • γ = Pi.single i 1 := by
      apply toStdB_injective n
      rw [toStdB_add, toStdB_nsmul', hrep.add_two_nsmul_eq, toStdB_single_of_lt n hk]
      simp only [boolSign_true, Bool.not_true, boolSign_false, Pi.single_neg, sub_eq_add_neg, i']
    have hne : δ + γ ≠ 0 := fun h => by
      have := congrArg (toStdB n) h
      rw [toStdB_add, hrep.add_eq, toStdB_zero] at this
      exact boolSign_ne_zero true (by simpa using congrFun this i)
    have hp : (1, 2) ∈ expPairs (Φ n K) δ γ :=
      ⟨one_pos, two_pos, by rw [one_smul, hsum]; exact (Φ n K).single_mem i⟩
    refine ⟨δ, hδ, γ, hγ, hne, 2, Or.inr rfl, hsum.symm, ?_⟩
    rw [cast_eq_commC hC hδ hγ hne hp, commC, (commCe_mixed hrep).2]
    exact isUnit_of_sign (mixedSign₂_eq_one_or_eq_neg_one _ _)
  ·
    set k : Fin n := ⟨0, by omega⟩
    have hik : i ≠ k := Fin.ne_of_val_ne (by simp [k]; omega)
    set δ := ofStdB n (Pi.single i (boolSign true) + Pi.single k (boolSign false))
    set γ := ofStdB n (Pi.single k (boolSign true))
    have hrep : (⟨i, k, true, false⟩ : PairRep n).IsMixedRep (toStdB n δ) (toStdB n γ) :=
      ⟨hik, toStdB_ofStdB n _, toStdB_ofStdB n _⟩
    have hδ : δ ∈ roots (isFiniteType_cartanB n) ∅ := roots_of_isRootVec (Or.inl hrep.isLong)
    have hγ : γ ∈ roots (isFiniteType_cartanB n) ∅ := roots_of_isRootVec (Or.inr hrep.isShort)
    have hsum : δ + γ = Pi.single i 1 := by
      apply toStdB_injective n
      rw [toStdB_add, hrep.add_eq, toStdB_single_of_not_lt n hk, boolSign_true]
    have hne : δ + γ ≠ 0 := by
      rw [hsum]
      exact hsingle
    have hp : (1, 1) ∈ expPairs (Φ n K) δ γ :=
      ⟨one_pos, one_pos, by rw [one_smul, one_smul, hsum]; exact (Φ n K).single_mem i⟩
    refine ⟨δ, hδ, γ, hγ, hne, 1, Or.inl rfl, by rw [one_smul, hsum], ?_⟩
    rw [cast_eq_commC hC hδ hγ hne hp, commC, (commCe_mixed hrep).1]
    exact isUnit_of_sign (mixedSign₁_eq_one_or_eq_neg_one _ _)

end CFSG.LieType.Steinberg.SpinOdd
