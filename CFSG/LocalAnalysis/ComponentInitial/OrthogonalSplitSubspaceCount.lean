module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitSubspaceCountFlags
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalPointCount

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module Submodule

section Std

variable {r : ℕ} {K : Type*} [Field K]

theorem mem_flag {i : ℕ} {v : Fin r ⊕ Fin r → K} :
    v ∈ flag r K i ↔ (∀ j, v (Sum.inr j) = 0) ∧ ∀ j : Fin r, i ≤ (j : ℕ) → v (Sum.inl j) = 0 := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      refine ⟨fun j => by simp, fun j hj => ?_⟩
      have hlj : l ≠ j := fun h => by
        subst h
        exact absurd hl (not_lt.mpr hj)
      simp [hlj.symm]
    | zero => exact ⟨fun _ => rfl, fun _ _ => rfl⟩
    | add x y _ _ hx hy =>
      exact ⟨fun j => by simp [hx.1 j, hy.1 j], fun j hj => by simp [hx.2 j hj, hy.2 j hj]⟩
    | smul c x _ hx => exact ⟨fun j => by simp [hx.1 j], fun j hj => by simp [hx.2 j hj]⟩
  · rintro ⟨h1, h2⟩
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun x _ => ?_
    rcases x with j | j
    · by_cases hj : (j : ℕ) < i
      · have : (Pi.single (Sum.inl j) (v (Sum.inl j)) : Fin r ⊕ Fin r → K) =
            v (Sum.inl j) • Pi.single (Sum.inl j) 1 := by
          rw [← Pi.single_smul, smul_eq_mul, mul_one]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
      · rw [h2 j (not_lt.mp hj), Pi.single_zero]
        exact Submodule.zero_mem _
    · rw [h1 j, Pi.single_zero]
      exact Submodule.zero_mem _

theorem polar_flag_eq_zero_iff {i : ℕ} {v : Fin r ⊕ Fin r → K} :
    (∀ w ∈ flag r K i, polar (quadPlus r K) v w = 0) ↔
      ∀ j : Fin r, (j : ℕ) < i → v (Sum.inr j) = 0 := by
  constructor
  · intro h j hj
    have := h _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    rwa [polar_single] at this
  · intro h w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      rw [polar_single]
      exact h j hj
    | zero => exact polar_zero_right _ _
    | add x y _ _ hx hy => rw [polar_add_right, hx, hy, add_zero]
    | smul c x _ hx => rw [polar_smul_right_eq, hx, mul_zero]

def splitIdx {j : ℕ} (hj : j ≤ r) : Fin j ⊕ Fin (r - j) ≃ Fin r :=
  finSumFinEquiv.trans (finCongr (by omega))

theorem splitIdx_inl {j : ℕ} (hj : j ≤ r) (i : Fin j) : (splitIdx hj (Sum.inl i) : ℕ) = i := by
  simp [splitIdx]

theorem splitIdx_inr {j : ℕ} (hj : j ≤ r) (t : Fin (r - j)) :
    (splitIdx hj (Sum.inr t) : ℕ) = j + t := by
  simp [splitIdx]

def highPart {j : ℕ} (hj : j ≤ r) (v : Fin r ⊕ Fin r → K) : Fin (r - j) ⊕ Fin (r - j) → K :=
  Sum.elim (fun t => v (Sum.inl (splitIdx hj (Sum.inr t))))
    (fun t => v (Sum.inr (splitIdx hj (Sum.inr t))))

theorem quadPlus_eq_add_highPart {j : ℕ} (hj : j ≤ r) (v : Fin r ⊕ Fin r → K) :
    quadPlus r K v = ∑ i : Fin j, v (Sum.inl (splitIdx hj (Sum.inl i))) *
        v (Sum.inr (splitIdx hj (Sum.inl i))) + quadPlus (r - j) K (highPart hj v) := by
  rw [quadPlus_apply, quadPlus_apply, ← Equiv.sum_comp (splitIdx hj), Fintype.sum_sum_type]
  rfl


def joinPart {j : ℕ} (hj : j ≤ r) (a : Fin j → K) (u : Fin (r - j) ⊕ Fin (r - j) → K) :
    Fin r ⊕ Fin r → K :=
  Sum.elim (fun p => Sum.elim a (fun t => u (Sum.inl t)) ((splitIdx hj).symm p))
    (fun p => Sum.elim (fun _ => (0 : K)) (fun t => u (Sum.inr t)) ((splitIdx hj).symm p))

theorem highPart_joinPart {j : ℕ} (hj : j ≤ r) (a : Fin j → K)
    (u : Fin (r - j) ⊕ Fin (r - j) → K) : highPart hj (joinPart hj a u) = u := by
  funext s
  rcases s with t | t <;> simp [highPart, joinPart]

theorem mem_flag_iff_highPart {j : ℕ} (hj : j ≤ r) {v : Fin r ⊕ Fin r → K}
    (hv : ∀ i : Fin j, v (Sum.inr (splitIdx hj (Sum.inl i))) = 0) :
    v ∈ flag r K j ↔ highPart hj v = 0 := by
  rw [mem_flag]
  constructor
  · rintro ⟨h1, h2⟩
    funext s
    rcases s with t | t
    · exact h2 _ (by rw [splitIdx_inr]; omega)
    · exact h1 _
  · intro h
    refine ⟨fun p => ?_, fun p hp => ?_⟩
    · obtain ⟨s, rfl⟩ := (splitIdx hj).surjective p
      rcases s with i | t
      · exact hv i
      · exact congrFun h (Sum.inr t)
    · obtain ⟨s, rfl⟩ := (splitIdx hj).surjective p
      rcases s with i | t
      · rw [splitIdx_inl] at hp
        exact absurd i.isLt (by omega)
      · exact congrFun h (Sum.inl t)

theorem polar_flag_eq_zero_iff' {j : ℕ} (hj : j ≤ r) {v : Fin r ⊕ Fin r → K} :
    (∀ w ∈ flag r K j, polar (quadPlus r K) v w = 0) ↔
      ∀ i : Fin j, v (Sum.inr (splitIdx hj (Sum.inl i))) = 0 := by
  rw [polar_flag_eq_zero_iff]
  constructor
  · intro h i
    exact h _ (by rw [splitIdx_inl]; exact i.isLt)
  · intro h p hp
    obtain ⟨s, rfl⟩ := (splitIdx hj).surjective p
    rcases s with i | t
    · exact h i
    · rw [splitIdx_inr] at hp
      omega

end Std

section Singular

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def singularOrthOutside (Q : QuadraticForm K V) (U : Submodule K V) : Set V :=
  {x | x ∉ U ∧ Q x = 0 ∧ ∀ w ∈ U, polar Q x w = 0}

end Singular

section StdCount

variable {r : ℕ} {K : Type*} [Field K]

theorem card_singularOrthOutside_flag {j : ℕ} (hj : j ≤ r) :
    Nat.card (singularOrthOutside (quadPlus r K) (flag r K j)) =
      Nat.card (Fin j → K) * Nat.card {u : Fin (r - j) ⊕ Fin (r - j) → K //
        u ≠ 0 ∧ quadPlus (r - j) K u = 0} := by
  rw [← Nat.card_prod]
  have hlow : ∀ x ∈ singularOrthOutside (quadPlus r K) (flag r K j),
      ∀ i : Fin j, x (Sum.inr (splitIdx hj (Sum.inl i))) = 0 :=
    fun x hx => (polar_flag_eq_zero_iff' hj).1 hx.2.2
  have hQ : ∀ x ∈ singularOrthOutside (quadPlus r K) (flag r K j),
      quadPlus (r - j) K (highPart hj x) = 0 := fun x hx => by
    have h := quadPlus_eq_add_highPart hj x
    rw [hx.2.1, Finset.sum_eq_zero fun i _ => by rw [hlow x hx i, mul_zero], zero_add] at h
    exact h.symm
  refine Nat.card_congr
    { toFun := fun x => (fun i => (x : Fin r ⊕ Fin r → K) (Sum.inl (splitIdx hj (Sum.inl i))),
        ⟨highPart hj x, fun h0 => x.2.1 ((mem_flag_iff_highPart hj (hlow x x.2)).2 h0),
          hQ x x.2⟩)
      invFun := fun p => ⟨joinPart hj p.1 p.2, ?_, ?_, ?_⟩
      left_inv := fun x => ?_
      right_inv := fun p => ?_ }
  · have hv : ∀ i : Fin j, joinPart hj p.1 p.2 (Sum.inr (splitIdx hj (Sum.inl i))) = 0 :=
      fun i => by simp [joinPart]
    rw [mem_flag_iff_highPart hj hv, highPart_joinPart]
    exact p.2.2.1
  · rw [quadPlus_eq_add_highPart hj, highPart_joinPart,
      Finset.sum_eq_zero fun i _ => by simp [joinPart], zero_add]
    exact p.2.2.2
  · rw [polar_flag_eq_zero_iff' hj]
    intro i
    simp [joinPart]
  · apply Subtype.ext
    funext c
    rcases c with p | p <;> obtain ⟨s, rfl⟩ := (splitIdx hj).surjective p <;>
      rcases s with i | t <;> simp [joinPart, highPart, hlow x x.2]
  · refine Prod.ext (funext fun i => by simp [joinPart]) (Subtype.ext (highPart_joinPart hj _ _))


theorem card_quadPlus_nonzero_singular [Finite K] (m : ℕ) :
    Nat.card {u : Fin m ⊕ Fin m → K // u ≠ 0 ∧ quadPlus m K u = 0} =
      (Nat.card K ^ m - 1) * (Nat.card K ^ (m - 1) + 1) := by
  rw [← (orthogonal_geometry_split_point_count K m).1, ← card_singular_vectors]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun u => by simp)

end StdCount

section Extensions

variable {r : ℕ} {K : Type*} [Field K]

theorem card_singularOrthOutside_map {V : Type*} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (U : Submodule K V) :
    Nat.card (singularOrthOutside Q (U.map (g : V →ₗ[K] V))) =
      Nat.card (singularOrthOutside Q U) := by
  have hmem : ∀ x, g x ∈ U.map (g : V →ₗ[K] V) ↔ x ∈ U := fun x =>
    ⟨fun ⟨y, hy, hyx⟩ => by rwa [g.injective hyx] at hy, fun hx => ⟨x, hx, rfl⟩⟩
  have hiff : ∀ x, x ∈ singularOrthOutside Q U ↔
      g x ∈ singularOrthOutside Q (U.map (g : V →ₗ[K] V)) := by
    intro x
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by rwa [hmem], by rw [map_of_mem hg]; exact h2, ?_⟩
      rintro _ ⟨w, hw, rfl⟩
      rw [LinearEquiv.coe_coe, polar_map_of_mem hg]
      exact h3 w hw
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by rwa [hmem] at h1, by rwa [map_of_mem hg] at h2, fun w hw => ?_⟩
      have := h3 (g w) ⟨w, hw, rfl⟩
      rwa [polar_map_of_mem hg] at this
  exact (Nat.card_congr (g.toEquiv.subtypeEquiv hiff)).symm

theorem card_singularOrthOutside [Finite K] {j : ℕ} (hj : j ≤ r)
    {U : Submodule K (Fin r ⊕ Fin r → K)} (hU : U ∈ singularSubspaces (quadPlus r K) j) :
    Nat.card (singularOrthOutside (quadPlus r K) U) =
      Nat.card K ^ j * ((Nat.card K ^ (r - j) - 1) * (Nat.card K ^ (r - j - 1) + 1)) := by
  obtain ⟨g, hg, rfl⟩ := exists_isometry_map_eq hj hU
  rw [card_singularOrthOutside_map hg, card_singularOrthOutside_flag hj,
    card_quadPlus_nonzero_singular, Nat.card_fun, Nat.card_fin]

theorem card_extensionsWith_singular [Finite K] {j : ℕ} (hj : j ≤ r)
    {U : Submodule K (Fin r ⊕ Fin r → K)} (hU : U ∈ singularSubspaces (quadPlus r K) j) :
    (Nat.card (extensionsWith (fun X => ∀ x ∈ X, quadPlus r K x = 0) U j) : ℚ) =
      ((Nat.card K : ℚ) ^ (r - j) - 1) * ((Nat.card K : ℚ) ^ (r - j - 1) + 1) /
        ((Nat.card K : ℚ) - 1) := by
  obtain ⟨hUd, hUs⟩ := hU
  have hS := card_vectors_eq_mul_card_extensions (W := U)
    (S := singularOrthOutside (quadPlus r K) U) (fun x hx => hx.1) fun c w x hc hw hx => by
      refine ⟨fun h => hx.1 ?_, ?_, fun w' hw' => ?_⟩
      · simpa [smul_smul, inv_mul_cancel₀ hc] using U.smul_mem c⁻¹ (U.sub_mem h hw)
      · rw [QuadraticMap.map_add (quadPlus r K), map_smul_eq_sq, hx.2.1, hUs w hw,
          polar_smul_left_eq, hx.2.2 w hw]
        ring
      · rw [polar_add_left, polar_smul_left_eq, hx.2.2 w' hw',
          polar_eq_zero_of_singular hUs hw hw', mul_zero, add_zero]
  have hext : extensionsIn U (singularOrthOutside (quadPlus r K) U) =
      extensionsWith (fun X => ∀ x ∈ X, quadPlus r K x = 0) U j := by
    ext W'
    constructor
    · rintro ⟨hUW', hd, hW'⟩
      refine ⟨hUW', by rw [hd, hUd], fun x hx => ?_⟩
      by_cases hxU : x ∈ U
      · exact hUs x hxU
      · exact (hW' x hx hxU).2.1
    · rintro ⟨hUW', hd, hW's⟩
      refine ⟨hUW', by rw [hd, hUd], fun x hx hxU => ⟨hxU, hW's x hx, fun w hw => ?_⟩⟩
      exact polar_eq_zero_of_singular hW's hx (hUW' hw)
  rw [hext, card_singularOrthOutside hj ⟨hUd, hUs⟩, hUd] at hS
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hq1 : 1 ≤ Nat.card K := hq.le
  have hpos := pow_succ_sub_pow_pos (K := K) j
  have h1 : 1 ≤ Nat.card K ^ (r - j) := Nat.one_le_pow _ _ (by omega)
  have hle' : Nat.card K ^ j ≤ Nat.card K ^ (j + 1) := Nat.pow_le_pow_right hq1 (by omega)
  have hS' := congrArg (Nat.cast : ℕ → ℚ) hS
  push_cast [Nat.cast_sub h1, Nat.cast_sub hle'] at hS'
  have hqQ : (1 : ℚ) < Nat.card K := by exact_mod_cast hq
  have hden : (Nat.card K : ℚ) - 1 ≠ 0 := by linarith
  have hqj : (Nat.card K : ℚ) ^ j ≠ 0 := pow_ne_zero _ (by linarith)
  rw [eq_div_iff hden]
  have hfac : (Nat.card K : ℚ) ^ (j + 1) - (Nat.card K : ℚ) ^ j =
      (Nat.card K : ℚ) ^ j * ((Nat.card K : ℚ) - 1) := by ring
  rw [hfac] at hS'
  have := hS'.symm
  apply mul_left_cancel₀ hqj
  linear_combination this

end Extensions


section Products

theorem prod_Icc_one_eq_prod_range {M : Type*} [CommMonoid M] (f : ℕ → M) (k : ℕ) :
    ∏ i ∈ Finset.Icc 1 k, f i = ∏ j ∈ Finset.range k, f (j + 1) := by
  rw [Finset.range_eq_Ico, Finset.prod_Ico_add' f 0 k 1, zero_add,
    Finset.Ico_add_one_right_eq_Icc]

theorem prod_range_pow_sub_one (q : ℚ) (k : ℕ) :
    ∏ j ∈ Finset.range k, (q ^ (k - j) - 1) = ∏ i ∈ Finset.Icc 1 k, (q ^ i - 1) := by
  rw [prod_Icc_one_eq_prod_range, ← Finset.prod_range_reflect (fun j => q ^ (j + 1) - 1) k]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [show k - 1 - j + 1 = k - j by omega]

end Products

section Count

variable {r : ℕ} {K : Type*} [Field K] [Finite K]

omit [Finite K] in
theorem singular_natFlag {k : ℕ} {Q : QuadraticForm K (Fin r ⊕ Fin r → K)}
    {W : Fin k → Submodule K (Fin r ⊕ Fin r → K)} (hW : ∀ i, ∀ x ∈ W i, Q x = 0) :
    ∀ x ∈ natFlag W k, Q x = 0 := by
  intro x hx
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [natFlag_of_not_pos W (by omega), mem_bot] at hx
    rw [hx, map_zero]
  · rw [natFlag_of_pos W hk le_rfl] at hx
    exact hW _ x hx

theorem card_singularFlags {k : ℕ} (hk : k ≤ r) :
    (Nat.card (singularFlags (quadPlus r K) k) : ℚ) =
      ∏ j ∈ Finset.range k, (((Nat.card K : ℚ) ^ (r - j) - 1) *
        ((Nat.card K : ℚ) ^ (r - j - 1) + 1) / ((Nat.card K : ℚ) - 1)) := by
  change (Nat.card (flagsWith (fun X => ∀ x ∈ X, quadPlus r K x = 0) k) : ℚ) = _
  apply card_flagsWith
  intro j hj W hW
  exact card_extensionsWith_singular (by omega) ⟨finrank_natFlag hW.1, singular_natFlag hW.2.2⟩

theorem card_singularFlags_eq_mul {k : ℕ} (hk : 0 < k) :
    (Nat.card (singularFlags (quadPlus r K) k) : ℚ) =
      Nat.card (singularSubspaces (quadPlus r K) k) *
        ∏ j ∈ Finset.range k, (((Nat.card K : ℚ) ^ k - (Nat.card K : ℚ) ^ j) /
          ((Nat.card K : ℚ) ^ (j + 1) - (Nat.card K : ℚ) ^ j)) := by
  classical
  have : Finite (Fin r ⊕ Fin r → K) := inferInstance
  let _ := Fintype.ofFinite (singularSubspaces (quadPlus r K) k)
  let top : singularFlags (quadPlus r K) k → singularSubspaces (quadPlus r K) k := fun W =>
    ⟨W.1 ⟨k - 1, by omega⟩, by rw [W.2.1]; simp only; omega, W.2.2.2 _⟩
  have hfib : ∀ X : singularSubspaces (quadPlus r K) k,
      Nat.card {W // top W = X} = Nat.card (flagsWith (· ≤ X.1) k) := by
    intro X
    refine Nat.card_congr
      { toFun := fun W => ⟨W.1.1, W.1.2.1, W.1.2.2.1, fun i => ?_⟩
        invFun := fun F => ⟨⟨F.1, F.2.1, F.2.2.1, fun i x hx => X.2.2 x (F.2.2.2 i hx)⟩, ?_⟩
        left_inv := fun W => rfl
        right_inv := fun F => rfl }
    · have h : (W.1.1 ⟨k - 1, by omega⟩ : Submodule K (Fin r ⊕ Fin r → K)) = X.1 :=
        congrArg Subtype.val W.2
      rw [← h]
      exact W.1.2.2.1 (Fin.le_def.2 (by simp only; omega))
    · apply Subtype.ext
      exact eq_of_le_of_finrank_eq (F.2.2.2 _) (by rw [F.2.1, X.2.1]; simp only; omega)
  have hF : ∀ X : singularSubspaces (quadPlus r K) k, (Nat.card (flagsWith (· ≤ X.1) k) : ℚ) =
      ∏ j ∈ Finset.range k, (((Nat.card K : ℚ) ^ k - (Nat.card K : ℚ) ^ j) /
        ((Nat.card K : ℚ) ^ (j + 1) - (Nat.card K : ℚ) ^ j)) := by
    intro X
    have h := card_flagsWith_le X.1
    rw [X.2.1] at h
    exact h
  have hsig := Nat.card_congr (Equiv.sigmaFiberEquiv top)
  rw [Nat.card_sigma] at hsig
  rw [← hsig, Nat.cast_sum, Finset.sum_congr rfl fun X _ =>
    show ((Nat.card {W // top W = X} : ℕ) : ℚ) = ∏ j ∈ Finset.range k,
      (((Nat.card K : ℚ) ^ k - (Nat.card K : ℚ) ^ j) /
        ((Nat.card K : ℚ) ^ (j + 1) - (Nat.card K : ℚ) ^ j)) by rw [hfib X]; exact hF X,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]


omit [Finite K] in
theorem card_singularSubspaces_zero :
    Nat.card (singularSubspaces (quadPlus r K) 0) = 1 := by
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨⊥, finrank_bot K _, fun x hx => by rw [(mem_bot K).1 hx, map_zero]⟩, ?_⟩
  rintro ⟨X, hX, -⟩
  exact Subtype.ext (Submodule.finrank_eq_zero.1 hX)

theorem card_singularSubspaces {k : ℕ} (hk : k ≤ r) :
    (Nat.card (singularSubspaces (quadPlus r K) k) : ℚ) =
      (∏ j ∈ Finset.range k, (((Nat.card K : ℚ) ^ (r - j) - 1) *
        ((Nat.card K : ℚ) ^ (r - j - 1) + 1))) /
        ∏ i ∈ Finset.Icc 1 k, ((Nat.card K : ℚ) ^ i - 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [card_singularSubspaces_zero, Finset.prod_range_zero, Finset.Icc_eq_empty (by omega),
      Finset.prod_empty, Nat.cast_one, div_one]
  set q : ℚ := (Nat.card K : ℚ) with hqdef
  have hq : 1 < q := by rw [hqdef]; exact_mod_cast Finite.one_lt_card
  have hq0 : q ≠ 0 := by linarith
  have hq1 : q - 1 ≠ 0 := by linarith
  have hFk : ∏ j ∈ Finset.range k, ((q ^ k - q ^ j) / (q ^ (j + 1) - q ^ j)) =
      ∏ j ∈ Finset.range k, ((q ^ (k - j) - 1) / (q - 1)) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [show q ^ k = q ^ j * q ^ (k - j) by rw [← pow_add]; congr 1; omega, pow_succ]
    rw [show q ^ j * q ^ (k - j) - q ^ j = q ^ j * (q ^ (k - j) - 1) by ring,
      show q ^ j * q - q ^ j = q ^ j * (q - 1) by ring, mul_div_mul_left _ _ (pow_ne_zero _ hq0)]
  have hpos : ∀ m, 1 ≤ m → (0 : ℚ) < q ^ m - 1 := fun m hm => by
    have := one_lt_pow₀ hq (by omega : m ≠ 0)
    linarith
  have hFne : ∏ j ∈ Finset.range k, ((q ^ (k - j) - 1) / (q - 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j hj => by
      rw [Finset.mem_range] at hj
      exact div_ne_zero (hpos _ (by omega)).ne' hq1
  have h := card_singularFlags_eq_mul (K := K) (r := r) hk0
  rw [card_singularFlags hk, ← hqdef, hFk] at h
  rw [eq_div_iff hFne |>.mpr h.symm, ← Finset.prod_div_distrib]
  rw [Finset.prod_congr rfl fun j _ => div_div_div_cancel_right₀ hq1 _ _, Finset.prod_div_distrib,
    prod_range_pow_sub_one]

theorem card_singularSubspaces_top (hr : 1 ≤ r) :
    (Nat.card (singularSubspaces (quadPlus r K) r) : ℚ) =
      2 * ∏ i ∈ Finset.Icc 1 (r - 1), ((Nat.card K : ℚ) ^ i + 1) := by
  set q : ℚ := (Nat.card K : ℚ) with hqdef
  have hq : 1 < q := by rw [hqdef]; exact_mod_cast Finite.one_lt_card
  have hne : ∏ i ∈ Finset.Icc 1 r, (q ^ i - 1) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i hi => by
      have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
      have := one_lt_pow₀ hq (by omega : i ≠ 0)
      linarith
  rw [card_singularSubspaces le_rfl, ← hqdef, Finset.prod_mul_distrib, prod_range_pow_sub_one,
    mul_div_cancel_left₀ _ hne]
  have hrefl : ∏ j ∈ Finset.range r, (q ^ (r - j - 1) + 1) = ∏ j ∈ Finset.range r, (q ^ j + 1) := by
    rw [← Finset.prod_range_reflect (fun j => q ^ j + 1) r]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Nat.sub_sub, Nat.add_comm j 1, ← Nat.sub_sub]
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  rw [hrefl, Finset.prod_range_succ', pow_zero, Nat.add_sub_cancel, prod_Icc_one_eq_prod_range]
  ring

end Count

theorem orthogonal_geometry_split_singular_subspace_count {K : Type*} [Field K] [Finite K]
    {r : ℕ} (hr : 1 ≤ r) {k : ℕ} (hk : k ≤ r) :
    (Nat.card (singularSubspaces (quadPlus r K) k) : ℚ) =
        (∏ j ∈ Finset.range k, (((Nat.card K : ℚ) ^ (r - j) - 1) *
          ((Nat.card K : ℚ) ^ (r - j - 1) + 1))) /
          ∏ i ∈ Finset.Icc 1 k, ((Nat.card K : ℚ) ^ i - 1) ∧
      (Nat.card (singularFlags (quadPlus r K) k) : ℚ) =
        ∏ j ∈ Finset.range k, (((Nat.card K : ℚ) ^ (r - j) - 1) *
          ((Nat.card K : ℚ) ^ (r - j - 1) + 1) / ((Nat.card K : ℚ) - 1)) ∧
      (Nat.card (singularSubspaces (quadPlus r K) r) : ℚ) =
        2 * ∏ i ∈ Finset.Icc 1 (r - 1), ((Nat.card K : ℚ) ^ i + 1) :=
  ⟨card_singularSubspaces hk, card_singularFlags hk, card_singularSubspaces_top hr⟩

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
