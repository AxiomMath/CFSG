module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRootData
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryPolar

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module Submodule
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (flag_le finrank_span_image_lt)

variable {K : Type*} [Field K]

section Pairs

variable {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_hypPairs_of_flag_of_le [FiniteDimensional K V] :
    ∀ (r : ℕ) (S : Submodule K V), PolarNondegOn Q S →
      ∀ T : Submodule K V, T ≤ S → (∀ x ∈ T, Q x = 0) → r ≤ finrank K T →
      ∀ (k : ℕ), k ≤ r → ∀ W : ℕ → Submodule K V, W k ≤ S → (∀ i ≤ k, finrank K (W i) = i) →
        (∀ i < k, W i ≤ W (i + 1)) → (∀ x ∈ W k, Q x = 0) →
        ∃ P : Fin r → HypPair Q, (∀ i, (P i).e ∈ S ∧ (P i).f ∈ S) ∧
          (∀ i j, i ≠ j → (P i).Orth (P j)) ∧
          ∀ i ≤ k, W i = span K ((fun j => (P j).e) '' {j : Fin r | (j : ℕ) < i}) := by
  intro r
  induction r with
  | zero =>
    intro S _ T _ _ _ k hk W _ hWd _ _
    refine ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i hi => ?_⟩
    have hi0 : i = 0 := by omega
    subst hi0
    rw [Submodule.finrank_eq_zero.1 (hWd 0 (Nat.zero_le k))]
    simp
  | succ r ih =>
    intro S hS T hTS hTs hTr k hk W hWS hWd hWm hWs
    obtain ⟨e, heS, he, he0, heW⟩ : ∃ e ∈ S, Q e = 0 ∧ e ≠ 0 ∧ (1 ≤ k → e ∈ W 1) := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk1
      · obtain ⟨e, heT, he0⟩ := exists_ne_zero_of_one_le_finrank (T := T) (by omega)
        exact ⟨e, hTS heT, hTs e heT, he0, fun h => absurd h (by omega)⟩
      · obtain ⟨e, heW, he0⟩ := exists_ne_zero_of_one_le_finrank (T := W 1) (by rw [hWd 1 hk1])
        have heWk : e ∈ W k := flag_le hWm hk1 le_rfl heW
        exact ⟨e, hWS heWk, hWs e heWk, he0, fun _ => heW⟩
    obtain ⟨f, hfS, hf, hef⟩ := exists_partner_of_polarNondegOn hS heS he he0
    let P₀ : HypPair Q := ⟨e, f, he, hf, hef⟩
    have hP₀e : P₀.e = e := rfl
    have hS' : PolarNondegOn Q (S ⊓ P₀.perp) := hS.inf_perp P₀ heS hfS
    obtain ⟨T', hT'p, hT's, hT'r, hT'le⟩ := quadratic_singular_subspace_descent Q he hef T hTs rfl
    have hT'S : T' ≤ S ⊓ P₀.perp := fun x hx =>
      ⟨(hT'le.trans (sup_le hTS ((span_singleton_le_iff_mem _ _).2 heS))) hx,
        HypPair.mem_perp_of_polar (P := P₀) (hT'p x hx)⟩
    obtain ⟨W', hW'S, hW'd, hW'm, hW's, hWW'⟩ : ∃ W' : ℕ → Submodule K V,
        W' (k - 1) ≤ S ⊓ P₀.perp ∧ (∀ i ≤ k - 1, finrank K (W' i) = i) ∧
        (∀ i < k - 1, W' i ≤ W' (i + 1)) ∧ (∀ x ∈ W' (k - 1), Q x = 0) ∧
        ∀ i, 1 ≤ i → i ≤ k → W i = span K {e} ⊔ W' (i - 1) := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk1
      · refine ⟨fun _ => ⊥, bot_le, fun i hi => ?_, fun _ _ => le_rfl, fun x hx => ?_,
          fun i hi hik => by omega⟩
        · rw [show i = 0 by omega]
          simp
        rw [(mem_bot K).1 hx, QuadraticMap.map_zero]
      · have heWi : ∀ i, 1 ≤ i → i ≤ k → e ∈ W i := fun i hi hik => flag_le hWm hi hik (heW hk1)
        have horth : ∀ i ≤ k, ∀ x ∈ W i, polar Q P₀.e x = 0 := fun i hik x hx =>
          polar_eq_zero_of_singular hWs (heWi k hk1 le_rfl) (flag_le hWm hik le_rfl hx)
        refine ⟨fun i => W (i + 1) ⊓ P₀.perp, ?_, fun i hi => ?_, fun i hi => ?_, fun x hx => ?_,
          fun i hi hik => ?_⟩
        · exact inf_le_inf_right _ (by rw [show k - 1 + 1 = k by omega]; exact hWS)
        · have h := finrank_inf_perp_add_one P₀ (heWi (i + 1) (by omega) (by omega))
            (horth (i + 1) (by omega))
          rw [hWd (i + 1) (by omega)] at h
          exact Nat.succ_injective h
        · exact inf_le_inf_right _ (hWm (i + 1) (by omega))
        · exact hWs x (by rw [show k = k - 1 + 1 by omega]; exact hx.1)
        · change W i = span K {P₀.e} ⊔ (W (i - 1 + 1) ⊓ P₀.perp)
          rw [show i - 1 + 1 = i by omega]
          exact (span_e_sup_inf_perp P₀ (heWi i hi hik) (horth i hik)).symm
    obtain ⟨P', hP'S, hP'o, hP'W⟩ := ih (S ⊓ P₀.perp) hS' T' hT'S hT's (by omega) (k - 1)
      (by omega) W' hW'S hW'd hW'm hW's
    let P : Fin (r + 1) → HypPair Q := Fin.cons P₀ P'
    have hPs : ∀ j : Fin r, P j.succ = P' j := fun j => rfl
    refine ⟨P, fun i => ?_, fun i j hij => ?_, fun i hik => ?_⟩
    · induction i using Fin.cases with
      | zero => exact ⟨heS, hfS⟩
      | succ j => exact ⟨(hP'S j).1.1, (hP'S j).2.1⟩
    · have h0 : ∀ j, P₀.Orth (P' j) := fun j => HypPair.orth_of_mem_perp (hP'S j).1.2 (hP'S j).2.2
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j => exact h0 j
      | succ i =>
        induction j using Fin.cases with
        | zero => exact (h0 i).symm
        | succ j => exact hP'o i j fun h => hij (by rw [h])
    · rcases Nat.eq_zero_or_pos i with rfl | hi1
      · rw [Submodule.finrank_eq_zero.1 (hWd 0 (Nat.zero_le k))]
        simp
      · have hset : (fun j => (P j).e) '' {j : Fin (r + 1) | (j : ℕ) < i} =
            insert e ((fun j => (P' j).e) '' {j : Fin r | (j : ℕ) < i - 1}) := by
          ext v
          constructor
          · rintro ⟨j, hj, rfl⟩
            induction j using Fin.cases with
            | zero => exact Or.inl rfl
            | succ j =>
              refine Or.inr ⟨j, ?_, by simp only [hPs]⟩
              simp only [Set.mem_ofPred_eq, Fin.val_succ] at hj ⊢
              omega
          · rintro (rfl | ⟨j, hj, rfl⟩)
            · exact ⟨0, by simpa using hi1, rfl⟩
            · refine ⟨j.succ, ?_, by simp only [hPs]⟩
              simp only [Set.mem_ofPred_eq, Fin.val_succ] at hj ⊢
              omega
        rw [hset, span_insert, hWW' i hi1 hik, hP'W (i - 1) (by omega)]

variable {r : ℕ} (P : Fin r → HypPair Q)

@[expose] def pairsSpan : Submodule K V :=
  span K (Set.range (fun i => (P i).e) ∪ Set.range (fun i => (P i).f))

@[expose] def pairsPerp : Submodule K V :=
  ⨅ i, (P i).perp

theorem mem_pairsPerp {x : V} : x ∈ pairsPerp P ↔ ∀ i, x ∈ (P i).perp :=
  Submodule.mem_iInf _

theorem polar_eq_zero_of_mem_span_left {S : Set V} {y : V} (h : ∀ s ∈ S, polar Q s y = 0)
    {x : V} (hx : x ∈ span K S) : polar Q x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem z hz => exact h z hz
  | zero => exact polar_zero_left Q y
  | add z z' _ _ hz hz' => rw [polar_add_left, hz, hz', add_zero]
  | smul a z _ hz => rw [polar_smul_left_eq, hz, mul_zero]

theorem polar_sum_right {ι : Type*} (s : Finset ι) (v : ι → V) (w : V) :
    polar Q w (∑ i ∈ s, v i) = ∑ i ∈ s, polar Q w (v i) := by
  have := map_sum (polarBilin Q w) v s
  simpa only [polarBilin_apply_apply] using this

theorem polar_pairsSpan_pairsPerp {x y : V} (hx : x ∈ pairsSpan P) (hy : y ∈ pairsPerp P) :
    polar Q x y = 0 := by
  refine polar_eq_zero_of_mem_span_left ?_ hx
  rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · exact (HypPair.mem_perp.1 ((mem_pairsPerp P).1 hy i)).1
  · exact (HypPair.mem_perp.1 ((mem_pairsPerp P).1 hy i)).2

variable {P} (hP : ∀ i j, i ≠ j → (P i).Orth (P j))
include hP

theorem polar_pairs :
    (∀ i j, polar Q (P i).e (P j).f = if i = j then 1 else 0) ∧
      (∀ i j, polar Q (P i).f (P j).e = if i = j then 1 else 0) ∧
      (∀ i j, polar Q (P i).e (P j).e = 0) ∧ ∀ i j, polar Q (P i).f (P j).f = 0 := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · split_ifs with h
    · subst h
      exact (P i).polar_ef
    · exact (hP i j h).ef
  · split_ifs with h
    · subst h
      exact (P i).polar_fe
    · rw [polar_comm]
      exact (hP j i (Ne.symm h)).ef
  · by_cases h : i = j
    · subst h
      exact (P i).polar_ee
    · exact (hP i j h).ee
  · by_cases h : i = j
    · subst h
      exact (P i).polar_ff
    · exact (hP i j h).ff

theorem sub_sum_mem_pairsPerp (x : V) :
    x - ∑ i, (polar Q x (P i).f • (P i).e + polar Q x (P i).e • (P i).f) ∈ pairsPerp P := by
  obtain ⟨hef, hfe, hee, hff⟩ := polar_pairs hP
  refine (mem_pairsPerp P).2 fun j => HypPair.mem_perp.2 ⟨?_, ?_⟩
  · rw [polar_sub_right, polar_sum_right]
    simp only [polar_add_right, polar_smul_right_eq, hee, hef, mul_zero, zero_add]
    simp [polar_comm Q x (P j).e]
  · rw [polar_sub_right, polar_sum_right]
    simp only [polar_add_right, polar_smul_right_eq, hfe, hff, mul_zero, add_zero]
    simp [polar_comm Q x (P j).f]

theorem linearIndependent_pairs :
    LinearIndependent K (Sum.elim (fun i => (P i).e) (fun i => (P i).f)) := by
  obtain ⟨hef, hfe, hee, hff⟩ := polar_pairs hP
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fintype.sum_sum_type] at hg
  simp only [Sum.elim_inl, Sum.elim_inr] at hg
  have hcoef : ∀ j, polar Q (∑ i, g (.inl i) • (P i).e + ∑ i, g (.inr i) • (P i).f) (P j).f =
      g (.inl j) ∧
      polar Q (∑ i, g (.inl i) • (P i).e + ∑ i, g (.inr i) • (P i).f) (P j).e = g (.inr j) := by
    intro j
    constructor <;> simp [polar_add_left, polar_sum_smul_left, hef, hff, hee, hfe]
  rintro (j | j)
  · have := (hcoef j).1
    rwa [hg, polar_zero_left, eq_comm] at this
  · have := (hcoef j).2
    rwa [hg, polar_zero_left, eq_comm] at this

theorem finrank_pairsSpan : finrank K (pairsSpan P) = 2 * r := by
  rw [pairsSpan, ← Set.Sum.elim_range, finrank_span_eq_card (linearIndependent_pairs hP),
    Fintype.card_sum, Fintype.card_fin, two_mul]

omit hP in
theorem sum_mem_pairsSpan (x : V) :
    ∑ i, (polar Q x (P i).f • (P i).e + polar Q x (P i).e • (P i).f) ∈ pairsSpan P :=
  sum_mem fun i _ => add_mem (smul_mem _ _ (subset_span (Or.inl ⟨i, rfl⟩)))
    (smul_mem _ _ (subset_span (Or.inr ⟨i, rfl⟩)))

theorem pairsSpan_sup_pairsPerp : pairsSpan P ⊔ pairsPerp P = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  rw [← add_sub_cancel (∑ i, (polar Q x (P i).f • (P i).e + polar Q x (P i).e • (P i).f)) x]
  exact add_mem_sup (sum_mem_pairsSpan (P := P) x) (sub_sum_mem_pairsPerp hP x)

variable (hQ : (polarBilin Q).Nondegenerate)
include hQ

theorem pairsSpan_inf_pairsPerp : pairsSpan P ⊓ pairsPerp P = ⊥ := by
  refine eq_bot_iff.2 fun x ⟨hxS, hxP⟩ => (mem_bot K).2 ?_
  refine eq_zero_of_polar_eq_zero hQ fun v => ?_
  rw [← add_sub_cancel (∑ i, (polar Q v (P i).f • (P i).e + polar Q v (P i).e • (P i).f)) v,
    polar_add_right, polar_comm, polar_pairsSpan_pairsPerp P (sum_mem_pairsSpan (P := P) v) hxP,
    polar_pairsSpan_pairsPerp P hxS (sub_sum_mem_pairsPerp hP v), zero_add]

theorem isCompl_pairsSpan_pairsPerp : IsCompl (pairsSpan P) (pairsPerp P) :=
  ⟨disjoint_iff.2 (pairsSpan_inf_pairsPerp hP hQ),
    codisjoint_iff.2 (pairsSpan_sup_pairsPerp hP)⟩

theorem polarNondegOn_pairsPerp : PolarNondegOn Q (pairsPerp P) := by
  intro x hx hxW
  refine eq_zero_of_polar_eq_zero hQ fun v => ?_
  rw [← add_sub_cancel (∑ i, (polar Q v (P i).f • (P i).e + polar Q v (P i).e • (P i).f)) v,
    polar_add_right, polar_comm, polar_pairsSpan_pairsPerp P (sum_mem_pairsSpan (P := P) v) hx,
    hxW _ (sub_sum_mem_pairsPerp hP v), zero_add]

theorem finrank_pairsPerp [FiniteDimensional K V] :
    finrank K (pairsPerp P) + 2 * r = finrank K V := by
  rw [← finrank_pairsSpan hP, add_comm]
  exact Submodule.finrank_add_eq_of_isCompl (isCompl_pairsSpan_pairsPerp hP hQ)

end Pairs

section Tail

variable {A : Type*} [AddCommGroup A] [Module K A] {r : ℕ} {qA : QuadraticForm K A}

theorem nondegenerate_polarBilin_quadTail (hreg : (polarBilin qA).Nondegenerate) :
    (polarBilin (quadTail r qA)).Nondegenerate := by
  refine nondegenerate_polarBilin_of_forall fun v hv => ?_
  have h1 : v.1 = 0 := eq_zero_of_polar_eq_zero (nondegenerate_polarBilin_quadPlus r K) fun w => by
    have := hv (w, 0)
    rwa [polar_quadTail, polar_zero_right, add_zero] at this
  have h2 : v.2 = 0 := eq_zero_of_polar_eq_zero hreg fun w => by
    have := hv (0, w)
    rwa [polar_quadTail, polar_zero_right, zero_add] at this
  exact Prod.ext h1 h2

theorem finrank_tailSpace [FiniteDimensional K A] :
    finrank K ((Fin r ⊕ Fin r → K) × A) = 2 * r + finrank K A := by
  rw [Module.finrank_prod, finrank_split]

theorem tailFlag_eq_map (i : ℕ) :
    tailFlag K A r i = (flag r K i).map (LinearMap.inl K (Fin r ⊕ Fin r → K) A) := by
  rw [tailFlag, flag, Submodule.map_span, ← Set.image_comp]
  rfl

theorem finrank_tailFlag {i : ℕ} (hi : i ≤ r) : finrank K (tailFlag K A r i) = i := by
  rw [tailFlag_eq_map, ← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective
    (LinearMap.inl K (Fin r ⊕ Fin r → K) A) LinearMap.inl_injective (flag r K i))]
  exact finrank_flag hi

theorem quadTail_eq_zero_of_mem_tailFlag {i : ℕ} {v : (Fin r ⊕ Fin r → K) × A}
    (hv : v ∈ tailFlag K A r i) : quadTail r qA v = 0 :=
  map_eq_zero_of_mem_span (by rintro _ ⟨j, -, rfl⟩; exact quadTail_hypVec _)
    (by rintro _ ⟨j, -, rfl⟩ _ ⟨l, -, rfl⟩; rw [polar_hypVec_hypVec, ite_eq_right (by simp)])
    hv

@[expose] def yProj : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] (Fin r ⊕ Fin r → K) where
  toFun v := Sum.elim 0 (fun i => v.1 (.inr i))
  map_add' v w := by
    funext c
    rcases c with i | i <;> simp
  map_smul' c v := by
    funext d
    rcases d with i | i <;> simp

theorem yProj_inl (v : (Fin r ⊕ Fin r → K) × A) (i : Fin r) : yProj v (.inl i) = 0 :=
  rfl

theorem yProj_inr (v : (Fin r ⊕ Fin r → K) × A) (i : Fin r) : yProj v (.inr i) = v.1 (.inr i) :=
  rfl

theorem yProj_eq_zero_iff {v : (Fin r ⊕ Fin r → K) × A} :
    yProj v = 0 ↔ ∀ i, v.1 (.inr i) = 0 := by
  constructor
  · intro h i
    rw [← yProj_inr, h, Pi.zero_apply]
  · intro h
    funext c
    rcases c with i | i
    · rfl
    · exact h i

theorem finrank_le_of_totSing_tail [FiniteDimensional K A] (hani : qA.Anisotropic)
    {T : Submodule K ((Fin r ⊕ Fin r → K) × A)} (hT : ∀ x ∈ T, quadTail r qA x = 0) :
    finrank K T ≤ r := by
  set Z := T ⊓ LinearMap.ker (yProj (K := K) (A := A) (r := r)) with hZ
  have hZ2 : ∀ z ∈ Z, z.2 = 0 ∧ ∀ i, z.1 (.inr i) = 0 := by
    intro z hz
    have hy : ∀ i, z.1 (.inr i) = 0 := yProj_eq_zero_iff.1 (LinearMap.mem_ker.1 hz.2)
    refine ⟨hani _ ?_, hy⟩
    have h := hT z hz.1
    rwa [quadTail_apply, quadPlus_apply, Finset.sum_eq_zero fun i _ => by rw [hy i, mul_zero],
      zero_add] at h
  set Z' := Z.map (LinearMap.fst K (Fin r ⊕ Fin r → K) A) with hZ'
  set T' := T.map (yProj (K := K) (A := A) (r := r)) with hT'
  have hS : ∀ v ∈ Z' ⊔ T', quadPlus r K v = 0 := by
    intro v hv
    obtain ⟨y, ⟨z, hz, rfl⟩, w, ⟨t, ht, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hv
    have hzt := polar_eq_zero_of_singular hT hz.1 ht
    rw [polar_quadTail, (hZ2 z hz).1, polar_zero_left, add_zero, polar_quadPlus] at hzt
    rw [quadPlus_apply, ← hzt]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [LinearMap.fst_apply, Pi.add_apply, yProj_inl, yProj_inr, (hZ2 z hz).2 i, add_zero,
      zero_add, mul_zero]
  have hdisj : Z' ⊓ T' = ⊥ := by
    refine eq_bot_iff.2 fun v ⟨⟨z, hz, hzv⟩, ⟨t, ht, htv⟩⟩ => (mem_bot K).2 ?_
    funext c
    rcases c with i | i
    · rw [← htv, yProj_inl, Pi.zero_apply]
    · rw [← hzv, LinearMap.fst_apply, (hZ2 z hz).2 i, Pi.zero_apply]
  have hZZ' : finrank K Z' = finrank K Z := by
    have hmap : Z'.map (LinearMap.inl K (Fin r ⊕ Fin r → K) A) = Z := by
      ext v
      constructor
      · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        have : LinearMap.inl K (Fin r ⊕ Fin r → K) A (LinearMap.fst K _ A z) = z :=
          Prod.ext rfl (hZ2 z hz).1.symm
        rwa [this]
      · intro hv
        refine ⟨v.1, ⟨v, hv, rfl⟩, Prod.ext rfl (hZ2 v hv).1.symm⟩
    rw [← hmap]
    exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective
      (LinearMap.inl K (Fin r ⊕ Fin r → K) A) LinearMap.inl_injective Z')
  have hrank : finrank K T' + finrank K Z = finrank K T := by
    have h := LinearMap.finrank_range_add_finrank_ker
      ((yProj (K := K) (A := A) (r := r)).domRestrict T)
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
    rw [← h, hZ, ← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq Z' T'
  rw [hdisj, finrank_bot, add_zero, hZZ'] at hsum
  have := finrank_le_of_totSing hS
  omega

theorem finrank_tailFlag_top : finrank K (tailFlag K A r r) = r :=
  finrank_tailFlag le_rfl

variable [FiniteDimensional K A] (hani : qA.Anisotropic) (hreg : (polarBilin qA).Nondegenerate)
include hani hreg

theorem exists_tail_pairs_of_flag {k : ℕ} (hk : k ≤ r)
    {W : ℕ → Submodule K ((Fin r ⊕ Fin r → K) × A)} (hWd : ∀ i ≤ k, finrank K (W i) = i)
    (hWm : ∀ i < k, W i ≤ W (i + 1)) (hWs : ∀ x ∈ W k, quadTail r qA x = 0) :
    ∃ P : Fin r → HypPair (quadTail r qA), (∀ i j, i ≠ j → (P i).Orth (P j)) ∧
      IsCompl (pairsSpan P) (pairsPerp P) ∧ finrank K (pairsPerp P) = finrank K A ∧
      PolarNondegOn (quadTail r qA) (pairsPerp P) ∧
      (∀ x ∈ pairsPerp P, quadTail r qA x = 0 → x = 0) ∧
      ∀ i ≤ k, W i = span K ((fun j => (P j).e) '' {j : Fin r | (j : ℕ) < i}) := by
  have hQ := nondegenerate_polarBilin_quadTail (r := r) hreg
  obtain ⟨P, -, hPo, hPW⟩ := exists_hypPairs_of_flag_of_le r ⊤ (polarNondegOn_top hQ)
    (tailFlag K A r r) le_top (fun x hx => quadTail_eq_zero_of_mem_tailFlag hx)
    finrank_tailFlag_top.ge k hk W le_top hWd hWm hWs
  have hli := linearIndependent_pairs hPo
  refine ⟨P, hPo, isCompl_pairsSpan_pairsPerp hPo hQ, ?_, polarNondegOn_pairsPerp hPo hQ, ?_, hPW⟩
  · have h := finrank_pairsPerp hPo hQ
    rw [finrank_tailSpace] at h
    omega
  ·
    intro x hx hQx
    by_contra hx0
    set E := span K (Set.range fun i => (P i).e) with hE
    have hlie : LinearIndependent K fun i => (P i).e := hli.comp Sum.inl Sum.inl_injective
    have hEr : finrank K E = r := by
      rw [hE, finrank_span_eq_card hlie, Fintype.card_fin]
    have hdisj : E ⊓ span K {x} = ⊥ := by
      refine eq_bot_iff.2 fun y ⟨hyE, hyx⟩ => ?_
      rw [← pairsSpan_inf_pairsPerp hPo hQ]
      refine ⟨span_mono (Set.subset_union_left) hyE, ?_⟩
      exact (span_singleton_le_iff_mem _ _).2 hx hyx
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq E (span K {x})
    rw [hdisj, finrank_bot, add_zero, hEr, finrank_span_singleton hx0] at hsum
    have hsing : ∀ y ∈ E ⊔ span K {x}, quadTail r qA y = 0 := by
      intro y hy
      rw [hE, ← span_union] at hy
      refine map_eq_zero_of_mem_span ?_ ?_ hy
      · rintro _ (⟨i, rfl⟩ | h)
        · exact (P i).Q_e
        · rw [Set.mem_singleton_iff.1 h]
          exact hQx
      · have hxe : ∀ i, polar (quadTail r qA) (P i).e x = 0 := fun i =>
          (HypPair.mem_perp.1 ((mem_pairsPerp P).1 hx i)).1
        rintro _ (⟨i, rfl⟩ | h) _ (⟨j, rfl⟩ | h')
        · exact (polar_pairs hPo).2.2.1 i j
        · rw [Set.mem_singleton_iff.1 h']
          exact hxe i
        · rw [Set.mem_singleton_iff.1 h, polar_comm]
          exact hxe j
        · rw [Set.mem_singleton_iff.1 h, Set.mem_singleton_iff.1 h']
          exact polar_self_eq_zero hQx
    have := finrank_le_of_totSing_tail hani hsing
    omega

end Tail


theorem orthogonal_geometry_tail_Witt_flags {K : Type*} [Field K] {A : Type*} [AddCommGroup A]
    [Module K A] [FiniteDimensional K A] {r : ℕ} {qA : QuadraticForm K A}
    (hani : qA.Anisotropic) (hreg : (polarBilin qA).Nondegenerate) :
    (∀ T : Submodule K ((Fin r ⊕ Fin r → K) × A), (∀ x ∈ T, quadTail r qA x = 0) →
      finrank K T ≤ r) ∧
    (∀ k ≤ r, ∀ W : ℕ → Submodule K ((Fin r ⊕ Fin r → K) × A),
      (∀ i ≤ k, finrank K (W i) = i) → (∀ i < k, W i ≤ W (i + 1)) →
      (∀ x ∈ W k, quadTail r qA x = 0) →
      ∃ (P : Fin r → HypPair (quadTail r qA)) (A' : Submodule K ((Fin r ⊕ Fin r → K) × A)),
        (∀ i j, i ≠ j → (P i).Orth (P j)) ∧ A' = pairsPerp P ∧ IsCompl (pairsSpan P) A' ∧
        finrank K A' = finrank K A ∧ PolarNondegOn (quadTail r qA) A' ∧
        (∀ x ∈ A', quadTail r qA x = 0 → x = 0) ∧
        ∀ i ≤ k, W i = span K ((fun j => (P j).e) '' {j : Fin r | (j : ℕ) < i})) ∧
    ∀ T : Submodule K ((Fin r ⊕ Fin r → K) × A), (∀ x ∈ T, quadTail r qA x = 0) →
      (∀ T' : Submodule K ((Fin r ⊕ Fin r → K) × A), T ≤ T' →
        (∀ x ∈ T', quadTail r qA x = 0) → T' = T) → finrank K T = r := by
  refine ⟨fun T hT => finrank_le_of_totSing_tail hani hT, fun k hk W hWd hWm hWs => ?_,
    fun T hTs hmax => ?_⟩
  · obtain ⟨P, hPo, hc, hd, hn, ha, hW⟩ := exists_tail_pairs_of_flag hani hreg hk hWd hWm hWs
    exact ⟨P, pairsPerp P, hPo, rfl, hc, hd, hn, ha, hW⟩
  ·
    set t := finrank K T with htdef
    have ht : t ≤ r := finrank_le_of_totSing_tail hani hTs
    set u := Module.finBasis K T
    set Wf : ℕ → Submodule K ((Fin r ⊕ Fin r → K) × A) :=
      fun i => span K ((fun j : Fin t => (u j : (Fin r ⊕ Fin r → K) × A)) '' {j | (j : ℕ) < i})
      with hWf
    have hli : LinearIndependent K (fun j : Fin t => (u j : (Fin r ⊕ Fin r → K) × A)) :=
      u.linearIndependent.map' T.subtype (ker_subtype T)
    have hWd : ∀ i ≤ t, finrank K (Wf i) = i := fun i hi => finrank_span_image_lt hli hi
    have hWm : ∀ i < t, Wf i ≤ Wf (i + 1) := fun i _ =>
      span_mono (Set.image_mono fun j (hj : (j : ℕ) < i) => Nat.lt_succ_of_lt hj)
    have hWt : Wf t ≤ T := span_le.2 (by rintro _ ⟨j, -, rfl⟩; exact (u j).2)
    obtain ⟨P, hPo, -, -, -, -, hPW⟩ := exists_tail_pairs_of_flag hani hreg ht hWd hWm
      (fun x hx => hTs x (hWt hx))
    have hWT : Wf t = T := eq_of_le_of_finrank_eq hWt (by rw [hWd t le_rfl])
    set X := span K ((fun j => (P j).e) '' {j : Fin r | (j : ℕ) < r}) with hX
    have hTX : T ≤ X := by
      rw [← hWT, hPW t le_rfl]
      exact span_mono (Set.image_mono fun j (hj : (j : ℕ) < t) => show (j : ℕ) < r by omega)
    have hXs : ∀ x ∈ X, quadTail r qA x = 0 := fun x hx =>
      map_eq_zero_of_mem_span (by rintro _ ⟨i, -, rfl⟩; exact (P i).Q_e)
        (by rintro _ ⟨i, -, rfl⟩ _ ⟨j, -, rfl⟩; exact (polar_pairs hPo).2.2.1 i j) hx
    have hXr : finrank K X = r :=
      finrank_span_image_lt ((linearIndependent_pairs hPo).comp Sum.inl Sum.inl_injective) le_rfl
    rw [htdef, ← hmax X hTX hXs, hXr]

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
