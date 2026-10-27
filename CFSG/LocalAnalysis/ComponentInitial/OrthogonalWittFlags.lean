module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasTwo
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagExtension
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagData

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module Submodule
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (flag_le finrank_span_inl_image
  finrank_span_image_lt)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem polar_sum_smul_left {ι : Type*} (s : Finset ι) (c : ι → K) (u : ι → V) (w : V) :
    polar Q (∑ i ∈ s, c i • u i) w = ∑ i ∈ s, c i * polar Q (u i) w := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, polar_add_left, polar_smul_left_eq, ih]

theorem polar_sum_smul_right {ι : Type*} (s : Finset ι) (c : ι → K) (u : ι → V) (w : V) :
    polar Q w (∑ i ∈ s, c i • u i) = ∑ i ∈ s, c i * polar Q w (u i) := by
  rw [polar_comm, polar_sum_smul_left]
  simp only [polar_comm Q (u _) w]

theorem polar_eq_zero_of_singular {X : Submodule K V} (hX : ∀ x ∈ X, Q x = 0) {x y : V}
    (hx : x ∈ X) (hy : y ∈ X) : polar Q x y = 0 := by
  rw [QuadraticMap.polar, hX _ (X.add_mem hx hy), hX x hx, hX y hy, sub_zero, sub_zero]

theorem span_e_sup_inf_perp (P : HypPair Q) {X : Submodule K V} (heX : P.e ∈ X)
    (hX : ∀ x ∈ X, polar Q P.e x = 0) : span K {P.e} ⊔ (X ⊓ P.perp) = X := by
  refine le_antisymm (sup_le ((span_singleton_le_iff_mem _ _).2 heX) inf_le_left) fun x hx => ?_
  have hmem : x - polar Q x P.f • P.e ∈ X ⊓ P.perp := by
    refine ⟨X.sub_mem hx (X.smul_mem _ heX), HypPair.mem_perp.2 ⟨?_, ?_⟩⟩
    · rw [polar_sub_right, polar_smul_right_eq, P.polar_ee, hX x hx, mul_zero, sub_zero]
    · rw [polar_sub_right, polar_smul_right_eq, P.polar_fe, mul_one, polar_comm Q P.f x,
        sub_self]
  rw [show x = polar Q x P.f • P.e + (x - polar Q x P.f • P.e) by abel]
  exact add_mem_sup (smul_mem _ _ (mem_span_singleton_self _)) hmem

theorem span_e_inf_inf_perp (P : HypPair Q) (X : Submodule K V) :
    span K {P.e} ⊓ (X ⊓ P.perp) = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hz, -, hzP⟩
  obtain ⟨c, rfl⟩ := mem_span_singleton.1 hz
  have h := (HypPair.mem_perp.1 hzP).2
  rw [polar_smul_right_eq, P.polar_fe, mul_one] at h
  rw [h, zero_smul]
  exact zero_mem _

theorem finrank_inf_perp_add_one [FiniteDimensional K V] (P : HypPair Q)
    {X : Submodule K V} (heX : P.e ∈ X) (hX : ∀ x ∈ X, polar Q P.e x = 0) :
    finrank K (X ⊓ P.perp : Submodule K V) + 1 = finrank K X := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (span K {P.e}) (X ⊓ P.perp)
  rw [span_e_sup_inf_perp P heX hX, span_e_inf_inf_perp P X, finrank_bot, add_zero,
    finrank_span_singleton P.e_ne_zero] at h
  omega

theorem span_pair_sup_inf_perp (P : HypPair Q) {S : Submodule K V} (he : P.e ∈ S)
    (hf : P.f ∈ S) : span K {P.e, P.f} ⊔ (S ⊓ P.perp) = S := by
  refine le_antisymm (sup_le ?_ inf_le_left) fun x hx => ?_
  · rw [span_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact he
    · exact hf
  · have hmem : P.proj x ∈ S ⊓ P.perp := ⟨by
      rw [HypPair.proj]
      exact S.sub_mem (S.sub_mem hx (S.smul_mem _ he)) (S.smul_mem _ hf), P.proj_mem_perp x⟩
    rw [P.eq_add_proj x]
    exact add_mem_sup (add_mem (smul_mem _ _ (subset_span (by simp)))
      (smul_mem _ _ (subset_span (by simp)))) hmem

theorem finrank_span_pair_hyp (P : HypPair Q) : finrank K (span K {P.e, P.f}) = 2 := by
  have hli : LinearIndependent K ![P.e, P.f] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (polar Q P.e) hst
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, P.polar_ee, P.polar_ef,
      polar_zero_right] at h1
    have ht : t = 0 := by linear_combination h1
    subst ht
    rw [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.1 hst).resolve_right P.e_ne_zero, rfl⟩
  have h := finrank_span_eq_card hli
  rwa [Matrix.range_cons_cons_empty, Fintype.card_fin] at h

theorem finrank_inf_perp_add_two [FiniteDimensional K V] (P : HypPair Q)
    {S : Submodule K V} (he : P.e ∈ S) (hf : P.f ∈ S) :
    finrank K (S ⊓ P.perp : Submodule K V) + 2 = finrank K S := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (span K {P.e, P.f}) (S ⊓ P.perp)
  have hinf : span K {P.e, P.f} ⊓ (S ⊓ P.perp) = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hz, -, hzP⟩
    obtain ⟨a, b, rfl⟩ := mem_span_pair.1 hz
    obtain ⟨h1, h2⟩ := HypPair.mem_perp.1 hzP
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, P.polar_ee, P.polar_ef] at h1
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, P.polar_fe, P.polar_ff] at h2
    have hb : b = 0 := by linear_combination h1
    have ha : a = 0 := by linear_combination h2
    simp [ha, hb]
  rw [span_pair_sup_inf_perp P he hf, hinf, finrank_bot, add_zero, finrank_span_pair_hyp P] at h
  omega

theorem exists_hypPairs_of_flag [FiniteDimensional K V] :
    ∀ (r : ℕ) (S : Submodule K V), PolarNondegOn Q S → finrank K S = 2 * r →
      ∀ T : Submodule K V, T ≤ S → (∀ x ∈ T, Q x = 0) → r ≤ finrank K T →
      ∀ (k : ℕ), k ≤ r → ∀ W : ℕ → Submodule K V, W k ≤ S → (∀ i ≤ k, finrank K (W i) = i) →
        (∀ i < k, W i ≤ W (i + 1)) → (∀ x ∈ W k, Q x = 0) →
        ∃ P : Fin r → HypPair Q, (∀ i, (P i).e ∈ S ∧ (P i).f ∈ S) ∧
          (∀ i j, i ≠ j → (P i).Orth (P j)) ∧
          ∀ i ≤ k, W i = span K ((fun j => (P j).e) '' {j : Fin r | (j : ℕ) < i}) := by
  intro r
  induction r with
  | zero =>
    intro S _ _ T _ _ _ k hk W _ hWd _ _
    refine ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i hi => ?_⟩
    have hi0 : i = 0 := by omega
    subst hi0
    rw [Submodule.finrank_eq_zero.1 (hWd 0 (Nat.zero_le k))]
    simp
  | succ r ih =>
    intro S hS hSr T hTS hTs hTr k hk W hWS hWd hWm hWs
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
    have hS'r : finrank K (S ⊓ P₀.perp : Submodule K V) = 2 * r := by
      have := finrank_inf_perp_add_two P₀ heS hfS
      omega
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
        rw [(mem_bot K).1 hx, map_zero]
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
    obtain ⟨P', hP'S, hP'o, hP'W⟩ := ih (S ⊓ P₀.perp) hS' hS'r T' hT'S hT's (by omega) (k - 1)
      (by omega) W' hW'S hW'd hW'm hW's
    let P : Fin (r + 1) → HypPair Q := Fin.cons P₀ P'
    have hP0 : P 0 = P₀ := rfl
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

theorem orthogonal_geometry_split_Witt_flags_aux [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {r : ℕ} (hV : finrank K V = 2 * r)
    (hT : ∃ T : Submodule K V, finrank K T = r ∧ ∀ x ∈ T, Q x = 0) (k : ℕ) (hk : k ≤ r)
    (W : ℕ → Submodule K V) (hWd : ∀ i ≤ k, finrank K (W i) = i) (hWm : ∀ i < k, W i ≤ W (i + 1))
    (hWs : ∀ x ∈ W k, Q x = 0) :
    ∃ b : Basis (Fin r ⊕ Fin r) K V,
      (∀ i, Q (b (.inl i)) = 0 ∧ Q (b (.inr i)) = 0) ∧
      (∀ i j, polar Q (b (.inl i)) (b (.inr j)) = if i = j then 1 else 0) ∧
      (∀ i j, polar Q (b (.inl i)) (b (.inl j)) = 0 ∧ polar Q (b (.inr i)) (b (.inr j)) = 0) ∧
      (∀ i ≤ k, W i = span K (b '' (Sum.inl '' {j : Fin r | (j : ℕ) < i}))) ∧
      ∀ x y : Fin r → K, Q (∑ i, x i • b (.inl i) + ∑ i, y i • b (.inr i)) = ∑ i, x i * y i := by
  obtain ⟨T, hTr, hTs⟩ := hT
  obtain ⟨P, -, hPo, hPW⟩ := exists_hypPairs_of_flag r ⊤ (polarNondegOn_top hQ)
    (by rw [finrank_top, hV]) T le_top hTs hTr.ge k hk W le_top hWd hWm hWs
  have hef : ∀ i j, polar Q (P i).e (P j).f = if i = j then 1 else 0 := fun i j => by
    split_ifs with h
    · subst h; exact (P i).polar_ef
    · exact (hPo i j h).ef
  have hee : ∀ i j, polar Q (P i).e (P j).e = 0 := fun i j => by
    by_cases h : i = j
    · subst h; exact (P i).polar_ee
    · exact (hPo i j h).ee
  have hff : ∀ i j, polar Q (P i).f (P j).f = 0 := fun i j => by
    by_cases h : i = j
    · subst h; exact (P i).polar_ff
    · exact (hPo i j h).ff
  have hfe : ∀ i j, polar Q (P i).f (P j).e = if i = j then 1 else 0 := fun i j => by
    rw [polar_comm, hef j i]
    simp only [eq_comm]
  have hcoef : ∀ (x y : Fin r → K) (j : Fin r),
      polar Q (∑ i, x i • (P i).e + ∑ i, y i • (P i).f) (P j).f = x j ∧
        polar Q (∑ i, x i • (P i).e + ∑ i, y i • (P i).f) (P j).e = y j := by
    intro x y j
    constructor <;> simp [polar_add_left, polar_sum_smul_left, hef, hff, hee, hfe]
  set v : Fin r ⊕ Fin r → V := Sum.elim (fun i => (P i).e) (fun i => (P i).f) with hv
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    simp only [hv, Sum.elim_inl, Sum.elim_inr] at hg
    rintro (j | j)
    · have := (hcoef (fun i => g (.inl i)) (fun i => g (.inr i)) j).1
      rwa [hg, polar_zero_left, eq_comm] at this
    · have := (hcoef (fun i => g (.inl i)) (fun i => g (.inr i)) j).2
      rwa [hg, polar_zero_left, eq_comm] at this
  have hsp : ⊤ ≤ span K (Set.range v) := by
    rw [top_le_iff]
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [finrank_span_eq_card hli, Fintype.card_sum, Fintype.card_fin, hV]
    ring
  set b := Basis.mk hli hsp with hb
  have hbl : ∀ i, b (.inl i) = (P i).e := fun i => by rw [hb, Basis.mk_apply]; rfl
  have hbr : ∀ i, b (.inr i) = (P i).f := fun i => by rw [hb, Basis.mk_apply]; rfl
  refine ⟨b, fun i => ?_, fun i j => ?_, fun i j => ?_, fun i hik => ?_, fun x y => ?_⟩
  · rw [hbl, hbr]; exact ⟨(P i).Q_e, (P i).Q_f⟩
  · rw [hbl, hbr]; exact hef i j
  · rw [hbl, hbl, hbr, hbr]; exact ⟨hee i j, hff i j⟩
  · rw [hPW i hik, ← Set.image_comp]
    congr 2
    funext j
    exact (hbl j).symm
  · simp only [hbl, hbr]
    have hX : Q (∑ i, x i • (P i).e) = 0 :=
      map_eq_zero_of_mem_span (S := Set.range fun i => (P i).e)
        (by rintro _ ⟨i, rfl⟩; exact (P i).Q_e)
        (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hee i j)
        (sum_mem fun i _ => smul_mem _ _ (subset_span ⟨i, rfl⟩))
    have hY : Q (∑ i, y i • (P i).f) = 0 :=
      map_eq_zero_of_mem_span (S := Set.range fun i => (P i).f)
        (by rintro _ ⟨i, rfl⟩; exact (P i).Q_f)
        (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hff i j)
        (sum_mem fun i _ => smul_mem _ _ (subset_span ⟨i, rfl⟩))
    rw [QuadraticMap.map_add Q, hX, hY, zero_add, zero_add, polar_sum_smul_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h := (hcoef x 0 j).1
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero] at h
    rw [h, mul_comm]

theorem orthogonal_geometry_split_Witt_flags [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {r : ℕ} (hV : finrank K V = 2 * r)
    (hT : ∃ T : Submodule K V, finrank K T = r ∧ ∀ x ∈ T, Q x = 0) :
    (∀ (k : ℕ), k ≤ r → ∀ W : ℕ → Submodule K V, (∀ i ≤ k, finrank K (W i) = i) →
      (∀ i < k, W i ≤ W (i + 1)) → (∀ x ∈ W k, Q x = 0) →
      ∃ b : Basis (Fin r ⊕ Fin r) K V,
        (∀ i, Q (b (.inl i)) = 0 ∧ Q (b (.inr i)) = 0) ∧
        (∀ i j, polar Q (b (.inl i)) (b (.inr j)) = if i = j then 1 else 0) ∧
        (∀ i j, polar Q (b (.inl i)) (b (.inl j)) = 0 ∧ polar Q (b (.inr i)) (b (.inr j)) = 0) ∧
        (∀ i ≤ k, W i = span K (b '' (Sum.inl '' {j : Fin r | (j : ℕ) < i}))) ∧
        ∀ x y : Fin r → K, Q (∑ i, x i • b (.inl i) + ∑ i, y i • b (.inr i)) = ∑ i, x i * y i) ∧
    ∀ T : Submodule K V, (∀ x ∈ T, Q x = 0) →
      (∀ T' : Submodule K V, T ≤ T' → (∀ x ∈ T', Q x = 0) → T' = T) → finrank K T = r := by
  refine ⟨fun k hk W hWd hWm hWs =>
    orthogonal_geometry_split_Witt_flags_aux hQ hV hT k hk W hWd hWm hWs, fun T hTs hmax => ?_⟩
  set t := finrank K T with htdef
  have hrefl : (polarBilin Q).IsRefl := fun x y h => by
    rw [polarBilin_apply_apply] at h ⊢
    rwa [polar_comm]
  have ht : t ≤ r := by
    have h := LinearMap.BilinForm.finrank_add_finrank_orthogonal hrefl T
    rw [LinearMap.BilinForm.orthogonal_top_eq_bot hQ, inf_bot_eq, finrank_bot, add_zero] at h
    have hle : T ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) T := fun x hx =>
      LinearMap.BilinForm.mem_orthogonal_iff.2 fun y hy => by
        rw [polarBilin_apply_apply]
        exact polar_eq_zero_of_singular hTs hy hx
    have := Submodule.finrank_mono hle
    omega
  set u := Module.finBasis K T
  set Wf : ℕ → Submodule K V := fun i => span K ((fun j : Fin t => (u j : V)) '' {j | (j : ℕ) < i})
    with hWf
  have hli : LinearIndependent K (fun j : Fin t => (u j : V)) :=
    u.linearIndependent.map' T.subtype (ker_subtype T)
  have hWd : ∀ i ≤ t, finrank K (Wf i) = i := fun i hi => finrank_span_image_lt hli hi
  have hWm : ∀ i < t, Wf i ≤ Wf (i + 1) := fun i _ =>
    span_mono (Set.image_mono fun j (hj : (j : ℕ) < i) => Nat.lt_succ_of_lt hj)
  have hWt : Wf t ≤ T := span_le.2 (by rintro _ ⟨j, -, rfl⟩; exact (u j).2)
  obtain ⟨b, hbQ, -, hbB, hbW, -⟩ := orthogonal_geometry_split_Witt_flags_aux hQ hV hT t ht Wf hWd
    hWm (fun x hx => hTs x (hWt hx))
  have hWT : Wf t = T := eq_of_le_of_finrank_eq hWt (by rw [hWd t le_rfl])
  set X := span K (b '' (Sum.inl '' {j : Fin r | (j : ℕ) < r})) with hX
  have hTX : T ≤ X := by
    rw [← hWT, hbW t le_rfl]
    exact span_mono (Set.image_mono (Set.image_mono fun j (hj : (j : ℕ) < t) =>
      show (j : ℕ) < r by omega))
  have hXs : ∀ x ∈ X, Q x = 0 := fun x hx =>
    map_eq_zero_of_mem_span (by rintro _ ⟨_, ⟨i, -, rfl⟩, rfl⟩; exact (hbQ i).1)
      (by rintro _ ⟨_, ⟨i, -, rfl⟩, rfl⟩ _ ⟨_, ⟨j, -, rfl⟩, rfl⟩; exact (hbB i j).1) hx
  rw [htdef, ← hmax X hTX hXs, finrank_span_inl_image b le_rfl]

end CFSG.LocalAnalysis.ComponentInitial
