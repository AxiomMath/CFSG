module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitFlagTransitivity

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open Module Submodule

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def extensionsIn (W : Submodule K V) (S : Set V) : Set (Submodule K V) :=
  {W' | W ≤ W' ∧ finrank K W' = finrank K W + 1 ∧ ∀ x ∈ W', x ∉ W → x ∈ S}

theorem finrank_sup_span_singleton [FiniteDimensional K V] {W : Submodule K V} {x : V}
    (hx : x ∉ W) : finrank K (W ⊔ K ∙ x : Submodule K V) = finrank K W + 1 := by
  have hx0 : x ≠ 0 := fun h => hx (h ▸ W.zero_mem)
  have hinf : W ⊓ K ∙ x = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyW, hyx⟩
    obtain ⟨c, rfl⟩ := mem_span_singleton.1 hyx
    by_cases hc : c = 0
    · rw [hc, zero_smul]
      exact zero_mem _
    · exact absurd (by simpa [smul_smul, inv_mul_cancel₀ hc] using W.smul_mem c⁻¹ hyW) hx
  have h := finrank_sup_add_finrank_inf_eq W (K ∙ x)
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hx0] at h
  exact h

theorem card_mem_not_mem [Finite K] [FiniteDimensional K V] {W W' : Submodule K V}
    (hWW' : W ≤ W') :
    Nat.card {x : V // x ∈ W' ∧ x ∉ W} = Nat.card K ^ finrank K W' - Nat.card K ^ finrank K W := by
  have : Finite V := Module.finite_of_finite K
  rw [← Module.natCard_eq_pow_finrank (K := K) (V := W'),
    ← Module.natCard_eq_pow_finrank (K := K) (V := W)]
  have h := Set.ncard_sdiff (s := (W : Set V)) (t := (W' : Set V)) hWW' (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at h
  rw [← SetLike.coe_sort_coe, ← SetLike.coe_sort_coe (p := W), ← h]
  rfl

theorem card_vectors_eq_mul_card_extensions [Finite K] [FiniteDimensional K V]
    {W : Submodule K V} {S : Set V} (hSW : ∀ x ∈ S, x ∉ W)
    (hS : ∀ (c : K) (w x : V), c ≠ 0 → w ∈ W → x ∈ S → c • x + w ∈ S) :
    Nat.card S = (Nat.card K ^ (finrank K W + 1) - Nat.card K ^ finrank K W) *
      Nat.card (extensionsIn W S) := by
  classical
  have : Finite V := Module.finite_of_finite K
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite (Submodule K V)
  let φ : S → extensionsIn W S := fun x => ⟨W ⊔ K ∙ (x : V), le_sup_left,
    finrank_sup_span_singleton (hSW x x.2), fun y hy hyW => by
      obtain ⟨w, hw, z, hz, rfl⟩ := mem_sup.1 hy
      obtain ⟨c, rfl⟩ := mem_span_singleton.1 hz
      have hc : c ≠ 0 := by
        rintro rfl
        rw [zero_smul, add_zero] at hyW
        exact hyW hw
      rw [add_comm]
      exact hS c w x hc hw x.2⟩
  have hfib : ∀ W' : extensionsIn W S, Nat.card {x : S // φ x = W'} =
      Nat.card K ^ (finrank K W + 1) - Nat.card K ^ finrank K W := by
    intro W'
    rw [← W'.2.2.1, ← card_mem_not_mem W'.2.1]
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1, ?_, hSW x.1 x.1.2⟩
        invFun := fun y => ⟨⟨y.1, W'.2.2.2 y.1 y.2.1 y.2.2⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · have h : W ⊔ K ∙ ((x.1 : S) : V) = (W' : Submodule K V) := congrArg Subtype.val x.2
      exact h ▸ mem_sup_right (mem_span_singleton_self _)
    · apply Subtype.ext
      exact eq_of_le_of_finrank_eq (sup_le W'.2.1 ((span_singleton_le_iff_mem _ _).2 y.2.1))
        (by rw [finrank_sup_span_singleton y.2.2, W'.2.2.1])
  have hsig := Nat.card_congr (Equiv.sigmaFiberEquiv φ)
  rw [Nat.card_sigma] at hsig
  rw [← hsig, Finset.sum_congr rfl fun W' _ => hfib W', Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Nat.card_eq_fintype_card (α := extensionsIn W S), mul_comm]


@[expose] def flagsWith (A : Submodule K V → Prop) (k : ℕ) : Set (Fin k → Submodule K V) :=
  {W | (∀ i, finrank K (W i) = i + 1) ∧ Monotone W ∧ ∀ i, A (W i)}

@[expose] def extensionsWith (A : Submodule K V → Prop) (U : Submodule K V) (j : ℕ) :
    Set (Submodule K V) :=
  {W' | U ≤ W' ∧ finrank K W' = j + 1 ∧ A W'}

theorem card_flagsWith_zero (A : Submodule K V → Prop) : Nat.card (flagsWith A 0) = 1 := by
  rw [show flagsWith A 0 = Set.univ from Set.eq_univ_of_forall fun W =>
    ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩, Nat.card_univ]
  exact Nat.card_unique

theorem le_natFlag {k : ℕ} {W : Fin k → Submodule K V} (hW : Monotone W) (i : Fin k) :
    W i ≤ natFlag W k := by
  rw [natFlag_of_pos W (by have := i.isLt; omega) le_rfl]
  exact hW (Fin.le_def.2 (by simp only; omega))

theorem monotone_snoc {k : ℕ} {W : Fin k → Submodule K V} (hW : Monotone W)
    {W' : Submodule K V} (hW' : ∀ i, W i ≤ W') :
    Monotone (Fin.snoc W W' : Fin (k + 1) → Submodule K V) := by
  intro a b hab
  induction b using Fin.lastCases with
  | last =>
    induction a using Fin.lastCases with
    | last => exact le_rfl
    | cast a => rw [Fin.snoc_castSucc, Fin.snoc_last]; exact hW' a
  | cast b =>
    induction a using Fin.lastCases with
    | last => exact absurd hab (not_le.2 (Fin.castSucc_lt_last b))
    | cast a =>
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact hW (Fin.castSucc_le_castSucc_iff.1 hab)

theorem card_flagsWith_succ [Finite K] [FiniteDimensional K V] (A : Submodule K V → Prop)
    {k : ℕ} {e : ℚ}
    (he : ∀ W ∈ flagsWith A k, (Nat.card (extensionsWith A (natFlag W k) k) : ℚ) = e) :
    (Nat.card (flagsWith A (k + 1)) : ℚ) = Nat.card (flagsWith A k) * e := by
  classical
  have : Finite V := Module.finite_of_finite K
  let _ := Fintype.ofFinite (flagsWith A k)
  let π : flagsWith A (k + 1) → flagsWith A k := fun F =>
    ⟨Fin.init F.1, fun i => (F.2.1 i.castSucc).trans (by rw [Fin.val_castSucc]),
      fun a b hab => F.2.2.1 (Fin.castSucc_le_castSucc_iff.2 hab), fun i => F.2.2.2 _⟩
  have hπ : ∀ F, (π F : Fin k → Submodule K V) = Fin.init F.1 := fun F => rfl
  have hfib : ∀ W : flagsWith A k, Nat.card {F // π F = W} =
      Nat.card (extensionsWith A (natFlag W.1 k) k) := by
    intro W
    refine Nat.card_congr
      { toFun := fun F => ⟨F.1.1 (Fin.last k), ?_, by simpa using F.1.2.1 (Fin.last k),
          F.1.2.2.2 _⟩
        invFun := fun W' => ⟨⟨Fin.snoc W.1 W'.1, fun i => ?_, monotone_snoc W.2.2.1
          fun i => (le_natFlag W.2.2.1 i).trans W'.2.1, fun i => ?_⟩, ?_⟩
        left_inv := fun F => ?_
        right_inv := fun W' => ?_ }
    ·
      have hW : Fin.init F.1.1 = W.1 := by rw [← hπ, F.2]
      rcases Nat.eq_zero_or_pos k with hk | hk
      · rw [natFlag_of_not_pos _ (by omega)]
        exact bot_le
      · rw [natFlag_of_pos _ hk le_rfl, ← hW, Fin.init]
        exact F.1.2.2.1 (Fin.le_def.2 (by simp))
    · induction i using Fin.lastCases with
      | last => rw [Fin.snoc_last, W'.2.2.1]; simp
      | cast i => rw [Fin.snoc_castSucc, W.2.1 i]; simp
    · induction i using Fin.lastCases with
      | last => rw [Fin.snoc_last]; exact W'.2.2.2
      | cast i => rw [Fin.snoc_castSucc]; exact W.2.2.2 i
    · exact Subtype.ext ((hπ _).trans (Fin.init_snoc _ _))
    · apply Subtype.ext
      apply Subtype.ext
      have hW : Fin.init F.1.1 = W.1 := by rw [← hπ, F.2]
      change Fin.snoc W.1 (F.1.1 (Fin.last k)) = F.1.1
      rw [← hW, Fin.snoc_init_self]
    · apply Subtype.ext
      change (Fin.snoc W.1 W'.1 : Fin (k + 1) → Submodule K V) (Fin.last k) = W'.1
      exact Fin.snoc_last _ _
  have hsig := Nat.card_congr (Equiv.sigmaFiberEquiv π)
  rw [Nat.card_sigma] at hsig
  rw [← hsig, Nat.cast_sum, Finset.sum_congr rfl fun W _ =>
    show ((Nat.card {x // π x = W} : ℕ) : ℚ) = e by rw [hfib W]; exact he W.1 W.2,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]

theorem card_flagsWith [Finite K] [FiniteDimensional K V] (A : Submodule K V → Prop) (e : ℕ → ℚ)
    (k : ℕ) (he : ∀ j < k, ∀ W ∈ flagsWith A j,
      (Nat.card (extensionsWith A (natFlag W j) j) : ℚ) = e j) :
    (Nat.card (flagsWith A k) : ℚ) = ∏ j ∈ Finset.range k, e j := by
  induction k with
  | zero => rw [card_flagsWith_zero, Nat.cast_one, Finset.prod_range_zero]
  | succ k ih =>
    rw [card_flagsWith_succ A (he k (by omega)), ih fun j hj => he j (by omega),
      Finset.prod_range_succ]


theorem card_extensionsWith_le_mul [Finite K] [FiniteDimensional K V] {X U : Submodule K V}
    (hUX : U ≤ X) :
    Nat.card (extensionsWith (· ≤ X) U (finrank K U)) *
        (Nat.card K ^ (finrank K U + 1) - Nat.card K ^ finrank K U) =
      Nat.card K ^ finrank K X - Nat.card K ^ finrank K U := by
  have hS := card_vectors_eq_mul_card_extensions (W := U) (S := {x | x ∈ X ∧ x ∉ U})
    (fun x hx => hx.2) fun c w x hc hw hx => ⟨X.add_mem (X.smul_mem c hx.1) (hUX hw), fun h => hx.2
      (by simpa [smul_smul, inv_mul_cancel₀ hc] using U.smul_mem c⁻¹ (U.sub_mem h hw))⟩
  have hext : extensionsIn U {x | x ∈ X ∧ x ∉ U} = extensionsWith (· ≤ X) U (finrank K U) := by
    ext W'
    constructor
    · rintro ⟨hUW', hd, hW'⟩
      refine ⟨hUW', hd, fun x hx => ?_⟩
      by_cases hxU : x ∈ U
      · exact hUX hxU
      · exact (hW' x hx hxU).1
    · rintro ⟨hUW', hd, hW'X⟩
      exact ⟨hUW', hd, fun x hx hxU => ⟨hW'X hx, hxU⟩⟩
  rw [hext, mul_comm] at hS
  rw [← hS, ← card_mem_not_mem hUX]
  rfl


theorem finrank_natFlag {k : ℕ} {W : Fin k → Submodule K V}
    (hW : ∀ i, finrank K (W i) = i + 1) : finrank K (natFlag W k) = k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [natFlag_of_not_pos W (by omega), finrank_bot, hk]
  · rw [natFlag_of_pos W hk le_rfl, hW]
    simp only
    omega

theorem natFlag_le_of_forall_le {k : ℕ} {W : Fin k → Submodule K V} {X : Submodule K V}
    (hW : ∀ i, W i ≤ X) : natFlag W k ≤ X := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [natFlag_of_not_pos W (by omega)]
    exact bot_le
  · rw [natFlag_of_pos W hk le_rfl]
    exact hW _

theorem pow_succ_sub_pow_pos [Finite K] (j : ℕ) :
    0 < Nat.card K ^ (j + 1) - Nat.card K ^ j := by
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have := Nat.pow_lt_pow_right hq (by omega : j < j + 1)
  omega

theorem card_flagsWith_le [Finite K] [FiniteDimensional K V] (X : Submodule K V) :
    (Nat.card (flagsWith (· ≤ X) (finrank K X)) : ℚ) =
      ∏ j ∈ Finset.range (finrank K X), (((Nat.card K : ℚ) ^ finrank K X - (Nat.card K : ℚ) ^ j) /
        ((Nat.card K : ℚ) ^ (j + 1) - (Nat.card K : ℚ) ^ j)) := by
  apply card_flagsWith
  intro j hj W hW
  have hU := finrank_natFlag hW.1
  have h := card_extensionsWith_le_mul (natFlag_le_of_forall_le hW.2.2)
  rw [hU] at h
  have hq1 : 1 ≤ Nat.card K := (Finite.one_lt_card (α := K)).le
  have hle : Nat.card K ^ j ≤ Nat.card K ^ finrank K X := Nat.pow_le_pow_right hq1 hj.le
  have hle' : Nat.card K ^ j ≤ Nat.card K ^ (j + 1) := Nat.pow_le_pow_right hq1 (by omega)
  have hpos : ((Nat.card K ^ (j + 1) - Nat.card K ^ j : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (pow_succ_sub_pow_pos (K := K) j).ne'
  rw [eq_div_iff (by push_cast [Nat.cast_sub hle'] at hpos; exact hpos)]
  have h' := congrArg (Nat.cast : ℕ → ℚ) h
  push_cast [Nat.cast_sub hle, Nat.cast_sub hle'] at h'
  exact h'

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
