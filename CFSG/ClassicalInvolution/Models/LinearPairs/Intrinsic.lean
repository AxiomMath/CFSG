module

public import CFSG.ClassicalInvolution.Models.LinearPairs.Pairs

public section

namespace CFSG.ClassicalInvolution.Models

open Matrix CFSG.ClassicalInvolution.WeakCT Module
open scoped MatrixGroups

section Involution

variable {K : Type} [Field K] {n : ℕ}

theorem isCompl_eigSpace (h2 : (2 : K) ≠ 0) {I : Matrix (Fin n) (Fin n) K} (hI : I * I = 1) :
    IsCompl (eigSpace I (-1)) (eigSpace I 1) := by
  have hII : ∀ u, I *ᵥ (I *ᵥ u) = u := fun u => by
    rw [mulVec_mulVec, hI, Matrix.one_mulVec]
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro v hv1 hv2
    rw [mem_eigSpace_neg_one] at hv1
    rw [mem_eigSpace_one] at hv2
    have h : v = -v := hv2.symm.trans hv1
    have h' : (2 : K) • v = 0 := by
      rw [two_smul]
      nth_rewrite 1 [h]
      exact neg_add_cancel v
    exact (smul_eq_zero.mp h').resolve_left h2
  · rw [codisjoint_iff, eq_top_iff]
    intro u _
    rw [Submodule.mem_sup]
    refine ⟨(2 : K)⁻¹ • (u - I *ᵥ u), ?_, (2 : K)⁻¹ • (u + I *ᵥ u), ?_, ?_⟩
    · rw [mem_eigSpace_neg_one, Matrix.mulVec_smul, Matrix.mulVec_sub, hII]
      module
    · rw [mem_eigSpace_one, Matrix.mulVec_smul, Matrix.mulVec_add, hII]
      module
    · have h22 : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
      calc (2 : K)⁻¹ • (u - I *ᵥ u) + (2 : K)⁻¹ • (u + I *ᵥ u) = ((2 : K)⁻¹ * 2) • u := by
            module
        _ = u := by rw [h22, one_smul]

theorem commute_and_fix_iff_vec (h2 : (2 : K) ≠ 0) {I X : Matrix (Fin n) (Fin n) K}
    (hI : I * I = 1) :
    (X * I = I * X ∧ X * (1 + I) = 1 + I) ↔
      (∀ w ∈ eigSpace I 1, X *ᵥ w = w) ∧ ∀ v ∈ eigSpace I (-1), X *ᵥ v ∈ eigSpace I (-1) := by
  have hII : ∀ u, I *ᵥ (I *ᵥ u) = u := fun u => by
    rw [mulVec_mulVec, hI, Matrix.one_mulVec]
  constructor
  · rintro ⟨h1, h3⟩
    refine ⟨fun w hw => ?_, fun v hv => ?_⟩
    · rw [mem_eigSpace_one] at hw
      have h := congrArg (fun M : Matrix (Fin n) (Fin n) K => M *ᵥ w) h3
      simp only [← mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, hw, Matrix.mulVec_add] at h
      have h' : (2 : K) • (X *ᵥ w - w) = 0 := by
        rw [smul_sub, two_smul, two_smul]
        exact sub_eq_zero.mpr h
      exact sub_eq_zero.mp ((smul_eq_zero.mp h').resolve_left h2)
    · rw [mem_eigSpace_neg_one] at hv ⊢
      rw [mulVec_mulVec, ← h1, ← mulVec_mulVec, hv, Matrix.mulVec_neg]
  · rintro ⟨hw, hv⟩
    have hp : ∀ u, u + I *ᵥ u ∈ eigSpace I 1 := fun u => by
      rw [mem_eigSpace_one, Matrix.mulVec_add, hII, add_comm]
    have hq : ∀ u, u - I *ᵥ u ∈ eigSpace I (-1) := fun u => by
      rw [mem_eigSpace_neg_one, Matrix.mulVec_sub, hII, neg_sub]
    have h2u : ∀ u : Fin n → K, (2 : K) • u = (u + I *ᵥ u) + (u - I *ᵥ u) := fun u => by
      rw [two_smul]
      abel
    refine ⟨?_, ?_⟩
    · rw [Matrix.ext_iff_mulVec]
      intro u
      have hxp := hw _ (hp u)
      have hxq := mem_eigSpace_neg_one.mp (hv _ (hq u))
      have hIp : I *ᵥ (u + I *ᵥ u) = u + I *ᵥ u := mem_eigSpace_one.mp (hp u)
      have hIq : I *ᵥ (u - I *ᵥ u) = -(u - I *ᵥ u) := mem_eigSpace_neg_one.mp (hq u)
      have e1 : (2 : K) • (X *ᵥ (I *ᵥ u)) = (u + I *ᵥ u) - X *ᵥ (u - I *ᵥ u) := by
        have h : (2 : K) • (I *ᵥ u) = (u + I *ᵥ u) - (u - I *ᵥ u) := by
          rw [two_smul]
          abel
        rw [← Matrix.mulVec_smul, h, Matrix.mulVec_sub, hxp]
      have e2 : (2 : K) • (I *ᵥ (X *ᵥ u)) = (u + I *ᵥ u) - X *ᵥ (u - I *ᵥ u) := by
        rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, h2u u, Matrix.mulVec_add, hxp,
          Matrix.mulVec_add, hIp, hxq]
        abel
      have key : (2 : K) • ((X * I) *ᵥ u) = (2 : K) • ((I * X) *ᵥ u) := by
        rw [← mulVec_mulVec, ← mulVec_mulVec, e1, e2]
      exact smul_right_injective _ h2 key
    · rw [Matrix.ext_iff_mulVec]
      intro u
      rw [← mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
      exact hw _ (hp u)

theorem mem_longRootGroup_iff_vec (h2 : (2 : K) ≠ 0) {I : Matrix (Fin n) (Fin n) K}
    (hI : I * I = 1) {x : SL(n, K)} :
    x ∈ longRootGroup I ↔ (∀ w ∈ eigSpace I 1, (x : Matrix (Fin n) (Fin n) K) *ᵥ w = w) ∧
      ∀ v ∈ eigSpace I (-1), (x : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ eigSpace I (-1) :=
  commute_and_fix_iff_vec h2 hI

end Involution

section LongRoot

variable {K : Type} [Field K] {n : ℕ}

theorem IsLongRootSL2.mem_iff_vec (h2 : (2 : K) ≠ 0) {hn : 2 ≤ n} {L : Subgroup SL(n, K)}
    {i : SL(n, K)} (h : IsLongRootSL2 hn L i) {x : SL(n, K)} :
    x ∈ L ↔ (∀ w ∈ fixSpace i, (x : Matrix (Fin n) (Fin n) K) *ᵥ w = w) ∧
      ∀ v ∈ minusSpace i, (x : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ minusSpace i := by
  have hI : (i : Matrix (Fin n) (Fin n) K) * i = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, h.mul_self, Matrix.SpecialLinearGroup.coe_one]
  rw [h.eq_longRootGroup h2]
  exact mem_longRootGroup_iff_vec h2 hI

theorem IsLongRootSL2.isCompl (h2 : (2 : K) ≠ 0) {hn : 2 ≤ n} {L : Subgroup SL(n, K)}
    {i : SL(n, K)} (h : IsLongRootSL2 hn L i) : IsCompl (minusSpace i) (fixSpace i) := by
  have hI : (i : Matrix (Fin n) (Fin n) K) * i = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, h.mul_self, Matrix.SpecialLinearGroup.coe_one]
  exact isCompl_eigSpace h2 hI

theorem IsLongRootSL2.exists_isCompl (h2 : (2 : K) ≠ 0) {hn : 2 ≤ n} {L : Subgroup SL(n, K)}
    {i : SL(n, K)} (h : IsLongRootSL2 hn L i) :
    ∃ V W : Submodule K (Fin n → K), IsCompl V W ∧ finrank K V = 2 ∧ ∀ x : SL(n, K),
      x ∈ L ↔ (∀ w ∈ W, (x : Matrix (Fin n) (Fin n) K) *ᵥ w = w) ∧
        ∀ v ∈ V, (x : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ V :=
  ⟨minusSpace i, fixSpace i, h.isCompl h2, h.finrank_minusSpace h2, fun _ => h.mem_iff_vec h2⟩

theorem mem_eigSpace_negBlock_neg_one_iff (h2 : (2 : K) ≠ 0) (j : ℕ) {v : Fin n → K} :
    v ∈ eigSpace (negBlock K n j) (-1) ↔
      ∀ a : Fin n, ¬ (j ≤ a.val ∧ a.val < j + 2) → v a = 0 := by
  rw [mem_eigSpace_neg_one, negBlock_eq_diagonal]
  constructor
  · intro h a ha
    have := congr_fun h a
    rw [Matrix.mulVec_diagonal] at this
    simp only [ha, ite_false, Pi.neg_apply] at this
    have h' : (2 : K) * v a = 0 := by linear_combination this
    exact (mul_eq_zero.mp h').resolve_left h2
  · intro h
    funext a
    rw [Matrix.mulVec_diagonal]
    by_cases ha : j ≤ a.val ∧ a.val < j + 2
    · simp [ha]
    · simp [ha, h a ha]

theorem mem_eigSpace_negBlock_one_iff (h2 : (2 : K) ≠ 0) (j : ℕ) {v : Fin n → K} :
    v ∈ eigSpace (negBlock K n j) 1 ↔ ∀ a : Fin n, (j ≤ a.val ∧ a.val < j + 2) → v a = 0 := by
  rw [mem_eigSpace_one, negBlock_eq_diagonal]
  constructor
  · intro h a ha
    have := congr_fun h a
    rw [Matrix.mulVec_diagonal] at this
    rw [ite_eq_left ha] at this
    have h' : (2 : K) * v a = 0 := by linear_combination -this
    exact (mul_eq_zero.mp h').resolve_left h2
  · intro h
    funext a
    rw [Matrix.mulVec_diagonal]
    by_cases ha : j ≤ a.val ∧ a.val < j + 2
    · simp [ha, h a ha]
    · simp [ha]

theorem mulVec_mem_of_columns {P : Matrix (Fin n) (Fin n) K} {U : Submodule K (Fin n → K)}
    {v : Fin n → K} (hv : ∀ a, v a ≠ 0 → (fun b => P b a) ∈ U) : P *ᵥ v ∈ U := by
  have : P *ᵥ v = ∑ a, v a • (fun b => P b a) := by
    ext b
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [this]
  refine Submodule.sum_mem _ fun a _ => ?_
  by_cases ha : v a = 0
  · rw [ha, zero_smul]
    exact U.zero_mem
  · exact U.smul_mem _ (hv a ha)

theorem exists_isLongRootSL2_of_isCompl (h2 : (2 : K) ≠ 0) (hn : 2 ≤ n)
    {V W : Submodule K (Fin n → K)} (hVW : IsCompl V W) (hV : finrank K V = 2)
    {L : Subgroup SL(n, K)}
    (hL : ∀ x : SL(n, K), x ∈ L ↔ (∀ w ∈ W, (x : Matrix (Fin n) (Fin n) K) *ᵥ w = w) ∧
      ∀ v ∈ V, (x : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ V) :
    ∃ i : SL(n, K), IsLongRootSL2 hn L i := by
  have hW : finrank K W = n - 2 := by
    have := Submodule.finrank_add_eq_of_isCompl hVW
    rw [Module.finrank_fin_fun] at this
    omega
  let E : Bool → Submodule K (Fin n → K) := fun b => cond b W V
  have hint : DirectSum.IsInternal E := by
    rw [DirectSum.isInternal_submodule_iff_isCompl E (i := false) (j := true) (by simp)
      (by ext b; cases b <;> simp)]
    exact hVW
  let ε : Fin n → Bool := fun j => decide (2 ≤ j.val)
  have hε : ∀ b, Nat.card {j // ε j = b} = finrank K (E b) := by
    intro b
    cases b
    · change _ = finrank K V
      rw [hV, Nat.card_congr (Equiv.subtypeEquivRight (q := fun j : Fin n => j.val < 2)
        (fun j => by simp only [ε, decide_eq_false_iff_not, not_le]))]
      exact card_fin_val_lt hn
    · change _ = finrank K W
      rw [hW, Nat.card_congr (Equiv.subtypeEquivRight (q := fun j : Fin n => 2 ≤ j.val)
        (fun j => by simp only [ε, decide_eq_true_eq]))]
      exact card_fin_val_ge hn
  obtain ⟨P, hP⟩ := exists_sl_adapted (by omega) E hint ε hε
  have hPQ := coe_mul_coe_inv P
  have hQP := coe_inv_mul_coe P
  have hN := negBlock_mul_self (K := K) n 0
  have hcompl₀ : IsCompl (eigSpace (negBlock K n 0) (-1)) (eigSpace (negBlock K n 0) 1) :=
    isCompl_eigSpace h2 hN
  have hsurj : ∀ v : Fin n → K, ∃ u, Matrix.toLin' (P : Matrix (Fin n) (Fin n) K) u = v := fun v =>
    ⟨((P⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) *ᵥ v, by
      rw [Matrix.toLin'_apply, mulVec_mulVec, hPQ, Matrix.one_mulVec]⟩
  have hmapV : (eigSpace (negBlock K n 0) (-1)).map (Matrix.toLin' (P : Matrix (Fin n) (Fin n) K)) ≤
      V := by
    rintro _ ⟨v, hv, rfl⟩
    rw [Matrix.toLin'_apply]
    refine mulVec_mem_of_columns fun a ha => ?_
    have hlt : a.val < 2 := by
      by_contra hcon
      exact ha ((mem_eigSpace_negBlock_neg_one_iff h2 0).mp hv a (by omega))
    have := hP a
    simpa [E, ε, show ¬ 2 ≤ a.val by omega] using this
  have hmapW : (eigSpace (negBlock K n 0) 1).map (Matrix.toLin' (P : Matrix (Fin n) (Fin n) K)) ≤
      W := by
    rintro _ ⟨v, hv, rfl⟩
    rw [Matrix.toLin'_apply]
    refine mulVec_mem_of_columns fun a ha => ?_
    have hge : 2 ≤ a.val := by
      by_contra hcon
      exact ha ((mem_eigSpace_negBlock_one_iff h2 0).mp hv a (by omega))
    have := hP a
    simpa [E, ε, hge] using this
  have hVeq : (eigSpace (negBlock K n 0) (-1)).map
      (Matrix.toLin' (P : Matrix (Fin n) (Fin n) K)) = V := by
    refine le_antisymm hmapV fun v hv => ?_
    obtain ⟨u, rfl⟩ := hsurj v
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp
      (hcompl₀.sup_eq_top ▸ (Submodule.mem_top : u ∈ ⊤))
    have h1 := hmapV ⟨u₁, hu₁, rfl⟩
    have h2' := hmapW ⟨u₂, hu₂, rfl⟩
    have hmem : Matrix.toLin' (P : Matrix (Fin n) (Fin n) K) u₂ ∈ V ⊓ W := by
      refine ⟨?_, h2'⟩
      have := V.sub_mem hv h1
      rwa [map_add, add_sub_cancel_left] at this
    rw [hVW.inf_eq_bot, Submodule.mem_bot] at hmem
    exact ⟨u₁, hu₁, by rw [map_add, hmem, add_zero]⟩
  have hWeq : (eigSpace (negBlock K n 0) 1).map
      (Matrix.toLin' (P : Matrix (Fin n) (Fin n) K)) = W := by
    refine le_antisymm hmapW fun w hw => ?_
    obtain ⟨u, rfl⟩ := hsurj w
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp
      (hcompl₀.sup_eq_top ▸ (Submodule.mem_top : u ∈ ⊤))
    have h1 := hmapV ⟨u₁, hu₁, rfl⟩
    have h2' := hmapW ⟨u₂, hu₂, rfl⟩
    have hmem : Matrix.toLin' (P : Matrix (Fin n) (Fin n) K) u₁ ∈ V ⊓ W := by
      refine ⟨h1, ?_⟩
      have := W.sub_mem hw h2'
      rwa [map_add, add_sub_cancel_right] at this
    rw [hVW.inf_eq_bot, Submodule.mem_bot] at hmem
    exact ⟨u₂, hu₂, by rw [map_add, hmem, zero_add]⟩
  have hII : ((P : Matrix (Fin n) (Fin n) K) * negBlock K n 0 *
      ((P⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K)) *
      ((P : Matrix (Fin n) (Fin n) K) * negBlock K n 0 *
        ((P⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K)) = 1 := by
    rw [conj_mul_conj hQP, hN, Matrix.mul_one, hPQ]
  refine ⟨P * rootInv K hn * P⁻¹, P, ?_, rfl⟩
  have e : (rootSL2 K hn).map (MulAut.conj P).toMonoidHom =
      longRootGroup ((P : Matrix (Fin n) (Fin n) K) * negBlock K n 0 *
        ((P⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K)) := by
    rw [longRootGroup_conj, rootSL2_eq_longRootGroup h2 hn]
  rw [e]
  ext x
  rw [hL, mem_longRootGroup_iff_vec h2 hII]
  simp only [eigSpace_conj_aux hPQ hQP, hVeq, hWeq]

theorem exists_isLongRootSL2_iff (h2 : (2 : K) ≠ 0) (hn : 2 ≤ n) (L : Subgroup SL(n, K)) :
    (∃ i : SL(n, K), IsLongRootSL2 hn L i) ↔
      ∃ V W : Submodule K (Fin n → K), IsCompl V W ∧ finrank K V = 2 ∧ ∀ x : SL(n, K),
        x ∈ L ↔ (∀ w ∈ W, (x : Matrix (Fin n) (Fin n) K) *ᵥ w = w) ∧
          ∀ v ∈ V, (x : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ V := by
  constructor
  · rintro ⟨i, h⟩
    exact h.exists_isCompl h2
  · rintro ⟨V, W, hVW, hV, hL⟩
    exact exists_isLongRootSL2_of_isCompl h2 hn hVW hV hL

end LongRoot

section Unique

variable {K : Type} [Field K] {n : ℕ}

theorem IsLongRootSL2.eq_of_orderOf_eq_two (h2 : (2 : K) ≠ 0) {hn : 2 ≤ n}
    {L : Subgroup SL(n, K)} {i : SL(n, K)} (h : IsLongRootSL2 hn L i) {t : SL(n, K)} (htL : t ∈ L)
    (ht : orderOf t = 2) : t = i := by
  have hc := h.isClassicalSL2 h2
  obtain ⟨e⟩ := hc.nonempty_mulEquiv
  have key : ∀ s : L, orderOf s = 2 → e s = -1 := fun s hs =>
    (CFSG.Semidihedral.OddFieldSL2.orderOf_eq_two_iff K h2 (e s)).mp
      (by rw [MulEquiv.orderOf_eq]; exact hs)
  have h1 := key ⟨t, htL⟩ (by rwa [Subgroup.orderOf_mk])
  have h2' := key ⟨i, hc.mem⟩ (by rw [Subgroup.orderOf_mk]; exact hc.orderOf_eq_two)
  exact congrArg Subtype.val (e.injective (h1.trans h2'.symm))

theorem IsLongRootSL2.involution_unique (h2 : (2 : K) ≠ 0) {hn : 2 ≤ n}
    {L : Subgroup SL(n, K)} {i i' : SL(n, K)} (h : IsLongRootSL2 hn L i)
    (h' : IsLongRootSL2 hn L i') : i = i' :=
  (h.eq_of_orderOf_eq_two h2 h'.mem ((h'.isClassicalSL2 h2).orderOf_eq_two)).symm

theorem IsLongRootSL2.normal_subgroupOf_centralizer (h2 : (2 : K) ≠ 0) {hn : 2 ≤ n}
    {L : Subgroup SL(n, K)} {i : SL(n, K)} (h : IsLongRootSL2 hn L i) :
    (L.subgroupOf (Subgroup.centralizer ({i} : Set SL(n, K)))).Normal := by
  have hc := h.isClassicalSL2 h2
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hc.le_centralizer]
  exact hc.centralizer_le_normalizer

theorem isLongRootSL2_range_blockSL (h2 : (2 : K) ≠ 0) {j : ℕ} (hj : j + 2 ≤ n) :
    IsLongRootSL2 (by omega : 2 ≤ n) (blockSL K n 2 j hj).range (blockSL K n 2 j hj (-1)) := by
  obtain ⟨i, hi⟩ := exists_isLongRootSL2_of_isCompl h2 (by omega : 2 ≤ n)
    (isCompl_eigSpace h2 (negBlock_mul_self (K := K) n j)) (finrank_eigSpace_negBlock h2 hj)
    (L := (blockSL K n 2 j hj).range) fun x => by
      rw [range_blockSL_eq_longRootGroup h2 hj]
      exact mem_longRootGroup_iff_vec h2 (negBlock_mul_self (K := K) n j)
  have hmem : blockSL K n 2 j hj (-1) ∈ (blockSL K n 2 j hj).range := ⟨-1, rfl⟩
  have hord : orderOf (blockSL K n 2 j hj (-1)) = 2 := by
    rw [orderOf_injective (blockSL K n 2 j hj) (blockSL_injective _) (-1)]
    exact CFSG.Semidihedral.OddFieldSL2.minusIdentity_orderOf K h2
  rw [hi.eq_of_orderOf_eq_two h2 hmem hord]
  exact hi

end Unique

end CFSG.ClassicalInvolution.Models
