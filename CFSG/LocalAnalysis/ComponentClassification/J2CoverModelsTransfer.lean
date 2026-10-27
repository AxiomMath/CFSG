module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsCocycle

public section

namespace CFSG.ComponentClassification.J2Cover.Models

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] noncomputable def transfer (h : S → S → ZMod 2) (g k : P) : ZMod 2 :=
  ∑ i : Fin 4725, h (factor i g) (factor (cosetAct i g) k)

theorem isNormCocycle_transfer {h : S → S → ZMod 2} (hh : IsNormCocycle h) :
    IsNormCocycle (transfer h) := by
  refine ⟨fun k => ?_, fun g => ?_, fun g k l => ?_⟩
  · exact Finset.sum_eq_zero fun i _ => by rw [factor_one, hh.1]
  · exact Finset.sum_eq_zero fun i _ => by rw [factor_one, hh.2.1]
  · unfold transfer
    rw [← Finset.sum_add_distrib, ← Equiv.sum_comp (cosetPerm g)
      (fun i => h (factor i k) (factor (cosetAct i k) l)), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [cosetPerm_apply]
    rw [factor_mul, cosetAct_mul, factor_mul (cosetAct i g)]
    exact hh.2.2 _ _ _

theorem transfer_add (h h' : S → S → ZMod 2) (g k : P) :
    transfer (fun s t => h s t + h' s t) g k = transfer h g k + transfer h' g k :=
  Finset.sum_add_distrib

theorem transfer_smul (e : ZMod 2) (h : S → S → ZMod 2) (g k : P) :
    transfer (fun s t => e * h s t) g k = e * transfer h g k :=
  (Finset.mul_sum _ _ _).symm

theorem transfer_sum {ι : Type*} (u : Finset ι) (h : ι → S → S → ZMod 2) (g k : P) :
    transfer (fun s t => ∑ j ∈ u, h j s t) g k = ∑ j ∈ u, transfer (h j) g k :=
  Finset.sum_comm

theorem transfer_cob (b : S → ZMod 2) (g k : P) :
    transfer (cob b) g k = cob (fun g => ∑ i : Fin 4725, b (factor i g)) g k := by
  have h1 : ∑ i : Fin 4725, b (factor (cosetAct i g) k) = ∑ i : Fin 4725, b (factor i k) :=
    Equiv.sum_comp (cosetPerm g) (fun i => b (factor i k))
  have h2 : ∑ i : Fin 4725, b (factor i g * factor (cosetAct i g) k) =
      ∑ i : Fin 4725, b (factor i (g * k)) :=
    Finset.sum_congr rfl fun i _ => by rw [factor_mul]
  simp only [transfer, cob]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h1, h2]

theorem IsNormCocycle.restrict {g : P → P → ZMod 2} (hg : IsNormCocycle g) :
    IsNormCocycle fun s t : S => g (incl s) (incl t) := by
  refine ⟨fun b => ?_, fun a => ?_, fun a b c => ?_⟩
  · change g (incl 1) (incl b) = 0
    rw [map_one, hg.1]
  · change g (incl a) (incl 1) = 0
    rw [map_one, hg.2.1]
  · change g (incl a) (incl b) + g (incl (a * b)) (incl c) =
      g (incl b) (incl c) + g (incl a) (incl (b * c))
    rw [map_mul, map_mul]
    exact hg.2.2 _ _ _

theorem xorFold_succ (p : ℕ → Bool) (n : ℕ) : xorFold (n + 1) p = (xorFold n p ^^ p n) := by
  rw [xorFold, xorFold, Nat.fold_succ]

theorem sum_range_ite_xorFold (p : ℕ → Bool) : ∀ n : ℕ,
    (∑ i ∈ Finset.range n, (if p i then (1 : ZMod 2) else 0)) = if xorFold n p then 1 else 0
  | 0 => by rw [xorFold, Nat.fold_zero]; simp
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_range_ite_xorFold p n, xorFold_succ]
    by_cases h1 : xorFold n p = true <;> by_cases h2 : p n = true <;>
      simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Bool.xor_true, Bool.xor_false,
        Bool.not_true, Bool.not_false] <;> decide

theorem sum_ite_xorFold (p : ℕ → Bool) (n : ℕ) :
    (∑ i : Fin n, (if p i then (1 : ZMod 2) else 0)) = if xorFold n p then 1 else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if p i then (1 : ZMod 2) else 0) n]
  exact sum_range_ite_xorFold p n

theorem trBit_eq (rows : Array ℕ) (a d : ℕ) :
    trBit rows a d = xorFold 4725 (fun i => bitAt rows (pTab i a) (pTab (iTab i a) d)) := rfl

theorem transfer_tbl_elt (rows : Array ℕ) {a d : ℕ} (ha : a < 128) (hd : d < 128) :
    transfer (tbl rows) (incl (elt a)) (incl (elt d)) = if trBit rows a d then 1 else 0 := by
  rw [trBit_eq, ← sum_ite_xorFold]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨h1, h2, h3, h4⟩ := decomp_elt i ha
  obtain ⟨h5, -, h7, -⟩ := decomp_elt ⟨iTab i a, h2⟩ hd
  rw [h3, h4, h7, tbl_elt rows h1 h5]

theorem transfer_tbl_gen (rows : Array ℕ) {k d : ℕ} (hk : k < 3) (hd : d < 128) :
    transfer (tbl rows) (incl (yS k)) (incl (elt d)) = if trBit rows (k + 1) d then 1 else 0 := by
  rw [← elt_succ hk]
  exact transfer_tbl_elt rows (by omega) hd

theorem mk1_cob_gen (m : ℕ) {k d : ℕ} (hk : k < 3) (hd : d < 128) :
    cob (mk1 m) (yS k) (elt d) = if cobBit m (k + 1) d then 1 else 0 := by
  rw [cob, ← elt_succ hk, ← (mulIdx_spec (a := k + 1) hd).2, mk1_elt _ (by omega), mk1_elt _ hd,
    mk1_elt _ (mulIdx_spec (a := k + 1) hd).1, cobBit, mulTab_get (by omega) hd]
  cases maskBit m (k + 1) <;> cases maskBit m d <;> cases maskBit m (mulIdx (k + 1) d) <;> decide

theorem tbl_gen (rows : Array ℕ) {k d : ℕ} (hk : k < 3) (hd : d < 128) :
    tbl rows (yS k) (elt d) = if bitAt rows (k + 1) d then 1 else 0 := by
  rw [← elt_succ hk]
  exact tbl_elt rows (by omega) hd

theorem transferCheck_parts :
    (∀ j < 6, maskBit (bMask j) 0 = false) ∧ maskBit muMask 0 = false ∧
    (∀ j < 6, ∀ k < 3, ∀ d < 128, trBit (hRowsT j) (k + 1) d =
      ((eBit j && bitAt fRows (k + 1) d) ^^ cobBit (bMask j) (k + 1) d)) ∧
    (∀ k < 3, ∀ d < 128,
      (trBit fRows (k + 1) d ^^ cobBit muMask (k + 1) d) = bitAt fRows (k + 1) d) := by
  have h := transferCheck_eq
  simp only [transferCheck, Bool.and_eq_true, allLt_iff, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

@[expose] noncomputable def muCoch : S → ZMod 2 := mk1 muMask

theorem bCoch_one {j : ℕ} (hj : j < 6) : bCoch j 1 = 0 := by
  rw [bCoch, ← elt_zero, mk1_elt _ (by norm_num), transferCheck_parts.1 j hj]
  rfl

theorem muCoch_one : muCoch 1 = 0 := by
  rw [muCoch, ← elt_zero, mk1_elt _ (by norm_num), transferCheck_parts.2.1]
  rfl

theorem transfer_hCoc {j : ℕ} (hj : j < 6) (s t : S) :
    transfer (hCoc j) (incl s) (incl t) = eFlag j * fCoc s t + cob (bCoch j) s t := by
  set c : S → S → ZMod 2 := fun s t =>
    transfer (hCoc j) (incl s) (incl t) + (eFlag j * fCoc s t + cob (bCoch j) s t) with hc
  have hcc : IsNormCocycle c :=
    (isNormCocycle_transfer (isNormCocycle_hCoc hj)).restrict.add
      ((isNormCocycle_fCoc.smul (eFlag j)).add (isNormCocycle_cob (bCoch_one hj)))
  have hgen : ∀ k < 3, ∀ t, c (yS k) t = 0 := by
    intro k hk t
    rw [hc]
    simp only
    rw [← elt_idx t, hCoc, transfer_tbl_gen _ hk (idx_lt t), fCoc, tbl_gen _ hk (idx_lt t),
      bCoch, mk1_cob_gen _ hk (idx_lt t), eFlag, transferCheck_parts.2.2.1 j hj k hk _ (idx_lt t)]
    cases eBit j <;> cases bitAt fRows (k + 1) (idx t) <;>
      cases cobBit (bMask j) (k + 1) (idx t) <;> decide
  have := eq_zero_of_gen hcc hgen s t
  rw [hc] at this
  simp only at this
  grind

theorem transfer_fCoc (s t : S) : transfer fCoc (incl s) (incl t) + cob muCoch s t = fCoc s t := by
  set c : S → S → ZMod 2 := fun s t =>
    transfer fCoc (incl s) (incl t) + cob muCoch s t + fCoc s t with hc
  have hcc : IsNormCocycle c :=
    ((isNormCocycle_transfer isNormCocycle_fCoc).restrict.add
      (isNormCocycle_cob muCoch_one)).add isNormCocycle_fCoc
  have hgen : ∀ k < 3, ∀ t, c (yS k) t = 0 := by
    intro k hk t
    rw [hc]
    simp only
    rw [← elt_idx t, fCoc, transfer_tbl_gen _ hk (idx_lt t), tbl_gen _ hk (idx_lt t), muCoch,
      mk1_cob_gen _ hk (idx_lt t), ← transferCheck_parts.2.2.2 k hk _ (idx_lt t)]
    cases trBit fRows (k + 1) (idx t) <;> cases cobBit muMask (k + 1) (idx t) <;> decide
  have := eq_zero_of_gen hcc hgen s t
  rw [hc] at this
  simp only at this
  grind

theorem transfer_hCoc_zero (s t : S) : transfer (hCoc 0) (incl s) (incl t) = fCoc s t := by
  rw [transfer_hCoc (by norm_num)]
  have he : eFlag 0 = 1 := by decide
  have hb : ∀ s : S, bCoch 0 s = 0 := fun s => by
    rw [bCoch, mk1, show bMask 0 = 0 by decide]
    simp [maskBit]
  rw [he, one_mul, cob, hb, hb, hb]
  simp

@[expose] def fixCount (σ : Perm315) : ℕ := Fintype.card {p : Fin 315 // σ p = p}

theorem fixCount_conj (g σ : Perm315) : fixCount (g * σ * g⁻¹) = fixCount σ := by
  unfold fixCount
  refine (Fintype.card_congr (Equiv.subtypeEquiv g fun p => ?_)).symm
  simp [Equiv.Perm.mul_apply]

theorem countFold_succ (p : ℕ → Bool) (n : ℕ) :
    countFold (n + 1) p = if p n then countFold n p + 1 else countFold n p := by
  rw [countFold, countFold, Nat.fold_succ]

theorem countFold_eq_range (p : ℕ → Bool) : ∀ n : ℕ,
    countFold n p = ∑ i ∈ Finset.range n, if p i then 1 else 0
  | 0 => by rw [countFold, Nat.fold_zero]; simp
  | n + 1 => by
    rw [Finset.sum_range_succ, ← countFold_eq_range p n, countFold_succ]
    by_cases h : p n = true <;> simp [h]

theorem countFold_eq (p : ℕ → Bool) (n : ℕ) :
    countFold n p = ∑ i : Fin n, if p i then 1 else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if p i then 1 else 0) n]
  exact countFold_eq_range p n

theorem fixCount_eq {t : Array ℕ} {σ : Perm315} (h : Rep 315 t σ) :
    fixCount σ = fixCountArr t := by
  rw [fixCount, Fintype.card_subtype, Finset.card_filter, fixCountArr, countFold_eq]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hb : (t[(p : ℕ)]! == (p : ℕ)) = decide (σ p = p) := by
    rw [h p]
    by_cases hp : σ p = p
    · simp [hp]
    · have hne : (σ p : ℕ) ≠ p := fun h' => hp (Fin.ext h')
      simp [hp, hne]
  simp only [hb, decide_eq_true_eq]

theorem involCheck_parts :
    fixCountArr eltArrs[4]! = 11 ∧ fixCountArr eltArrs[2]! = 15 ∧
    ∀ a < 128, a ≠ 0 → (mulTab[a]!)[a]! = 0 →
      (((conjOf a).1 = 4 ∧ fixCountArr eltArrs[a]! = 11 ∧ bitAt fRows a a = false) ∨
        ((conjOf a).1 = 2 ∧ fixCountArr eltArrs[a]! = 15 ∧ bitAt fRows a a = true)) ∧
      eqA 315 (compA 315 (wordArr (conjOf a).2) eltArrs[a]!)
        (compA 315 eltArrs[(conjOf a).1]! (wordArr (conjOf a).2)) = true := by
  have h := involCheck_eq
  simp only [involCheck, Bool.and_eq_true, allLt_iff, beq_iff_eq, Bool.or_eq_true,
    bne_iff_ne, ne_eq, Bool.not_eq_true', and_assoc, or_assoc] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun a ha ha0 haa => ?_⟩
  rcases h3 a ha with h | h | h
  · exact absurd h ha0
  · exact absurd haa h
  · exact h

theorem fixCount_elt {a : ℕ} (ha : a < 128) :
    fixCount (elt a : Perm315) = fixCountArr eltArrs[a]! :=
  fixCount_eq (rep_eltArrs ha)

theorem fixCount_elt_four : fixCount (elt 4 : Perm315) = 11 := by
  rw [fixCount_elt (by norm_num), involCheck_parts.1]

theorem fixCount_elt_two : fixCount (elt 2 : Perm315) = 15 := by
  rw [fixCount_elt (by norm_num), involCheck_parts.2.1]

theorem mulIdx_self_of_orderOf {a : ℕ} (ha : a < 128) (h : orderOf (elt a) = 2) :
    a ≠ 0 ∧ (mulTab[a]!)[a]! = 0 := by
  refine ⟨fun h0 => ?_, ?_⟩
  · subst h0
    rw [elt_zero, orderOf_one] at h
    exact absurd h (by norm_num)
  · rw [mulTab_get ha ha]
    have h1 : elt (mulIdx a a) = elt 0 := by
      have := pow_orderOf_eq_one (elt a)
      rw [h, pow_two] at this
      rw [(mulIdx_spec ha).2, elt_zero, this]
    exact elt_injective (mulIdx_spec ha).1 (by norm_num) h1

theorem fCoc_diag (s : S) (hs : orderOf s = 2) :
    (fixCount (s : Perm315) = 11 ∧ fCoc s s = 0) ∨
      (fixCount (s : Perm315) = 15 ∧ fCoc s s = 1) := by
  rw [← elt_idx s] at hs ⊢
  obtain ⟨h0, haa⟩ := mulIdx_self_of_orderOf (idx_lt s) hs
  obtain ⟨hc, -⟩ := involCheck_parts.2.2 _ (idx_lt s) h0 haa
  rw [fixCount_elt (idx_lt s), fCoc, tbl_elt _ (idx_lt s) (idx_lt s)]
  rcases hc with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
  · left
    rw [h1, h2]
    exact ⟨rfl, rfl⟩
  · right
    rw [h1, h2]
    exact ⟨rfl, rfl⟩

theorem orderOf_elt_two : orderOf (elt 2) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · have h22 : (mulTab[2]!)[2]! = 0 := by
      rw [mulTab_get (by norm_num) (by norm_num)]
      decide +kernel
    rw [pow_two, ← (mulIdx_spec (a := 2) (by norm_num)).2, ← mulTab_get (by norm_num)
      (by norm_num), h22, elt_zero]
  · intro h
    exact absurd (elt_injective (by norm_num) (by norm_num) (h.trans elt_zero.symm))
      (by norm_num)

theorem fCoc_not_cob : ¬ ∃ b : S → ZMod 2, ∀ s t, fCoc s t = cob b s t := by
  rintro ⟨b, hb⟩
  have hw := orderOf_elt_two
  have hd := fCoc_diag (elt 2) hw
  rw [fixCount_elt_two] at hd
  have hf : fCoc (elt 2) (elt 2) = 1 := by
    rcases hd with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h (by norm_num)
    · exact h
  have h1 := hb 1 1
  have h2 := hb (elt 2) (elt 2)
  rw [isNormCocycle_fCoc.1, cob, mul_one] at h1
  have hsq : elt 2 * elt 2 = 1 := by
    have := pow_orderOf_eq_one (elt 2)
    rw [hw, pow_two] at this
    exact this
  rw [hf, cob, hsq] at h2
  grind

theorem exists_conj_mem_S (x : P) (hx : orderOf x = 2) :
    ∃ g : P, ((g * x * g⁻¹ : P) : Perm315) ∈ S := by
  have hp : IsPGroup 2 (Subgroup.zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P Q sylowS
  refine ⟨g, ?_⟩
  have hmem : g * x * g⁻¹ ∈ ((g • Q : Sylow 2 P) : Subgroup P) := by
    rw [Sylow.coe_subgroup_smul]
    exact ⟨x, hQ (Subgroup.mem_zpowers x), rfl⟩
  rw [hg, coe_sylowS, Subgroup.mem_subgroupOf] at hmem
  exact hmem

theorem conj_to_rep {a : ℕ} (ha : a < 128) (h : orderOf (elt a) = 2) :
    ∃ g : P, (g : Perm315) * (elt a : Perm315) * (g : Perm315)⁻¹ =
      (elt (conjOf a).1 : Perm315) ∧ ((conjOf a).1 = 4 ∨ (conjOf a).1 = 2) := by
  obtain ⟨h0, haa⟩ := mulIdx_self_of_orderOf ha h
  obtain ⟨hc, he⟩ := involCheck_parts.2.2 a ha h0 haa
  have ht : (conjOf a).1 < 128 := by rcases hc with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> norm_num
  have hg := eq_of_eqA (rep_compA (rep_wordArr _) (rep_eltArrs ha))
    (rep_compA (rep_eltArrs ht) (rep_wordArr _)) he
  refine ⟨⟨wordPerm (conjOf a).2, wordPerm_mem _⟩, ?_, ?_⟩
  · simp only
    rw [hg, mul_inv_cancel_right]
  · rcases hc with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h

theorem involution_conj_rep (x : P) (hx : orderOf x = 2) :
    ∃ g : P, (fixCount (x : Perm315) = 11 ∧ (g * x * g⁻¹ : P) = incl (elt 4)) ∨
      (fixCount (x : Perm315) = 15 ∧ (g * x * g⁻¹ : P) = incl (elt 2)) := by
  obtain ⟨g, hg⟩ := exists_conj_mem_S x hx
  set s : S := ⟨_, hg⟩ with hs
  have hso : orderOf s = 2 := by
    have h1 : orderOf (g * x * g⁻¹) = 2 := by
      have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      rw [this, hx]
    rw [← h1, ← orderOf_injective incl (Subgroup.inclusion_injective S_le_P) s]
    congr 1
  obtain ⟨g', hg', ht⟩ := conj_to_rep (idx_lt s) (by rw [elt_idx]; exact hso)
  rw [elt_idx] at hg'
  have hfix : fixCount (x : Perm315) = fixCount (elt (conjOf (idx s)).1 : Perm315) := by
    rw [← hg', fixCount_conj, hs]
    simp only
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, fixCount_conj]
  refine ⟨g' * g, ?_⟩
  have hconj : ((g' * g * x * (g' * g)⁻¹ : P) : Perm315) =
      (elt (conjOf (idx s)).1 : Perm315) := by
    rw [← hg', hs]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
    group
  rcases ht with h4 | h2
  · left
    refine ⟨by rw [hfix, h4, fixCount_elt_four], Subtype.ext ?_⟩
    rw [hconj, h4, incl_coe]
  · right
    refine ⟨by rw [hfix, h2, fixCount_elt_two], Subtype.ext ?_⟩
    rw [hconj, h2, incl_coe]

theorem involution_fixCount (x : P) (hx : orderOf x = 2) :
    fixCount (x : Perm315) = 11 ∨ fixCount (x : Perm315) = 15 := by
  obtain ⟨g, h | h⟩ := involution_conj_rep x hx
  · exact Or.inl h.1
  · exact Or.inr h.1

theorem involution_conj {x y : P} (hx : orderOf x = 2) (hy : orderOf y = 2)
    (h : fixCount (x : Perm315) = fixCount (y : Perm315)) : ∃ g : P, g * x * g⁻¹ = y := by
  obtain ⟨g, hg⟩ := involution_conj_rep x hx
  obtain ⟨g', hg'⟩ := involution_conj_rep y hy
  have key : ∀ (z : P), g * x * g⁻¹ = z → g' * y * g'⁻¹ = z → ∃ k : P, k * x * k⁻¹ = y := by
    intro z h1 h2
    refine ⟨g'⁻¹ * g, ?_⟩
    have : y = g'⁻¹ * z * g' := by rw [← h2]; group
    rw [this, ← h1]
    group
  rcases hg with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩ <;> rcases hg' with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
  · exact key _ hx2 hy2
  · omega
  · omega
  · exact key _ hx2 hy2

end CFSG.ComponentClassification.J2Cover.Models
