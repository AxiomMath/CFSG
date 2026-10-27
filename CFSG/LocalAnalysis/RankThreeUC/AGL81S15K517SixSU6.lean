module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517SixSU

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K517Six

open scoped commutatorElement

section Swap

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.CurtisTits
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

theorem su6_heis_row_rev_of_col {x : SU σ n} {a u : Fin n} {c c' : F} (hcc : σ c * c' = 1)
    (hcol : ∀ t, mat σ n x t a = if t = u then c else 0) (b : Fin n) :
    mat σ n x (Fin.rev u) b = if b = Fin.rev a then c' else 0 := by
  have h := sum_mat_mul_mat x a b
  rw [Finset.sum_eq_single u] at h
  · rw [hcol u, if_pos rfl] at h
    split_ifs at h ⊢ with hb
    · linear_combination c' * h - mat σ n x (Fin.rev u) b * hcc
    · linear_combination c' * h - mat σ n x (Fin.rev u) b * hcc
  · intro t _ ht
    rw [hcol t, if_neg ht, map_zero, zero_mul]
  · simp

variable [CharP F 2]

@[expose] def su6_heis_swapSL : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; 1, 0], by rw [Matrix.det_fin_two_of]; simp [CharTwo.neg_eq]⟩

@[expose] def su6_heis_swapFun (p q : Fin n) (u : Fin n) : Fin n :=
  if u = p then q else if u = q then p else if u = Fin.rev q then Fin.rev p
    else if u = Fin.rev p then Fin.rev q else u

variable (hσ : ∀ c, σ (σ c) = c) {k : Fin (n / 2)} (hk : k.val + 1 < n / 2)

@[expose] noncomputable def su6_heis_shortSwap : SU σ n :=
  (((rankOneShortEquiv (hσ := hσ) hk).symm su6_heis_swapSL :
    ↥(rankOne (rootGroup σ hσ n) k)) : SU σ n)

theorem su6_heis_shortSwap_mem : su6_heis_shortSwap hσ hk ∈ rankOne (rootGroup σ hσ n) k :=
  ((rankOneShortEquiv (hσ := hσ) hk).symm su6_heis_swapSL).2

theorem su6_heis_toBlock_shortSwap :
    SUExtras.toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat σ n (su6_heis_shortSwap hσ hk)) =
      !![0, 1; 1, 0] := by
  have h := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F))
    ((rankOneShortEquiv (hσ := hσ) hk).apply_symm_apply su6_heis_swapSL)
  exact h

theorem su6_heis_mat_shortSwap :
    mat σ n (su6_heis_shortSwap hσ hk) =
      Matrix.of fun u b =>
        if b = su6_heis_swapFun (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) u then 1 else 0 := by
  obtain ⟨hpq, hp, hq, hqp⟩ := short_facts (n := n) hk
  have hpq' : lowIdx (n := n) k ≠ Fin.rev (lowIdx ⟨k.val + 1, hk⟩) := lowIdx_ne_rev _ _
  have hmem := su6_heis_shortSwap_mem hσ hk
  obtain ⟨hblk, -⟩ := isBlk_short_of_mem hk hmem
  have hb := su6_heis_toBlock_shortSwap hσ hk
  set x := su6_heis_shortSwap hσ hk with hx
  set p : Fin n := lowIdx k with hpdef
  set q : Fin n := lowIdx ⟨k.val + 1, hk⟩ with hqdef
  have hpp : mat σ n x p p = 0 := by simpa [SUExtras.toBlock] using congrFun (congrFun hb 0) 0
  have hpq0 : mat σ n x p q = 1 := by simpa [SUExtras.toBlock] using congrFun (congrFun hb 0) 1
  have hqp0 : mat σ n x q p = 1 := by simpa [SUExtras.toBlock] using congrFun (congrFun hb 1) 0
  have hqq : mat σ n x q q = 0 := by simpa [SUExtras.toBlock] using congrFun (congrFun hb 1) 1
  have hout : ∀ u c, (c = p ∨ c = q) → u ≠ p → u ≠ q →
      mat σ n x u c = 0 ∧ mat σ n x c u = 0 := by
    intro u c hc hup huq
    have h1 : blkShort k hk c = 1 := (blkShort_eq_one_iff hk c).2 hc
    have h2 : blkShort k hk u ≠ 1 := fun h => by
      rcases (blkShort_eq_one_iff hk u).1 h with h | h
      exacts [hup h, huq h]
    have huc : u ≠ c := by
      rintro rfl
      rcases hc with h | h
      exacts [hup h, huq h]
    constructor
    · rw [hblk u c (fun h => h2 (h.1.trans h1)), Matrix.one_apply_ne huc]
    · rw [hblk c u (fun h => h2 (h.1.symm.trans h1)), Matrix.one_apply_ne huc.symm]
  have hcolp : ∀ u, mat σ n x u p = if u = q then 1 else 0 := by
    intro u
    by_cases huq : u = q
    · rw [huq, hqp0, if_pos rfl]
    · by_cases hup : u = p
      · rw [hup, hpp, if_neg hpq]
      · rw [(hout u p (Or.inl rfl) hup huq).1, if_neg huq]
  have hcolq : ∀ u, mat σ n x u q = if u = p then 1 else 0 := by
    intro u
    by_cases hup : u = p
    · rw [hup, hpq0, if_pos rfl]
    · by_cases huq : u = q
      · rw [huq, hqq, if_neg hpq.symm]
      · rw [(hout u q (Or.inr rfl) hup huq).1, if_neg hup]
  have hrowp : ∀ b, mat σ n x p b = if b = q then 1 else 0 := by
    intro b
    by_cases hbq : b = q
    · rw [hbq, hpq0, if_pos rfl]
    · by_cases hbp : b = p
      · rw [hbp, hpp, if_neg hpq]
      · rw [(hout b p (Or.inl rfl) hbp hbq).2, if_neg hbq]
  have hrowq : ∀ b, mat σ n x q b = if b = p then 1 else 0 := by
    intro b
    by_cases hbp : b = p
    · rw [hbp, hqp0, if_pos rfl]
    · by_cases hbq : b = q
      · rw [hbq, hqq, if_neg hpq.symm]
      · rw [(hout b q (Or.inr rfl) hbp hbq).2, if_neg hbp]
  have hrowp' : ∀ b, mat σ n x (Fin.rev p) b = if b = Fin.rev q then 1 else 0 :=
    su6_heis_row_rev_of_col (a := q) (u := p) (c := 1) (c' := 1) (by rw [map_one, one_mul]) hcolq
  have hrowq' : ∀ b, mat σ n x (Fin.rev q) b = if b = Fin.rev p then 1 else 0 :=
    su6_heis_row_rev_of_col (a := p) (u := q) (c := 1) (c' := 1) (by rw [map_one, one_mul]) hcolp
  have hrow0 : ∀ u b, u ≠ p → u ≠ q → u ≠ Fin.rev p → u ≠ Fin.rev q →
      mat σ n x u b = (1 : Matrix (Fin n) (Fin n) F) u b := by
    intro u b h1 h2 h3 h4
    refine hblk u b fun h => h.2 ?_
    unfold blkShort
    rw [if_neg (by tauto), if_neg (by tauto)]
  have key : ∀ (c : F) (a b : Fin n), (if b = a then c else 0) = if a = b then c else 0 := by
    intro c a b
    by_cases h : b = a
    · simp [h]
    · simp [h, Ne.symm h]
  ext u b
  rw [Matrix.of_apply]
  by_cases hup : u = p
  · rw [hup, hrowp b]
    simp [su6_heis_swapFun]
  by_cases huq : u = q
  · rw [huq, hrowq b]
    simp [su6_heis_swapFun, hpq.symm]
  by_cases hup' : u = Fin.rev p
  · rw [hup', hrowp' b]
    have h : Fin.rev p ≠ Fin.rev q := fun h => hpq (Fin.rev_injective h)
    simp [su6_heis_swapFun, hp.symm, hqp.symm, h]
  by_cases huq' : u = Fin.rev q
  · rw [huq', hrowq' b]
    simp [su6_heis_swapFun, hpq'.symm, hq.symm]
  · rw [hrow0 u b hup huq hup' huq', Matrix.one_apply]
    have hu : su6_heis_swapFun p q u = u := by simp [su6_heis_swapFun, hup, huq, huq', hup']
    rw [hu]
    exact key 1 b u

end Swap

section Six

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.CurtisTits
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

variable {F : Type*} [Field F] [CharP F 2] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)

theorem su6_heis_hk0 : (⟨0, by norm_num⟩ : Fin (6 / 2)).val + 1 < 6 / 2 := by norm_num

theorem su6_heis_hk1 : (⟨1, by norm_num⟩ : Fin (6 / 2)).val + 1 < 6 / 2 := by norm_num

theorem su6_heis_mat_x0 : mat σ 6 (su6_heis_shortSwap hσ su6_heis_hk0) =
    !![0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1;
      0, 0, 0, 0, 1, 0] := by
  rw [su6_heis_mat_shortSwap]
  ext u b
  fin_cases u <;> fin_cases b <;> simp [su6_heis_swapFun, lowIdx]

theorem su6_heis_mat_x1 : mat σ 6 (su6_heis_shortSwap hσ su6_heis_hk1) =
    !![1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 1] := by
  rw [su6_heis_mat_shortSwap]
  ext u b
  fin_cases u <;> fin_cases b <;> simp [su6_heis_swapFun, lowIdx]

@[expose] def su6_heis_cyc (F : Type*) [Field F] : Matrix (Fin 6) (Fin 6) F :=
  !![0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1;
    0, 0, 0, 1, 0, 0]

theorem su6_heis_mat_b :
    mat σ 6 (su6_heis_shortSwap hσ su6_heis_hk0 * su6_heis_shortSwap hσ su6_heis_hk1) =
      su6_heis_cyc F := by
  rw [map_mul, su6_heis_mat_x0, su6_heis_mat_x1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su6_heis_cyc, Matrix.mul_apply, Fin.sum_univ_succ]

omit [CharP F 2] in
theorem su6_heis_cyc_mul_self : su6_heis_cyc F * su6_heis_cyc F =
    !![0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su6_heis_cyc, Matrix.mul_apply, Fin.sum_univ_succ]

omit [CharP F 2] in
theorem su6_heis_cyc_pow_three : su6_heis_cyc F ^ 3 = 1 := by
  rw [pow_succ, sq, su6_heis_cyc_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su6_heis_cyc, Matrix.mul_apply, Fin.sum_univ_succ]

theorem su6_heis_b_pow_three :
    (su6_heis_shortSwap hσ su6_heis_hk0 * su6_heis_shortSwap hσ su6_heis_hk1) ^ 3 = 1 := by
  apply mat_injective
  rw [map_pow, su6_heis_mat_b, map_one]
  exact su6_heis_cyc_pow_three

omit [CharP F 2] in
theorem su6_heis_mat_a {ω : F} (hω3 : ω ^ 3 = 1) (hσω : σ ω = ω ^ 2) (hts : ω * ω ^ 2 = 1) :
    mat σ 6 (su_shortDiag hσ su6_heis_hk1 hts) = Matrix.diagonal ![1, ω, ω ^ 2, ω ^ 2, ω, 1] := by
  rw [su_mat_shortDiag]
  congr 1
  funext u
  fin_cases u <;> simp [su_dshort, lowIdx, map_pow, hσω]
  linear_combination ω * hω3

omit [CharP F 2] in
theorem su6_heis_diag_mul_cyc {ω : F} (hω3 : ω ^ 3 = 1) :
    Matrix.diagonal ![1, ω, ω ^ 2, ω ^ 2, ω, 1] * su6_heis_cyc F =
      Matrix.diagonal (fun _ : Fin 6 => ω) *
        (su6_heis_cyc F * Matrix.diagonal ![1, ω, ω ^ 2, ω ^ 2, ω, 1]) := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.diagonal_mul, Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [su6_heis_cyc]
  all_goals first | ring1 | linear_combination (-1 : F) * hω3

theorem su6_heis_core {ω : F} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hσω : σ ω = ω ^ 2) :
    ∃ a b : SU σ 6,
      a ∈ rankOne (rootGroup σ hσ 6) (⟨0, by norm_num⟩ : Fin (6 / 2)) ⊔
        rankOne (rootGroup σ hσ 6) (⟨1, by norm_num⟩ : Fin (6 / 2)) ∧
      b ∈ rankOne (rootGroup σ hσ 6) (⟨0, by norm_num⟩ : Fin (6 / 2)) ⊔
        rankOne (rootGroup σ hσ 6) (⟨1, by norm_num⟩ : Fin (6 / 2)) ∧
      a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ ⁅a, b⁆ ∈ Subgroup.center (SU σ 6) ∧
      a ∉ Subgroup.center (SU σ 6) ∧
      ∀ (i : ℕ) (z : SU σ 6), z ∈ Subgroup.center (SU σ 6) → b ≠ a ^ i * z := by
  have hω0 : ω ≠ 0 := fun h => by rw [h] at hω3; norm_num at hω3
  have hω6 : (ω ^ 2) ^ 3 = 1 := by linear_combination (ω ^ 3 + 1) * hω3
  have hdet : ω ^ 6 = 1 := by linear_combination (ω ^ 3 + 1) * hω3
  have hts : ω * ω ^ 2 = 1 := by linear_combination hω3
  have hiso : σ ω * ω = 1 := by rw [hσω]; linear_combination hω3
  have hamat := su6_heis_mat_a hσ hω3 hσω hts
  have hamem := su_shortDiag_mem hσ su6_heis_hk1 hts
  have ha3 : su_shortDiag hσ su6_heis_hk1 hts ^ 3 = 1 := by
    apply mat_injective
    rw [map_pow, su_mat_shortDiag, Matrix.diagonal_pow, map_one]
    ext i j
    simp only [Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs
    · exact su_dshort_pow_three hω3 hω6 i
    · rfl
  generalize su_shortDiag hσ su6_heis_hk1 hts = a at hamat hamem ha3
  have hbmat := su6_heis_mat_b hσ (F := F)
  have hb3 := su6_heis_b_pow_three hσ (F := F)
  have hbmem := Subgroup.mul_mem_sup (su6_heis_shortSwap_mem hσ su6_heis_hk0 (F := F))
    (su6_heis_shortSwap_mem hσ su6_heis_hk1 (F := F))
  generalize su6_heis_shortSwap hσ su6_heis_hk0 * su6_heis_shortSwap hσ su6_heis_hk1 = b
    at hbmat hb3 hbmem
  have hsmat := su_mat_scalarSU σ hω0 hdet hiso
  have hscomm := su_commute_scalarSU σ hω0 hdet hiso
  generalize su_scalarSU σ hω0 hdet hiso = s at hsmat hscomm
  have hab : a * b = s * (b * a) := by
    apply mat_injective
    rw [map_mul (mat σ 6) a b, map_mul (mat σ 6) s (b * a), map_mul (mat σ 6) b a, hamat, hbmat,
      hsmat]
    exact su6_heis_diag_mul_cyc hω3
  have hcomm : ⁅a, b⁆ = s := by
    rw [commutatorElement_def, hab]
    group
  have hsc : s ∈ Subgroup.center (SU σ 6) := Subgroup.mem_center_iff.2 fun g => hscomm g
  have hs1 : s ≠ 1 := by
    intro h
    have h0 : mat σ 6 s = 1 := by rw [h, map_one]
    rw [hsmat] at h0
    have h1 := congrFun (congrFun h0 0) 0
    simp at h1
    exact hω1 h1
  refine ⟨a, b, Subgroup.mem_sup_right hamem, hbmem, ha3, hb3, by rw [hcomm]; exact hsc, ?_, ?_⟩
  · refine su_not_mem_center_of_row_col hσ (i := (0 : Fin 6)) (j := (1 : Fin 6)) (by decide)
      (by decide) (by decide) (by decide) (c := 1) (c' := ω) ?_ ?_ hω1.symm
    · intro t
      rw [hamat, Matrix.diagonal_apply]
      by_cases ht : t = 0
      · subst ht
        simp
      · rw [if_neg (Ne.symm ht), if_neg ht]
    · intro t
      rw [hamat, Matrix.diagonal_apply]
      by_cases ht : t = 1
      · subst ht
        simp
      · rw [if_neg ht, if_neg ht]
  · intro i z hz hbz
    have hcz : ∀ g : SU σ 6, g * z = z * g := Subgroup.mem_center_iff.1 hz
    have hcomm_ab : a * b = b * a := by
      rw [hbz]
      exact ((Commute.self_pow a i).mul_right (hcz a : Commute a z)).eq
    apply hs1
    have h : s * (b * a) = 1 * (b * a) := by rw [← hab, one_mul]; exact hcomm_ab
    exact mul_right_cancel h

end Six

open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.CurtisTits
  CFSG.LieType.BorelTits

theorem su_six_heis {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (h3 : 3 ∣ 2 ^ f + 1) :
    ∃ a b : SU (unitaryInvolution F 2 f) 6,
      a ∈ rankOne (rootDatum hF 6).rootGroup ⟨0, by show 0 < 6 / 2; norm_num⟩ ⊔
        rankOne (rootDatum hF 6).rootGroup ⟨1, by show 1 < 6 / 2; norm_num⟩ ∧
      b ∈ rankOne (rootDatum hF 6).rootGroup ⟨0, by show 0 < 6 / 2; norm_num⟩ ⊔
        rankOne (rootDatum hF 6).rootGroup ⟨1, by show 1 < 6 / 2; norm_num⟩ ∧
      a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ ⁅a, b⁆ ∈ Subgroup.center (SU (unitaryInvolution F 2 f) 6) ∧
      a ∉ Subgroup.center (SU (unitaryInvolution F 2 f) 6) ∧
      ∀ (i : ℕ) (z : SU (unitaryInvolution F 2 f) 6),
        z ∈ Subgroup.center (SU (unitaryInvolution F 2 f) 6) → b ≠ a ^ i * z := by
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨ω, hω3, hω1, hσω⟩ := su_exists_omega hF h3
  exact su6_heis_core hσ hω3 hω1 hσω

end CFSG.LocalAnalysis.RankThreeUC.S15.K517Six
