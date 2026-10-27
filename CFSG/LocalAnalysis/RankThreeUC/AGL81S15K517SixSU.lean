module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenSU

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K517Six

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.CurtisTits
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

section Omega

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

theorem su_exists_order_norm_one (hF : Nat.card F = (2 ^ f) ^ 2) {r : ℕ} (hr : r.Prime)
    (hrd : r ∣ 2 ^ f + 1) :
    ∃ s : F, s ^ r = 1 ∧ s ≠ 1 ∧ unitaryInvolution F 2 f s = s⁻¹ := by
  obtain ⟨l, hl, hord⟩ := exists_norm_one_orderOf_eq (F := F) (p := 2) (f := f) hF
  obtain ⟨j, hj⟩ := hrd
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h, mul_zero] at hj
      have : 0 < 2 ^ f + 1 := by positivity
      omega
    · exact h
  have hlr : (l ^ j) ^ r = 1 := by
    rw [← pow_mul, mul_comm, ← hj, ← hord, pow_orderOf_eq_one]
  have hl1 : l ^ j ≠ 1 := by
    intro h
    have hd : 2 ^ f + 1 ∣ j := by
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one h
    have hpos : 0 < 2 ^ f + 1 := by positivity
    have hdj : j ∣ 2 ^ f + 1 := ⟨r, by rw [hj, mul_comm]⟩
    have heq : j = 2 ^ f + 1 := Nat.dvd_antisymm hdj hd
    rw [heq] at hj
    have hcancel : r = 1 := by
      apply Nat.mul_right_cancel hpos
      rw [one_mul]
      exact hj.symm
    exact hr.one_lt.ne' hcancel
  refine ⟨((l ^ j : Fˣ) : F), ?_, ?_, ?_⟩
  · rw [← Units.val_pow_eq_pow_val, hlr, Units.val_one]
  · intro h
    exact hl1 (Units.ext (by simpa using h))
  · have hnorm : unitaryInvolution F 2 f ((l ^ j : Fˣ) : F) * ((l ^ j : Fˣ) : F) = 1 := by
      rw [Units.val_pow_eq_pow_val, map_pow, ← mul_pow, hl, one_pow]
    exact eq_inv_of_mul_eq_one_left hnorm

theorem su_exists_omega (hF : Nat.card F = (2 ^ f) ^ 2) (h3 : 3 ∣ 2 ^ f + 1) :
    ∃ ω : F, ω ^ 3 = 1 ∧ ω ≠ 1 ∧ unitaryInvolution F 2 f ω = ω ^ 2 := by
  obtain ⟨ω, hω3, hω1, hω⟩ := su_exists_order_norm_one hF Nat.prime_three h3
  refine ⟨ω, hω3, hω1, ?_⟩
  rw [hω]
  have h : ω * ω ^ 2 = 1 := by linear_combination hω3
  exact inv_eq_of_mul_eq_one_right h

end Omega

section Generic

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

theorem su_not_mem_center_of_row_col (hσ : ∀ c, σ (σ c) = c) {g : SU σ n} {i j : Fin n}
    (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j) (hji : j ≠ Fin.rev i) {c c' : F}
    (hrow : ∀ t, mat σ n g i t = if t = i then c else 0)
    (hcol : ∀ t, mat σ n g t j = if t = j then c' else 0) (hcc : c ≠ c') :
    g ∉ Subgroup.center (SU σ n) := by
  intro hg
  set x : SU σ n := rootHom σ hσ hij hi hj (Multiplicative.ofAdd (1 : F)) with hx
  have hxij : mat σ n x i j = 1 := by
    rw [mat_apply, hx, coe_rootHom, toAdd_ofAdd]
    exact rootMatrix_apply_pq hij hji 1
  have hcomm : g * x = x * g := Subgroup.mem_center_iff.1 hg x |>.symm
  have h := congrArg (fun y : SU σ n => mat σ n y i j) hcomm
  simp only [map_mul, Matrix.mul_apply] at h
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j] at h
  · rw [hrow i, if_pos rfl, hcol j, if_pos rfl, hxij] at h
    exact hcc (by simpa using h)
  · intro t _ ht
    rw [hcol t, if_neg ht, mul_zero]
  · simp
  · intro t _ ht
    rw [hrow t, if_neg ht, zero_mul]
  · simp

theorem su_row_rev_of_col {x : SU σ n} {a : Fin n} {c c' : F} (hcc : σ c * c' = 1)
    (hcol : ∀ u, mat σ n x u a = if u = a then c else 0) (b : Fin n) :
    mat σ n x (Fin.rev a) b = if b = Fin.rev a then c' else 0 := by
  have h := sum_mat_mul_mat x a b
  rw [Finset.sum_eq_single a] at h
  · rw [hcol a, if_pos rfl] at h
    split_ifs at h ⊢ with hb
    · linear_combination c' * h - mat σ n x (Fin.rev a) b * hcc
    · linear_combination c' * h - mat σ n x (Fin.rev a) b * hcc
  · intro u _ hu
    rw [hcol u, if_neg hu, map_zero, zero_mul]
  · simp

theorem su_eq_diagonal_of_isBlkOn {r : ℕ} {e : Fin r → Fin n} (he : Function.Injective e)
    {M : Matrix (Fin n) (Fin n) F} (hM : IsBlkOn e M) {c : Fin r → F}
    (hc : M.submatrix e e = Matrix.diagonal c) :
    M = Matrix.diagonal (Function.extend e c 1) := by
  ext u v
  by_cases hu : u ∈ Set.range e
  · by_cases hv : v ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hu
      obtain ⟨j, rfl⟩ := hv
      have h := congrFun (congrFun hc i) j
      rw [Matrix.submatrix_apply, Matrix.diagonal_apply] at h
      rw [h, Matrix.diagonal_apply, he.extend_apply]
      simp only [he.eq_iff]
    · have huv : u ≠ v := fun h => hv (h ▸ hu)
      rw [hM u v (Or.inr hv), Matrix.diagonal_apply, if_neg huv, Matrix.one_apply_ne huv]
  · rw [hM u v (Or.inl hu), Matrix.diagonal_apply, Matrix.one_apply]
    by_cases huv : u = v
    · subst huv
      rw [if_pos rfl, if_pos rfl, Function.extend_apply' _ _ _ (fun ⟨a, ha⟩ => hu ⟨a, ha⟩)]
      rfl
    · rw [if_neg huv, if_neg huv]

@[expose] noncomputable def su_scalarGL {r : ℕ} {c : F} (hc : c ≠ 0) : GL (Fin r) F :=
  ⟨Matrix.diagonal fun _ => c, Matrix.diagonal fun _ => c⁻¹,
    by rw [Matrix.diagonal_mul_diagonal]; simp [hc],
    by rw [Matrix.diagonal_mul_diagonal]; simp [hc]⟩

@[expose] noncomputable def su_scalarSU (σ : F ≃+* F) {r : ℕ} {c : F} (hc : c ≠ 0)
    (hdet : c ^ r = 1) (hiso : σ c * c = 1) : SU σ r :=
  ⟨su_scalarGL hc, mem_SU.2 ⟨by simp [su_scalarGL, Matrix.det_diagonal, hdet], by
    ext i j
    simp [su_scalarGL, conjTr, Matrix.diagonal_map, Matrix.mul_assoc, Matrix.diagonal_mul,
      Matrix.mul_diagonal]
    linear_combination (antidiag r : Matrix (Fin r) (Fin r) F) i j * hiso⟩⟩

theorem su_mat_scalarSU (σ : F ≃+* F) {r : ℕ} {c : F} (hc : c ≠ 0) (hdet : c ^ r = 1)
    (hiso : σ c * c = 1) :
    mat σ r (su_scalarSU σ hc hdet hiso) = Matrix.diagonal fun _ => c :=
  rfl

theorem su_scalarSU_pow_three (σ : F ≃+* F) {r : ℕ} {c : F} (hc : c ≠ 0) (hdet : c ^ r = 1)
    (hiso : σ c * c = 1) (h3 : c ^ 3 = 1) : su_scalarSU σ hc hdet hiso ^ 3 = 1 := by
  apply mat_injective
  rw [map_pow, su_mat_scalarSU, Matrix.diagonal_pow, map_one]
  ext i j
  simp [Matrix.diagonal_apply, Matrix.one_apply, h3]

theorem su_commute_scalarSU (σ : F ≃+* F) {r : ℕ} {c : F} (hc : c ≠ 0) (hdet : c ^ r = 1)
    (hiso : σ c * c = 1) (g : SU σ r) :
    g * su_scalarSU σ hc hdet hiso = su_scalarSU σ hc hdet hiso * g := by
  apply mat_injective
  rw [map_mul, map_mul, su_mat_scalarSU]
  ext i j
  simp [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem su_transport_q {K G : Type*} [Group K] [Group G] {R : Subgroup K} (e : ↥R ≃* G) {A B M : G}
    {r : ℕ} (hA : A ^ r = 1) (hB : B ^ r = 1) (hMA : M * A * M⁻¹ = A⁻¹)
    (hAB : A * B = B * A) (hMB : M * B = B * M) :
    ((e.symm A : ↥R) : K) ^ r = 1 ∧ ((e.symm B : ↥R) : K) ^ r = 1 ∧
      ((e.symm M : ↥R) : K) * ((e.symm A : ↥R) : K) * ((e.symm M : ↥R) : K)⁻¹ =
        ((e.symm A : ↥R) : K)⁻¹ ∧
      ((e.symm A : ↥R) : K) * ((e.symm B : ↥R) : K) =
        ((e.symm B : ↥R) : K) * ((e.symm A : ↥R) : K) ∧
      ((e.symm M : ↥R) : K) * ((e.symm B : ↥R) : K) =
        ((e.symm B : ↥R) : K) * ((e.symm M : ↥R) : K) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h : (e.symm A) ^ r = 1 := by rw [← map_pow, hA, map_one]
    simpa using congrArg (fun x : ↥R => (x : K)) h
  · have h : (e.symm B) ^ r = 1 := by rw [← map_pow, hB, map_one]
    simpa using congrArg (fun x : ↥R => (x : K)) h
  · have h : e.symm M * e.symm A * (e.symm M)⁻¹ = (e.symm A)⁻¹ := by
      simpa [map_mul, map_inv] using congrArg e.symm hMA
    simpa using congrArg (fun x : ↥R => (x : K)) h
  · have h : e.symm A * e.symm B = e.symm B * e.symm A := by
      rw [← map_mul, ← map_mul, hAB]
    simpa using congrArg (fun x : ↥R => (x : K)) h
  · have h : e.symm M * e.symm B = e.symm B * e.symm M := by
      rw [← map_mul, ← map_mul, hMB]
    simpa using congrArg (fun x : ↥R => (x : K)) h

theorem su_transport {K G : Type*} [Group K] [Group G] {R : Subgroup K} (e : ↥R ≃* G) {A B M : G}
    (hA3 : A ^ 3 = 1) (hB3 : B ^ 3 = 1) (hMA : M * A * M⁻¹ = A⁻¹) (hAB : A * B = B * A)
    (hMB : M * B = B * M) :
    ((e.symm A : ↥R) : K) ^ 3 = 1 ∧ ((e.symm B : ↥R) : K) ^ 3 = 1 ∧
      ((e.symm M : ↥R) : K) * ((e.symm A : ↥R) : K) * ((e.symm M : ↥R) : K)⁻¹ =
        ((e.symm A : ↥R) : K)⁻¹ ∧
      ((e.symm A : ↥R) : K) * ((e.symm B : ↥R) : K) =
        ((e.symm B : ↥R) : K) * ((e.symm A : ↥R) : K) ∧
      ((e.symm M : ↥R) : K) * ((e.symm B : ↥R) : K) =
        ((e.symm B : ↥R) : K) * ((e.symm M : ↥R) : K) :=
  su_transport_q e (r := 3) hA3 hB3 hMA hAB hMB

end Generic

section Last

theorem su_last_E9 {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 5 ≤ n) (hodd : Odd n) (h3 : 3 ∣ 2 ^ f + 1)
    (k : Fin (n / 2)) (hk : ¬ k.val + 1 < n / 2) :
    ∃ a b m : SU (unitaryInvolution F 2 f) n,
      a ∈ rankOne (rootDatum hF n).rootGroup k ∧ b ∈ rankOne (rootDatum hF n).rootGroup k ∧
      m ∈ rankOne (rootDatum hF n).rootGroup k ∧ a ^ 3 = 1 ∧ b ^ 3 = 1 ∧
      a ∉ Subgroup.center (SU (unitaryInvolution F 2 f) n) ∧
      b ∉ Subgroup.center (SU (unitaryInvolution F 2 f) n) ∧
      m * a * m⁻¹ = a⁻¹ ∧ a * b = b * a ∧ m * b = b * m := by
  have hne : ¬ Even n := Nat.not_even_iff_odd.2 hodd
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨ω, hω3, hω1, hσω⟩ := su_exists_omega hF h3
  have hω0 : ω ≠ 0 := fun h => by rw [h] at hω3; norm_num at hω3
  have hiso : unitaryInvolution F 2 f ω * ω = 1 := by rw [hσω]; linear_combination hω3
  have hf1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hk' : ∀ c ∈ fixedSubfield F 2 f, unitaryInvolution F 2 f c = c := fun c hc =>
    mem_fixedSubfield.1 hc
  have hpd' : 3 ∣ Nat.card (fixedSubfield F 2 f) ^ 2 - 1 := by
    rw [card_fixedSubfield hF]
    exact h3.trans (CFSG.AGLEmbedding.ParabPrime.sub_one_dvd_and_add_one_dvd _ hf1).2
  obtain ⟨w, m₀, hw, hw1, hm⟩ := exists_order_inverted_sl2 (F := fixedSubfield F 2 f)
    Nat.prime_three (by norm_num) hpd'
  set e := rankOneLastOddEquiv hF hne hk with he
  set A : SU (unitaryInvolution F 2 f) 3 := blk3Hom (fixedSubfield F 2 f) hk' w with hA
  set M : SU (unitaryInvolution F 2 f) 3 := blk3Hom (fixedSubfield F 2 f) hk' m₀ with hM
  set B : SU (unitaryInvolution F 2 f) 3 := su_scalarSU (unitaryInvolution F 2 f) hω0 hω3 hiso
    with hB
  have hA3 : A ^ 3 = 1 := by rw [hA, ← map_pow, hw, map_one]
  have hA1 : A ≠ 1 := fun h =>
    hw1 (blk3Hom_injective (fixedSubfield F 2 f) hk' (by rw [← hA, h, map_one]))
  have hMA : M * A * M⁻¹ = A⁻¹ := by
    simpa [map_mul, map_inv] using congrArg (blk3Hom (fixedSubfield F 2 f) hk') hm
  have hB3 : B ^ 3 = 1 := su_scalarSU_pow_three _ hω0 hω3 hiso hω3
  have hAB : A * B = B * A := su_commute_scalarSU _ hω0 hω3 hiso A
  have hMB : M * B = B * M := su_commute_scalarSU _ hω0 hω3 hiso M
  obtain ⟨ha3, hb3, hma, hab, hmb⟩ := su_transport (K := SU (unitaryInvolution F 2 f) n) e hA3 hB3
    hMA hAB hMB
  have ha1 : (e.symm A : SU (unitaryInvolution F 2 f) n) ≠ 1 := fun h =>
    hA1 (e.symm.injective ((Subtype.ext h).trans (map_one e.symm).symm))
  refine ⟨(e.symm A : SU (unitaryInvolution F 2 f) n), (e.symm B : SU (unitaryInvolution F 2 f) n),
    (e.symm M : SU (unitaryInvolution F 2 f) n), (e.symm A).2, (e.symm B).2, (e.symm M).2, ha3, hb3,
    not_mem_center_of_inverted (p := 3) (by decide) ha3 ha1 hma, ?_, hma, hab, hmb⟩
  have hbmat : mat (unitaryInvolution F 2 f) n (e.symm B : SU (unitaryInvolution F 2 f) n) =
      Matrix.diagonal (Function.extend (lastIdxOdd k hne) (fun _ => ω) 1) := by
    refine su_eq_diagonal_of_isBlkOn (lastIdxOdd_injective hk hne)
      (isBlkOn_lastIdxOdd hne hk (e.symm B).2) ?_
    have h := toBlock3_mat_rankOneLastOddEquiv_symm (hF := hF) (hn := hne) (hk := hk) B
    rw [toBlock3_eq_submatrix] at h
    exact h.trans (su_mat_scalarSU _ hω0 hω3 hiso)
  have hk1 : 1 ≤ k.val := by
    have := k.isLt
    omega
  obtain ⟨r, hr⟩ := hodd
  have hj0 : 0 < n / 2 := by omega
  have hdp : Function.extend (lastIdxOdd k hne) (fun _ => ω) 1 (lowIdx k) = ω :=
    (lastIdxOdd_injective hk hne).extend_apply (fun _ => ω) 1 0
  have hdj : Function.extend (lastIdxOdd k hne) (fun _ => ω) 1 (lowIdx (⟨0, hj0⟩ : Fin (n / 2))) =
      1 := by
    rw [Function.extend_apply']
    · rfl
    · rintro ⟨a, ha⟩
      have h := congrArg Fin.val ha
      fin_cases a <;> simp [lastIdxOdd, lowIdx, midIdx] at h <;> omega
  refine su_not_mem_center_of_row_col hσ (i := lowIdx k) (j := lowIdx (⟨0, hj0⟩ : Fin (n / 2)))
    (Fin.ne_of_val_ne (by show k.val ≠ 0; omega)) (lowIdx_ne_rev k k) (lowIdx_ne_rev _ _)
    (lowIdx_ne_rev _ _) (c := ω) (c' := 1) ?_ ?_ hω1
  · intro t
    rw [hbmat, Matrix.diagonal_apply]
    by_cases ht : t = lowIdx k
    · subst ht
      simp [hdp]
    · rw [if_neg ht, if_neg (Ne.symm ht)]
  · intro t
    rw [hbmat, Matrix.diagonal_apply]
    by_cases ht : t = lowIdx (⟨0, hj0⟩ : Fin (n / 2))
    · subst ht
      simp [hdj]
    · rw [if_neg ht, if_neg ht]

end Last

section Short

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

@[expose] def su_diagSL {t s : F} (hts : t * s = 1) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![t, 0; 0, s], by rw [Matrix.det_fin_two_of]; simp [hts]⟩

@[expose] def su_dshort (σ : F ≃+* F) (p q : Fin n) (t s : F) (u : Fin n) : F :=
  if u = p then t else if u = q then s else if u = Fin.rev q then σ t
    else if u = Fin.rev p then σ s else 1

section Eval

variable {p q : Fin n} {t s : F}

theorem su_dshort_p : su_dshort σ p q t s p = t := by
  simp [su_dshort]

theorem su_dshort_q (hpq : p ≠ q) : su_dshort σ p q t s q = s := by
  simp [su_dshort, hpq.symm]

theorem su_dshort_rev_q (hpq : p ≠ Fin.rev q) (hq : q ≠ Fin.rev q) :
    su_dshort σ p q t s (Fin.rev q) = σ t := by
  simp [su_dshort, hpq.symm, hq.symm]

theorem su_dshort_rev_p (hpq : p ≠ q) (hp : p ≠ Fin.rev p) (hqp : q ≠ Fin.rev p) :
    su_dshort σ p q t s (Fin.rev p) = σ s := by
  have h : Fin.rev p ≠ Fin.rev q := fun h => hpq (Fin.rev_injective h)
  simp [su_dshort, hp.symm, hqp.symm, h]

theorem su_dshort_of_ne {u : Fin n} (h1 : u ≠ p) (h2 : u ≠ q) (h3 : u ≠ Fin.rev q)
    (h4 : u ≠ Fin.rev p) : su_dshort σ p q t s u = 1 := by
  simp [su_dshort, h1, h2, h3, h4]

theorem su_dshort_pow {r : ℕ} (ht : t ^ r = 1) (hs : s ^ r = 1) (u : Fin n) :
    su_dshort σ p q t s u ^ r = 1 := by
  unfold su_dshort
  split_ifs
  · exact ht
  · exact hs
  · rw [← map_pow, ht, map_one]
  · rw [← map_pow, hs, map_one]
  · exact one_pow r

theorem su_dshort_pow_three (ht : t ^ 3 = 1) (hs : s ^ 3 = 1) (u : Fin n) :
    su_dshort σ p q t s u ^ 3 = 1 :=
  su_dshort_pow ht hs u

end Eval

variable (hσ : ∀ c, σ (σ c) = c) {k : Fin (n / 2)} (hk : k.val + 1 < n / 2)

@[expose] noncomputable def su_shortDiag {t s : F} (hts : t * s = 1) : SU σ n :=
  (((rankOneShortEquiv (hσ := hσ) hk).symm (su_diagSL hts) :
    ↥(rankOne (rootGroup σ hσ n) k)) : SU σ n)

theorem su_shortDiag_mem {t s : F} (hts : t * s = 1) :
    su_shortDiag hσ hk hts ∈ rankOne (rootGroup σ hσ n) k :=
  ((rankOneShortEquiv (hσ := hσ) hk).symm (su_diagSL hts)).2

theorem su_toBlock_shortDiag {t s : F} (hts : t * s = 1) :
    SUExtras.toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat σ n (su_shortDiag hσ hk hts)) =
      !![t, 0; 0, s] := by
  have h := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F))
    ((rankOneShortEquiv (hσ := hσ) hk).apply_symm_apply (su_diagSL hts))
  exact h

theorem su_mat_shortDiag {t s : F} (hts : t * s = 1) :
    mat σ n (su_shortDiag hσ hk hts) =
      Matrix.diagonal (su_dshort σ (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) t s) := by
  obtain ⟨hpq, hp, hq, hqp⟩ := short_facts (n := n) hk
  have hpq' : lowIdx (n := n) k ≠ Fin.rev (lowIdx ⟨k.val + 1, hk⟩) := lowIdx_ne_rev _ _
  have hmem := su_shortDiag_mem hσ hk hts
  obtain ⟨hblk, -⟩ := isBlk_short_of_mem hk hmem
  have hb := su_toBlock_shortDiag hσ hk hts
  set x := su_shortDiag hσ hk hts with hx
  set p : Fin n := lowIdx k with hpdef
  set q : Fin n := lowIdx ⟨k.val + 1, hk⟩ with hqdef
  have hpp : mat σ n x p p = t := by simpa [SUExtras.toBlock] using congrFun (congrFun hb 0) 0
  have hpq0 : mat σ n x p q = 0 := by simpa [SUExtras.toBlock] using congrFun (congrFun hb 0) 1
  have hqp0 : mat σ n x q p = 0 := by simpa [SUExtras.toBlock] using congrFun (congrFun hb 1) 0
  have hqq : mat σ n x q q = s := by simpa [SUExtras.toBlock] using congrFun (congrFun hb 1) 1
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
  have hcolp : ∀ u, mat σ n x u p = if u = p then t else 0 := by
    intro u
    by_cases hup : u = p
    · rw [hup, hpp, if_pos rfl]
    · by_cases huq : u = q
      · rw [huq, hqp0, if_neg (Ne.symm hpq)]
      · rw [(hout u p (Or.inl rfl) hup huq).1, if_neg hup]
  have hcolq : ∀ u, mat σ n x u q = if u = q then s else 0 := by
    intro u
    by_cases huq : u = q
    · rw [huq, hqq, if_pos rfl]
    · by_cases hup : u = p
      · rw [hup, hpq0, if_neg hpq]
      · rw [(hout u q (Or.inr rfl) hup huq).1, if_neg huq]
  have hrowp : ∀ b, mat σ n x p b = if b = p then t else 0 := by
    intro b
    by_cases hbp : b = p
    · rw [hbp, hpp, if_pos rfl]
    · by_cases hbq : b = q
      · rw [hbq, hpq0, if_neg hpq.symm]
      · rw [(hout b p (Or.inl rfl) hbp hbq).2, if_neg hbp]
  have hrowq : ∀ b, mat σ n x q b = if b = q then s else 0 := by
    intro b
    by_cases hbq : b = q
    · rw [hbq, hqq, if_pos rfl]
    · by_cases hbp : b = p
      · rw [hbp, hqp0, if_neg hpq]
      · rw [(hout b q (Or.inr rfl) hbp hbq).2, if_neg hbq]
  have hrowp' : ∀ b, mat σ n x (Fin.rev p) b = if b = Fin.rev p then σ s else 0 :=
    su_row_rev_of_col (by rw [← map_mul, hts, map_one]) hcolp
  have hrowq' : ∀ b, mat σ n x (Fin.rev q) b = if b = Fin.rev q then σ t else 0 :=
    su_row_rev_of_col (by rw [← map_mul, mul_comm, hts, map_one]) hcolq
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
  rw [Matrix.diagonal_apply]
  by_cases hup : u = p
  · rw [hup, hrowp b, su_dshort_p]
    exact key _ _ _
  by_cases huq : u = q
  · rw [huq, hrowq b, su_dshort_q hpq]
    exact key _ _ _
  by_cases hup' : u = Fin.rev p
  · rw [hup', hrowp' b, su_dshort_rev_p hpq hp hqp]
    exact key _ _ _
  by_cases huq' : u = Fin.rev q
  · rw [huq', hrowq' b, su_dshort_rev_q hpq' hq]
    exact key _ _ _
  · rw [hrow0 u b hup huq hup' huq', Matrix.one_apply, su_dshort_of_ne hup huq huq' hup']

theorem su_blkShort_cases (u : Fin n) (hu : blkShort k hk u ≠ 0) :
    blkShort k hk u = 1 ∨ blkShort k hk u = 2 := by
  unfold blkShort at hu ⊢
  split_ifs at hu ⊢ <;> simp_all

theorem su_commute_diagonal_short {g : SU σ n} (hg : g ∈ rankOne (rootGroup σ hσ n) k)
    {d : Fin n → F} (h1 : d (lowIdx k) = d (lowIdx ⟨k.val + 1, hk⟩))
    (h2 : d (Fin.rev (lowIdx k)) = d (Fin.rev (lowIdx ⟨k.val + 1, hk⟩))) :
    mat σ n g * Matrix.diagonal d = Matrix.diagonal d * mat σ n g := by
  obtain ⟨hblk, -⟩ := isBlk_short_of_mem hk hg
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : blkShort k hk i = blkShort k hk j ∧ blkShort k hk i ≠ 0
  · obtain ⟨hij, hi0⟩ := h
    have hd : d i = d j := by
      rcases su_blkShort_cases hk i hi0 with hc | hc
      · have hj1 : blkShort k hk j = 1 := hij.symm.trans hc
        rcases (blkShort_eq_one_iff hk i).1 hc with rfl | rfl <;>
          rcases (blkShort_eq_one_iff hk j).1 hj1 with rfl | rfl <;>
          first | rfl | exact h1 | exact h1.symm
      · have hj2 : blkShort k hk j = 2 := hij.symm.trans hc
        rcases (blkShort_eq_two_iff hk i).1 hc with rfl | rfl <;>
          rcases (blkShort_eq_two_iff hk j).1 hj2 with rfl | rfl <;>
          first | rfl | exact h2 | exact h2.symm
    rw [hd, mul_comm]
  · rw [hblk i j h]
    by_cases hij : i = j
    · subst hij
      rw [mul_comm]
    · rw [Matrix.one_apply_ne hij, zero_mul, mul_zero]

end Short

section ShortPair

theorem su_short_pair_E9 {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 8 ≤ n) (heven : Even n) (h3 : 3 ∣ 2 ^ f + 1)
    (k k' : Fin (n / 2)) (hk' : k'.val = k.val + 1) (hkk' : k'.val + 1 < n / 2) :
    ∃ a b m : SU (unitaryInvolution F 2 f) n,
      a ∈ rankOne (rootDatum hF n).rootGroup k ∧ m ∈ rankOne (rootDatum hF n).rootGroup k ∧
      b ∈ rankOne (rootDatum hF n).rootGroup k ⊔ rankOne (rootDatum hF n).rootGroup k' ∧
      a ^ 3 = 1 ∧ b ^ 3 = 1 ∧
      a ∉ Subgroup.center (SU (unitaryInvolution F 2 f) n) ∧
      b ∉ Subgroup.center (SU (unitaryInvolution F 2 f) n) ∧
      m * a * m⁻¹ = a⁻¹ ∧ a * b = b * a ∧ m * b = b * m := by
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨r, hr⟩ := heven
  have hk : k.val + 1 < n / 2 := by omega
  obtain rfl : k' = ⟨k.val + 1, hk⟩ := Fin.ext hk'
  obtain ⟨ω, hω3, hω1, hσω⟩ := su_exists_omega hF h3
  have hω0 : ω ≠ 0 := fun h => by rw [h] at hω3; norm_num at hω3
  have hω6 : (ω ^ 2) ^ 3 = 1 := by linear_combination (ω ^ 3 + 1) * hω3
  have hts : ω * ω ^ 2 = 1 := by linear_combination hω3
  have hts' : ω ^ 2 * ω = 1 := by linear_combination hω3
  have hf1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hpd : 3 ∣ Nat.card F ^ 2 - 1 := by
    rw [hF]
    exact dvd_sq_sq_sub_one_of_dvd_add_one hf1 h3
  obtain ⟨w, m₀, hw, hw1, hm⟩ := exists_order_inverted_sl2 (F := F) Nat.prime_three (by norm_num)
    hpd
  obtain ⟨ha3, -, hma, -, -⟩ := su_transport (K := SU (unitaryInvolution F 2 f) n)
    (rankOneShortEquiv (hσ := hσ) hk) (B := 1) hw (one_pow 3) hm (by rw [mul_one, one_mul])
    (by rw [mul_one, one_mul])
  have ha1 : (((rankOneShortEquiv (hσ := hσ) hk).symm w : ↥(rankOne (rootGroup
      (unitaryInvolution F 2 f) hσ n) k)) : SU (unitaryInvolution F 2 f) n) ≠ 1 := fun h =>
    hw1 ((rankOneShortEquiv (hσ := hσ) hk).symm.injective
      ((Subtype.ext h).trans (map_one _).symm))
  have hxmat := su_mat_shortDiag hσ hk hts
  have hymat := su_mat_shortDiag hσ (k := (⟨k.val + 1, hk⟩ : Fin (n / 2))) hkk' hts'
  have hxmem := su_shortDiag_mem hσ hk hts
  have hymem := su_shortDiag_mem hσ (k := (⟨k.val + 1, hk⟩ : Fin (n / 2))) hkk' hts'
  generalize su_shortDiag hσ hk hts = x at hxmat hxmem
  generalize su_shortDiag hσ (k := (⟨k.val + 1, hk⟩ : Fin (n / 2))) hkk' hts' = y at hymat hymem
  set cp : Fin n := lowIdx k with hcp
  set cq : Fin n := lowIdx (⟨k.val + 1, hk⟩ : Fin (n / 2)) with hcq
  set cr : Fin n := lowIdx (⟨(⟨k.val + 1, hk⟩ : Fin (n / 2)).val + 1, hkk'⟩ : Fin (n / 2)) with hcr
  have hpq : cp ≠ cq := Fin.ne_of_val_ne (by show k.val ≠ k.val + 1; omega)
  have hpr : cp ≠ cr := Fin.ne_of_val_ne (by show k.val ≠ k.val + 1 + 1; omega)
  have hqr : cq ≠ cr := Fin.ne_of_val_ne (by show k.val + 1 ≠ k.val + 1 + 1; omega)
  have hbmat : mat (unitaryInvolution F 2 f) n (x * y) = Matrix.diagonal (fun u =>
      su_dshort (unitaryInvolution F 2 f) cp cq ω (ω ^ 2) u *
        su_dshort (unitaryInvolution F 2 f) cq cr (ω ^ 2) ω u) := by
    rw [map_mul, hxmat, hymat, Matrix.diagonal_mul_diagonal]
  have hdp : su_dshort (unitaryInvolution F 2 f) cp cq ω (ω ^ 2) cp *
      su_dshort (unitaryInvolution F 2 f) cq cr (ω ^ 2) ω cp = ω := by
    rw [su_dshort_p, su_dshort_of_ne hpq hpr (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _), mul_one]
  have hdq : su_dshort (unitaryInvolution F 2 f) cp cq ω (ω ^ 2) cq *
      su_dshort (unitaryInvolution F 2 f) cq cr (ω ^ 2) ω cq = ω := by
    rw [su_dshort_q hpq, su_dshort_p]
    linear_combination ω * hω3
  have hdrp : su_dshort (unitaryInvolution F 2 f) cp cq ω (ω ^ 2) (Fin.rev cp) *
      su_dshort (unitaryInvolution F 2 f) cq cr (ω ^ 2) ω (Fin.rev cp) = ω := by
    rw [su_dshort_rev_p hpq (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _),
      su_dshort_of_ne (Ne.symm (lowIdx_ne_rev _ _)) (Ne.symm (lowIdx_ne_rev _ _))
        (fun h => hpr (Fin.rev_injective h)) (fun h => hpq (Fin.rev_injective h)), mul_one,
      map_pow, hσω]
    linear_combination ω * hω3
  have hdrq : su_dshort (unitaryInvolution F 2 f) cp cq ω (ω ^ 2) (Fin.rev cq) *
      su_dshort (unitaryInvolution F 2 f) cq cr (ω ^ 2) ω (Fin.rev cq) = ω := by
    rw [su_dshort_rev_q (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _),
      su_dshort_rev_p hqr (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _), hσω]
    linear_combination ω * hω3
  have hcomm : ∀ g : SU (unitaryInvolution F 2 f) n,
      g ∈ rankOne (rootGroup (unitaryInvolution F 2 f) hσ n) k → g * (x * y) = (x * y) * g := by
    intro g hg
    have h := su_commute_diagonal_short hσ hk hg (d := fun u =>
      su_dshort (unitaryInvolution F 2 f) cp cq ω (ω ^ 2) u *
        su_dshort (unitaryInvolution F 2 f) cq cr (ω ^ 2) ω u) (hdp.trans hdq.symm)
      (hdrp.trans hdrq.symm)
    apply mat_injective
    rw [map_mul (mat (unitaryInvolution F 2 f) n) g (x * y),
      map_mul (mat (unitaryInvolution F 2 f) n) (x * y) g, hbmat]
    exact h
  have hb3 : (x * y) ^ 3 = 1 := by
    apply mat_injective
    rw [map_pow, hbmat, Matrix.diagonal_pow, map_one]
    ext i j
    simp only [Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs
    · show (su_dshort (unitaryInvolution F 2 f) cp cq ω (ω ^ 2) i *
        su_dshort (unitaryInvolution F 2 f) cq cr (ω ^ 2) ω i) ^ 3 = 1
      rw [mul_pow, su_dshort_pow_three hω3 hω6 i, su_dshort_pow_three hω6 hω3 i, one_mul]
    · rfl
  obtain ⟨jv, hjv, hj1, hj2, hj3⟩ : ∃ jv : ℕ, jv < n / 2 ∧ jv ≠ k.val ∧ jv ≠ k.val + 1 ∧
      jv ≠ k.val + 1 + 1 := by
    by_cases h0 : k.val = 0
    · exact ⟨3, by omega, by omega, by omega, by omega⟩
    · exact ⟨0, by omega, by omega, by omega, by omega⟩
  set cj : Fin n := lowIdx (⟨jv, hjv⟩ : Fin (n / 2)) with hcj
  have hjp : cj ≠ cp := Fin.ne_of_val_ne (by show jv ≠ k.val; exact hj1)
  have hjq : cj ≠ cq := Fin.ne_of_val_ne (by show jv ≠ k.val + 1; exact hj2)
  have hjr : cj ≠ cr := Fin.ne_of_val_ne (by show jv ≠ k.val + 1 + 1; exact hj3)
  have hdj : su_dshort (unitaryInvolution F 2 f) cp cq ω (ω ^ 2) cj *
      su_dshort (unitaryInvolution F 2 f) cq cr (ω ^ 2) ω cj = 1 := by
    rw [su_dshort_of_ne hjp hjq (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _),
      su_dshort_of_ne hjq hjr (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _), one_mul]
  have hbc : x * y ∉ Subgroup.center (SU (unitaryInvolution F 2 f) n) := by
    refine su_not_mem_center_of_row_col hσ (i := cp) (j := cj) (Ne.symm hjp)
      (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) (c := ω) (c' := 1) ?_ ?_ hω1
    · intro t
      rw [hbmat, Matrix.diagonal_apply]
      by_cases ht : t = cp
      · subst ht
        simp only [if_true, hdp]
      · rw [if_neg ht, if_neg (Ne.symm ht)]
    · intro t
      rw [hbmat, Matrix.diagonal_apply]
      by_cases ht : t = cj
      · subst ht
        simp only [if_true, hdj]
      · rw [if_neg ht, if_neg ht]
  exact ⟨_, x * y, _, (rankOneShortEquiv (hσ := hσ) hk).symm w |>.2,
    (rankOneShortEquiv (hσ := hσ) hk).symm m₀ |>.2, Subgroup.mul_mem_sup hxmem hymem, ha3, hb3,
    not_mem_center_of_inverted (p := 3) (by decide) ha3 ha1 hma, hbc, hma,
    hcomm _ ((rankOneShortEquiv (hσ := hσ) hk).symm w).2,
    hcomm _ ((rankOneShortEquiv (hσ := hσ) hk).symm m₀).2⟩


theorem su_short_pair_q {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 6 ≤ n) (heven : Even n)
    {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hrd : r ∣ 2 ^ f + 1)
    (k k' : Fin (n / 2)) (hk' : k'.val = k.val + 1) (hkk' : k'.val + 1 < n / 2) :
    ∃ a b m : SU (unitaryInvolution F 2 f) n,
      a ∈ rankOne (rootDatum hF n).rootGroup k ∧ m ∈ rankOne (rootDatum hF n).rootGroup k ∧
      b ∈ rankOne (rootDatum hF n).rootGroup k ⊔ rankOne (rootDatum hF n).rootGroup k' ∧
      a ^ r = 1 ∧ b ^ r = 1 ∧
      a ∉ Subgroup.center (SU (unitaryInvolution F 2 f) n) ∧
      b ∉ Subgroup.center (SU (unitaryInvolution F 2 f) n) ∧
      m * a * m⁻¹ = a⁻¹ ∧ a * b = b * a ∧ m * b = b * m := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hσ := unitaryInvolution_involutive hF
  have hf1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hr2 : r ≠ 2 := by omega
  have hpd : r ∣ Nat.card F ^ 2 - 1 := by
    rw [hF]
    exact dvd_sq_sq_sub_one_of_dvd_add_one hf1 hrd
  obtain ⟨w, m₀, hw, hw1, hm⟩ := exists_order_inverted_sl2 (F := F) hr hr2 hpd
  have hk : k.val + 1 < n / 2 := by omega
  obtain rfl : k' = ⟨k.val + 1, hk⟩ := Fin.ext hk'
  obtain ⟨s, hs, hs1, hσs⟩ := su_exists_order_norm_one hF hr hrd
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, zero_pow hr.pos.ne'] at hs
    exact zero_ne_one hs
  have hsinv : (s⁻¹) ^ r = 1 := by rw [inv_pow, hs, inv_one]
  have hs2 : (s ^ 2) ^ r = 1 := by rw [← pow_mul, mul_comm, pow_mul, hs, one_pow]
  have hs2inv : ((s ^ 2)⁻¹) ^ r = 1 := by rw [inv_pow, hs2, inv_one]
  have hts : s * s⁻¹ = 1 := mul_inv_cancel₀ hs0
  have hts2 : s ^ 2 * (s ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 hs0)
  have hxmat := su_mat_shortDiag hσ hk hts
  have hymat := su_mat_shortDiag hσ (k := (⟨k.val + 1, hk⟩ : Fin (n / 2))) hkk' hts2
  have hxmem := su_shortDiag_mem hσ hk hts
  have hymem := su_shortDiag_mem hσ (k := (⟨k.val + 1, hk⟩ : Fin (n / 2))) hkk' hts2
  generalize su_shortDiag hσ hk hts = x at hxmat hxmem
  generalize su_shortDiag hσ (k := (⟨k.val + 1, hk⟩ : Fin (n / 2))) hkk' hts2 = y at hymat hymem
  set cp : Fin n := lowIdx k with hcp
  set cq : Fin n := lowIdx (⟨k.val + 1, hk⟩ : Fin (n / 2)) with hcq
  set cr : Fin n := lowIdx (⟨(⟨k.val + 1, hk⟩ : Fin (n / 2)).val + 1, hkk'⟩ : Fin (n / 2)) with hcr
  have hpq : cp ≠ cq := Fin.ne_of_val_ne (by show k.val ≠ k.val + 1; omega)
  have hpr : cp ≠ cr := Fin.ne_of_val_ne (by show k.val ≠ k.val + 1 + 1; omega)
  have hqr : cq ≠ cr := Fin.ne_of_val_ne (by show k.val + 1 ≠ k.val + 1 + 1; omega)
  have hbmat : mat (unitaryInvolution F 2 f) n (x * y) = Matrix.diagonal (fun u =>
      su_dshort (unitaryInvolution F 2 f) cp cq s s⁻¹ u *
        su_dshort (unitaryInvolution F 2 f) cq cr (s ^ 2) (s ^ 2)⁻¹ u) := by
    rw [map_mul, hxmat, hymat, Matrix.diagonal_mul_diagonal]
  have hdp : su_dshort (unitaryInvolution F 2 f) cp cq s s⁻¹ cp *
      su_dshort (unitaryInvolution F 2 f) cq cr (s ^ 2) (s ^ 2)⁻¹ cp = s := by
    rw [su_dshort_p, su_dshort_of_ne hpq hpr (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _),
      mul_one]
  have hdq : su_dshort (unitaryInvolution F 2 f) cp cq s s⁻¹ cq *
      su_dshort (unitaryInvolution F 2 f) cq cr (s ^ 2) (s ^ 2)⁻¹ cq = s := by
    rw [su_dshort_q hpq, su_dshort_p, pow_two, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
  have hσinv : (unitaryInvolution F 2 f) (s⁻¹) = s := by
    rw [← hσs]
    exact hσ s
  have hσsq : (unitaryInvolution F 2 f) (s ^ 2) = (s ^ 2)⁻¹ := by
    rw [map_pow, hσs, inv_pow]
  have hσ2 : (unitaryInvolution F 2 f) ((s ^ 2)⁻¹) = s ^ 2 := by
    rw [← hσsq]
    exact hσ (s ^ 2)
  have hdrp : su_dshort (unitaryInvolution F 2 f) cp cq s s⁻¹ (Fin.rev cp) *
      su_dshort (unitaryInvolution F 2 f) cq cr (s ^ 2) (s ^ 2)⁻¹ (Fin.rev cp) = s := by
    rw [su_dshort_rev_p hpq (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _),
      su_dshort_of_ne (Ne.symm (lowIdx_ne_rev _ _)) (Ne.symm (lowIdx_ne_rev _ _))
        (fun h => hpr (Fin.rev_injective h)) (fun h => hpq (Fin.rev_injective h)), mul_one,
      hσinv]
  have hdrq : su_dshort (unitaryInvolution F 2 f) cp cq s s⁻¹ (Fin.rev cq) *
      su_dshort (unitaryInvolution F 2 f) cq cr (s ^ 2) (s ^ 2)⁻¹ (Fin.rev cq) = s := by
    rw [su_dshort_rev_q (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _),
      su_dshort_rev_p hqr (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _), hσs, hσ2,
      pow_two, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
  have hcomm : ∀ g : SU (unitaryInvolution F 2 f) n,
      g ∈ rankOne (rootGroup (unitaryInvolution F 2 f) hσ n) k →
        g * (x * y) = (x * y) * g := by
    intro g hg
    have h := su_commute_diagonal_short hσ hk hg (d := fun u =>
      su_dshort (unitaryInvolution F 2 f) cp cq s s⁻¹ u *
        su_dshort (unitaryInvolution F 2 f) cq cr (s ^ 2) (s ^ 2)⁻¹ u)
      (hdp.trans hdq.symm) (hdrp.trans hdrq.symm)
    apply mat_injective
    rw [map_mul (mat (unitaryInvolution F 2 f) n) g (x * y),
      map_mul (mat (unitaryInvolution F 2 f) n) (x * y) g, hbmat]
    exact h
  have hbr : (x * y) ^ r = 1 := by
    apply mat_injective
    rw [map_pow, hbmat, Matrix.diagonal_pow, map_one]
    ext i j
    simp only [Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs
    · show (su_dshort (unitaryInvolution F 2 f) cp cq s s⁻¹ i *
        su_dshort (unitaryInvolution F 2 f) cq cr (s ^ 2) (s ^ 2)⁻¹ i) ^ r = 1
      rw [mul_pow, su_dshort_pow hs hsinv i, su_dshort_pow hs2 hs2inv i, one_mul]
    · rfl
  have hdcr : su_dshort (unitaryInvolution F 2 f) cp cq s s⁻¹ cr *
      su_dshort (unitaryInvolution F 2 f) cq cr (s ^ 2) (s ^ 2)⁻¹ cr = (s ^ 2)⁻¹ := by
    rw [su_dshort_of_ne hpr.symm hqr.symm (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _),
      su_dshort_q hqr, one_mul]
  have hcc : s ≠ (s ^ 2)⁻¹ := by
    intro h
    have hs3 : s ^ 3 = 1 := by
      have h' := congrArg (fun z => z * s ^ 2) h
      rw [inv_mul_cancel₀ (pow_ne_zero 2 hs0)] at h'
      simpa [pow_succ, pow_two, mul_assoc] using h'
    have hds : orderOf s ∣ 3 := orderOf_dvd_of_pow_eq_one hs3
    have horder : orderOf s = r := orderOf_eq_prime hs hs1
    rw [horder] at hds
    have hle : r ≤ 3 := Nat.le_of_dvd (by norm_num) hds
    omega
  have hbc : x * y ∉ Subgroup.center (SU (unitaryInvolution F 2 f) n) := by
    refine su_not_mem_center_of_row_col hσ (i := cp) (j := cr) hpr
      (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) (c := s) (c' := (s ^ 2)⁻¹)
      ?_ ?_ hcc
    · intro t
      rw [hbmat, Matrix.diagonal_apply]
      by_cases ht : t = cp
      · subst ht
        simp only [if_true, hdp]
      · rw [if_neg ht, if_neg (Ne.symm ht)]
    · intro t
      rw [hbmat, Matrix.diagonal_apply]
      by_cases ht : t = cr
      · subst ht
        simp only [if_true, hdcr]
      · rw [if_neg ht, if_neg ht]
  set e := rankOneShortEquiv (hσ := hσ) hk with he
  obtain ⟨har, -, hma, -, -⟩ := su_transport_q (K := SU (unitaryInvolution F 2 f) n) e
    (r := r) (A := w) (B := 1) (M := m₀) hw (one_pow r) hm
    (by rw [mul_one, one_mul]) (by rw [mul_one, one_mul])
  have ha1 : (e.symm w : SU (unitaryInvolution F 2 f) n) ≠ 1 := fun h =>
    hw1 (e.symm.injective ((Subtype.ext h).trans (map_one e.symm).symm))
  exact ⟨(e.symm w : SU (unitaryInvolution F 2 f) n), x * y,
    (e.symm m₀ : SU (unitaryInvolution F 2 f) n), (e.symm w).2, (e.symm m₀).2,
    Subgroup.mul_mem_sup hxmem hymem, har, hbr,
    not_mem_center_of_inverted (hr.odd_of_ne_two hr2) har ha1 hma, hbc, hma,
    hcomm _ (e.symm w).2, hcomm _ (e.symm m₀).2⟩

end ShortPair

end CFSG.LocalAnalysis.RankThreeUC.S15.K517Six
