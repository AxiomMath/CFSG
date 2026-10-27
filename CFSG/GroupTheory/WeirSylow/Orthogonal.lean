module

public import CFSG.GroupTheory.WeirSylow.OrthogonalTypes

public section

namespace CFSG.GroupTheory.WeirSylow

open Module Finset QuadraticMap
open CFSG.LieType.Universal.Spin (quadPlus quadMinus quadOdd)
open CFSG.Assembly.LowTwoRank (StatedSp)

variable {p : ℕ} [hp : Fact p.Prime] {K : Type} [Fintype K]

section Arith

variable (p K) in
noncomputable abbrev weirE : ℕ :=
  orderOf (Fintype.card K : ZMod p)

variable (p K) in
noncomputable abbrev weirA : ℕ :=
  padicValNat p (Fintype.card K ^ weirE p K - 1)

theorem weirE_pos (hpK : ¬ p ∣ Fintype.card K) : 0 < weirE p K := by
  rw [weirE, ← ordMod_natCast]
  exact ordMod_pos (c := (Fintype.card K : ℤ)) (by exact_mod_cast hpK)

theorem intCast_pow_sub_one_eq [Nonempty K] (k : ℕ) :
    (((Fintype.card K ^ k - 1 : ℕ) : ℤ)) = (Fintype.card K : ℤ) ^ k - 1 := by
  rw [Nat.cast_sub (Nat.one_le_pow _ _ Fintype.card_pos), Nat.cast_pow, Nat.cast_one]

theorem dvd_pow_sub_one_iff_weirE (j : ℕ) :
    (p : ℤ) ∣ (Fintype.card K : ℤ) ^ j - 1 ↔ weirE p K ∣ j := by
  rw [dvd_pow_sub_one_iff, ordMod_natCast]

theorem pow_weirA_dvd : p ^ weirA p K ∣ Fintype.card K ^ weirE p K - 1 :=
  pow_padicValNat_dvd

theorem one_le_weirA [Nontrivial K] (hpK : ¬ p ∣ Fintype.card K) : 1 ≤ weirA p K := by
  refine one_le_padicValNat_of_dvd ?_ ?_
  · have := Nat.one_lt_pow (weirE_pos hpK).ne' (Fintype.one_lt_card (α := K))
    omega
  · have h := (dvd_pow_sub_one_iff_weirE (p := p) (K := K) (weirE p K)).2 dvd_rfl
    rw [← intCast_pow_sub_one_eq] at h
    exact_mod_cast h

theorem pow_weirA_dvd_pow_add_one [Nonempty K] (hpK : ¬ p ∣ Fintype.card K) {f : ℕ}
    (hf : weirE p K = 2 * f) : p ^ weirA p K ∣ Fintype.card K ^ f + 1 := by
  have hf0 : 0 < f := by have := weirE_pos hpK; omega
  have hnd : ¬ p ∣ Fintype.card K ^ f - 1 := by
    intro h
    have h' : (p : ℤ) ∣ (Fintype.card K : ℤ) ^ f - 1 := by
      rw [← intCast_pow_sub_one_eq]
      exact_mod_cast h
    rw [dvd_pow_sub_one_iff_weirE] at h'
    have := Nat.le_of_dvd hf0 h'
    omega
  have hcop : (p ^ weirA p K).Coprime (Fintype.card K ^ f - 1) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hnd)
  refine hcop.dvd_of_dvd_mul_left ?_
  have h1 : 1 ≤ Fintype.card K ^ f := Nat.one_le_pow _ _ Fintype.card_pos
  have hfac : (Fintype.card K ^ f - 1) * (Fintype.card K ^ f + 1) =
      Fintype.card K ^ weirE p K - 1 := by
    have h2 : 1 ≤ Fintype.card K ^ weirE p K := Nat.one_le_pow _ _ Fintype.card_pos
    zify [h1, h2]
    rw [hf, pow_mul']
    ring
  rw [hfac]
  exact pow_weirA_dvd

theorem dvd_pow_mul_sub_neg_one_pow [Nontrivial K] (hpK : ¬ p ∣ Fintype.card K) {f : ℕ}
    (hf : weirE p K = 2 * f) (m : ℕ) :
    (p : ℤ) ∣ (Fintype.card K : ℤ) ^ (f * m) - (-1) ^ m := by
  have h1 : (p : ℤ) ∣ (Fintype.card K : ℤ) ^ f + 1 := by
    have := (dvd_pow_self p (Nat.one_le_iff_ne_zero.1 (one_le_weirA hpK))).trans
      (pow_weirA_dvd_pow_add_one hpK hf)
    exact_mod_cast this
  have h2 := sub_dvd_pow_sub_pow ((Fintype.card K : ℤ) ^ f) (-1) m
  rw [sub_neg_eq_add, ← pow_mul] at h2
  exact h1.trans h2

theorem padicValNat_factorial_pred_lt {a m : ℕ} (ha : 1 ≤ a) (hm : 1 ≤ m) :
    a * (m - 1) + padicValNat p (m - 1).factorial < a * m + padicValNat p m.factorial := by
  have h := Nat.mul_factorial_pred (n := m) (by omega)
  rw [← h, padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have : a * (m' + 1) = a * m' + a := by ring
  omega

end Arith

theorem exists_irreducible_quadratic (K : Type) [Field K] [Finite K] :
    ∃ b c : K, ∀ s : K, s ^ 2 + b * s + c ≠ 0 := by
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  let L := FiniteField.Extension K (ringChar K) 2
  have hL : finrank K L = 2 := FiniteField.finrank_extension K _ 2
  obtain ⟨x, hx⟩ : ∃ x : L, ∀ s : K, algebraMap K L s ≠ x := by
    by_contra! h
    have hsurj : Function.Surjective (Algebra.linearMap K L) := fun y =>
      let ⟨s, hs⟩ := h y
      ⟨s, hs⟩
    have := LinearMap.finrank_range_le (Algebra.linearMap K L)
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top, hL, Module.finrank_self] at this
    omega
  have hli : LinearIndependent K ![(1 : L), x] := by
    refine LinearIndependent.pair_iff.2 fun s t h => ?_
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero, Algebra.smul_def, mul_one, map_eq_zero_iff _
        (algebraMap K L).injective] at h
      exact ⟨h, rfl⟩
    · exfalso
      apply hx (-s / t)
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at h
      rw [map_div₀, map_neg, div_eq_iff ((map_ne_zero _).2 ht)]
      linear_combination -h
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hL])
  have hB : ∀ i, B i = ![(1 : L), x] i := fun i => by
    simp [B]
  have hx2 := B.sum_repr (x ^ 2)
  rw [Fin.sum_univ_two, hB, hB] at hx2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx2
  set r₀ := B.repr (x ^ 2) 0
  set r₁ := B.repr (x ^ 2) 1
  refine ⟨-r₁, -r₀, fun s hs => ?_⟩
  have key : (x - algebraMap K L s) * (x + algebraMap K L s - algebraMap K L r₁) = 0 := by
    have hs' := congrArg (algebraMap K L) hs
    simp only [map_add, map_mul, map_pow, map_neg, map_zero] at hs'
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hx2
    linear_combination -hx2 - hs'
  rcases mul_eq_zero.1 key with h | h
  · exact hx s (sub_eq_zero.1 h).symm
  · apply hx (r₁ - s)
    rw [map_sub]
    linear_combination -h

section Complete

variable [Field K]

omit [Fintype K] in
theorem isPlusType_of_finrank_eq_zero {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (h : finrank K V = 0) : IsPlusType Q :=
  have : Subsingleton V := Module.finrank_zero_iff.1 h
  isPlusType_of_subsingleton Q

theorem exists_injective_orthogonal_of_model {G : Type} [Group G] (S : FormSpace K K)
    {QS : QuadraticForm K S.V} (hSF : ∀ x y, S.F x y = QS x) (hQS : (polarBilin QS).Nondegenerate)
    {t : ℕ} (hSdim : finrank K S.V = 2 * t) (φ : G →* S.isom) (hφ : Function.Injective φ)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) {n : ℕ} (hdim : finrank K V = 2 * n) (htn : t ≤ n)
    (htype : t = n → (IsPlusType QS ↔ IsPlusType Q)) :
    ∃ ψ : G →* TauCeti.QuadraticMap.orthogonalGroup Q, Function.Injective ψ := by
  rcases eq_or_lt_of_le htn with rfl | hlt
  · obtain ⟨e⟩ := nonempty_isometry_of_isPlusType_iff hQS hQ hSdim hdim (htype rfl)
    let ι := (isomEquivOrthogonal S hSF).trans (TauCeti.QuadraticMap.orthogonalGroupCongr e)
    exact ⟨ι.toMonoidHom.comp φ, ι.injective.comp hφ⟩
  obtain ⟨b₀, c₀, hirr⟩ := exists_irreducible_quadratic K
  set r := n - t with hr
  have hr1 : 1 ≤ r := by omega
  have hS0 : t = 0 → IsPlusType QS := fun h => isPlusType_of_finrank_eq_zero QS (by omega)
  by_cases hiff : IsPlusType QS ↔ IsPlusType Q
  · let T : FormSpace K K := ⟨Fin r ⊕ Fin r → K, fun x _ => quadPlus r K x⟩
    have hT : ∀ x y, T.F x y = quadPlus r K x := fun _ _ => rfl
    have hnd := nondegenerate_polarBilin_prod hQS
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus r K)
    have htyp : IsPlusType (QS.prod (quadPlus r K)) ↔ IsPlusType Q := by
      by_cases hp : IsPlusType QS
      · exact ⟨fun _ => hiff.1 hp, fun _ => hp.prod (isPlusType_quadPlus K r)⟩
      · have ht1 : 1 ≤ t := by
          by_contra h0
          exact hp (hS0 (by omega))
        exact ⟨fun h => absurd h (not_isPlusType_prod_quadPlus hQS ht1 hSdim hp r),
          fun h => absurd (hiff.2 h) hp⟩
    obtain ⟨e⟩ := nonempty_isometry_of_isPlusType_iff hnd hQ
      (by rw [Module.finrank_prod, hSdim, finrank_quadPlus_space]; omega) hdim htyp
    exact exists_injective_orthogonal_of_prod S T hSF hT φ hφ e
  · let T : FormSpace K K := ⟨Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K,
      fun x _ => quadMinus r K b₀ c₀ x⟩
    have hT : ∀ x y, T.F x y = quadMinus r K b₀ c₀ x := fun _ _ => rfl
    have hnd := nondegenerate_polarBilin_prod hQS
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite r K hirr)
    have htyp : IsPlusType (QS.prod (quadMinus r K b₀ c₀)) ↔ IsPlusType Q := by
      by_cases hp : IsPlusType QS
      · exact ⟨fun h => absurd h (not_isPlusType_prod_quadMinus hQS hSdim hp hr1 hirr),
          fun h => absurd (iff_of_true hp h) hiff⟩
      · have ht1 : 1 ≤ t := by
          by_contra h0
          exact hp (hS0 (by omega))
        refine ⟨fun _ => ?_, fun _ => isPlusType_prod_quadMinus hQS ht1 hSdim hp r hirr⟩
        by_contra hq
        exact hiff (iff_of_false hp hq)
    obtain ⟨e⟩ := nonempty_isometry_of_isPlusType_iff hnd hQ
      (by rw [Module.finrank_prod, hSdim, finrank_quadMinus_space hr1]; omega) hdim htyp
    exact exists_injective_orthogonal_of_prod S T hSF hT φ hφ e


theorem exists_injective_orthogonal_of_model_odd (h2 : ringChar K ≠ 2) {G : Type}
    [Group G] (S : FormSpace K K) {QS : QuadraticForm K S.V} (hSF : ∀ x y, S.F x y = QS x)
    (hQS : (polarBilin QS).Nondegenerate) {t : ℕ} (hSdim : finrank K S.V = 2 * t)
    (φ : G →* S.isom) (hφ : Function.Injective φ) {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank K V = 2 * n + 1) (htn : t ≤ n) :
    ∃ ψ : G →* TauCeti.QuadraticMap.orthogonalGroup Q, Function.Injective ψ := by
  have h2' : (2 : K) ≠ 0 := fun h => h2 (by
    have := charP_two_of_two_eq_zero h
    exact ringChar.eq K 2)
  set r := n - t
  let T : FormSpace K K := ⟨Fin r ⊕ Fin r ⊕ Unit → K, fun x _ => quadOdd r K x⟩
  have hT : ∀ x y, T.F x y = quadOdd r K x := fun _ _ => rfl
  obtain ⟨ψ₀, hψ₀⟩ := exists_rep_prod S T φ hφ
  have hXT : ∀ x y, (S.prod T).F x y = (QS.prod (quadOdd r K)) x := fun x y => by
    change S.F x.1 y.1 + T.F x.2 y.2 = _
    rw [hSF, hT, QuadraticMap.prod_apply]
  have hnd := nondegenerate_polarBilin_prod hQS
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadOdd r K h2')
  have hdimXT : finrank K (S.V × (Fin r ⊕ Fin r ⊕ Unit → K)) = 2 * n + 1 := by
    rw [Module.finrank_prod, hSdim, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
      Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    omega
  obtain ⟨d₁, hd₁, ⟨e₁⟩⟩ := exists_smul_isometry_quadOdd h2 _ hnd hdimXT
  obtain ⟨d₂, hd₂, ⟨e₂⟩⟩ := exists_smul_isometry_quadOdd h2 Q hQ hdim
  let ι : (S.prod T).isom ≃* TauCeti.QuadraticMap.orthogonalGroup Q :=
    (isomEquivOrthogonal (S.prod T) hXT).trans
      ((MulEquiv.subgroupCongr (orthogonalGroup_smul _ hd₁).symm).trans
        ((TauCeti.QuadraticMap.orthogonalGroupCongr (e₁.trans e₂.symm)).trans
          (MulEquiv.subgroupCongr (orthogonalGroup_smul Q hd₂))))
  exact ⟨ι.toMonoidHom.comp ψ₀, ι.injective.comp hψ₀⟩

theorem two_mul_pred_div {f m : ℕ} (hf : 0 < f) (hm : 1 ≤ m) :
    2 * (f * m - 1) / (2 * f) = m - 1 := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  refine Nat.div_eq_of_lt_le ?_ ?_
  · have h1 : 1 ≤ f * (m' + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    zify [h1]
    nlinarith
  · have h1 : 1 ≤ f * (m' + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    zify [h1]
    nlinarith

theorem isPlusType_iff_even (hp1 : Odd p) (hpK : ¬ p ∣ Fintype.card K) {f : ℕ}
    (hf : weirE p K = 2 * f) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) {m : ℕ} (hm : 1 ≤ m)
    (hdim : finrank K V = 2 * (f * m)) {G : Type} [Group G]
    (φ : G →* TauCeti.QuadraticMap.orthogonalGroup Q) (hφ : Function.Injective φ)
    (hG : Nat.card G = p ^ (weirA p K * m + padicValNat p m.factorial)) :
    IsPlusType Q ↔ Even m := by
  have hf0 : 0 < f := by have := weirE_pos hpK; omega
  have hn : 1 ≤ f * m := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hpK' : ¬ p ∣ Nat.card K := by rwa [Nat.card_eq_fintype_card]
  have hf' : orderOf (Fintype.card K : ZMod p) = 2 * f := hf
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V))
    fun g h hgh => LinearEquiv.ext (congrFun hgh)
  have hle : weirA p K * m + padicValNat p m.factorial ≤
      (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q)).factorization p := by
    refine (Nat.Prime.pow_dvd_iff_le_factorization hp.out Nat.card_pos.ne').1 ?_
    rw [← hG]
    exact Subgroup.card_dvd_of_injective φ hφ
  have hcong := dvd_pow_mul_sub_neg_one_pow hpK hf m
  have key : ∀ ε : ℤ, ((ε = 1 ∧ IsPlusType Q) ∨ (ε = -1 ∧ ¬ IsPlusType Q)) → ε = (-1) ^ m := by
    intro ε hε
    have hεpm : ε = 1 ∨ ε = -1 := by rcases hε with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
    by_contra hne
    have hε' : ε = -(-1) ^ m := by
      rcases neg_one_pow_eq_or ℤ m with h | h <;> rcases hεpm with rfl | rfl <;> simp_all
    have hnd : ¬ (p : ℤ) ∣ (Fintype.card K : ℤ) ^ (f * m) - ε := by
      intro h
      have h2 : (p : ℤ) ∣ 2 * (-1) ^ m := by
        have := dvd_sub h hcong
        rw [hε'] at this
        convert this using 1
        ring
      rcases (Nat.prime_iff_prime_int.mp hp.out).dvd_or_dvd h2 with h | h
      · exact not_dvd_two hp1 h
      · exact (Nat.prime_iff_prime_int.mp hp.out).not_isUnit
          (isUnit_of_dvd_unit h ((isUnit_neg_one).pow m))
    have hval := (factorization_card_orthogonalGroup_even hp1 hpK' hQ hn hdim hε).2
      (by rwa [Nat.card_eq_fintype_card])
    rw [hval, factorization_card_statedSp hp1 K hpK, hf', ite_eq_left (even_two_mul f),
      two_mul_pred_div hf0 hm,
      show padicValNat p (Fintype.card K ^ (2 * f) - 1) = weirA p K by rw [← hf']] at hle
    exact absurd hle (not_le.2 (padicValNat_factorial_pred_lt (one_le_weirA hpK) hm))
  constructor
  · intro h
    have := key 1 (Or.inl ⟨rfl, h⟩)
    exact (neg_one_pow_eq_one_iff_even (by norm_num)).1 this.symm
  · intro h
    by_contra hnp
    have := key (-1) (Or.inr ⟨rfl, hnp⟩)
    rw [(neg_one_pow_eq_one_iff_even (by norm_num)).2 h] at this
    norm_num at this


theorem exists_injective_sigmaModel_split (hpK : ¬ p ∣ Fintype.card K) {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) {n : ℕ} (hdim : finrank K V = 2 * n) {k : ℕ}
    (hk : k ≤ n) (htype : weirE p K * (k / weirE p K) = n → IsPlusType Q) :
    ∃ ψ : sigmaModel p (weirE p K) (weirA p K) k →* TauCeti.QuadraticMap.orthogonalGroup Q,
      Function.Injective ψ := by
  obtain ⟨S, ⟨QS, hSF, hQS, hplus⟩, hSdim, φ, hφ⟩ :=
    exists_sigmaModel_rep_plus (weirE_pos hpK) pow_weirA_dvd k
  exact exists_injective_orthogonal_of_model S hSF hQS (t := weirE p K * (k / weirE p K))
    (by rw [hSdim]; ring) φ hφ hQ hdim ((Nat.mul_div_le k _).trans hk)
    fun h => iff_of_true hplus (htype h)

theorem exists_injective_sigmaModel_split_odd (h2 : ringChar K ≠ 2)
    (hpK : ¬ p ∣ Fintype.card K) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank K V = 2 * n + 1) {k : ℕ} (hk : k ≤ n) :
    ∃ ψ : sigmaModel p (weirE p K) (weirA p K) k →* TauCeti.QuadraticMap.orthogonalGroup Q,
      Function.Injective ψ := by
  obtain ⟨S, ⟨QS, hSF, hQS, -⟩, hSdim, φ, hφ⟩ :=
    exists_sigmaModel_rep_plus (weirE_pos hpK) pow_weirA_dvd k
  exact exists_injective_orthogonal_of_model_odd h2 S hSF hQS (t := weirE p K * (k / weirE p K))
    (by rw [hSdim]; ring) φ hφ hQ hdim ((Nat.mul_div_le k _).trans hk)

theorem exists_injective_sigmaModel_aniso (hp1 : Odd p) (hpK : ¬ p ∣ Fintype.card K) {f : ℕ}
    (hf : weirE p K = 2 * f) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank K V = 2 * n) {k : ℕ} (hk : k ≤ n)
    (htype : f * (k / f) = n → (IsPlusType Q ↔ Even (k / f))) :
    ∃ ψ : sigmaModel p (weirE p K) (weirA p K) (2 * k) →*
      TauCeti.QuadraticMap.orthogonalGroup Q, Function.Injective ψ := by
  have hf0 : 0 < f := by have := weirE_pos hpK; omega
  obtain ⟨S, ⟨QS, hSF, hQS⟩, hSdim, φ, hφ⟩ :=
    exists_sigmaModel_rep_aniso hf0 (pow_weirA_dvd_pow_add_one hpK hf) (2 * k)
  have hdivk : 2 * k / (2 * f) = k / f := Nat.mul_div_mul_left k f two_pos
  have hSdim' : finrank K S.V = 2 * (f * (k / f)) := by rw [hSdim, hdivk]; ring
  have htypeS : IsPlusType QS ↔ Even (k / f) := by
    rcases Nat.eq_zero_or_pos (k / f) with h0 | hpos
    · rw [h0]
      exact iff_of_true (isPlusType_of_finrank_eq_zero QS (by rw [hSdim', h0]; ring)) ⟨0, rfl⟩
    · exact isPlusType_iff_even hp1 hpK hf hQS hpos hSdim'
        ((isomEquivOrthogonal S hSF).toMonoidHom.comp φ)
        (by exact (isomEquivOrthogonal S hSF).injective.comp hφ)
        (by rw [card_sigmaModel, hdivk])
  obtain ⟨ψ, hψ⟩ := exists_injective_orthogonal_of_model S hSF hQS hSdim' φ hφ hQ hdim
    ((Nat.mul_div_le k f).trans hk) fun h => htypeS.trans (htype h).symm
  rw [hf]
  exact ⟨ψ, hψ⟩

theorem exists_injective_sigmaModel_aniso_odd (h2 : ringChar K ≠ 2)
    (hpK : ¬ p ∣ Fintype.card K) {f : ℕ} (hf : weirE p K = 2 * f) {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) {n : ℕ} (hdim : finrank K V = 2 * n + 1) {k : ℕ}
    (hk : k ≤ n) :
    ∃ ψ : sigmaModel p (weirE p K) (weirA p K) (2 * k) →*
      TauCeti.QuadraticMap.orthogonalGroup Q, Function.Injective ψ := by
  have hf0 : 0 < f := by have := weirE_pos hpK; omega
  obtain ⟨S, ⟨QS, hSF, hQS⟩, hSdim, φ, hφ⟩ :=
    exists_sigmaModel_rep_aniso hf0 (pow_weirA_dvd_pow_add_one hpK hf) (2 * k)
  have hdivk : 2 * k / (2 * f) = k / f := Nat.mul_div_mul_left k f two_pos
  obtain ⟨ψ, hψ⟩ := exists_injective_orthogonal_of_model_odd h2 S hSF hQS
    (t := f * (k / f)) (by rw [hSdim, hdivk]; ring) φ hφ hQ hdim ((Nat.mul_div_le k f).trans hk)
  rw [hf]
  exact ⟨ψ, hψ⟩

theorem nonempty_sylow_mulEquiv_of_sigmaModel (hp1 : Odd p) (hpK : ¬ p ∣ Fintype.card K)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (k : ℕ) (hfac : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q)).factorization p =
      (Nat.card (StatedSp k K)).factorization p)
    (ψ : sigmaModel p (weirE p K) (weirA p K) (if Even (weirE p K) then 2 * k else k) →*
      TauCeti.QuadraticMap.orthogonalGroup Q) (hψ : Function.Injective ψ)
    (P : Sylow p (TauCeti.QuadraticMap.orthogonalGroup Q)) (P' : Sylow p (StatedSp k K)) :
    Nonempty (P ≃* P') := by
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V))
    fun g h hgh => LinearEquiv.ext (congrFun hgh)
  obtain ⟨e'⟩ := sylow_Sp hp1 K hpK k P'
  refine nonempty_sylow_mulEquiv_of_injective (ψ.comp e'.toMonoidHom) (hψ.comp e'.injective) ?_ P
  rw [hfac]
  exact P'.card_eq_multiplicity

end Complete

@[expose] def IsMinusType {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) : Prop :=
  (∃ W : Submodule K V, 2 * finrank K W + 2 = finrank K V ∧ ∀ x ∈ W, Q x = 0) ∧ ¬ IsPlusType Q

theorem sylow_orthogonal_odd [Field K] (hp1 : Odd p) (hK : Odd (Fintype.card K))
    (hpK : ¬ p ∣ Fintype.card K) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {n : ℕ} (hdim : finrank K V = 2 * n + 1) (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate) (P : Sylow p (TauCeti.QuadraticMap.orthogonalGroup Q))
    (P' : Sylow p (StatedSp n K)) : Nonempty (P ≃* P') := by
  have h2 : ringChar K ≠ 2 := fun h => by
    have := FiniteField.even_card_iff_char_two.1 h
    exact Nat.not_even_iff_odd.2 hK (Nat.even_iff.2 this)
  have hfac := factorization_card_orthogonalGroup_odd hp1 (by rwa [Nat.card_eq_fintype_card])
    h2 hQ hdim
  obtain ⟨ψ, hψ⟩ : ∃ ψ : sigmaModel p (weirE p K) (weirA p K)
      (if Even (weirE p K) then 2 * n else n) →* TauCeti.QuadraticMap.orthogonalGroup Q,
      Function.Injective ψ := by
    by_cases he : Even (weirE p K)
    · obtain ⟨f, hf⟩ := he
      rw [ite_eq_left ⟨f, hf⟩]
      exact exists_injective_sigmaModel_aniso_odd h2 hpK (f := f) (by omega) hQ hdim le_rfl
    · rw [ite_eq_right he]
      exact exists_injective_sigmaModel_split_odd h2 hpK hQ hdim le_rfl
  exact nonempty_sylow_mulEquiv_of_sigmaModel hp1 hpK n hfac ψ hψ P P'

theorem sylow_orthogonal_even [Field K] (hp1 : Odd p) (hpK : ¬ p ∣ Fintype.card K) {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {n : ℕ} (hn : 1 ≤ n)
    (hdim : finrank K V = 2 * n) (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate)
    {ε : ℤ} (hε : (ε = 1 ∧ IsPlusType Q) ∨ (ε = -1 ∧ IsMinusType Q))
    (P : Sylow p (TauCeti.QuadraticMap.orthogonalGroup Q)) :
    (¬ (p : ℤ) ∣ (Fintype.card K : ℤ) ^ n + ε →
      ∀ P' : Sylow p (StatedSp n K), Nonempty (P ≃* P')) ∧
    (¬ (p : ℤ) ∣ (Fintype.card K : ℤ) ^ n - ε →
      ∀ P' : Sylow p (StatedSp (n - 1) K), Nonempty (P ≃* P')) ∧
    (¬ (p : ℤ) ∣ (Fintype.card K : ℤ) ^ n + ε ∨ ¬ (p : ℤ) ∣ (Fintype.card K : ℤ) ^ n - ε) := by
  have hε' : (ε = 1 ∧ IsPlusType Q) ∨ (ε = -1 ∧ ¬ IsPlusType Q) :=
    hε.imp id fun h => ⟨h.1, h.2.2⟩
  have hεpm : ε = 1 ∨ ε = -1 := by rcases hε with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  have hpK' : ¬ p ∣ Nat.card K := by rwa [Nat.card_eq_fintype_card]
  obtain ⟨hfac1, hfac2⟩ := factorization_card_orthogonalGroup_even hp1 hpK' hQ hn hdim hε'
  rw [Nat.card_eq_fintype_card] at hfac1 hfac2
  refine ⟨fun h P' => ?_, fun h P' => ?_, ?_⟩
  ·
    obtain ⟨ψ, hψ⟩ : ∃ ψ : sigmaModel p (weirE p K) (weirA p K)
        (if Even (weirE p K) then 2 * n else n) →* TauCeti.QuadraticMap.orthogonalGroup Q,
        Function.Injective ψ := by
      by_cases he : Even (weirE p K)
      · obtain ⟨f, hf⟩ := he
        rw [ite_eq_left ⟨f, hf⟩]
        refine exists_injective_sigmaModel_aniso hp1 hpK (f := f) (by omega) hQ hdim le_rfl
          fun hfn => ?_
        have hcong := dvd_pow_mul_sub_neg_one_pow hpK (f := f) (by omega) (n / f)
        rw [hfn] at hcong
        have hεm : ε = (-1) ^ (n / f) := by
          by_contra hne
          apply h
          have hε'' : ε = -(-1) ^ (n / f) := by
            rcases neg_one_pow_eq_or ℤ (n / f) with h' | h' <;> rcases hεpm with rfl | rfl <;>
              simp_all
          rw [hε'', ← sub_eq_add_neg]
          exact hcong
        rcases hε' with ⟨rfl, hpl⟩ | ⟨rfl, hnp⟩
        · exact iff_of_true hpl ((neg_one_pow_eq_one_iff_even (by norm_num)).1 hεm.symm)
        · refine iff_of_false hnp fun hev => ?_
          rw [(neg_one_pow_eq_one_iff_even (by norm_num)).2 hev] at hεm
          norm_num at hεm
      · rw [ite_eq_right he]
        refine exists_injective_sigmaModel_split hpK hQ hdim le_rfl fun hen => ?_
        have hd : (p : ℤ) ∣ (Fintype.card K : ℤ) ^ n - 1 :=
          (dvd_pow_sub_one_iff_weirE n).2 ⟨n / weirE p K, hen.symm⟩
        rcases hε' with ⟨rfl, hpl⟩ | ⟨rfl, -⟩
        · exact hpl
        · exact absurd (by rw [← sub_eq_add_neg]; exact hd) h
    exact nonempty_sylow_mulEquiv_of_sigmaModel hp1 hpK n (hfac1 h) ψ hψ P P'
  ·
    obtain ⟨ψ, hψ⟩ : ∃ ψ : sigmaModel p (weirE p K) (weirA p K)
        (if Even (weirE p K) then 2 * (n - 1) else n - 1) →*
          TauCeti.QuadraticMap.orthogonalGroup Q, Function.Injective ψ := by
      by_cases he : Even (weirE p K)
      · obtain ⟨f, hf⟩ := he
        rw [ite_eq_left ⟨f, hf⟩]
        refine exists_injective_sigmaModel_aniso hp1 hpK (f := f) (by omega) hQ hdim
          (by omega) fun hfn => ?_
        have := Nat.mul_div_le (n - 1) f
        omega
      · rw [ite_eq_right he]
        refine exists_injective_sigmaModel_split hpK hQ hdim (by omega) fun hen => ?_
        have := Nat.mul_div_le (n - 1) (weirE p K)
        omega
    exact nonempty_sylow_mulEquiv_of_sigmaModel hp1 hpK (n - 1) (hfac2 h) ψ hψ P P'
  ·
    rcases hεpm with rfl | rfl
    · exact not_dvd_add_one_or_not_dvd_sub_one hp1 _
    · rw [← sub_eq_add_neg, sub_neg_eq_add]
      exact (not_dvd_add_one_or_not_dvd_sub_one hp1 _).symm

end CFSG.GroupTheory.WeirSylow
