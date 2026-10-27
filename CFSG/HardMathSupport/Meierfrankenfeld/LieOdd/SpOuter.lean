module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SpRouteA

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open Matrix CFSG.Assembly.LowTwoRank CFSG.LargeExtraspecial.A2Mod.FrC
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

variable {K : Type} [Field K] {r : ℕ}

@[expose] def symB (v w : Fin r ⊕ Fin r → K) : K := v ⬝ᵥ (formJ r K *ᵥ w)

theorem symB_eq (v w : Fin r ⊕ Fin r → K) :
    symB v w = ∑ i, (v (Sum.inl i) * w (Sum.inr i) - v (Sum.inr i) * w (Sum.inl i)) := by
  simp [symB, formJ, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, fromBlocks,
    Matrix.one_apply, Finset.sum_sub_distrib]
  ring

theorem symB_swap (v w : Fin r ⊕ Fin r → K) : symB w v = - symB v w := by
  rw [symB_eq, symB_eq, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem symB_self (h2 : (2 : K) ≠ 0) (v : Fin r ⊕ Fin r → K) : symB v v = 0 := by
  have := symB_swap v v
  have h : (2 : K) * symB v v = 0 := by linear_combination this
  exact (mul_eq_zero.1 h).resolve_left h2

theorem symB_add_left (u v w : Fin r ⊕ Fin r → K) : symB (u + v) w = symB u w + symB v w := by
  simp [symB, add_dotProduct]

theorem symB_add_right (u v w : Fin r ⊕ Fin r → K) : symB u (v + w) = symB u v + symB u w := by
  simp [symB, Matrix.mulVec_add, dotProduct_add]

theorem symB_smul_left (c : K) (v w : Fin r ⊕ Fin r → K) : symB (c • v) w = c * symB v w := by
  simp [symB, smul_dotProduct]

theorem symB_smul_right (c : K) (v w : Fin r ⊕ Fin r → K) : symB v (c • w) = c * symB v w := by
  simp [symB, Matrix.mulVec_smul, dotProduct_smul]

theorem eq_zero_of_symB_forall [NeZero r] {v : Fin r ⊕ Fin r → K} (h : ∀ w, symB w v = 0) :
    v = 0 := by
  ext j
  rcases j with i | i
  · have := h (Pi.single (Sum.inr i) 1)
    simpa [symB_eq, Pi.single_apply] using this
  · have := h (Pi.single (Sum.inl i) 1)
    simpa [symB_eq, Pi.single_apply] using this

theorem matrix_ext_of_dotProduct {M M' : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (h : ∀ v w, v ⬝ᵥ (M *ᵥ w) = v ⬝ᵥ (M' *ᵥ w)) : M = M' := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  simpa [Matrix.mulVec_single_one] using this

theorem mulVec_dotProduct_eq {ι : Type} [Fintype ι] (M : Matrix ι ι K) (a b : ι → K) :
    (M *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (Mᵀ *ᵥ b) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]

theorem symB_mulVec (X : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (v w : Fin r ⊕ Fin r → K) :
    symB (X *ᵥ v) (X *ᵥ w) = v ⬝ᵥ ((Xᵀ * formJ r K * X) *ᵥ w) := by
  unfold symB
  rw [mulVec_dotProduct_eq, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem symB_similitude {A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} {μ : K}
    (hA : Aᵀ * formJ r K * A = μ • formJ r K) (v w : Fin r ⊕ Fin r → K) :
    symB (A *ᵥ v) (A *ᵥ w) = μ * symB v w := by
  rw [symB_mulVec, hA, Matrix.smul_mulVec, dotProduct_smul]
  rfl

theorem matrix_ext_of_mulVec {M M' : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (h : ∀ w, M *ᵥ w = M' *ᵥ w) : M = M' :=
  matrix_ext_of_dotProduct fun v w => by rw [h w]

@[expose] def rank1 (a u : Fin r ⊕ Fin r → K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  Matrix.vecMulVec a (formJ r K *ᵥ u)

theorem rank1_mulVec (a u w : Fin r ⊕ Fin r → K) : rank1 a u *ᵥ w = symB w u • a := by
  rw [rank1, Matrix.vecMulVec_mulVec, op_smul_eq_smul, dotProduct_comm]
  rfl

theorem exists_sp_one_add (N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (hN2 : N * N = 0)
    (hB : ∀ v w, symB (N *ᵥ v) w + symB v (N *ᵥ w) + symB (N *ᵥ v) (N *ᵥ w) = 0) :
    ∃ x : StatedSp r K,
      ((x : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 + N := by
  have h1 : (1 + N) * (1 - N) = 1 := by
    rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, hN2]
    abel
  have h2 : (1 - N) * (1 + N) = 1 := by
    rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, hN2]
    abel
  refine ⟨⟨⟨1 + N, 1 - N, h1, h2⟩, ?_⟩, rfl⟩
  rw [mem_statedSp_iff]
  change (1 + N)ᵀ * formJ r K * (1 + N) = formJ r K
  apply matrix_ext_of_dotProduct
  intro v w
  have h := symB_mulVec (1 + N) v w
  rw [← h]
  have e1 : (1 + N) *ᵥ v = v + N *ᵥ v := by rw [Matrix.add_mulVec, Matrix.one_mulVec]
  have e2 : (1 + N) *ᵥ w = w + N *ᵥ w := by rw [Matrix.add_mulVec, Matrix.one_mulVec]
  rw [e1, e2, symB_add_left, symB_add_right, symB_add_right]
  have := hB v w
  change _ = symB v w
  linear_combination this

theorem pow_one_add (N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (hN2 : N * N = 0) (n : ℕ) :
    (1 + N) ^ n = 1 + (n : K) • N := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul,
      Matrix.smul_mul, Matrix.mul_one, Matrix.smul_mul, hN2]
    simp only [smul_zero, add_zero, Nat.cast_succ, add_smul,
      one_smul, Matrix.one_mul]
    abel

theorem not_scalar_of_nilp [NeZero r] (N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    (hN2 : N * N = 0) (hN : N ≠ 0) (c : Kˣ)
    (h : ((Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 + N) : False := by
  have hs : ((Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (c : K) • 1 := by
    ext i j
    by_cases hij : i = j <;>
      simp [Matrix.GeneralLinearGroup.scalar, hij]
  rw [hs] at h
  have hN' : N = ((c : K) - 1) • 1 := by
    rw [sub_smul, one_smul, h]
    abel
  have hsq : N * N = (((c : K) - 1) * ((c : K) - 1)) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    rw [hN', Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
  rw [hsq] at hN2
  let i0 : Fin r ⊕ Fin r := Sum.inl ⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩
  have h0 := congrFun (congrFun hN2 i0) i0
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.zero_apply] at h0
  apply hN
  rw [hN', show (c : K) - 1 = 0 from mul_self_eq_zero.1 h0]
  simp

theorem exists_inverted_of_nilp [NeZero r] {p : ℕ} [Fact p.Prime] [CharP K p] (A : gsp r K)
    (N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (hN2 : N * N = 0) (hN : N ≠ 0)
    (hB : ∀ v w, symB (N *ᵥ v) w + symB v (N *ᵥ w) + symB (N *ᵥ v) (N *ᵥ w) = 0)
    (hAN : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * N =
      -(N * ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))) :
    ∃ x : StatedProj (StatedSp r K), orderOf x = p ∧ conjAut r K A x = x⁻¹ := by
  obtain ⟨x, hx⟩ := exists_sp_one_add N hN2 hB
  have h1 : (1 + N) * (1 - N) = 1 := by
    rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, hN2]
    abel
  refine ⟨proj r K x, ?_, ?_⟩
  · have hpow : x ^ p = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hx, pow_one_add N hN2, CharP.cast_eq_zero,
        zero_smul, add_zero]
      rfl
    apply orderOf_eq_prime
    · rw [← map_pow, hpow, map_one]
    · intro h1'
      have hmem : x ∈ spScalars r K := (QuotientGroup.eq_one_iff x).1 h1'
      rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hmem
      obtain ⟨c, hc⟩ := hmem
      exact not_scalar_of_nilp N hN2 hN c (by rw [hc]; exact hx)
  · have hconj : conjSp r K A x = x⁻¹ := by
      apply Subtype.ext
      rw [coe_conjSp, Subgroup.coe_inv, mul_inv_eq_iff_eq_mul]
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, hx, Matrix.inv_eq_right_inv h1]
      rw [Matrix.mul_add, Matrix.sub_mul, hAN, Matrix.mul_one, Matrix.one_mul]
      abel
    rw [conjAut_proj, hconj, map_inv]

theorem exists_symB_one [NeZero r] : ∃ v w : Fin r ⊕ Fin r → K, symB v w = 1 := by
  let i0 : Fin r := ⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩
  refine ⟨Pi.single (Sum.inl i0) 1, Pi.single (Sum.inr i0) 1, ?_⟩
  simp [symB_eq, Pi.single_apply]

section CaseI

variable {a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} {μ ε : K}

theorem caseI [NeZero r] (h2 : (2 : K) ≠ 0) (hA : aᵀ * formJ r K * a = μ • formJ r K)
    (hε : ε * ε = -μ) (hε0 : ε ≠ 0) {v : Fin r ⊕ Fin r → K} (hv0 : v ≠ 0)
    (hv : a *ᵥ v = ε • v) :
    rank1 v v * rank1 v v = 0 ∧ rank1 v v ≠ 0 ∧
      (∀ x y, symB (rank1 v v *ᵥ x) y + symB x (rank1 v v *ᵥ y) +
        symB (rank1 v v *ᵥ x) (rank1 v v *ᵥ y) = 0) ∧
      a * rank1 v v = -(rank1 v v * a) := by
  have key : ∀ w, symB (a *ᵥ w) v = -ε * symB w v := by
    intro w
    have h := symB_similitude hA w v
    rw [hv, symB_smul_right] at h
    apply mul_left_cancel₀ hε0
    linear_combination h + symB w v * hε
  have hN2 : rank1 v v * rank1 v v = 0 := by
    apply matrix_ext_of_mulVec
    intro w
    rw [← Matrix.mulVec_mulVec, rank1_mulVec v v w, Matrix.mulVec_smul, rank1_mulVec v v v,
      symB_self h2, zero_smul, smul_zero, Matrix.zero_mulVec]
  refine ⟨hN2, ?_, ?_, ?_⟩
  · intro h0
    obtain ⟨w, hw⟩ : ∃ w, symB w v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hv0 (eq_zero_of_symB_forall hcon)
    have := congrArg (fun M => M *ᵥ w) h0
    simp only [rank1_mulVec, Matrix.zero_mulVec] at this
    exact (smul_ne_zero hw hv0) this
  · intro x y
    simp only [rank1_mulVec, symB_smul_left, symB_smul_right, symB_self h2]
    have := symB_swap y v
    have h' := symB_swap v x
    have h3 : symB v y = - symB y v := symB_swap y v
    linear_combination (symB x v) * h3
  · apply matrix_ext_of_mulVec
    intro w
    rw [Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, rank1_mulVec v v w,
      rank1_mulVec v v (a *ᵥ w), Matrix.mulVec_smul, hv, key, smul_smul, ← neg_smul]
    congr 1
    ring

end CaseI

section CaseII

variable {a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} {μ : K}

theorem caseII [NeZero r] (h2 : (2 : K) ≠ 0) (hA : aᵀ * formJ r K * a = μ • formJ r K)
    (hμ0 : μ ≠ 0) (hA2 : a * a = μ • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
    (hnsq : ¬ IsSquare μ) {u : Fin r ⊕ Fin r → K} (hu0 : u ≠ 0) :
    ∃ N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K, N * N = 0 ∧ N ≠ 0 ∧
      (∀ x y, symB (N *ᵥ x) y + symB x (N *ᵥ y) + symB (N *ᵥ x) (N *ᵥ y) = 0) ∧
      a * N = -(N * a) := by
  have haa : ∀ x, a *ᵥ (a *ᵥ x) = μ • x := by
    intro x
    rw [Matrix.mulVec_mulVec, hA2, Matrix.smul_mulVec, Matrix.one_mulVec]
  have sa : ∀ x y, symB (a *ᵥ x) y = symB x (a *ᵥ y) := by
    intro x y
    have h := symB_similitude hA (a *ᵥ x) y
    rw [haa, symB_smul_left] at h
    exact mul_left_cancel₀ hμ0 h.symm
  set u' := a *ᵥ u with hu'
  have h_uu : symB u u = 0 := symB_self h2 u
  have h_uu' : symB u u' = 0 := by
    have s1 := sa u u
    have s2 := symB_swap u u'
    rw [← hu'] at s1
    have h : (2 : K) * symB u u' = 0 := by linear_combination s2 - s1
    exact (mul_eq_zero.1 h).resolve_left h2
  have h_u'u : symB u' u = 0 := by
    have s1 := sa u u
    rw [← hu'] at s1
    rw [s1, h_uu']
  have h_u'u' : symB u' u' = 0 := symB_self h2 u'
  set N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    rank1 ((-μ) • u) u + rank1 u' u' with hN
  have Nmul : ∀ x, N *ᵥ x = symB x u • ((-μ) • u) + symB x u' • u' := by
    intro x
    rw [hN, Matrix.add_mulVec, rank1_mulVec, rank1_mulVec]
  have Nu : N *ᵥ u = 0 := by rw [Nmul, h_uu, h_uu']; simp
  have Nu' : N *ᵥ u' = 0 := by rw [Nmul, h_u'u, h_u'u']; simp
  have hN2 : N * N = 0 := by
    apply matrix_ext_of_mulVec
    intro w
    rw [← Matrix.mulVec_mulVec, Nmul w, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, Matrix.mulVec_smul, Nu, Nu']
    simp
  refine ⟨N, hN2, ?_, ?_, ?_⟩
  · intro h0
    have hw : ∀ w, symB w u' • u' = (μ * symB w u) • u := by
      intro w
      have := congrArg (fun M => M *ᵥ w) h0
      simp only [Nmul, Matrix.zero_mulVec, smul_smul] at this
      have h3 : symB w u' • u' = -((symB w u * -μ) • u) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]
        exact this
      rw [h3, ← neg_smul]
      congr 1
      ring
    by_cases hall : ∀ w, symB w u' = 0
    · have : u' = 0 := eq_zero_of_symB_forall hall
      have h3 := haa u
      rw [← hu', this, Matrix.mulVec_zero] at h3
      exact hu0 ((smul_eq_zero.1 h3.symm).resolve_left hμ0)
    · push Not at hall
      obtain ⟨w, hw0⟩ := hall
      have hc : u' = (μ * symB w u / symB w u') • u := by
        have := hw w
        calc u' = (symB w u')⁻¹ • (symB w u' • u') := by rw [smul_smul, inv_mul_cancel₀ hw0, one_smul]
          _ = (symB w u')⁻¹ • ((μ * symB w u) • u) := by rw [this]
          _ = _ := by rw [smul_smul, div_eq_inv_mul]
      set c := μ * symB w u / symB w u' with hcdef
      have h3 : μ • u = (c * c) • u := by
        calc μ • u = a *ᵥ u' := (haa u).symm
          _ = c • (a *ᵥ u) := by rw [hc, Matrix.mulVec_smul]
          _ = c • u' := rfl
          _ = (c * c) • u := by rw [hc, smul_smul]
      have h4 : (μ - c * c) • u = 0 := by rw [sub_smul, h3, sub_self]
      have h5 : μ = c * c := sub_eq_zero.1 ((smul_eq_zero.1 h4).resolve_right hu0)
      exact hnsq ⟨c, h5⟩
  · intro x y
    simp only [Nmul, symB_add_left, symB_add_right, symB_smul_left, symB_smul_right, h_uu,
      h_uu', h_u'u, h_u'u']
    rw [symB_swap y u, symB_swap y u']
    ring
  · apply matrix_ext_of_mulVec
    intro w
    rw [Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Nmul w,
      Nmul (a *ᵥ w), Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_smul, haa u, sa w u, ← hu']
    have h6 : symB (a *ᵥ w) u' = μ * symB w u := by
      have := symB_similitude hA w u
      rw [← hu'] at this
      exact this
    rw [h6]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring

end CaseII

theorem isSquare_neg_of_not_isSquare [Finite K] {μ : K} (hneg : ¬ IsSquare (-1 : K))
    (hμ : ¬ IsSquare μ) : IsSquare (-μ) := by
  classical
  have := Fintype.ofFinite K
  have hμ0 : μ ≠ 0 := fun h => hμ (h ▸ IsSquare.zero)
  have h1 := quadraticChar_neg_one_iff_not_isSquare.2 hneg
  have h2 := quadraticChar_neg_one_iff_not_isSquare.2 hμ
  have h3 : quadraticChar K (-μ) = 1 := by
    rw [show -μ = (-1) * μ by ring, map_mul, h1, h2]
    norm_num
  exact (quadraticChar_one_iff_isSquare (neg_ne_zero.2 hμ0)).1 h3

theorem exists_inverted_proj [NeZero r] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) (hneg : ¬ IsSquare (-1 : K)) (A : gsp r K) {lam : K}
    (hA2 : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = lam • 1)
    (hμ : ¬ IsSquare ((multiplier r K A : Kˣ) : K)) :
    ∃ x : StatedProj (StatedSp r K), orderOf x = p ∧ conjAut r K A x = x⁻¹ := by
  set a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with ha
  set μ : K := ((multiplier r K A : Kˣ) : K) with hμdef
  have hA : aᵀ * formJ r K * a = μ • formJ r K := multiplier_spec A
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h' := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h')
  have hμ0 : μ ≠ 0 := Units.ne_zero _
  have haa : ∀ x, a *ᵥ (a *ᵥ x) = lam • x := by
    intro x
    rw [Matrix.mulVec_mulVec, hA2, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hlam : lam * lam = μ * μ := by
    obtain ⟨v, w, hvw⟩ := exists_symB_one (K := K) (r := r)
    have h := symB_similitude hA (a *ᵥ v) (a *ᵥ w)
    rw [haa, haa, symB_smul_left, symB_smul_right, symB_similitude hA v w, hvw] at h
    linear_combination h
  have hcase : lam = μ ∨ lam = -μ := by
    have : (lam - μ) * (lam + μ) = 0 := by linear_combination hlam
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases hcase with rfl | hneg'
  ·
    let i0 : Fin r := ⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩
    have hu0 : (Pi.single (Sum.inl i0) 1 : Fin r ⊕ Fin r → K) ≠ 0 := by
      intro h
      have := congrFun h (Sum.inl i0)
      simp at this
    obtain ⟨N, hN2, hN, hB, hAN⟩ := caseII h2 hA hμ0 hA2 hμ hu0
    exact exists_inverted_of_nilp A N hN2 hN hB hAN
  ·
    obtain ⟨ε, hε⟩ := isSquare_neg_of_not_isSquare hneg hμ
    have hε0 : ε ≠ 0 := by
      intro h
      rw [h, mul_zero] at hε
      exact hμ0 (neg_eq_zero.1 hε)
    have hlam' : lam = ε * ε := by rw [hneg', hε]
    by_cases hex : ∃ w, (a + ε • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) *ᵥ w ≠ 0
    · obtain ⟨w, hw⟩ := hex
      have hv : a *ᵥ ((a + ε • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) *ᵥ w) =
          ε • ((a + ε • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) *ᵥ w) := by
        rw [Matrix.add_mulVec, Matrix.mulVec_add, haa, Matrix.smul_mulVec, Matrix.one_mulVec,
          Matrix.mulVec_smul, smul_add, smul_smul, hlam']
        rw [add_comm]
      obtain ⟨hN2, hN, hB, hAN⟩ := caseI h2 hA hε.symm hε0 hw hv
      exact exists_inverted_of_nilp A _ hN2 hN hB hAN
    · exfalso
      push Not at hex
      have hall : ∀ w, a *ᵥ w = (-ε) • w := by
        intro w
        have := hex w
        rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at this
        rw [neg_smul]
        exact eq_neg_of_add_eq_zero_left this
      obtain ⟨v, w, hvw⟩ := exists_symB_one (K := K) (r := r)
      have h := symB_similitude hA v w
      rw [hall v, hall w, symB_smul_left, symB_smul_right, hvw] at h
      have h3 : (2 : K) * (ε * ε) = 0 := by linear_combination h - hε
      exact mul_ne_zero h2 (mul_ne_zero hε0 hε0) h3

section Transvection

theorem rank1_self_sq (h2 : (2 : K) ≠ 0) (v : Fin r ⊕ Fin r → K) :
    rank1 v v * rank1 v v = 0 := by
  apply matrix_ext_of_mulVec
  intro w
  rw [← Matrix.mulVec_mulVec, rank1_mulVec v v w, Matrix.mulVec_smul, rank1_mulVec v v v,
    symB_self h2, zero_smul, smul_zero, Matrix.zero_mulVec]

theorem rank1_self_hB (h2 : (2 : K) ≠ 0) (v x y : Fin r ⊕ Fin r → K) :
    symB (rank1 v v *ᵥ x) y + symB x (rank1 v v *ᵥ y) + symB (rank1 v v *ᵥ x) (rank1 v v *ᵥ y) =
      0 := by
  simp only [rank1_mulVec, symB_smul_left, symB_smul_right, symB_self h2]
  have h3 : symB v y = - symB y v := symB_swap y v
  linear_combination (symB x v) * h3

theorem trace_rank1_self (h2 : (2 : K) ≠ 0) (v : Fin r ⊕ Fin r → K) :
    Matrix.trace (rank1 v v) = 0 := by
  have : Matrix.trace (rank1 v v) = v ⬝ᵥ (formJ r K *ᵥ v) := by
    simp [Matrix.trace, rank1, Matrix.vecMulVec_apply, dotProduct]
  rw [this]
  exact symB_self h2 v

theorem commute_rank1_of_conjAut_trivial [NeZero r] (h2 : (2 : K) ≠ 0)
    (h2r : ((r + r : ℕ) : K) ≠ 0) (M : gsp r K) (h : conjAut r K M = 1) (v : Fin r ⊕ Fin r → K) :
    ((M : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * rank1 v v =
      rank1 v v * ((M : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  obtain ⟨x, hx⟩ := exists_sp_one_add (rank1 v v) (rank1_self_sq h2 v) (rank1_self_hB h2 v)
  have h1 : conjAut r K M (proj r K x) = proj r K x := by rw [h]; rfl
  rw [conjAut_proj] at h1
  have h3 := QuotientGroup.eq.1 h1
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at h3
  obtain ⟨c, hc⟩ := h3
  set a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    ((M : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with ha
  set ai : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    (((M : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hai
  have hai1 : ai * a = 1 := Units.inv_mul _
  have ha1 : a * ai = 1 := Units.mul_inv _
  set X : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := 1 + rank1 v v with hX
  have e1 : c • (a * X * ai) = X := by
    have h4 : (Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c : GL (Fin r ⊕ Fin r) K) =
        (conjSp r K M x)⁻¹ * x := hc
    have h5 : conjSp r K M x * Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c =
        (x : GL (Fin r ⊕ Fin r) K) := by
      rw [h4]; simp
    have h6 := congrArg (fun g : GL (Fin r ⊕ Fin r) K =>
      (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) h5
    have hs : ((Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (c : K) • 1 := by
      ext i j
      by_cases hij : i = j <;>
        simp [Matrix.GeneralLinearGroup.scalar, hij]
    simp only [Units.val_mul, hs, coe_conjSp, hx] at h6
    rw [Matrix.mul_smul, Matrix.mul_one] at h6
    exact h6
  have etr : c * Matrix.trace X = Matrix.trace X := by
    have h7 := congrArg Matrix.trace e1
    rw [Matrix.trace_smul, Units.smul_def, smul_eq_mul] at h7
    have h8 : Matrix.trace (a * X * ai) = Matrix.trace X := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hai1, Matrix.one_mul]
    rwa [h8] at h7
  have htr : Matrix.trace X = ((r + r : ℕ) : K) := by
    rw [hX, Matrix.trace_add, Matrix.trace_one, trace_rank1_self h2, add_zero]
    simp [Fintype.card_sum]
  have hc1 : c = 1 := by
    have : ((c : K) - 1) * ((r + r : ℕ) : K) = 0 := by
      rw [htr] at etr
      linear_combination etr
    exact Units.ext (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h2r))
  rw [hc1] at e1
  simp only [one_smul] at e1
  have e2 : a * X = X * a := by
    calc a * X = (a * X * ai) * a := by rw [Matrix.mul_assoc (a * X), hai1, Matrix.mul_one]
      _ = X * a := by rw [e1]
  rw [hX, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at e2
  exact add_left_cancel e2

theorem exists_scalar_of_conjAut_trivial [NeZero r] (h2 : (2 : K) ≠ 0)
    (h2r : ((r + r : ℕ) : K) ≠ 0) (M : gsp r K) (h : conjAut r K M = 1) :
    ∃ lam : K, ((M : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      lam • 1 := by
  set a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    ((M : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with ha
  have hcol : ∀ v : Fin r ⊕ Fin r → K, v ≠ 0 → ∃ c : K, a *ᵥ v = c • v := by
    intro v hv
    obtain ⟨w, hw⟩ : ∃ w, symB w v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hv (eq_zero_of_symB_forall hcon)
    have hc := commute_rank1_of_conjAut_trivial h2 h2r M h v
    have := congrArg (fun N => N *ᵥ w) hc
    simp only [← Matrix.mulVec_mulVec, rank1_mulVec v v w, Matrix.mulVec_smul] at this
    have h' : a *ᵥ v = (symB (a *ᵥ w) v / symB w v) • v := by
      rw [rank1_mulVec v v (a *ᵥ w)] at this
      calc a *ᵥ v = (symB w v)⁻¹ • (symB w v • a *ᵥ v) := by
            rw [smul_smul, inv_mul_cancel₀ hw, one_smul]
        _ = (symB w v)⁻¹ • (symB (a *ᵥ w) v • v) := by rw [this]
        _ = _ := by rw [smul_smul, div_eq_inv_mul]
    exact ⟨_, h'⟩
  have hnot : ∀ v, ¬ LinearIndependent K ![v, Matrix.mulVecLin a v] := by
    intro v
    by_cases hv : v = 0
    · simp [hv, linearIndependent_fin2]
    · obtain ⟨c, hc⟩ := hcol v hv
      rw [LinearIndependent.pair_iff' hv]
      push Not
      exact ⟨c, by simpa using hc.symm⟩
  obtain ⟨lam, hlam⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hnot
  refine ⟨lam, matrix_ext_of_mulVec fun w => ?_⟩
  have := LinearMap.congr_fun hlam w
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  simpa using this

end Transvection

theorem conjAut_mem_range_of_isSquare [NeZero r] (A : gsp r K)
    (hs : IsSquare ((multiplier r K A : Kˣ) : K)) :
    conjAut r K A ∈ (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))).range := by
  obtain ⟨s, hs⟩ := hs
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, mul_zero] at hs
    exact Units.ne_zero _ hs
  set c : Kˣ := Units.mk0 s hs0 with hc
  set a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with ha
  have hAJ : aᵀ * formJ r K * a = ((multiplier r K A : Kˣ) : K) • formJ r K := multiplier_spec A
  set B : GL (Fin r ⊕ Fin r) K :=
    Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c⁻¹ * (A : GL (Fin r ⊕ Fin r) K) with hB
  have hsc : ∀ d : Kˣ, ((Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) d : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (d : K) • 1 := by
    intro d
    ext i j
    by_cases hij : i = j <;>
      simp [Matrix.GeneralLinearGroup.scalar, hij]
  have hBmat : (B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = ((c⁻¹ : Kˣ) : K) • a := by
    rw [hB, Units.val_mul, hsc, Matrix.smul_mul, Matrix.one_mul]
  have hBsp : B ∈ StatedSp r K := by
    have key : ∀ d : K, (d • a)ᵀ * formJ r K * (d • a) = (d * d) • (aᵀ * formJ r K * a) := by
      intro d
      rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [mem_statedSp_iff, hBmat, key, hAJ, smul_smul]
    have : ((c⁻¹ : Kˣ) : K) * ((c⁻¹ : Kˣ) : K) * ((multiplier r K A : Kˣ) : K) = 1 := by
      rw [hs]
      have : ((c : Kˣ) : K) = s := rfl
      rw [Units.val_inv_eq_inv_val, this]
      field_simp
    rw [this, one_smul]
  let Bg : gsp r K := ⟨B, statedSp_le_gsp hBsp⟩
  let Sg : gsp r K := ⟨Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c, scalar_mem_gsp c⟩
  have hABg : A = Sg * Bg := by
    apply Subtype.ext
    change (A : GL (Fin r ⊕ Fin r) K) = Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c *
      (Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c⁻¹ * (A : GL (Fin r ⊕ Fin r) K))
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hSg : conjAut r K Sg = 1 := conjAut_scalar_sp c
  refine ⟨proj r K ⟨B, hBsp⟩, ?_⟩
  rw [hABg, map_mul, hSg, one_mul]
  ext x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  change MulAut.conj (proj r K ⟨B, hBsp⟩) (proj r K g) = conjAut r K Bg (proj r K g)
  rw [conjAut_proj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem outer_involution_inverts_psp [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) (hK : Nat.card K = p) (hr : 2 ≤ r) (hneg : ¬ IsSquare (-1 : K))
    (h2r : ((r + r : ℕ) : K) ≠ 0) (ψ : MulAut (StatedProj (StatedSp r K)))
    (hψ : ψ ∉ (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))).range) (hψ2 : ψ * ψ = 1) :
    ∃ x : StatedProj (StatedSp r K), orderOf x = p ∧ ψ x = x⁻¹ := by
  have : NeZero r := ⟨by omega⟩
  have hK1 : Nat.card K = p ^ 1 := by rw [pow_one]; exact hK
  obtain ⟨A, σ, hσ⟩ := exists_conjAut_fieldAut hp2 hK1 hr ψ
  have hAut : Nat.card (K ≃+* K) = 1 :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic (Fact.out : p.Prime) K hK1).1
  have hσ1 : σ = 1 := by
    have := (Nat.card_eq_one_iff_unique.1 hAut).1
    exact Subsingleton.elim _ _
  rw [hσ1, map_one, mul_one] at hσ
  subst hσ
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h' := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h')
  have hμ : ¬ IsSquare ((multiplier r K A : Kˣ) : K) := fun hs =>
    hψ (conjAut_mem_range_of_isSquare A hs)
  have hAA : conjAut r K (A * A) = 1 := by rw [map_mul]; exact hψ2
  obtain ⟨lam, hlam⟩ := exists_scalar_of_conjAut_trivial h2 h2r (A * A) hAA
  have hA2 : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = lam • 1 := by
    rw [← hlam]
    rfl
  obtain ⟨x, hx, hxinv⟩ := exists_inverted_proj hp2 hneg A hA2 hμ
  exact ⟨x, hx, hxinv⟩

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
