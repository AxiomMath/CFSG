module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankPair
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankClsThree

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.SectionRank Matrix

section Field

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

@[expose] def frobQ (K : Type) [Field K] (p f : ℕ) [Fact p.Prime] [CharP K p] : K →+* K :=
  iterateFrobenius K p f

omit [Finite K] in
theorem frobQ_apply (x : K) : frobQ K p f x = x ^ p ^ f := rfl

theorem frobQ_frobQ (hK : Nat.card K = (p ^ f) ^ 2) (x : K) :
    frobQ K p f (frobQ K p f x) = x := by
  rw [frobQ_apply, frobQ_apply, ← pow_mul, ← sq, ← hK]
  have : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

theorem exists_frobQ_ne (hK : Nat.card K = (p ^ f) ^ 2) (hf : 1 ≤ f) :
    ∃ θ : K, frobQ K p f θ ≠ θ := by
  by_contra h
  push Not at h
  have hq : 1 < p ^ f := Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt
  classical
  have : Fintype K := Fintype.ofFinite K
  have hroots : (Finset.univ : Finset K).val ⊆
      (Polynomial.X ^ p ^ f - Polynomial.X : Polynomial K).roots := by
    intro x _
    rw [Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero K hq)]
    simp [Polynomial.IsRoot, sub_eq_zero]
    exact h x
  have h1 := Polynomial.card_le_degree_of_subset_roots hroots
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by simpa using hq)] at h1
  simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one, Finset.card_univ] at h1
  rw [← Nat.card_eq_fintype_card, hK, sq] at h1
  nlinarith

theorem exists_trace_eq_neg_one (hK : Nat.card K = (p ^ f) ^ 2) (hf : 1 ≤ f) :
    ∃ α : K, α + frobQ K p f α = -1 := by
  obtain ⟨θ, hθ⟩ := exists_frobQ_ne hK hf
  have hne : θ - frobQ K p f θ ≠ 0 := fun h => hθ (sub_eq_zero.1 h).symm
  refine ⟨-θ * (θ - frobQ K p f θ)⁻¹, ?_⟩
  have hφ : frobQ K p f (θ - frobQ K p f θ) = -(θ - frobQ K p f θ) := by
    rw [map_sub, frobQ_frobQ hK]
    ring
  rw [map_mul, map_neg, map_inv₀, hφ, inv_neg]
  field_simp
  ring

theorem exists_norm_eq (hK : Nat.card K = (p ^ f) ^ 2) (hf : 1 ≤ f) {y : K}
    (hy : frobQ K p f y = y) : ∃ γ : K, γ * frobQ K p f γ = y := by
  by_cases hy0 : y = 0
  · exact ⟨0, by simp [hy0]⟩
  have hq : 1 < p ^ f := Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = (p ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  obtain ⟨k, hk0⟩ := (mem_powers_iff_mem_zpowers (x := g) (y := Units.mk0 y hy0)).2 (hg _)
  have hk : g ^ k = Units.mk0 y hy0 := hk0
  have hyq : y ^ (p ^ f - 1) = 1 := by
    have h1 : y ^ p ^ f = y := hy
    have : y ^ (p ^ f - 1) * y = 1 * y := by
      rw [← pow_succ, Nat.sub_add_cancel hq.le, one_mul, h1]
    exact mul_right_cancel₀ hy0 this
  have hdvd : (p ^ f + 1) * (p ^ f - 1) ∣ k * (p ^ f - 1) := by
    have h1 : g ^ (k * (p ^ f - 1)) = 1 := by
      rw [pow_mul, hk]
      ext
      simpa using hyq
    have := orderOf_dvd_of_pow_eq_one h1
    rwa [hord, show (p ^ f) ^ 2 - 1 = (p ^ f + 1) * (p ^ f - 1) by
      zify [hq.le, (by nlinarith : 1 ≤ (p ^ f) ^ 2)]; ring] at this
  obtain ⟨m, hm⟩ := Nat.dvd_of_mul_dvd_mul_right (by omega) hdvd
  refine ⟨((g ^ m : Kˣ) : K), ?_⟩
  rw [frobQ_apply, ← pow_succ']
  have : ((g ^ m) ^ (p ^ f + 1) : Kˣ) = Units.mk0 y hy0 := by
    rw [← hk, ← pow_mul, hm]
    ring_nf
  simpa using congrArg Units.val this

end Field

section Matrices

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K]

theorem pairMatrix_cube {i j : ι} (hij : i ≠ j) {a b c d : K} (htr : a + d = -1)
    (hdet : a * d - b * c = 1) : (pairMatrix i j a b c d) ^ 3 = 1 := by
  have h2 : pairMatrix i j a b c d * pairMatrix i j a b c d =
      pairMatrix i j (-a - 1) (-b) (-c) (-d - 1) := by
    rw [pairMatrix_mul hij]
    congr 1
    · linear_combination a * htr - hdet
    · linear_combination b * htr
    · linear_combination c * htr
    · linear_combination d * htr - hdet
  rw [pow_three', h2, pairMatrix_mul hij, ← pairMatrix_one i j]
  congr 1
  · linear_combination (-a) * htr + hdet
  · linear_combination (-b) * htr
  · linear_combination (-c) * htr
  · linear_combination (-d) * htr + hdet

end Matrices

section Main

variable {K : Type} [Field K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem pow_mulVec_single_of_fix {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι K} {t : ι}
    (h : M *ᵥ Pi.single t 1 = Pi.single t 1) (n : ℕ) :
    (M ^ n) *ᵥ Pi.single t 1 = Pi.single t 1 := by
  induction n with
  | zero => rw [pow_zero, one_mulVec]
  | succ n ih => rw [pow_succ, ← mulVec_mulVec, h, ih]

theorem scalar_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] (u : Kˣ) (v : ι → K) :
    ((Matrix.GeneralLinearGroup.scalar ι u : GL ι K) : Matrix ι ι K) *ᵥ v = (u : K) • v := by
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

theorem three_ne_zero_of_ne (hp3 : p ≠ 3) : (3 : K) ≠ 0 := by
  intro h
  have : p ∣ 3 := (CharP.cast_eq_zero_iff K p 3).1 (by exact_mod_cast h)
  exact hp3 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).1 this)

theorem psu_two_le_pRank_three_of_four_le [Finite K] (hK : Nat.card K = (p ^ f) ^ 2)
    (hf : 1 ≤ f) (hp3 : p ≠ 3) {n : ℕ} (hn : 4 ≤ n) :
    2 ≤ pRank 3 (⊤ : Subgroup (StatedProj (StatedSU n (p ^ f) K))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨α, hα⟩ := exists_trace_eq_neg_one hK hf
  have hy0 : frobQ K p f (1 - α * frobQ K p f α) = 1 - α * frobQ K p f α := by
    rw [map_sub, map_one, map_mul, frobQ_frobQ hK]
    ring
  obtain ⟨γ, hγ⟩ := exists_norm_eq hK hf hy0
  have hdet : α * frobQ K p f α - (-frobQ K p f γ) * γ = 1 := by linear_combination hγ
  have hq0 : p ^ f ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  let i3 : Fin n := ⟨3, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h23 : i2 ≠ i3 := by simp [i2, i3, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have h03 : i0 ≠ i3 := by simp [i0, i3, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  have h13 : i1 ≠ i3 := by simp [i1, i3, Fin.ext_iff]
  have hX3 := pairMatrix_cube h01 hα hdet
  have hY3 := pairMatrix_cube h23 hα hdet
  have hunit : ∀ {i j : Fin n}, i ≠ j →
      ((pairMatrix i j α (-frobQ K p f γ) γ (frobQ K p f α)).map (· ^ p ^ f))ᵀ * pairMatrix i j α (-frobQ K p f γ) γ (frobQ K p f α)
        = 1 := by
    intro i j hij
    rw [pairMatrix_map (fun x : K => x ^ p ^ f) (zero_pow hq0) (one_pow _),
      pairMatrix_transpose hij, pairMatrix_mul hij, ← pairMatrix_one i j]
    simp only [← frobQ_apply (K := K) (p := p) (f := f), map_neg, frobQ_frobQ hK]
    congr 1
    · linear_combination hγ
    · ring
    · ring
    · linear_combination hγ
  have hmem : ∀ {i j : Fin n} (hij : i ≠ j),
      glOfPowThree _ (pairMatrix_cube hij hα hdet) ∈ StatedSU n (p ^ f) K := fun {i j} hij =>
    Subgroup.subset_closure ⟨by simpa [coe_glOfPowThree, det_pairMatrix hij] using hdet,
      by simpa [coe_glOfPowThree] using hunit hij⟩
  refine CFSG.QuasithinUnique.Lin2.OddRank.two_le_pRank_statedProj (hmem h01) (hmem h23)
    (glOfPowThree_pow_three _ _) (glOfPowThree_pow_three _ _) ?_ ?_ ?_
  · exact Commute.units_val_iff.1 (pairMatrix_commute h01 h23 h02 h03 h12 h13 _ _ _ _ _ _ _ _)
  · intro hc
    obtain ⟨u, hu⟩ := hc
    have hsc : ∀ v : Fin n → K, pairMatrix i0 i1 α (-frobQ K p f γ) γ (frobQ K p f α) *ᵥ v =
        (u : K) • v := fun v => by
      have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) *ᵥ v) hu
      simpa [coe_glOfPowThree, scalar_mulVec] using this.symm
    have h2 := hsc (Pi.single i2 1)
    rw [pairMatrix_mulVec_of_ne _ _ _ _ h02.symm h12.symm] at h2
    have hu1 : (u : K) = 1 := by
      have := congrFun h2 i2
      simpa using this.symm
    have h0 := hsc (Pi.single i0 1)
    rw [pairMatrix_mulVec_left _ _ _ _ h01, hu1, one_smul] at h0
    have h1 := hsc (Pi.single i1 1)
    rw [pairMatrix_mulVec_right _ _ _ _ h01, hu1, one_smul] at h1
    have ha := congrFun h0 i0
    have hd := congrFun h1 i1
    simp [h01, h01.symm] at ha hd
    have : (3 : K) = 0 := by linear_combination hα - ha - hd
    exact three_ne_zero_of_ne hp3 this
  · intro m c hc he
    obtain ⟨u, rfl⟩ := hc
    have hfix2 : (pairMatrix i0 i1 α (-frobQ K p f γ) γ (frobQ K p f α) ^ m) *ᵥ Pi.single i2 1 =
        Pi.single i2 1 :=
      pow_mulVec_single_of_fix (pairMatrix_mulVec_of_ne _ _ _ _ h02.symm h12.symm) m
    have hfix3 : (pairMatrix i0 i1 α (-frobQ K p f γ) γ (frobQ K p f α) ^ m) *ᵥ Pi.single i3 1 =
        Pi.single i3 1 :=
      pow_mulVec_single_of_fix (pairMatrix_mulVec_of_ne _ _ _ _ h03.symm h13.symm) m
    have e2 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i2 1) he
    have e3 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i3 1) he
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, coe_glOfPowThree, ← mulVec_mulVec,
      scalar_mulVec, mulVec_smul, hfix2, hfix3] at e2 e3
    rw [pairMatrix_mulVec_left _ _ _ _ h23] at e2
    rw [pairMatrix_mulVec_right _ _ _ _ h23] at e3
    have c1 := congrFun e2 i2
    have c2 := congrFun e2 i3
    have c3 := congrFun e3 i3
    simp [h23, h23.symm] at c1 c2 c3
    have h4 : (3 : K) = 0 := by
      have hu : (u : K) = α := c1
      have hd : (u : K) = frobQ K p f α := c3
      have hg : γ = 0 := by simpa using c2.symm
      have h2 : α = frobQ K p f α := hu.symm.trans hd
      linear_combination (α + frobQ K p f α - 1) * hα - (α - frobQ K p f α) * h2 - 4 * hdet +
        4 * frobQ K p f γ * hg
    exact three_ne_zero_of_ne hp3 h4

end Main

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls
