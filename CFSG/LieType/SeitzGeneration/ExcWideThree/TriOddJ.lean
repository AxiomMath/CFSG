module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddShape
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.QPlusMain

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal
  CFSG.HardMathSupport.Seitz.TrialityOdd.Inner CFSG.RankThree.PartOne.SEITZ3
  CFSG.RankThree.PartOne.K1214 CFSG.RankThree.PartOne.SEITZ11.G2Seven
open scoped MatrixGroups

section Abstract

open CFSG.RankThree.PartOne.CTP

theorem triOdd_fixedSubgroup_conj_eq_map_centralizer {G H : Type*} [Group G] [Group H] (ε : G ≃* H) (x : G) :
    fixedSubgroup (MulAut.conj (ε x)) = (Subgroup.centralizer ({x} : Set G)).map ε.toMonoidHom := by
  ext y
  constructor
  · intro hy
    refine ⟨ε.symm y, ?_, ε.apply_symm_apply y⟩
    show ε.symm y ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply ε.injective
    have : ε x * y * (ε x)⁻¹ = y := hy
    rw [map_mul, map_mul, ε.apply_symm_apply]
    calc y * ε x = (ε x * y * (ε x)⁻¹) * ε x := by rw [this]
      _ = ε x * y := by group
  · rintro ⟨z, hz, rfl⟩
    have hz' : z ∈ Subgroup.centralizer ({x} : Set G) := hz
    rw [Subgroup.mem_centralizer_singleton_iff] at hz'
    show ε x * ε z * (ε x)⁻¹ = ε z
    have : ε z * ε x = ε x * ε z := by rw [← map_mul, ← map_mul, hz']
    rw [← this]; group


end Abstract

section Model

variable
  {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (hσ3 : ∀ c, σ (σ (σ c)) = c)

include hσ3

theorem triOdd_fixedSub_sup_slShort :
    FixedSub σ ⊔ (slShort σ.toRingHom hσ3).range = ⊤ := by
  have h := CFSG.ClassicalInvolution.G2D4Models.range_slLong_sup_range_slShort (σ := σ.toRingHom) hσ3
  rw [eq_top_iff, ← h]
  refine sup_le_sup_right ?_ _
  rintro _ ⟨A, rfl⟩
  exact slLong_mem_FixedSub σ hσ3 A

def triOddNhat : twistedGroup σ.toRingHom := nHat σ.toRingHom (ng 0) * nHat σ.toRingHom (ng 1)

theorem triOddNhat_mem_fixedSub : triOddNhat σ ∈ FixedSub σ :=
  mul_mem (nHat_zero_mem_FixedSub σ hσ3) (nHat_one_mem_FixedSub σ hσ3)

theorem triOdd_slShort_le_centralizer_conj_slLong (M : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ.toRingHom))
    (a : twistedGroup σ.toRingHom) (ha : a ∈ (slShort σ.toRingHom hσ3).range) :
    a * (triOddNhat σ * slLong σ.toRingHom hσ3 M * (triOddNhat σ)⁻¹) =
      (triOddNhat σ * slLong σ.toRingHom hσ3 M * (triOddNhat σ)⁻¹) * a := by
  set b := slLong σ.toRingHom hσ3 M
  set b₀ := triOddNhat σ * b * (triOddNhat σ)⁻¹ with hb₀
  have hb₀theta : ((b₀ : twistedGroup σ.toRingHom) : adjointGroup d4 K) ∈
      (thetaGroup : Subgroup (adjointGroup d4 K)) := by
    have e : ((b₀ : twistedGroup σ.toRingHom) : adjointGroup d4 K) =
        (nHatE K (ng 0) * nHatE K (ng 1)) * (b : adjointGroup d4 K) *
          (nHatE K (ng 0) * nHatE K (ng 1))⁻¹ := by
      have hn0 : (nHat σ.toRingHom (ng 0) : adjointGroup d4 K) = nHatE K (ng 0) := nHat_val _ _
      have hn1 : (nHat σ.toRingHom (ng 1) : adjointGroup d4 K) = nHatE K (ng 1) := nHat_val _ _
      simp only [hb₀, triOddNhat, Subgroup.coe_mul, Subgroup.coe_inv, hn0, hn1, mul_assoc, mul_inv_rev]
    rw [e]
    exact conj_mem_thetaGroup (slLong_coe_mem_central σ.toRingHom hσ3 M)
  obtain ⟨B, rfl⟩ := ha
  refine Subtype.ext ?_
  exact (commute_thetaGroup_outerRankOne hb₀theta
    (slShort_coe_mem_outer σ.toRingHom hσ3 B)).eq.symm

theorem triOdd_centralizer_sup_fixedSub_of_slLong (x : twistedGroup σ.toRingHom) (j : twistedGroup σ.toRingHom)
    (hj : j ∈ FixedSub σ) (M : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ.toRingHom))
    (hx : j * x * j⁻¹ = slLong σ.toRingHom hσ3 M) :
    Subgroup.centralizer ({x} : Set (twistedGroup σ.toRingHom)) ⊔ FixedSub σ = ⊤ := by
  set g := triOddNhat σ * j with hg
  have hgJ : g ∈ FixedSub σ := mul_mem (triOddNhat_mem_fixedSub σ hσ3) hj
  have hgx : g * x * g⁻¹ = triOddNhat σ * slLong σ.toRingHom hσ3 M * (triOddNhat σ)⁻¹ := by
    rw [hg, ← hx]; group
  have hA : (slShort σ.toRingHom hσ3).range ≤ Subgroup.centralizer ({g * x * g⁻¹} : Set _) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff, hgx]
    exact (triOdd_slShort_le_centralizer_conj_slLong σ hσ3 M a ha)
  have hAx : (slShort σ.toRingHom hσ3).range ≤
      Subgroup.centralizer ({x} : Set (twistedGroup σ.toRingHom)) ⊔ FixedSub σ := by
    intro a ha
    have h1 : g⁻¹ * a * g ∈ Subgroup.centralizer ({x} : Set _) := by
      have := hA ha
      rw [Subgroup.mem_centralizer_singleton_iff] at this ⊢
      have h2 : g⁻¹ * a * g * x = x * (g⁻¹ * a * g) := by
        calc g⁻¹ * a * g * x = g⁻¹ * (a * (g * x * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * x * g⁻¹) * a) * g := by rw [this]
          _ = x * (g⁻¹ * a * g) := by group
      exact h2
    have h3 : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
    rw [h3]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hgJ)
      (Subgroup.mem_sup_left h1)) (Subgroup.inv_mem _ (Subgroup.mem_sup_right hgJ))
  rw [eq_top_iff, ← triOdd_fixedSub_sup_slShort σ hσ3]
  exact sup_le le_sup_right hAx

end Model

section SL2

open CFSG.HardMathSupport.Seitz.TrialityOdd.Proving Polynomial Matrix

variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem triOdd_mem_range_of_quadratic (h3 : Module.finrank F K = 3) (x : K) (a b : F)
    (hx : x ^ 2 + algebraMap F K a * x + algebraMap F K b = 0) :
    x ∈ (algebraMap F K).range := by
  haveI : Module.Finite F K := Module.finite_of_finrank_pos (by omega)
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have hmon : (X ^ 2 + C a * X + C b : F[X]).Monic := by
    have : (X ^ 2 + C a * X + C b : F[X]).natDegree = 2 := by
      compute_degree!
    refine Polynomial.Monic.def.2 ?_
    simp [Polynomial.leadingCoeff, this]
  have hroot : aeval x (X ^ 2 + C a * X + C b : F[X]) = 0 := by simpa using hx
  have hle : (minpoly F x).degree ≤ (X ^ 2 + C a * X + C b : F[X]).degree := minpoly.min F x hmon hroot
  have hdeg2 : (X ^ 2 + C a * X + C b : F[X]).natDegree = 2 := by compute_degree!
  have hle' : (minpoly F x).natDegree ≤ 2 := by
    have := Polynomial.natDegree_le_natDegree hle
    omega
  have hdvd : (minpoly F x).natDegree ∣ 3 := by
    rw [← IntermediateField.adjoin.finrank hint, ← h3]
    exact Module.finrank_dvd_finrank_right (F := F) (K := (IntermediateField.adjoin F {x} : IntermediateField F K))
      (A := K)
  have hpos : 0 < (minpoly F x).natDegree := minpoly.natDegree_pos hint
  have h1 : (minpoly F x).natDegree = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact h
    · omega
  exact (minpoly.natDegree_eq_one_iff).1 h1


theorem triOdd_trace_eq_neg_one_of_pow_three {R : Type} [Field R] (L : SpecialLinearGroup (Fin 2) R)
    (hL3 : L ^ 3 = 1) (hL1 : L ≠ 1) :
    (L : Matrix (Fin 2) (Fin 2) R) 0 0 + (L : Matrix (Fin 2) (Fin 2) R) 1 1 = -1 := by
  have hdet : (L : Matrix (Fin 2) (Fin 2) R).det = 1 := L.2
  set T := (L : Matrix (Fin 2) (Fin 2) R) 0 0 + (L : Matrix (Fin 2) (Fin 2) R) 1 1 with hT
  have hCH : (L : Matrix (Fin 2) (Fin 2) R) * (L : Matrix (Fin 2) (Fin 2) R) =
      T • (L : Matrix (Fin 2) (Fin 2) R) - 1 := by
    rw [Matrix.det_fin_two] at hdet
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hT, Matrix.one_apply] <;>
      first | ring1 | linear_combination (-1 : R) * hdet
  have h3 : (L : Matrix (Fin 2) (Fin 2) R) * ((L : Matrix (Fin 2) (Fin 2) R) *
      (L : Matrix (Fin 2) (Fin 2) R)) = 1 := by
    have := congrArg (fun M : SpecialLinearGroup (Fin 2) R => (M : Matrix (Fin 2) (Fin 2) R)) hL3
    simpa [pow_succ, mul_assoc] using this
  rw [hCH, Matrix.mul_sub, Matrix.mul_smul, hCH, Matrix.mul_one] at h3
  have hkey : (T ^ 2 - 1) • (L : Matrix (Fin 2) (Fin 2) R) = (1 + T) • (1 : Matrix (Fin 2) (Fin 2) R) := by
    have : T • (T • (L : Matrix (Fin 2) (Fin 2) R) - 1) - (L : Matrix (Fin 2) (Fin 2) R) = 1 := h3
    ext i j
    have := congrFun (congrFun this i) j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] at this ⊢
    split_ifs at this ⊢ <;> linear_combination this
  by_cases hT2 : T ^ 2 - 1 = 0
  · have h1T : (1 + T) = 0 := by
      have := congrFun (congrFun hkey 0) 0
      simp [hT2] at this
      linear_combination (-1 : R) * this
    linear_combination h1T
  · exfalso
    have hscal : (L : Matrix (Fin 2) (Fin 2) R) = ((1 + T) / (T ^ 2 - 1)) • (1 : Matrix (Fin 2) (Fin 2) R) := by
      have := congrArg (fun M => (T ^ 2 - 1)⁻¹ • M) hkey
      simp only [smul_smul, inv_mul_cancel₀ hT2, one_smul] at this
      rw [this, div_eq_mul_inv, mul_comm]
    set c := (1 + T) / (T ^ 2 - 1) with hc
    have hc2 : c ^ 2 = 1 := by
      have : (L : Matrix (Fin 2) (Fin 2) R).det = c ^ 2 := by
        rw [hscal]; simp [Matrix.det_fin_two, sq]
      rw [← this]; exact hdet
    have hc3 : c ^ 3 = 1 := by
      have h' := congrArg (fun M : SpecialLinearGroup (Fin 2) R => (M : Matrix (Fin 2) (Fin 2) R) 0 0) hL3
      have hL' : (L : Matrix (Fin 2) (Fin 2) R) 0 0 = c := by rw [hscal]; simp
      have h30 : ((L ^ 3 : SpecialLinearGroup (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
          (L : Matrix (Fin 2) (Fin 2) R) * ((L : Matrix (Fin 2) (Fin 2) R) * (L : Matrix (Fin 2) (Fin 2) R)) := by
        simp [pow_succ, mul_assoc]
      simp only [h30, hscal] at h'
      simpa [pow_succ, mul_assoc, Matrix.smul_apply] using h'
    have hc1 : c = 1 := by
      have : c = c ^ 3 / c ^ 2 := by
        have hc0 : c ≠ 0 := by rintro h0; rw [h0] at hc2; simp at hc2
        field_simp
      rw [this, hc3, hc2]; simp
    apply hL1
    apply Subtype.ext
    rw [hscal, hc1]; simp


theorem triOdd_exists_comm_not_mem_sl2Range (h3 : Module.finrank F K = 3)
    (L : SpecialLinearGroup (Fin 2) K) (hL : L ∈ sl2Range F K) (hL3 : L ^ 3 = 1) (hL1 : L ≠ 1) :
    ∃ t : SpecialLinearGroup (Fin 2) K, t * L = L * t ∧ t ∉ sl2Range F K := by
  classical
  haveI : Module.Finite F K := Module.finite_of_finrank_pos (by omega)
  obtain ⟨L', hL'⟩ := hL
  have htr := triOdd_trace_eq_neg_one_of_pow_three L hL3 hL1
  have hdet : (L : Matrix (Fin 2) (Fin 2) K).det = 1 := L.2
  have hent : ∀ i j, (L : Matrix (Fin 2) (Fin 2) K) i j = algebraMap F K (L' i j) := by
    intro i j
    rw [← hL', SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  obtain ⟨m, hm⟩ : ∃ m : K, m ∉ (algebraMap F K).range := by
    by_contra hcon
    push Not at hcon
    have hbt : (⊥ : Subalgebra F K) = ⊤ := by
      ext x
      simp only [Algebra.mem_bot, Algebra.mem_top, iff_true]
      exact hcon x
    have := (Subalgebra.bot_eq_top_iff_finrank_eq_one).1 hbt
    omega
  have hD : m ^ 2 - m + 1 ≠ 0 := by
    intro h0
    apply hm
    refine triOdd_mem_range_of_quadratic h3 m (-1) 1 ?_
    simp only [map_neg, map_one]
    linear_combination h0
  set D := m ^ 2 - m + 1 with hDdef
  set x : K := (m ^ 2 - 1) / D with hx
  set y : K := m * (m - 2) / D with hy
  have hxy : x ^ 2 - x * y + y ^ 2 = 1 := by
    rw [hx, hy]; field_simp; ring
  have hdett : (x • (1 : Matrix (Fin 2) (Fin 2) K) + y • (L : Matrix (Fin 2) (Fin 2) K)).det = 1 := by
    rw [Matrix.det_fin_two] at hdet ⊢
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq, mul_zero, add_zero, mul_one, zero_add]
    linear_combination hxy + (y ^ 2) * hdet + (x * y) * htr
  refine ⟨⟨x • (1 : Matrix (Fin 2) (Fin 2) K) + y • (L : Matrix (Fin 2) (Fin 2) K), hdett⟩, ?_, ?_⟩
  · apply Subtype.ext
    show (x • (1 : Matrix (Fin 2) (Fin 2) K) + y • (L : Matrix (Fin 2) (Fin 2) K)) *
        (L : Matrix (Fin 2) (Fin 2) K) = (L : Matrix (Fin 2) (Fin 2) K) *
        (x • (1 : Matrix (Fin 2) (Fin 2) K) + y • (L : Matrix (Fin 2) (Fin 2) K))
    rw [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul]
  ·
    have hy_not : ¬ ∃ y' : F, algebraMap F K y' = y := by
      rintro ⟨y', hy'⟩
      apply hm
      have hyD : y * D = m * (m - 2) := by rw [hy]; field_simp
      by_cases h1 : (1 : F) - y' = 0
      · have hy1 : y' = 1 := by linear_combination -h1
        subst hy1
        rw [map_one] at hy'
        have : m = algebraMap F K (-1) := by
          rw [← hy'] at hyD
          rw [map_neg, map_one]
          rw [hDdef] at hyD
          linear_combination hyD
        exact ⟨-1, this.symm⟩
      · refine triOdd_mem_range_of_quadratic h3 m ((y' - 2) / (1 - y')) (-y' / (1 - y')) ?_
        have h1K : (1 : K) - y ≠ 0 := by
          intro h0
          apply h1
          have : algebraMap F K (1 - y') = 0 := by rw [map_sub, map_one, hy']; exact h0
          exact (map_eq_zero_iff _ (algebraMap F K).injective).1 this
        simp only [map_div₀, map_sub, map_neg, map_one, hy', map_ofNat]
        rw [hDdef] at hyD
        field_simp
        linear_combination (-1 : K) * hyD
    rintro ⟨t', ht'⟩
    have htent : ∀ i j, (x • (1 : Matrix (Fin 2) (Fin 2) K) + y • (L : Matrix (Fin 2) (Fin 2) K)) i j =
        algebraMap F K (t' i j) := by
      intro i j
      have := congrArg (fun M : SpecialLinearGroup (Fin 2) K => (M : Matrix (Fin 2) (Fin 2) K) i j) ht'
      simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at this
      exact this.symm
    apply hy_not
    have e01 := htent 0 1
    have e10 := htent 1 0
    have e00 := htent 0 0
    have e11 := htent 1 1
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, hent, Fin.isValue,
      ↓reduceIte, Fin.reduceEq, mul_zero, add_zero, zero_add, mul_one] at e01 e10 e00 e11
    by_cases hb : L' 0 1 = 0
    · by_cases hc : L' 1 0 = 0
      ·
        have hdetF : L' 0 0 * L' 1 1 = 1 := by
          have h := L'.2
          rw [Matrix.det_fin_two] at h
          simp only [hb, hc, mul_zero, sub_zero] at h
          exact h
        have htrF : L' 0 0 + L' 1 1 = -1 := by
          apply (algebraMap F K).injective
          rw [map_add, map_neg, map_one, ← hent, ← hent]
          exact htr
        have had : L' 0 0 ≠ L' 1 1 := by
          intro had
          rw [← had] at hdetF htrF
          have h1 : (L' 0 0 - 1) * (L' 0 0 + 1) = 0 := by linear_combination hdetF
          rcases mul_eq_zero.1 h1 with h | h
          · have ha : L' 0 0 = 1 := by linear_combination h
            apply hL1
            apply Subtype.ext
            ext i j
            rw [hent]
            fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, ← had]
          · have ha : L' 0 0 = -1 := by linear_combination h
            rw [ha] at htrF
            have : (1 : F) = 0 := by linear_combination (-1 : F) * htrF
            exact one_ne_zero this
        refine ⟨(t' 0 0 - t' 1 1) / (L' 0 0 - L' 1 1), ?_⟩
        have hne : algebraMap F K (L' 0 0) - algebraMap F K (L' 1 1) ≠ 0 := by
          intro h0
          apply had
          apply (algebraMap F K).injective
          linear_combination h0
        rw [map_div₀, map_sub, map_sub, ← e00, ← e11]
        field_simp
        ring
      · refine ⟨t' 1 0 / L' 1 0, ?_⟩
        rw [map_div₀, ← e10]
        have : algebraMap F K (L' 1 0) ≠ 0 := by
          intro h0; exact hc ((map_eq_zero_iff _ (algebraMap F K).injective).1 h0)
        field_simp
    · refine ⟨t' 0 1 / L' 0 1, ?_⟩
      rw [map_div₀, ← e01]
      have : algebraMap F K (L' 0 1) ≠ 0 := by
        intro h0; exact hb ((map_eq_zero_iff _ (algebraMap F K).injective).1 h0)
      field_simp

end SL2

section ThreeA

open CFSG.HardMathSupport.Seitz.TrialityOdd.Proving Matrix

variable
  {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (hσ3 : ∀ c, σ (σ (σ c)) = c)

include hσ3 in
theorem triOdd_centralizer_sup_fixedSub_of_slShort (hK2 : ringChar K ≠ 2)
    (h3 : Module.finrank (fixedField σ.toRingHom) K = 3)
    (hF5 : 5 ≤ Nat.card (fixedField σ.toRingHom))
    (M : SpecialLinearGroup (Fin 2) (fixedField σ.toRingHom))
    (hM3 : M ^ 3 = 1) (hM1 : M ≠ 1) :
    Subgroup.centralizer ({(slShort σ.toRingHom hσ3
        (SpecialLinearGroup.map (fixedField σ.toRingHom).subtype M))} :
          Set (twistedGroup σ.toRingHom)) ⊔ FixedSub σ = ⊤ := by
  classical
  set L : SpecialLinearGroup (Fin 2) K := SpecialLinearGroup.map (fixedField σ.toRingHom).subtype M with hLdef
  set N := Subgroup.centralizer ({(slShort σ.toRingHom hσ3 L)} : Set (twistedGroup σ.toRingHom)) ⊔
    FixedSub σ with hN
  have hLM : L ∈ sl2Range (fixedField σ.toRingHom) K := ⟨M, rfl⟩
  have hL3 : L ^ 3 = 1 := by
    rw [hLdef, ← map_pow (SpecialLinearGroup.map (fixedField σ.toRingHom).subtype) M 3, hM3, map_one]
  have hL1 : L ≠ 1 := by
    intro h
    apply hM1
    apply sl_map_injective (fixedField σ.toRingHom).subtype
    rw [← hLdef, h, map_one]
  have hfix : ∀ M'' : SpecialLinearGroup (Fin 2) (fixedField σ.toRingHom),
      SpecialLinearGroup.map σ.toRingHom (SpecialLinearGroup.map (algebraMap (fixedField σ.toRingHom) K) M'') =
        SpecialLinearGroup.map (algebraMap (fixedField σ.toRingHom) K) M'' := by
    intro M''
    refine Subtype.ext ?_
    ext i j
    simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact (M''.1 i j).2
  have hHM : sl2Range (fixedField σ.toRingHom) K ≤ N.comap (slShort σ.toRingHom hσ3) := by
    rintro M' ⟨M'', rfl⟩
    show slShort σ.toRingHom hσ3 _ ∈ N
    exact Subgroup.mem_sup_right (slShort_mem_FixedSub σ hσ3 _ (hfix M''))
  obtain ⟨t, htL, htn⟩ := triOdd_exists_comm_not_mem_sl2Range h3 L hLM hL3 hL1
  have ht : t ∈ N.comap (slShort σ.toRingHom hσ3) := by
    show slShort σ.toRingHom hσ3 t ∈ N
    refine Subgroup.mem_sup_left ?_
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, htL]
  have htop := sl2_range_maximal h3 hK2 hF5 (N.comap (slShort σ.toRingHom hσ3)) hHM ht htn
  have hrange : (slShort σ.toRingHom hσ3).range ≤ N := by
    rintro _ ⟨A, rfl⟩
    have : A ∈ N.comap (slShort σ.toRingHom hσ3) := htop ▸ Subgroup.mem_top A
    exact this
  rw [eq_top_iff, ← triOdd_fixedSub_sup_slShort σ hσ3]
  exact sup_le le_sup_right hrange


include hσ3 in
@[expose] def TriOddJClassSplit : Prop :=
  ringChar K ≠ 2 → 5 ≤ Nat.card (fixedField σ.toRingHom) →
    Module.finrank (fixedField σ.toRingHom) K = 3 →
    ∀ x ∈ FixedSub σ, x ^ 3 = 1 → x ≠ 1 →
      ∃ j ∈ FixedSub σ,
        (∃ M : SpecialLinearGroup (Fin 2) (fixedField σ.toRingHom),
          j * x * j⁻¹ = slLong σ.toRingHom hσ3 M) ∨
        (∃ M : SpecialLinearGroup (Fin 2) (fixedField σ.toRingHom),
          j * x * j⁻¹ = slShort σ.toRingHom hσ3
            (SpecialLinearGroup.map (fixedField σ.toRingHom).subtype M))

theorem triOdd_sup_centralizer_eq_top_of_conj {G : Type*} [Group G] (J : Subgroup G) (x j : G)
    (hj : j ∈ J) (h : Subgroup.centralizer ({j * x * j⁻¹} : Set G) ⊔ J = ⊤) :
    Subgroup.centralizer ({x} : Set G) ⊔ J = ⊤ := by
  rw [eq_top_iff, ← h]
  refine sup_le (fun g hg => ?_) le_sup_right
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  have h1 : j⁻¹ * g * j ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : j⁻¹ * g * j * x = x * (j⁻¹ * g * j) := by
      calc j⁻¹ * g * j * x = j⁻¹ * (g * (j * x * j⁻¹)) * j := by group
        _ = j⁻¹ * ((j * x * j⁻¹) * g) * j := by rw [hg]
        _ = x * (j⁻¹ * g * j) := by group
    exact this
  have h2 : g = j * (j⁻¹ * g * j) * j⁻¹ := by group
  rw [h2]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hj)
    (Subgroup.mem_sup_left h1)) (Subgroup.inv_mem _ (Subgroup.mem_sup_right hj))

include hσ3 in
theorem triOdd_centralizer_sup_fixedSub_of_split (hS : TriOddJClassSplit σ hσ3) (hK2 : ringChar K ≠ 2)
    (hF5 : 5 ≤ Nat.card (fixedField σ.toRingHom))
    (h3 : Module.finrank (fixedField σ.toRingHom) K = 3)
    (x : twistedGroup σ.toRingHom) (hxJ : x ∈ FixedSub σ) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set (twistedGroup σ.toRingHom)) ⊔ FixedSub σ = ⊤ := by
  obtain ⟨j, hj, hcase⟩ := hS hK2 hF5 h3 x hxJ hx3 hx1
  rcases hcase with ⟨M, hM⟩ | ⟨M, hM⟩
  · exact triOdd_centralizer_sup_fixedSub_of_slLong σ hσ3 x j hj M hM
  · refine triOdd_sup_centralizer_eq_top_of_conj _ x j hj ?_
    have hx'3 : (j * x * j⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3]; group
    have hx'1 : j * x * j⁻¹ ≠ 1 := fun h => hx1 (by
      have : x = j⁻¹ * (j * x * j⁻¹) * j := by group
      rw [this, h]; group)
    rw [hM] at hx'3 hx'1 ⊢
    have hM3 : M ^ 3 = 1 := by
      have h1 : slShort σ.toRingHom hσ3
          (SpecialLinearGroup.map (fixedField σ.toRingHom).subtype (M ^ 3)) = 1 := by
        rw [map_pow, map_pow]; exact hx'3
      have h2 := slShort_injective hσ3 (h1.trans (map_one _).symm)
      exact sl_map_injective _ (h2.trans (map_one _).symm)
    have hM1 : M ≠ 1 := fun h => hx'1 (by rw [h, map_one, map_one])
    exact triOdd_centralizer_sup_fixedSub_of_slShort σ hσ3 hK2 h3 hF5 M hM3 hM1

end ThreeA

section Transport

open CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.RankThree.PartOne.CTP CFSG.LieType.SeitzGeneration
  CFSG.RankThree.PartTwo.Sec19 CFSG.ClassicalInvolution.G2D4Models

variable
  {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (hσ3 : ∀ c, σ (σ (σ c)) = c)

omit hσ3 in
@[expose] def triOddEqRoot (hK2 : ringChar K ≠ 2) {q : ℕ} (hq : 2 ≤ q)
    (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q) :
    twistedGroup σ.toRingHom ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
  MulEquiv.ofBijective
    ((twistedIncl σ.toRingHom).codRestrict (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      (fun z => twistedIncl_mem_root σ hK2 hq hK hσq z))
    ⟨fun a b h => by
      have h1 : twistedIncl σ.toRingHom a = twistedIncl σ.toRingHom b :=
        congrArg (Subtype.val : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →
          ModGL TwistTag.D4.tag K) h
      exact CFSG.ClassicalInvolution.G2D4Models.twistedIncl_injective σ.toRingHom h1, by
      rintro ⟨g, hg⟩
      have h := CFSG.LieType.Steinberg.CentralExt.TrialityClosed.map_twistedGroup_eq_graphFixedRootGroup
        (σ := σ.toRingHom) hK2 hq hK hσq
      rw [← h] at hg
      obtain ⟨a, ha, rfl⟩ := hg
      exact ⟨⟨a, ha⟩, rfl⟩⟩

theorem triOddEqRoot_coe (hK2 : ringChar K ≠ 2) {q : ℕ} (hq : 2 ≤ q)
    (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q) (z : twistedGroup σ.toRingHom) :
    ((triOddEqRoot σ hK2 hq hK hσq z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) = twistedIncl σ.toRingHom z := rfl

include hσ3 in
theorem triOdd_fixedSubgroup_tau_eq_map (hK2 : ringChar K ≠ 2) {q : ℕ} (hq : 2 ≤ q)
    (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q) :
    fixedSubgroup (tauAut σ) =
      (FixedSub σ).map (triOddEqRoot σ hK2 hq hK hσq).toMonoidHom := by
  ext y
  set ε := triOddEqRoot σ hK2 hq hK hσq with hε
  have hcoe : ∀ z, ((ε z : C0 σ) : ModGL TwistTag.D4.tag K) = twistedIncl σ.toRingHom z :=
    fun z => rfl
  constructor
  · intro hy
    refine ⟨ε.symm y, ?_, ε.apply_symm_apply y⟩
    have h1 : ((ε (ε.symm y) : C0 σ) : ModGL TwistTag.D4.tag K) ∈ trialityFieldImage σ σ := by
      rw [ε.apply_symm_apply]
      exact (d4_mem_trialityFieldImage_self_iff σ hσ3 y).2 hy
    rw [hcoe] at h1
    exact (mem_J_iff σ hK2 hq hK hσq hσ3 _).1 h1
  · rintro ⟨z, hz, rfl⟩
    show tauAut σ (ε z) = ε z
    refine (d4_mem_trialityFieldImage_self_iff σ hσ3 (ε z)).1 ?_
    rw [hcoe]
    exact (mem_J_iff σ hK2 hq hK hσq hσ3 z).2 hz

end Transport

section Main

open CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.RankThree.PartOne.CTP CFSG.LieType.SeitzGeneration
  CFSG.RankThree.PartTwo.Sec19 CFSG.ClassicalInvolution.G2D4Models CFSG.Fischer
  CFSG.LocalAnalysis.ComponentInitial


@[expose] def TriOddJClassSplitAll : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (hσ3 : ∀ c, σ (σ (σ c)) = c) {q : ℕ},
    ringChar K ≠ 3 → 4 ≤ q → Nat.card K = q ^ 3 → (∀ c, σ c = c ^ q) →
      TriOddJClassSplit σ hσ3

theorem triOdd_fixedSubgroup_sup_tau_of_split (hS : TriOddJClassSplitAll) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (x₀ : C0 σ) (hx3 : x₀ ^ 3 = 1) (hx1 : x₀ ≠ 1) (hτx : tauAut σ x₀ = x₀) :
    fixedSubgroup (MulAut.conj x₀) ⊔ fixedSubgroup (tauAut σ) = ⊤ := by
  classical
  have hq2 : 2 ≤ ℓ ^ f := by
    calc 2 ≤ ℓ := hℓ.two_le
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf
  have hℓ5 : 5 ≤ ℓ := by
    have h2 := hℓ.two_le
    rcases (by omega : ℓ = 2 ∨ ℓ = 3 ∨ ℓ = 4 ∨ 5 ≤ ℓ) with h | h | h | h
    · exact absurd h hℓ2
    · exact absurd h hℓ3
    · subst h; exact absurd hℓ (by norm_num)
    · exact h
  have hq5 : 5 ≤ ℓ ^ f := le_trans hℓ5 (by
    calc ℓ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf)
  have hK' : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul]; ring_nf
  haveI : CharP K ℓ := finite_field_prime_power_characteristic hℓ (k := 3 * f) (by omega) hK'
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have hσ3 : ∀ c, σ (σ (σ c)) = c := CFSG.LieType.Steinberg.TwistedD4.sigma_three_of_card
    (σ := σ.toRingHom) hK hσ
  have hF : Nat.card (fixedField σ.toRingHom) = ℓ ^ f :=
    CFSG.GH74.GLS.Stage4.Hex.card_fixedField_of_cube σ.toRingHom hq2 hK hσ
  have h3 : Module.finrank (fixedField σ.toRingHom) K = 3 := by
    haveI : Module.Finite (fixedField σ.toRingHom) K := Module.Finite.of_finite
    have h := Module.natCard_eq_pow_finrank (K := fixedField σ.toRingHom) (V := K)
    rw [hK, hF] at h
    exact Nat.pow_right_injective hq2 h.symm
  set ε := triOddEqRoot σ hK2 hq2 hK hσ with hε
  set x := ε.symm x₀ with hx
  have hfixτ := triOdd_fixedSubgroup_tau_eq_map σ hσ3 hK2 hq2 hK hσ
  have hxJ : x ∈ FixedSub σ := by
    have h0 : x₀ ∈ fixedSubgroup (tauAut σ) := hτx
    rw [hfixτ] at h0
    obtain ⟨z, hz, hzx⟩ := h0
    have hzx' : z = x := ε.injective (hzx.trans (ε.apply_symm_apply x₀).symm)
    rwa [hzx'] at hz
  have hx3' : x ^ 3 = 1 := by
    apply ε.injective
    rw [map_pow, hx, ε.apply_symm_apply, hx3, map_one]
  have hx1' : x ≠ 1 := by
    intro h
    apply hx1
    rw [← ε.apply_symm_apply x₀, ← hx, h, map_one]
  have hK3 : ringChar K ≠ 3 := by rw [ringChar.eq K ℓ]; exact hℓ3
  have hsup := triOdd_centralizer_sup_fixedSub_of_split σ hσ3
    (hS K σ hσ3 hK3 (by omega : 4 ≤ ℓ ^ f) hK hσ) hK2 (hF ▸ hq5) h3 x hxJ hx3' hx1'
  have hconj : fixedSubgroup (MulAut.conj x₀) =
      (Subgroup.centralizer ({x} : Set (twistedGroup σ.toRingHom))).map ε.toMonoidHom := by
    have := triOdd_fixedSubgroup_conj_eq_map_centralizer ε x
    rwa [hx, ε.apply_symm_apply] at this
  rw [hconj, hfixτ, ← Subgroup.map_sup, hsup, Subgroup.map_top]
  exact MonoidHom.range_eq_top.2 ε.surjective

theorem triOddJPlanes_of_split (hS : TriOddJClassSplitAll) : TriOddJPlanes := by
  classical
  intro ℓ f hℓ hℓ2 hℓ3 hf K _ _ hK σ hσ x₀ hx3 hx1 hτx
  have hW := triOdd_fixedSubgroup_sup_tau_of_split hS hℓ hℓ2 hℓ3 hf hK σ hσ x₀ hx3 hx1 hτx
  obtain ⟨-, -, -, -, -, -, hZ, -⟩ := odd_triality_exact_automorphism_normal_form hℓ hℓ2 hf K hK σ hσ
  have hτin := triOdd_tauAut_not_mem_innerAut σ hℓ hℓ2 hf hK hσ
  set E := Subgroup.closure ({MulAut.conj x₀, tauAut σ} : Set (MulAut (C0 σ))) with hE
  have hcx : MulAut.conj x₀ ∈ E := Subgroup.subset_closure (by simp)
  have hτE : tauAut σ ∈ E := Subgroup.subset_closure (by simp)
  have hcx1 : (MulAut.conj x₀ : MulAut (C0 σ)) ≠ 1 := fun h =>
    hx1 (nf1_conj_injective hZ (h.trans (map_one MulAut.conj).symm))
  have hτ1 : tauAut σ ≠ 1 := fun h => hτin (h ▸ one_mem _)
  have hc1 : fixedSubgroup (MulAut.conj x₀) ≤ Subgroup.closure (fixUnion E) := fun y hy =>
    Subgroup.subset_closure (fixedSubgroup_subset_fixUnion hcx hcx1 hy)
  have hc2 : fixedSubgroup (tauAut σ) ≤ Subgroup.closure (fixUnion E) := fun y hy =>
    Subgroup.subset_closure (fixedSubgroup_subset_fixUnion hτE hτ1 hy)
  rw [eq_top_iff, ← hW]
  exact sup_le hc1 hc2

end Main

end CFSG.LieType.SeitzGeneration.ExcWideThree
