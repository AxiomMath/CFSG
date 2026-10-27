module

public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.Transvection
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.PGlue
public import CFSG.HardMathSupport.Lang.Proving.CubeNormOne
public import CFSG.RankThree.PartOne.KF.UnitaryDiag
public import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylowInner

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem prime_ne_three_of_dvd (hp : p.Prime) (hf : 1 ≤ f) (h3 : 3 ∣ p ^ f + 1) : p ≠ 3 := by
  rintro rfl
  have h1 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
  have : 3 ∣ 1 := (Nat.dvd_add_right h1).1 h3
  omega

theorem exists_ne_eq_of_pow_three (hn : 3 ≤ n) (d : Fin n → K)
    (hd : ∀ i, d i ^ 3 = 1) (hdet : n = 3 → ∏ i, d i ≠ 1) : ∃ i j, i ≠ j ∧ d i = d j := by
  classical
  by_contra hcon
  have hinj : Function.Injective d := fun i j hij => by
    by_contra hne
    exact hcon ⟨i, j, hne, hij⟩
  have hcard : n ≤ 3 := by
    have hsub : ∀ i ∈ (Finset.univ : Finset (Fin n)), d i ∈ Polynomial.nthRootsFinset 3 (1 : K) :=
      fun i _ => (Polynomial.mem_nthRootsFinset (by norm_num) 1).2 (hd i)
    have := Finset.card_le_card_of_injOn d hsub (hinj.injOn)
    rw [Finset.card_univ, Fintype.card_fin] at this
    refine this.trans ?_
    rw [Polynomial.nthRootsFinset_def]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
  obtain rfl : n = 3 := le_antisymm hcard hn
  have hprod := hdet rfl
  apply hprod
  rw [Fin.prod_univ_three]
  have n01 : d 0 ≠ d 1 := fun h => by simpa using hinj h
  have n02 : d 0 ≠ d 2 := fun h => by simpa using hinj h
  have n12 : d 1 ≠ d 2 := fun h => by simpa using hinj h
  have h01 : d 0 ^ 2 + d 0 * d 1 + d 1 ^ 2 = 0 :=
    mul_left_cancel₀ (sub_ne_zero.2 n01) (by linear_combination hd 0 - hd 1)
  have h02 : d 0 ^ 2 + d 0 * d 2 + d 2 ^ 2 = 0 :=
    mul_left_cancel₀ (sub_ne_zero.2 n02) (by linear_combination hd 0 - hd 2)
  have hs : d 0 + d 1 + d 2 = 0 :=
    mul_left_cancel₀ (sub_ne_zero.2 n12) (by linear_combination h01 - h02)
  have : d 2 = -d 0 - d 1 := by linear_combination hs
  rw [this]
  linear_combination (-d 0) * h01 + hd 0

@[expose] def planeVec (i j : Fin n) (ε : K) : Fin n → K := Pi.single i 1 + ε • Pi.single j 1

theorem hpair_planeVec (h : UnitaryFieldData p f K) {i j : Fin n} (hij : i ≠ j) (ε ε' : K) :
    hpair h (planeVec i j ε) (planeVec i j ε') = 1 + h.bar ε * ε' := by
  simp [hpair, planeVec, Pi.single_apply, mul_add, add_mul, hij, hij.symm, Finset.sum_add_distrib]

theorem transvMat_smul_vec (h : UnitaryFieldData p f K) (e : Fin n → K) (β ζ : K) :
    transvMat h (ζ • e) β = transvMat h e (β * (h.bar ζ * ζ)) := by
  ext i j
  simp only [transvMat, Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply,
    smul_eq_mul, map_mul]
  ring

theorem transvGL_mem_gramSU (h : UnitaryFieldData p f K) {e : Fin n → K} (he : hpair h e e = 0)
    {β : K} (hβ : β + h.bar β = 0) :
    transvGL he β ∈ gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  refine ⟨?_, det_transvMat he β⟩
  have := transvMat_unitary he hβ
  simpa [coe_transvGL] using this

theorem commute_transvGL (h : UnitaryFieldData p f K)
    (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    {e : Fin n → K} (he : hpair h e e = 0) (β ζ : K) (hζ : h.bar ζ * ζ = 1)
    (hAe : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ e = ζ • e) :
    (A : GL (Fin n) K) * transvGL he β = transvGL he β * (A : GL (Fin n) K) := by
  have hA : (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    have := mem_primeFormUnitary.1 A.2
    simpa using this
  have hAA : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (((A : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hA' : (((A : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have key := conj_transvMat (h := h) hA hAA e β
  rw [hAe, transvMat_smul_vec, hζ, mul_one] at key
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_transvGL]
  calc _ = ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * transvMat h e β *
        (((A : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        simp only [Matrix.mul_assoc, hA', Matrix.mul_one]
    _ = _ := by rw [key]

theorem hasFixedThreePair_of_eigen (h : UnitaryFieldData p f K) (hp3 : p ≠ 3) (hn : 3 ≤ n)
    (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    {e e' : Fin n → K} (he : hpair h e e = 0) (he' : hpair h e' e' = 0)
    (hc : hpair h e e' ≠ 0) (ζ : K) (hζ : h.bar ζ * ζ = 1)
    (hAe : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ e = ζ • e)
    (hAe' : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ e' = ζ • e') :
    HasFixedThreePair
      (primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) A) := by
  have hchar := h.charP
  have h3 : (3 : K) ≠ 0 := by
    intro h0
    have : ((3 : ℕ) : K) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff K p] at this
    exact hp3 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).1 this)
  set c := hpair h e e' with hcdef
  have hbc : h.bar c ≠ 0 := (map_ne_zero h.bar).2 hc
  obtain ⟨c0, hc0⟩ := h.exists_bar_ne
  set τ : K := c0 - h.bar c0 with hτ
  have hτ0 : τ ≠ 0 := fun h0 => hc0 (by rw [hτ, sub_eq_zero] at h0; exact h0.symm)
  have hbτ : h.bar τ = -τ := by
    rw [hτ, map_sub, h.bar_bar]; ring
  have hN : c * h.bar c ≠ 0 := mul_ne_zero hc hbc
  have hbN : h.bar (c * h.bar c) = c * h.bar c := by
    rw [map_mul, h.bar_bar, mul_comm]
  set β' : K := -3 / (τ * (c * h.bar c)) with hβ'
  have hβτ : τ + h.bar τ = 0 := by rw [hbτ]; ring
  have hβ'1 : β' + h.bar β' = 0 := by
    have hb3 : h.bar (3 : K) = 3 := map_ofNat h.bar 3
    rw [hβ', map_div₀, map_neg, hb3, map_mul, hbτ, hbN]
    field_simp
    ring
  have hββ : τ * β' * (c * h.bar c) = -3 := by
    rw [hβ']
    field_simp
  have hx := transvGL_mem_gramSU h he hβτ
  have hy := transvGL_mem_gramSU h he' hβ'1
  let x : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := ⟨_, hx⟩
  let y : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := ⟨_, hy⟩
  have hcop : (Nat.Coprime p 3) := (Nat.coprime_primes h.prime Nat.prime_three).2 hp3
  have hxp : ((x : GL (Fin n) K)) ^ p = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val]; exact transvMat_pow_char he τ)
  have hyp : ((y : GL (Fin n) K)) ^ p = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val]; exact transvMat_pow_char he' β')
  refine ⟨(x : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)),
    (y : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)), ?_, ?_, ?_, ?_, ?_⟩
  · exact fixed_conjHom_of_commute h A x (commute_transvGL h A he τ ζ hζ hAe)
  · exact fixed_conjHom_of_commute h A y (commute_transvGL h A he' β' ζ hζ hAe')
  · exact Nat.Coprime.coprime_dvd_left (orderOf_mk_dvd h x p hxp) hcop
  · exact Nat.Coprime.coprime_dvd_left (orderOf_mk_dvd h y p hyp) hcop
  · rw [← QuotientGroup.mk_mul]
    refine orderOf_mk_eq_three h (x * y) ?_ ?_
    · apply Units.ext
      exact (Units.val_pow_eq_pow_val _ _).trans (transvMat_pair_cube he he' hc hββ)
    · intro s
      exact transvMat_pair_not_scalar he he' hc hββ h3 hn s

theorem hasFixedThreePair_diag_of_pow_three (h : UnitaryFieldData p f K) (h3 : 3 ∣ p ^ f + 1)
    (hn : 3 ≤ n)
    (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hA : (A : GL (Fin n) K) ^ 3 = 1)
    (hdet : n = 3 → ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det ≠ 1) :
    HasFixedThreePair
      (primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) A) := by
  classical
  have hp3 : p ≠ 3 := prime_ne_three_of_dvd h.prime h.one_le h3
  have hA3 : A ^ 3 = 1 := Subtype.ext (by simpa using hA)
  obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag h (n := n)
    Nat.prime_three h3 (Subgroup.zpowers A)
    (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact (Commute.zpow_zpow_self A a b).eq)
    (by
      rintro _ ⟨a, rfl⟩
      show (A ^ a) ^ 3 = 1
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hA3,
        _root_.one_zpow])
  have hD := hP A (Subgroup.mem_zpowers A)
  set Q : GL (Fin n) K := (P : GL (Fin n) K) with hQ
  set Aq : GL (Fin n) K := (A : GL (Fin n) K) with hAq
  set g : GL (Fin n) K := Q⁻¹ * Aq * Q with hg
  have hD' : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag := hD
  set M : Matrix (Fin n) (Fin n) K := ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hM
  set d : Fin n → K := fun i => M i i with hd
  have hMd : M = diagonal d := hD'.diagonal_diag.symm
  have hg3 : g ^ 3 = 1 := by
    have : g ^ 3 = Q⁻¹ * Aq ^ 3 * Q⁻¹⁻¹ := by
      rw [← conj_pow]
      simp [hg]
    rw [this, hA, mul_one, mul_inv_cancel]
  have hd3 : ∀ i, d i ^ 3 = 1 := by
    intro i
    have h1 : M ^ 3 = 1 := by
      rw [hM, ← Units.val_pow_eq_pow_val, hg3, Units.val_one]
    rw [hMd, Matrix.diagonal_pow] at h1
    have := congrFun (congrFun h1 i) i
    simpa using this
  have hU : (M.map h.bar)ᵀ * M = 1 := by
    have this : (M.map h.bar)ᵀ * ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M =
        ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := mem_primeFormUnitary.1 (P⁻¹ * A * P).2
    simpa only [Units.val_one, Matrix.mul_one] using this
  have hdn : ∀ i, h.bar (d i) * d i = 1 := by
    intro i
    rw [hMd] at hU
    have := congrFun (congrFun hU i) i
    simpa [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply] using this
  have hdetM : M.det = ((Aq : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det := by
    have h1 : M.det = ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det *
        ((Aq : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det *
          ((Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det := by
      rw [hM, hg, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul]
    have h2 : ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det *
        ((Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    rw [h1]
    linear_combination ((Aq : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det * h2
  have hdet' : n = 3 → ∏ i, d i ≠ 1 := by
    intro hn3
    rw [← Matrix.det_diagonal, ← hMd, hdetM]
    exact hdet hn3
  obtain ⟨i, j, hij, hdij⟩ := exists_ne_eq_of_pow_three hn d hd3 hdet'
  obtain ⟨ε, hε⟩ := CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow.exists_norm_eq_neg_one h
  have hε' : h.bar ε * ε = -1 := by
    rw [mul_comm]; exact hε
  have hfin := h.finite
  obtain ⟨ω, hω3, hω1, -, hωq⟩ := CFSG.HardMathSupport.Lang.Proving.exists_primitive_cube_root_normOne
    (K := K) (q := p ^ f) (by rw [h.card, pow_mul']) h3
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω3
  have hωb : h.bar ω * ω = 1 := by
    rw [h.bar_apply, hωq, inv_mul_cancel₀ hω0]
  have e00 : hpair h (planeVec i j ε) (planeVec i j ε) = 0 := by
    rw [hpair_planeVec h hij, hε']; ring
  have e11 : hpair h (planeVec i j (ε * ω)) (planeVec i j (ε * ω)) = 0 := by
    rw [hpair_planeVec h hij, map_mul]
    linear_combination (h.bar ω * ω) * hε' - hωb
  have e01 : hpair h (planeVec i j ε) (planeVec i j (ε * ω)) ≠ 0 := by
    rw [hpair_planeVec h hij]
    intro h0
    apply hω1
    linear_combination ω * hε' - h0
  set Pm : Matrix (Fin n) (Fin n) K := (Q : Matrix (Fin n) (Fin n) K) with hPm
  have hPu : (Pm.map h.bar)ᵀ * Pm = 1 := by
    have := mem_primeFormUnitary.1 P.2
    simpa using this
  have hAP : ((Aq : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Pm = Pm * M := by
    have h1 : Pm * ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [hPm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hM, hg, Units.val_mul, Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1,
      Matrix.one_mul]
  have hMv : ∀ t : K, M *ᵥ planeVec i j t = d i • planeVec i j t := by
    intro t
    rw [hMd]
    ext k
    rw [Matrix.mulVec_diagonal]
    by_cases hki : k = i
    · subst hki
      simp
    · by_cases hkj : k = j
      · subst hkj
        simp [planeVec, hki, hdij]
      · simp [planeVec, hki, hkj]
  have heig : ∀ t : K, ((Aq : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (Pm *ᵥ planeVec i j t) =
      d i • (Pm *ᵥ planeVec i j t) := by
    intro t
    rw [Matrix.mulVec_mulVec, hAP, ← Matrix.mulVec_mulVec, hMv, Matrix.mulVec_smul]
  refine hasFixedThreePair_of_eigen h hp3 hn A (e := Pm *ᵥ planeVec i j ε)
    (e' := Pm *ᵥ planeVec i j (ε * ω)) ?_ ?_ ?_ (d i) (hdn i) (heig ε) (heig (ε * ω))
  · rw [hpair_mulVec hPu]; exact e00
  · rw [hpair_mulVec hPu]; exact e11
  · rw [hpair_mulVec hPu]; exact e01

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
