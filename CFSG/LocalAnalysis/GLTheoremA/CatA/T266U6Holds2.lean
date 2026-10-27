module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2UniResF
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUSplit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172ALayerBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T266U6

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open Matrix

variable {n : ℕ} {K : Type} [Field K]

@[expose] def U6MatConcl (h : UnitaryFieldData 2 n K)
    (Ab : Subgroup (MulAut (primeFormP h (idGram K 6)))) : Prop :=
  ∃ (Eb : Subgroup (MulAut (primeFormP h (idGram K 6)))) (yb : MulAut (primeFormP h (idGram K 6))),
    Eb ≤ Ab ∧ Nat.card Ab ≤ 3 * Nat.card Eb ∧ yb ∈ Eb ∧ yb ≠ 1 ∧
    (∃ Jb : Subgroup (primeFormP h (idGram K 6)), GLAPComponent 3 (fixSubgroup yb) Jb ∧
      (∀ ε ∈ Eb, Jb ≤ fixSubgroup ε) ∧ catalogIs (PSimple 3 Jb) (S10.isUrn n)) ∧
    ∃ Tb' : Subgroup (primeFormP h (idGram K 6)), IsPGroup 2 Tb' ∧ Tb' ≤ fixSubgroup yb ∧
      (∀ α ∈ Ab, Tb'.map α.toMonoidHom = Tb') ∧ (∃ α ∈ Ab, ∃ t ∈ Tb', α t ≠ t) ∧ Nat.card Tb' ≠ 8

private theorem cj_fixSubgroup_conj {G : Type*} [Group G] (σ τ : MulAut G) :
    fixSubgroup (MulAut.conj σ τ) = (fixSubgroup τ).map σ.toMonoidHom := by
  ext x
  rw [mem_fixSubgroup, Subgroup.mem_map]
  constructor
  · intro hx
    refine ⟨σ⁻¹ x, ?_, by simp⟩
    rw [mem_fixSubgroup]
    have h1 : (σ * τ * σ⁻¹) x = x := hx
    have h2 : σ (τ (σ⁻¹ x)) = x := h1
    calc τ (σ⁻¹ x) = σ⁻¹ (σ (τ (σ⁻¹ x))) := by simp
      _ = σ⁻¹ x := by rw [h2]
  · rintro ⟨z, hz, rfl⟩
    rw [mem_fixSubgroup] at hz
    show (σ * τ * σ⁻¹) (σ z) = σ z
    simp [MulAut.mul_apply, hz]

theorem u6MatConcl_map_conj [Finite K] (h : UnitaryFieldData 2 n K)
    {Ab : Subgroup (MulAut (primeFormP h (idGram K 6)))} (σ : MulAut (primeFormP h (idGram K 6)))
    (hAb : U6MatConcl h Ab) : U6MatConcl h (Ab.map (MulAut.conj σ).toMonoidHom) := by
  have := h.finite
  obtain ⟨Eb, yb, hEbAb, hcard, hyb, hyb1, ⟨Jb, hJb, hJbE, hJbcat⟩, Tb', hTb2, hTbfix, hTbN, hTbA,
    hTbcard⟩ := hAb
  have hκinj : Function.Injective (MulAut.conj σ).toMonoidHom := (MulAut.conj σ).injective
  have hσinj : Function.Injective σ.toMonoidHom := σ.injective
  refine ⟨Eb.map (MulAut.conj σ).toMonoidHom, MulAut.conj σ yb, Subgroup.map_mono hEbAb, ?_,
    Subgroup.mem_map_of_mem _ hyb, ?_, ⟨Jb.map σ.toMonoidHom, ?_, ?_, ?_⟩,
    Tb'.map σ.toMonoidHom, hTb2.map _, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hκinj, Subgroup.card_map_of_injective hκinj]
    exact hcard
  · intro h1
    apply hyb1
    have : MulAut.conj σ yb = MulAut.conj σ 1 := by rw [h1, map_one]
    exact (MulAut.conj σ).injective this
  · rw [cj_fixSubgroup_conj]
    exact (CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPComponent_map_iff Nat.prime_three hσinj).2 hJb
  · rintro _ ⟨ε, hε, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, cj_fixSubgroup_conj]
    exact Subgroup.map_mono (hJbE ε hε)
  · obtain ⟨i, hi, ⟨f⟩⟩ := hJbcat
    have hJb' : GLAPComponent 3 ((fixSubgroup yb).map σ.toMonoidHom) (Jb.map σ.toMonoidHom) :=
      (CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPComponent_map_iff Nat.prime_three hσinj).2 hJb
    obtain ⟨e⟩ := CFSG.LocalAnalysis.GLTheoremA.nonempty_pSimple_equiv_map Nat.prime_three
      σ.toMonoidHom hJb hJb'
    exact ⟨i, hi, ⟨e.symm.trans f⟩⟩
  · rw [cj_fixSubgroup_conj]
    exact Subgroup.map_mono hTbfix
  · rintro _ ⟨α, hα, rfl⟩
    rw [Subgroup.map_map]
    have e1 : ((MulAut.conj σ).toMonoidHom α).toMonoidHom.comp σ.toMonoidHom =
        σ.toMonoidHom.comp α.toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, MulAut.mul_apply]
    rw [e1, ← Subgroup.map_map, hTbN α hα]
  · obtain ⟨α, hα, t, ht, hαt⟩ := hTbA
    refine ⟨MulAut.conj σ α, Subgroup.mem_map_of_mem _ hα, σ t, Subgroup.mem_map_of_mem _ ht, ?_⟩
    intro h1
    apply hαt
    have h2 : σ (α t) = σ t := by simpa [MulAut.conj_apply, MulAut.mul_apply] using h1
    exact σ.injective h2
  · rw [Subgroup.card_map_of_injective hσinj]
    exact hTbcard

private noncomputable def root_u (a b : Fin 6) : Fin 6 → K := Pi.single a 1 + Pi.single b 1

private noncomputable def root_N (h : UnitaryFieldData 2 n K) (a b c : Fin 6) (t s : K) :
    Matrix (Fin 6) (Fin 6) K :=
  s • vecMulVec (root_u (K := K) a b) (root_u a b) +
    t • vecMulVec (Pi.single c (1 : K)) (root_u a b) +
    h.bar t • vecMulVec (root_u (K := K) a b) (Pi.single c (1 : K))

private noncomputable def root_g (h : UnitaryFieldData 2 n K) (a b c : Fin 6) (t s : K) :
    Matrix (Fin 6) (Fin 6) K :=
  1 + root_N h a b c t s

section Root

variable (h : UnitaryFieldData 2 n K) {a b c : Fin 6}

private theorem root_u_left (hab : a ≠ b) : root_u (K := K) a b a = 1 := by
  simp [root_u, Pi.single_apply, hab]

private theorem root_u_right (hab : a ≠ b) : root_u (K := K) a b b = 1 := by
  simp [root_u, Pi.single_apply, hab, Ne.symm hab]

private theorem root_u_third (hac : a ≠ c) (hbc : b ≠ c) : root_u (K := K) a b c = 0 := by
  simp [root_u, Pi.single_apply, Ne.symm hac, Ne.symm hbc]

private theorem root_dot_uu [CharP K 2] (hab : a ≠ b) :
    root_u (K := K) a b ⬝ᵥ root_u a b = 0 := by
  show (Pi.single a 1 + Pi.single b 1) ⬝ᵥ root_u a b = 0
  rw [add_dotProduct, single_dotProduct, single_dotProduct, root_u_left hab, root_u_right hab,
    one_mul, CharTwo.add_self_eq_zero]

private theorem root_dot_ue (hac : a ≠ c) (hbc : b ≠ c) :
    root_u (K := K) a b ⬝ᵥ Pi.single c 1 = 0 := by
  rw [dotProduct_single, root_u_third hac hbc, zero_mul]

private theorem root_dot_eu (hac : a ≠ c) (hbc : b ≠ c) :
    (Pi.single c 1 : Fin 6 → K) ⬝ᵥ root_u a b = 0 := by
  rw [single_dotProduct, root_u_third hac hbc, mul_zero]

private theorem root_dot_ee : (Pi.single c 1 : Fin 6 → K) ⬝ᵥ Pi.single c 1 = 1 := by
  rw [single_dotProduct, Pi.single_eq_same, mul_one]

private theorem root_N_mul [CharP K 2] (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (t s t' s' : K) :
    root_N h a b c t s * root_N h a b c t' s' =
      (h.bar t * t') • vecMulVec (root_u (K := K) a b) (root_u a b) := by
  simp only [root_N, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    vecMulVec_mul_vecMulVec, root_dot_uu hab, root_dot_ue hac hbc, root_dot_eu hac hbc, root_dot_ee,
    zero_smul, one_smul, vecMulVec_zero, smul_zero, add_zero, zero_add, smul_smul]
  rw [mul_comm t' (h.bar t)]

private theorem root_g_mul [CharP K 2] (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (t s t' s' : K) :
    root_g h a b c t s * root_g h a b c t' s' = root_g h a b c (t + t') (s + s' + h.bar t * t') := by
  simp only [root_g, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
  rw [root_N_mul h hab hac hbc]
  simp only [root_N, add_smul, map_add]
  abel

private theorem root_g_zero : root_g h a b c 0 0 = 1 := by
  simp only [root_g, root_N, map_zero, zero_smul, add_zero]

private theorem root_g_apply (t s : K) (i j : Fin 6) :
    root_g h a b c t s i j = (1 : Matrix (Fin 6) (Fin 6) K) i j +
      s * root_u a b i * root_u a b j + t * (Pi.single c (1 : K) : Fin 6 → K) i * root_u a b j +
      h.bar t * root_u a b i * (Pi.single c (1 : K) : Fin 6 → K) j := by
  simp only [root_g, root_N, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  ring

private theorem root_bar_u (i : Fin 6) : h.bar (root_u (K := K) a b i) = root_u a b i := by
  simp only [root_u, Pi.add_apply, map_add]
  rw [Pi.single_apply, Pi.single_apply]
  split_ifs <;> simp

private theorem root_bar_e (i : Fin 6) :
    h.bar ((Pi.single c (1 : K) : Fin 6 → K) i) = (Pi.single c (1 : K) : Fin 6 → K) i := by
  rw [Pi.single_apply]
  split_ifs <;> simp

private theorem root_bar_one (i j : Fin 6) :
    h.bar ((1 : Matrix (Fin 6) (Fin 6) K) j i) = (1 : Matrix (Fin 6) (Fin 6) K) i j := by
  by_cases hij : i = j
  · subst hij
    simp
  · rw [one_apply_ne hij, one_apply_ne (Ne.symm hij), map_zero]

private theorem root_g_star (t s : K) :
    ((root_g h a b c t s).map h.bar)ᵀ = root_g h a b c t (h.bar s) := by
  ext i j
  rw [transpose_apply, map_apply, root_g_apply, root_g_apply]
  simp only [map_add, map_mul, h.bar_bar, root_bar_u h, root_bar_e h, root_bar_one h]
  ring

private theorem root_g_mul_inv [CharP K 2] (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (t s : K) :
    root_g h a b c t s * root_g h a b c t (s + h.bar t * t) = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [root_g_mul h hab hac hbc, CharTwo.add_self_eq_zero,
    show s + (s + h.bar t * t) + h.bar t * t = 0 by linear_combination (s + h.bar t * t) * h2,
    root_g_zero]

private theorem root_g_inv_mul [CharP K 2] (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (t s : K) :
    root_g h a b c t (s + h.bar t * t) * root_g h a b c t s = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [root_g_mul h hab hac hbc, CharTwo.add_self_eq_zero,
    show s + h.bar t * t + s + h.bar t * t = 0 by linear_combination (s + h.bar t * t) * h2,
    root_g_zero]

private theorem root_g_pow_four [CharP K 2] (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (t s : K) :
    root_g h a b c t s ^ 4 = 1 := by
  have hsq : root_g h a b c t s ^ 2 = root_g h a b c 0 (h.bar t * t) := by
    rw [sq, root_g_mul h hab hac hbc]
    simp only [CharTwo.add_self_eq_zero, zero_add]
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq, sq, root_g_mul h hab hac hbc]
  simp only [CharTwo.add_self_eq_zero, map_zero, zero_mul, add_zero, root_g_zero]

private theorem root_eq_one_of_pow_four [CharP K 2] {x : K} (hx : x ^ 4 = 1) : x = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h4 : (x + 1) ^ 4 = 0 := by
    linear_combination hx + (2 * x ^ 3 + 3 * x ^ 2 + 2 * x + 1) * h2
  have h1 : x + 1 = 0 := (pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)).mp h4
  linear_combination h1 - h2

private noncomputable def root_G (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (t s : K) :
    GL (Fin 6) K where
  val := root_g h a b c t s
  inv := root_g h a b c t (s + h.bar t * t)
  val_inv := by
    haveI := h.charP
    exact root_g_mul_inv h hab hac hbc t s
  inv_val := by
    haveI := h.charP
    exact root_g_inv_mul h hab hac hbc t s

private noncomputable def root_R (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Subgroup (GL (Fin 6) K) where
  carrier := {M | ∃ t s : K, s + h.bar s = h.bar t * t ∧ M = root_G h hab hac hbc t s}
  mul_mem' := by
    haveI := h.charP
    rintro _ _ ⟨t, s, hts, rfl⟩ ⟨t', s', hts', rfl⟩
    refine ⟨t + t', s + s' + h.bar t * t', ?_, Units.ext (root_g_mul h hab hac hbc t s t' s')⟩
    simp only [map_add, map_mul, h.bar_bar]
    linear_combination hts + hts'
  one_mem' := ⟨0, 0, by simp, Units.ext (root_g_zero h).symm⟩
  inv_mem' := by
    haveI := h.charP
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    rintro _ ⟨t, s, hts, rfl⟩
    refine ⟨t, s + h.bar t * t, ?_, Units.ext rfl⟩
    simp only [map_add, map_mul, h.bar_bar]
    linear_combination hts + h.bar t * t * h2

private theorem root_G_mem (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {t s : K}
    (hts : s + h.bar s = h.bar t * t) : root_G h hab hac hbc t s ∈ gramSU h (idGram K 6) := by
  haveI := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨?_, ?_⟩
  · show ((root_g h a b c t s).map h.bar)ᵀ * 1 * root_g h a b c t s = 1
    rw [Matrix.mul_one, root_g_star, root_g_mul h hab hac hbc, CharTwo.add_self_eq_zero,
      show h.bar s + s + h.bar t * t = 0 by linear_combination hts + h.bar t * t * h2, root_g_zero]
  · show (root_g h a b c t s).det = 1
    apply root_eq_one_of_pow_four
    rw [← det_pow, root_g_pow_four h hab hac hbc, det_one]

private noncomputable def root_S (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {t s : K}
    (hts : s + h.bar s = h.bar t * t) : gramSU h (idGram K 6) :=
  ⟨root_G h hab hac hbc t s, root_G_mem h hab hac hbc hts⟩

private theorem root_S_congr (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {t t' s : K}
    (hts : s + h.bar s = h.bar t * t) (hts' : s + h.bar s = h.bar t' * t') (htt : t = t') :
    root_S h hab hac hbc hts = root_S h hab hac hbc hts' := by
  subst htt
  rfl

private theorem root_diag_mul (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {D : Matrix (Fin 6) (Fin 6) K} (hD : D.IsDiag) (hDa : D a a = 1) (hDb : D b b = 1)
    (hDc : h.bar (D c c) * D c c = 1) (t s : K) :
    D * root_g h a b c t s = root_g h a b c (D c c * t) s * D := by
  obtain ⟨d, rfl⟩ : ∃ d, D = diagonal d := ⟨D.diag, hD.diagonal_diag.symm⟩
  simp only [diagonal_apply_eq] at hDa hDb hDc ⊢
  have hdu : ∀ i, d i * root_u (K := K) a b i = root_u a b i := by
    intro i
    by_cases hia : i = a
    · rw [hia, hDa, one_mul]
    by_cases hib : i = b
    · rw [hib, hDb, one_mul]
    simp [root_u, Pi.single_apply, hia, hib]
  have hde : ∀ i, d i * (Pi.single c (1 : K) : Fin 6 → K) i =
      d c * (Pi.single c (1 : K) : Fin 6 → K) i := by
    intro i
    by_cases hic : i = c
    · rw [hic]
    simp [Pi.single_apply, hic]
  have hone : ∀ i j, d i * (1 : Matrix (Fin 6) (Fin 6) K) i j =
      (1 : Matrix (Fin 6) (Fin 6) K) i j * d j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact mul_comm _ _
    · rw [one_apply_ne hij, mul_zero, zero_mul]
  ext i j
  rw [diagonal_mul, mul_diagonal, root_g_apply, root_g_apply, map_mul]
  linear_combination hone i j + (s * root_u a b j) * hdu i - (s * root_u a b i) * hdu j +
    (t * root_u a b j) * hde i - (d c * t * (Pi.single c (1 : K) : Fin 6 → K) i) * hdu j +
    (h.bar t * (Pi.single c (1 : K) : Fin 6 → K) j) * hdu i -
    (h.bar (d c) * h.bar t * root_u a b i) * hde j -
    (h.bar t * root_u a b i * (Pi.single c (1 : K) : Fin 6 → K) j) * hDc

private theorem root_conj (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (A : GL (Fin 6) K)
    (hAd : (A : Matrix (Fin 6) (Fin 6) K).IsDiag) (hAa : (A : Matrix (Fin 6) (Fin 6) K) a a = 1)
    (hAb : (A : Matrix (Fin 6) (Fin 6) K) b b = 1)
    (hAc : h.bar ((A : Matrix (Fin 6) (Fin 6) K) c c) * (A : Matrix (Fin 6) (Fin 6) K) c c = 1)
    (t s : K) :
    A * root_G h hab hac hbc t s * A⁻¹ =
      root_G h hab hac hbc ((A : Matrix (Fin 6) (Fin 6) K) c c * t) s := by
  rw [mul_inv_eq_iff_eq_mul]
  exact Units.ext (root_diag_mul h hab hac hbc hAd hAa hAb hAc t s)

private theorem root_diag_norm {X : GL (Fin 6) K} (hX : X ∈ primeFormUnitary h (idGram K 6))
    (hXd : (X : Matrix (Fin 6) (Fin 6) K).IsDiag) (i : Fin 6) :
    h.bar ((X : Matrix (Fin 6) (Fin 6) K) i i) * (X : Matrix (Fin 6) (Fin 6) K) i i = 1 := by
  have hU : ((X : Matrix (Fin 6) (Fin 6) K).map h.bar)ᵀ * 1 * (X : Matrix (Fin 6) (Fin 6) K) = 1 :=
    hX
  rw [Matrix.mul_one, ← hXd.diagonal_diag, diagonal_map (map_zero h.bar), diagonal_transpose,
    diagonal_mul_diagonal] at hU
  have := congrFun (congrFun hU i) i
  simpa [diagonal_apply_eq] using this

private theorem root_diag_pow {X : GL (Fin 6) K} (hXd : (X : Matrix (Fin 6) (Fin 6) K).IsDiag)
    {k : ℕ} (hk : X ^ k = 1) (i : Fin 6) : ((X : Matrix (Fin 6) (Fin 6) K) i i) ^ k = 1 := by
  have h1 : (X : Matrix (Fin 6) (Fin 6) K) ^ k = 1 := by
    rw [← Units.val_pow_eq_pow_val, hk, Units.val_one]
  rw [← hXd.diagonal_diag, diagonal_pow] at h1
  have := congrFun (congrFun h1 i) i
  simpa [diagonal_apply_eq] using this

private theorem root_eq_scalar {M M' : gramSU h (idGram K 6)}
    (hMM' : (M : primeFormP h (idGram K 6)) = (M' : primeFormP h (idGram K 6))) :
    ∃ μ : K, ∀ i j, ((M' : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j =
      ((M : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j * μ := by
  obtain ⟨z, -, -, hz⟩ := mem_normOneScalars.mp (QuotientGroup.eq.mp hMM')
  refine ⟨(z : K), fun i j => ?_⟩
  have hM' : (M' : GL (Fin 6) K) = (M : GL (Fin 6) K) * GeneralLinearGroup.scalar (Fin 6) z := by
    rw [← hz, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [hM', Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply, mul_diagonal]

private theorem root_g_cc (hac : a ≠ c) (hbc : b ≠ c) (t s : K) : root_g h a b c t s c c = 1 := by
  simp [root_g_apply, root_u_third hac hbc]

private theorem root_g_ca (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (t s : K) :
    root_g h a b c t s c a = t := by
  simp [root_g_apply, root_u_third hac hbc, root_u_left hab, one_apply_ne (Ne.symm hac),
    Pi.single_apply, hac]

private theorem root_g_ab (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (t s : K) :
    root_g h a b c t s a b = s := by
  simp [root_g_apply, root_u_left hab, root_u_right hab, one_apply_ne hab, Pi.single_apply, hac,
    hbc]

end Root

theorem u6_root_props [Finite K] (h : UnitaryFieldData 2 n K) (hn : Odd n) (hn1 : 1 < n)
    {Δ : Subgroup (primeFormUnitary h (idGram K 6))}
    (hdiag : ∀ X ∈ Δ, ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag)
    (hcube : ∀ X ∈ Δ, X ^ 3 = 1) {a b c : Fin 6} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : ∀ X ∈ Δ, ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) a a = 1)
    (hb : ∀ X ∈ Δ, ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) b b = 1)
    (Y : primeFormUnitary h (idGram K 6))
    (hYdiag : ((Y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag)
    (hYa : ((Y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) a a = 1)
    (hYb : ((Y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) b b = 1)
    (hYc : ((Y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) c c = 1)
    {X₀ : primeFormUnitary h (idGram K 6)} (hX₀ : X₀ ∈ Δ)
    (hX₀c : ((X₀ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) c c ≠ 1) :
    ∃ Tb' : Subgroup (primeFormP h (idGram K 6)), IsPGroup 2 Tb' ∧
      Tb' ≤ fixSubgroup (primeFormConjHom h (idGram K 6) Y) ∧
      (∀ X ∈ Δ, Tb'.map (primeFormConjHom h (idGram K 6) X).toMonoidHom = Tb') ∧
      (∃ t ∈ Tb', primeFormConjHom h (idGram K 6) X₀ t ≠ t) ∧ Nat.card Tb' ≠ 8 := by
  classical
  haveI := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  let T : Subgroup (primeFormP h (idGram K 6)) :=
    ((root_R h hab hac hbc).subgroupOf (gramSU h (idGram K 6))).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 6)) 6))
  have hmem : ∀ x, x ∈ T ↔ ∃ (t s : K) (hts : s + h.bar s = h.bar t * t),
      ((root_S h hab hac hbc hts : gramSU h (idGram K 6)) : primeFormP h (idGram K 6)) = x := by
    intro x
    constructor
    · rintro ⟨M, hM, rfl⟩
      obtain ⟨t, s, hts, hMe⟩ := Subgroup.mem_subgroupOf.mp hM
      exact ⟨t, s, hts, by rw [QuotientGroup.mk'_apply]; exact congrArg _ (Subtype.ext hMe.symm)⟩
    · rintro ⟨t, s, hts, rfl⟩
      exact ⟨root_S h hab hac hbc hts, Subgroup.mem_subgroupOf.mpr ⟨t, s, hts, rfl⟩, rfl⟩
  have hconj : ∀ A : primeFormUnitary h (idGram K 6),
      ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag →
      ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) a a = 1 →
      ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) b b = 1 →
      ∀ (t s : K) (hts : s + h.bar s = h.bar t * t),
      ∃ hts' : s + h.bar s = h.bar (((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) c c * t) *
          (((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) c c * t),
        primeFormConjHom h (idGram K 6) A
            ((root_S h hab hac hbc hts : gramSU h (idGram K 6)) : primeFormP h (idGram K 6)) =
          ((root_S h hab hac hbc hts' : gramSU h (idGram K 6)) : primeFormP h (idGram K 6)) := by
    intro A hAd hAa hAb t s hts
    have hAc := root_diag_norm h A.2 hAd c
    refine ⟨by rw [map_mul]; linear_combination hts - h.bar t * t * hAc, ?_⟩
    rw [primeFormConjHom_mk]
    exact congrArg _ (Subtype.ext (root_conj h hab hac hbc (A : GL (Fin 6) K) hAd hAa hAb hAc t s))
  set δ := ((X₀ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) c c with hδdef
  have hδu : h.bar δ * δ = 1 := root_diag_norm h X₀.2 (hdiag X₀ hX₀) c
  have hδ3 : δ ^ 3 = 1 :=
    root_diag_pow (hdiag X₀ hX₀) (by rw [← Subgroup.coe_pow, hcube X₀ hX₀, Subgroup.coe_one]) c
  have hq : δ ^ 2 + δ + 1 = 0 := by
    have : (δ - 1) * (δ ^ 2 + δ + 1) = 0 := by linear_combination hδ3
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd (sub_eq_zero.mp h') hX₀c
    · exact h'
  have hbδ : h.bar δ = δ ^ 2 := by linear_combination (-h.bar δ) * hδ3 + δ ^ 2 * hδu
  have htr : δ + h.bar δ = h.bar 1 * 1 := by
    rw [map_one, one_mul, hbδ]
    linear_combination hq - h2
  refine ⟨T, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x
    obtain ⟨t, s, hts, hx⟩ := (hmem x).mp x.2
    refine ⟨2, Subtype.ext ?_⟩
    have hpow : (root_S h hab hac hbc hts) ^ 4 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact root_g_pow_four h hab hac hbc t s
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hx, ← QuotientGroup.mk_pow,
      show (2 : ℕ) ^ 2 = 4 by norm_num, hpow, QuotientGroup.mk_one]
  ·
    intro x hx
    obtain ⟨t, s, hts, rfl⟩ := (hmem x).mp hx
    rw [mem_fixSubgroup]
    obtain ⟨hts', he⟩ := hconj Y hYdiag hYa hYb t s hts
    rw [he, root_S_congr h hab hac hbc hts' hts (by rw [hYc, one_mul])]
  ·
    have hstab : ∀ X ∈ Δ, ∀ x ∈ T, primeFormConjHom h (idGram K 6) X x ∈ T := by
      intro X hX x hx
      obtain ⟨t, s, hts, rfl⟩ := (hmem x).mp hx
      obtain ⟨hts', he⟩ := hconj X (hdiag X hX) (ha X hX) (hb X hX) t s hts
      rw [he]
      exact (hmem _).mpr ⟨_, s, hts', rfl⟩
    intro X hX
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hstab X hX x hx
    · intro y hy
      refine ⟨primeFormConjHom h (idGram K 6) X⁻¹ y, hstab X⁻¹ (inv_mem hX) y hy, ?_⟩
      show primeFormConjHom h (idGram K 6) X (primeFormConjHom h (idGram K 6) X⁻¹ y) = y
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  ·
    refine ⟨_, (hmem _).mpr ⟨1, δ, htr, rfl⟩, ?_⟩
    obtain ⟨hts', he⟩ := hconj X₀ (hdiag X₀ hX₀) (ha X₀ hX₀) (hb X₀ hX₀) 1 δ htr
    rw [he]
    intro heq
    obtain ⟨μ, hμ⟩ := root_eq_scalar h heq
    have hcc := hμ c c
    have hca := hμ c a
    change root_g h a b c 1 δ c c = root_g h a b c (δ * 1) δ c c * μ at hcc
    change root_g h a b c 1 δ c a = root_g h a b c (δ * 1) δ c a * μ at hca
    rw [root_g_cc h hac hbc, root_g_cc h hac hbc, one_mul] at hcc
    rw [root_g_ca h hab hac hbc, root_g_ca h hab hac hbc, ← hcc, mul_one, mul_one] at hca
    exact hX₀c hca.symm
  ·
    have hfix : ∀ s : h.fixedField, (s : K) + h.bar s = h.bar 0 * 0 := by
      intro s
      rw [(h.mem_fixedField).mp s.2, map_zero, zero_mul, CharTwo.add_self_eq_zero]
    let f : Option h.fixedField → T := fun o =>
      ⟨Option.elim o ((root_S h hab hac hbc htr : gramSU h (idGram K 6)) : primeFormP h (idGram K 6))
        (fun s => ((root_S h hab hac hbc (hfix s) : gramSU h (idGram K 6)) :
          primeFormP h (idGram K 6))), by
        cases o with
        | none => exact (hmem _).mpr ⟨1, δ, htr, rfl⟩
        | some s => exact (hmem _).mpr ⟨0, s, hfix s, rfl⟩⟩
    have hf : Function.Injective f := by
      rintro (_ | s) (_ | s') hss
      · rfl
      · exfalso
        obtain ⟨μ, hμ⟩ := root_eq_scalar h (congrArg Subtype.val hss)
        have hcc := hμ c c
        have hca := hμ c a
        change root_g h a b c 0 s' c c = root_g h a b c 1 δ c c * μ at hcc
        change root_g h a b c 0 s' c a = root_g h a b c 1 δ c a * μ at hca
        rw [root_g_cc h hac hbc, root_g_cc h hac hbc, one_mul] at hcc
        rw [root_g_ca h hab hac hbc, root_g_ca h hab hac hbc, ← hcc, mul_one] at hca
        exact zero_ne_one hca
      · exfalso
        obtain ⟨μ, hμ⟩ := root_eq_scalar h (congrArg Subtype.val hss)
        have hcc := hμ c c
        have hca := hμ c a
        change root_g h a b c 1 δ c c = root_g h a b c 0 s c c * μ at hcc
        change root_g h a b c 1 δ c a = root_g h a b c 0 s c a * μ at hca
        rw [root_g_cc h hac hbc, root_g_cc h hac hbc, one_mul] at hcc
        rw [root_g_ca h hab hac hbc, root_g_ca h hab hac hbc, ← hcc, mul_one] at hca
        exact one_ne_zero hca
      · obtain ⟨μ, hμ⟩ := root_eq_scalar h (congrArg Subtype.val hss)
        have hcc := hμ c c
        have hab' := hμ a b
        change root_g h a b c 0 s' c c = root_g h a b c 0 s c c * μ at hcc
        change root_g h a b c 0 s' a b = root_g h a b c 0 s a b * μ at hab'
        rw [root_g_cc h hac hbc, root_g_cc h hac hbc, one_mul] at hcc
        rw [root_g_ab h hab hac hbc, root_g_ab h hab hac hbc, ← hcc, mul_one] at hab'
        exact congrArg some (Subtype.ext hab'.symm)
    have hcard := Nat.card_le_card_of_injective f hf
    rw [Finite.card_option, h.card_fixedField] at hcard
    obtain ⟨k, rfl⟩ := hn
    have h8 : 8 ≤ 2 ^ (2 * k + 1) :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 * k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h9 : 8 + 1 ≤ Nat.card T := le_trans (Nat.add_le_add_right h8 1) hcard
    omega

private theorem blk_exists_omega (h : UnitaryFieldData 2 n K) : ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  haveI : Finite K := h.finite
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3dvd : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]
    have h4 : (4 : ℕ) ≡ 1 [MOD 3] := by decide
    have hp : (4 : ℕ) ^ n ≡ 1 [MOD 3] := by simpa using h4.pow n
    exact hp.symm.dvd'
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h3dvd
  refine ⟨(x : K), ?_, ?_⟩
  · rw [← Units.val_pow_eq_pow_val, ← hx, pow_orderOf_eq_one, Units.val_one]
  · intro h1
    have hx1 : x = 1 := Units.ext h1
    rw [hx1, orderOf_one] at hx
    norm_num at hx

private theorem blk_norm_of_cube (h : UnitaryFieldData 2 n K) (hn : Odd n) {c : K} (hc : c ^ 3 = 1) :
    h.norm c = 1 := by
  obtain ⟨k, hk⟩ := Odd.nat_add_dvd_pow_add_pow 2 1 hn
  have hk' : 2 ^ n + 1 = 3 * k := by simpa using hk
  rw [UnitaryFieldData.norm, h.bar_apply]
  calc c * c ^ 2 ^ n = c ^ (2 ^ n + 1) := by ring
    _ = (c ^ 3) ^ k := by rw [hk', pow_mul]
    _ = 1 := by rw [hc, one_pow]

private theorem blk_le (h : UnitaryFieldData 2 n K) : StatedSU 6 (2 ^ n) K ≤ gramSU h (idGram K 6) :=
  (unitarySU_eq_gramSU h 6).le

private noncomputable def blk_jMap (h : UnitaryFieldData 2 n K) :
    ↥(StatedSU 6 (2 ^ n) K) →* primeFormP h (idGram K 6) :=
  (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 6)) 6)).comp (Subgroup.inclusion (blk_le h))

private theorem blk_jMap_apply (h : UnitaryFieldData 2 n K) (g : ↥(StatedSU 6 (2 ^ n) K)) :
    blk_jMap h g = ((⟨(g : GL (Fin 6) K), blk_le h g.2⟩ : gramSU h (idGram K 6)) :
      primeFormP h (idGram K 6)) :=
  rfl

private theorem blk_inj (h : UnitaryFieldData 2 n K) {I₀ : Finset (Fin 6)} (hI6 : I₀.card < 6) :
    Function.Injective ((blk_jMap h).comp (CFSG.ComponentClassification.Burgoyne.U.uBlock 2 n K I₀).subtype) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨g, hg⟩ hg1
  change blk_jMap h g = 1 at hg1
  rw [blk_jMap_apply] at hg1
  obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.1 ((QuotientGroup.eq_one_iff _).1 hg1)
  have hc' : (g : GL (Fin 6) K) = GeneralLinearGroup.scalar (Fin 6) c := hc
  obtain ⟨l, hl⟩ : ∃ l : Fin 6, l ∉ I₀ := by
    by_contra! hcon
    have hu : I₀ = Finset.univ := Finset.eq_univ_of_forall hcon
    rw [hu, Finset.card_univ, Fintype.card_fin] at hI6
    exact lt_irrefl _ hI6
  have hll := CFSG.ComponentClassification.Burgoyne.U.mem_uBlock_iff.1 hg l l (Or.inl hl)
  rw [hc', GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq, if_pos rfl] at hll
  have hc1 : c = 1 := Units.ext hll
  apply Subtype.ext
  apply Subtype.ext
  rw [Subgroup.coe_one, Subgroup.coe_one]
  change (g : GL (Fin 6) K) = 1
  rw [hc', hc1, map_one]

private theorem blk_comm_diag {I₀ : Finset (Fin 6)} {X M : Matrix (Fin 6) (Fin 6) K} (hX : X.IsDiag)
    (hXI : ∀ i ∈ I₀, X i i = 1) (hM : ∀ i j, (i ∉ I₀ ∨ j ∉ I₀) → M i j = if i = j then 1 else 0) :
    X * M = M * X := by
  rw [← hX.diagonal_diag]
  ext i j
  rw [diagonal_mul, mul_diagonal, diag_apply, diag_apply]
  by_cases hij : i ∉ I₀ ∨ j ∉ I₀
  · rw [hM i j hij]
    split_ifs with h'
    · rw [h', mul_one, one_mul]
    · rw [mul_zero, zero_mul]
  · push Not at hij
    rw [hXI i hij.1, hXI j hij.2, one_mul, mul_one]

private theorem blk_mem_fix (h : UnitaryFieldData 2 n K) {I₀ : Finset (Fin 6)}
    {X : primeFormUnitary h (idGram K 6)}
    (hX : ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag)
    (hXI : ∀ i ∈ I₀, ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i i = 1)
    {g : ↥(StatedSU 6 (2 ^ n) K)} (hg : g ∈ CFSG.ComponentClassification.Burgoyne.U.uBlock 2 n K I₀) :
    blk_jMap h g ∈ fixSubgroup (primeFormConjHom h (idGram K 6) X) := by
  have hXg : (X : GL (Fin 6) K) * (g : GL (Fin 6) K) = (g : GL (Fin 6) K) * (X : GL (Fin 6) K) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact blk_comm_diag hX hXI (CFSG.ComponentClassification.Burgoyne.U.mem_uBlock_iff.1 hg)
  rw [mem_fixSubgroup, blk_jMap_apply, primeFormConjHom_mk]
  congr 1
  apply Subtype.ext
  show (X : GL (Fin 6) K) * (g : GL (Fin 6) K) * (X : GL (Fin 6) K)⁻¹ = (g : GL (Fin 6) K)
  rw [hXg, mul_inv_cancel_right]

private theorem blk_grp {G : Type*} [Group G] {x y z : G} (hz : x * z = z * x)
    (h : (x * y * x⁻¹)⁻¹ * y = z) : y * x = x * y * z := by
  have e1 : y = x * y * x⁻¹ * z := inv_mul_eq_iff_eq_mul.1 h
  calc y * x = (x * y * x⁻¹ * z) * x := by rw [← e1]
    _ = x * y * (x⁻¹ * (z * x)) := by simp only [mul_assoc]
    _ = x * y * (x⁻¹ * (x * z)) := by rw [hz]
    _ = x * y * z := by rw [inv_mul_cancel_left]

private theorem blk_commute_compInd (h : UnitaryFieldData 2 n K) {I₀ : Finset (Fin 6)} (hI3 : 3 ≤ I₀.card)
    {Y : primeFormUnitary h (idGram K 6)}
    (hYdiag : ((Y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag)
    (hYI : ∀ i, ((Y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i i = 1 ↔ i ∈ I₀)
    {g : gramSU h (idGram K 6)}
    (hfix : (g : primeFormP h (idGram K 6)) ∈ fixSubgroup (primeFormConjHom h (idGram K 6) Y)) :
    CFSG.ComponentClassification.Burgoyne.PSL.compInd K I₀ * ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * CFSG.ComponentClassification.Burgoyne.PSL.compInd K I₀ := by
  classical
  haveI : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  set M : Matrix (Fin 6) (Fin 6) K := ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) with hM
  set d : Fin 6 → K := fun i => ((Y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i i
  have hYd : ((Y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal d := hYdiag.diagonal_diag.symm
  have hdI : ∀ i, d i = 1 ↔ i ∈ I₀ := hYI
  rw [mem_fixSubgroup, primeFormConjHom_mk] at hfix
  obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.1 (QuotientGroup.eq.1 hfix)
  have hc' : ((Y : GL (Fin 6) K) * (g : GL (Fin 6) K) * (Y : GL (Fin 6) K)⁻¹)⁻¹ * (g : GL (Fin 6) K) =
      GeneralLinearGroup.scalar (Fin 6) c := hc
  have e2 := blk_grp (commute_scalar c (Y : GL (Fin 6) K)).eq hc'
  have e3 : ∀ k l, M k l * d l = d k * M k l * (c : K) := by
    intro k l
    have h1 := congrArg (fun A : GL (Fin 6) K => (A : Matrix (Fin 6) (Fin 6) K) k l) e2
    simpa only [Units.val_mul, hYd, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.mul_diagonal, Matrix.diagonal_mul] using h1
  have hdet : M.det ≠ 0 := by
    rw [hM, (mem_gramSU.1 g.2).2]
    exact one_ne_zero
  obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm (Fin 6), ∀ k, M (τ k) k ≠ 0 := by
    rw [Matrix.det_apply] at hdet
    obtain ⟨τ, -, hτ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdet
    refine ⟨τ, fun k => ?_⟩
    have hprod : ∏ i, M (τ i) i ≠ 0 := by
      intro h0
      apply hτ
      rw [h0, smul_zero]
    exact Finset.prod_ne_zero_iff.1 hprod k (Finset.mem_univ k)
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  have hrel : ∀ k, d (τ k) = d k * (c : K)⁻¹ := by
    intro k
    have e := e3 (τ k) k
    have e' : M (τ k) k * d k = M (τ k) k * (d (τ k) * (c : K)) := by rw [e]; ring
    have e'' := mul_left_cancel₀ (hτ k) e'
    rw [e'', mul_assoc, mul_inv_cancel₀ hc0, mul_one]
  have hc1 : (c : K) = 1 := by
    by_contra hcne
    set e : K := (c : K)⁻¹ with he
    have he1 : e ≠ 1 := by
      intro h1
      apply hcne
      rw [he, inv_eq_one] at h1
      exact h1
    have he0 : e ≠ 0 := inv_ne_zero hc0
    have hee1 : e * e ≠ 1 := by
      intro h1
      have hsq : (e + 1) * (e + 1) = 0 := by linear_combination h1 + (1 + e) * h2
      have he' : e + 1 = 0 := mul_self_eq_zero.1 hsq
      exact he1 (by linear_combination he' - h2)
    have hee : e * e ≠ e := by
      intro h1
      have : e * (e - 1) = 0 := by linear_combination h1
      rcases mul_eq_zero.1 this with h0 | h0
      · exact he0 h0
      · exact he1 (sub_eq_zero.1 h0)
    set S1 := Finset.univ.filter (fun k => d k = e) with hS1
    set S2 := Finset.univ.filter (fun k => d k = e * e) with hS2
    have hle1 : I₀.card ≤ S1.card := by
      refine Finset.card_le_card_of_injOn τ ?_ (fun a _ b _ hab => τ.injective hab)
      intro k hk
      have hk' : k ∈ I₀ := hk
      simp only [hS1, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      rw [hrel k, (hdI k).2 hk', one_mul]
    have hle2 : S1.card ≤ S2.card := by
      refine Finset.card_le_card_of_injOn τ ?_ (fun a _ b _ hab => τ.injective hab)
      intro k hk
      simp only [hS1, hS2, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hk ⊢
      rw [hrel k, hk]
    have hd01 : Disjoint I₀ S1 := by
      rw [Finset.disjoint_left]
      intro k hk hk1
      simp only [hS1, Finset.mem_filter, Finset.mem_univ, true_and] at hk1
      exact he1 (hk1.symm.trans ((hdI k).2 hk))
    have hd012 : Disjoint (I₀ ∪ S1) S2 := by
      rw [Finset.disjoint_left]
      intro k hk hk2
      simp only [hS2, Finset.mem_filter, Finset.mem_univ, true_and] at hk2
      rcases Finset.mem_union.1 hk with hk0 | hk1
      · exact hee1 (hk2.symm.trans ((hdI k).2 hk0))
      · simp only [hS1, Finset.mem_filter, Finset.mem_univ, true_and] at hk1
        exact hee (hk2.symm.trans hk1)
    have hcard := Finset.card_le_univ (I₀ ∪ S1 ∪ S2)
    rw [Finset.card_union_of_disjoint hd012, Finset.card_union_of_disjoint hd01, Fintype.card_fin]
      at hcard
    omega
  rw [CFSG.ComponentClassification.Burgoyne.PSL.commute_compInd_iff]
  intro i j hij
  by_contra hne
  have e := e3 i j
  rw [hc1, mul_one] at e
  have hdij : d j = d i := by
    have e' : M i j * d j = M i j * d i := by rw [e]; ring
    exact mul_left_cancel₀ hne e'
  have hiff : i ∈ I₀ ↔ j ∈ I₀ := by rw [← hdI i, ← hdI j, hdij]
  tauto

private theorem blk_normal (h : UnitaryFieldData 2 n K) {I₀ : Finset (Fin 6)} (hI3 : 3 ≤ I₀.card)
    {Y : primeFormUnitary h (idGram K 6)}
    (hYdiag : ((Y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag)
    (hYI : ∀ i, ((Y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i i = 1 ↔ i ∈ I₀)
    (hJY : ((blk_jMap h).comp (CFSG.ComponentClassification.Burgoyne.U.uBlock 2 n K I₀).subtype).range ≤
      fixSubgroup (primeFormConjHom h (idGram K 6) Y)) :
    ((((blk_jMap h).comp (CFSG.ComponentClassification.Burgoyne.U.uBlock 2 n K I₀).subtype).range).subgroupOf
      (fixSubgroup (primeFormConjHom h (idGram K 6) Y))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff hJY]
  rintro _ x ⟨⟨g, hg⟩, rfl⟩ hx
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective x
  have hcomm := blk_commute_compInd h hI3 hYdiag hYI hx
  set g'' : ↥(StatedSU 6 (2 ^ n) K) := ⟨(g' : GL (Fin 6) K), (unitarySU_eq_gramSU h 6).ge g'.2⟩
  have hconj : g'' * g * g''⁻¹ ∈ CFSG.ComponentClassification.Burgoyne.U.uBlock 2 n K I₀ := by
    refine CFSG.ComponentClassification.Burgoyne.U.conj_mem_uBlock
      (D := ((g' : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))
      (Di := (((g'⁻¹ : gramSU h (idGram K 6)) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) ?_ ?_ hcomm hg ?_
    · rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
    · rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
    · rfl
  refine ⟨⟨g'' * g * g''⁻¹, hconj⟩, ?_⟩
  have hg''P : blk_jMap h g'' = (g' : primeFormP h (idGram K 6)) := rfl
  change blk_jMap h (g'' * g * g''⁻¹) =
    (g' : primeFormP h (idGram K 6)) * blk_jMap h g * (g' : primeFormP h (idGram K 6))⁻¹
  rw [map_mul, map_mul, map_inv, hg''P]

private theorem blk_three_dvd (h : UnitaryFieldData 2 n K) (hn : Odd n) {I₀ : Finset (Fin 6)}
    (hI3 : 3 ≤ I₀.card)
    (hinj : Function.Injective
      ((blk_jMap h).comp (CFSG.ComponentClassification.Burgoyne.U.uBlock 2 n K I₀).subtype)) :
    3 ∣ Nat.card
      (↥((blk_jMap h).comp (CFSG.ComponentClassification.Burgoyne.U.uBlock 2 n K I₀).subtype).range ⧸
        Subgroup.center
          ↥((blk_jMap h).comp (CFSG.ComponentClassification.Burgoyne.U.uBlock 2 n K I₀).subtype).range) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set U := CFSG.ComponentClassification.Burgoyne.U.uBlock 2 n K I₀
  set φ := (blk_jMap h).comp U.subtype
  obtain ⟨ω, hω3, hω1⟩ := blk_exists_omega h
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω3
  have hωN : h.norm ω = 1 := blk_norm_of_cube h hn hω3
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h2
    apply hω1
    calc ω = ω * ω ^ 2 := by rw [h2, mul_one]
      _ = ω ^ 3 := by ring
      _ = 1 := hω3
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 (by omega : 1 < I₀.card)
  set δ := CFSG.ComponentClassification.Burgoyne.U.uDiag2 h hij hω0 hωN with hδ
  set σ := CFSG.ComponentClassification.Burgoyne.U.uRot h hij with hσ
  have hδU : δ ∈ U := CFSG.ComponentClassification.Burgoyne.U.uDiag2_mem_uBlock h hij hi hj hω0 hωN
  have hσU : σ ∈ U := CFSG.ComponentClassification.Burgoyne.U.uRot_mem_uBlock h hij hi hj
  have hδ3 : δ ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hδ, CFSG.ComponentClassification.Burgoyne.U.coe_uDiag2,
      Subgroup.coe_one, Units.val_one, diagonal_pow, ← diagonal_one]
    congr 1
    funext k
    simp only [Pi.pow_apply]
    split_ifs
    · exact hω3
    · rw [inv_pow, hω3, inv_one]
    · exact one_pow 3
  have hne : δ * σ ≠ σ * δ := by
    intro e
    have e1 := congrArg
      (fun x : ↥(StatedSU 6 (2 ^ n) K) => ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j) e
    have hR : ∀ R : Matrix (Fin 6) (Fin 6) K,
        R = 1 - single i i 1 - single j j 1 + single i j 1 - single j i 1 → R i j = 1 := by
      rintro R rfl
      simp [Matrix.single_apply, hij, Ne.symm hij]
    simp only [Subgroup.coe_mul, Units.val_mul, hδ, hσ, CFSG.ComponentClassification.Burgoyne.U.coe_uDiag2,
      CFSG.ComponentClassification.Burgoyne.U.coe_uRot, diagonal_mul, mul_diagonal, hR _ rfl, hij,
      Ne.symm hij, ↓reduceIte, mul_one, one_mul] at e1
    apply hω2
    calc ω ^ 2 = ω * ω := sq ω
      _ = ω * ω⁻¹ := by rw [← e1]
      _ = 1 := mul_inv_cancel₀ hω0
  let x : ↥φ.range := ⟨φ ⟨δ, hδU⟩, ⟨_, rfl⟩⟩
  let y : ↥φ.range := ⟨φ ⟨σ, hσU⟩, ⟨_, rfl⟩⟩
  have hxy : x * y ≠ y * x := by
    intro e
    have e1 : φ (⟨δ, hδU⟩ * ⟨σ, hσU⟩) = φ (⟨σ, hσU⟩ * ⟨δ, hδU⟩) := by
      rw [map_mul, map_mul]
      exact congrArg Subtype.val e
    exact hne (congrArg Subtype.val (hinj e1))
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    change (φ ⟨δ, hδU⟩) ^ 3 = 1
    rw [← map_pow]
    have h1 : (⟨δ, hδU⟩ : ↥U) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hδ3)
    rw [h1, map_one]
  set xb : ↥φ.range ⧸ Subgroup.center ↥φ.range := (x : ↥φ.range ⧸ Subgroup.center ↥φ.range) with hxb
  have hxb1 : xb ≠ 1 := by
    intro e
    rw [hxb, QuotientGroup.eq_one_iff] at e
    exact hxy (Subgroup.mem_center_iff.1 e y).symm
  have hxb3 : xb ^ 3 = 1 := by
    rw [hxb, ← QuotientGroup.mk_pow, hx3, QuotientGroup.mk_one]
  rw [← orderOf_eq_prime hxb3 hxb1]
  exact orderOf_dvd_natCard xb

theorem u6_block_props [Finite K] (h : UnitaryFieldData 2 n K) (hn : Odd n) (hn1 : 1 < n)
    {I₀ : Finset (Fin 6)} (hI3 : 3 ≤ I₀.card) (hI6 : I₀.card < 6)
    (Y : primeFormUnitary h (idGram K 6))
    (hYdiag : ((Y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag) (hY3 : Y ^ 3 = 1)
    (hYI : ∀ i, ((Y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i i = 1 ↔ i ∈ I₀)
    (Δ₀ : Set (primeFormUnitary h (idGram K 6)))
    (hΔdiag : ∀ X ∈ Δ₀, ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag)
    (hΔI : ∀ X ∈ Δ₀, ∀ i ∈ I₀, ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i i = 1) :
    ∃ Jb : Subgroup (primeFormP h (idGram K 6)),
      GLAPComponent 3 (fixSubgroup (primeFormConjHom h (idGram K 6) Y)) Jb ∧
      (∀ X ∈ Δ₀, Jb ≤ fixSubgroup (primeFormConjHom h (idGram K 6) X)) ∧
      catalogIs (PSimple 3 Jb) (S10.isUrn n) := by
  haveI : CharP K 2 := h.charP
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set U := CFSG.ComponentClassification.Burgoyne.U.uBlock 2 n K I₀
  set φ := (blk_jMap h).comp U.subtype
  have hinj : Function.Injective φ := blk_inj h hI6
  have hJY : φ.range ≤ fixSubgroup (primeFormConjHom h (idGram K 6) Y) := by
    rintro _ ⟨⟨g, hg⟩, rfl⟩
    exact blk_mem_fix h hYdiag (fun i hi => (hYI i).2 hi) hg
  let e : ↥(StatedSU I₀.card (2 ^ n) K) ≃* ↥φ.range :=
    (CFSG.ComponentClassification.Burgoyne.U.uBlockEquiv h I₀).trans (MonoidHom.ofInjective hinj)
  have hq2 : (I₀.card, 2 ^ n) ≠ (3, 2) := by
    intro h32
    have h2n : 2 ^ n = 2 := congrArg Prod.snd h32
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
    omega
  have hQ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := K) (p := 2) (f := n)
    h.card_eq_sq hI3 hq2
  have hQJ : CFSG.IsQuasisimple ↥φ.range := CFSG.LocalCores.isQuasisimple_of_mulEquiv e hQ.1
  have hq : CFSG.Open.IsQuasisimple ↥φ.range := ⟨hQJ.1.commutator_eq_top, hQJ.2.1⟩
  have h3 : 3 ∣ Nat.card (↥φ.range ⧸ Subgroup.center ↥φ.range) := blk_three_dvd h hn hI3 hinj
  refine ⟨φ.range, ?_, ?_, ?_⟩
  · exact CFSG.LocalAnalysis.GLTheoremA.S10.glaPComponent_of_quasisimple Nat.prime_three
      (IsSubnormal.step hJY (blk_normal h hI3 hYdiag hYI hJY) (IsSubnormal.refl _)) hq h3
  · intro X hX
    rintro _ ⟨⟨g, hg⟩, rfl⟩
    exact blk_mem_fix h (hΔdiag X hX) (hΔI X hX) hg
  · haveI : Fintype K := Fintype.ofFinite K
    have hKc : Fintype.card K = (2 ^ n) ^ 2 := by
      rw [← Nat.card_eq_fintype_card]
      exact h.card_eq_sq
    obtain ⟨q', hv, hq'p, hq'card, ⟨eT⟩⟩ :=
      CFSG.Adapters.CatalogueFieldBridges.exists_twistedA_mulEquiv_centerQuotient_statedSU hKc hI3 hq2
    obtain ⟨eP⟩ := CFSG.LocalAnalysis.GLTheoremA.S172A.pSimple_equiv_centerQuot hq
      (h3.trans (Subgroup.card_quotient_dvd_card _))
    let eC : ↥(StatedSU I₀.card (2 ^ n) K) ⧸ Subgroup.center ↥(StatedSU I₀.card (2 ^ n) K) ≃*
        ↥φ.range ⧸ Subgroup.center ↥φ.range :=
      QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
    refine ⟨.lie ⟨.twistedA (I₀.card - 1) q', hv⟩, ?_, ⟨(eP.symm.trans eC.symm).trans eT⟩⟩
    have hp2 : q'.p = 2 := by
      rw [hq'p]
      exact ringChar.eq K 2
    have hexp : q'.exponent = n := by
      have hc := hq'card
      rw [TauCeti.PrimePower.card_def, hp2] at hc
      exact Nat.pow_right_injective (le_refl 2) hc
    show 2 ≤ I₀.card - 1 ∧ q'.p = 2 ∧ q'.exponent = n
    exact ⟨by omega, hp2, hexp⟩

private theorem cj_mul_diag_entry {A B : Matrix (Fin 6) (Fin 6) K} (hA : A.IsDiag) (i : Fin 6) :
    (A * B) i i = A i i * B i i := by
  have e : (A * B) i i = (Matrix.diagonal A.diag * B) i i := by rw [hA.diagonal_diag]
  rw [e, Matrix.diagonal_mul]
  rfl

private theorem cj_diag_entry_pow_three {h : UnitaryFieldData 2 n K}
    {X : primeFormUnitary h (idGram K 6)}
    (hX : ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag) (h3 : X ^ 3 = 1) (i : Fin 6) :
    (((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i i) ^ 3 = 1 := by
  have h1 : ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, h3, Subgroup.coe_one, Units.val_one]
  have h2 := congrFun (congrFun h1 i) i
  rw [← hX.diagonal_diag, Matrix.diagonal_pow, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h2
  exact h2

private def cj_coordKer {h : UnitaryFieldData 2 n K} (D : Subgroup (primeFormUnitary h (idGram K 6)))
    (hD : ∀ X ∈ D, ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag) (i : Fin 6) :
    Subgroup (primeFormUnitary h (idGram K 6)) where
  carrier := {X | X ∈ D ∧ ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i i = 1}
  one_mem' := ⟨D.one_mem, by simp⟩
  mul_mem' := by
    rintro X Y ⟨hX, hXi⟩ ⟨hY, hYi⟩
    refine ⟨D.mul_mem hX hY, ?_⟩
    show (((X * Y : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i i = 1
    rw [Subgroup.coe_mul, Units.val_mul, cj_mul_diag_entry (hD X hX), hXi, hYi, one_mul]
  inv_mem' := by
    rintro X ⟨hX, hXi⟩
    refine ⟨D.inv_mem hX, ?_⟩
    have h1 : ((((X⁻¹ : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) i i = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one,
        Matrix.one_apply_eq]
    rwa [cj_mul_diag_entry (hD _ (D.inv_mem hX)), hXi, mul_one] at h1

private theorem cj_mem_coordKer {h : UnitaryFieldData 2 n K} {D : Subgroup (primeFormUnitary h (idGram K 6))}
    {hD : ∀ X ∈ D, ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag} {i : Fin 6}
    {X : primeFormUnitary h (idGram K 6)} :
    X ∈ cj_coordKer D hD i ↔ X ∈ D ∧ ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i i = 1 :=
  Iff.rfl

private theorem cj_card_le_three_mul [Finite K] {h : UnitaryFieldData 2 n K}
    (D : Subgroup (primeFormUnitary h (idGram K 6)))
    (hD : ∀ X ∈ D, ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag)
    (hD3 : ∀ X ∈ D, X ^ 3 = 1) (i : Fin 6) :
    Nat.card D ≤ 3 * Nat.card (cj_coordKer D hD i) := by
  classical
  have := h.finite
  have hne : ∀ X : D, (((X : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) i i ≠ 0 := by
    intro X h0
    have := cj_diag_entry_pow_three (hD X X.2) (hD3 X X.2) i
    rw [h0] at this
    norm_num at this
  let χ : D →* Kˣ :=
    { toFun := fun X => Units.mk0 _ (hne X)
      map_one' := Units.ext (by simp)
      map_mul' := fun X Y => Units.ext (by
        simp only [Units.val_mk0, Units.val_mul, Subgroup.coe_mul]
        exact cj_mul_diag_entry (hD X X.2) i) }
  have hker : Nat.card χ.ker = Nat.card (cj_coordKer D hD i) := by
    have e : χ.ker = (cj_coordKer D hD i).subgroupOf D := by
      ext X
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, cj_mem_coordKer, Units.ext_iff]
      simp [χ, X.2]
    rw [e]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (fun X hX => (cj_mem_coordKer.1 hX).1)).toEquiv
  have hrange : Nat.card χ.range ≤ 3 := by
    have hsub : χ.range ≤ rootsOfUnity 3 K := by
      rintro _ ⟨X, rfl⟩
      rw [mem_rootsOfUnity]
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val, Units.val_one]
      exact cj_diag_entry_pow_three (hD X X.2) (hD3 X X.2) i
    have h1 : Nat.card χ.range ≤ Nat.card (rootsOfUnity 3 K) := Subgroup.card_le_of_le hsub
    have h2 : Nat.card (rootsOfUnity 3 K) ≤ 3 := card_rootsOfUnity K 3
    exact h1.trans h2
  have hmul := Subgroup.card_mul_index χ.ker
  rw [Subgroup.index_ker] at hmul
  rw [← hker, ← hmul, mul_comm]
  exact Nat.mul_le_mul_right _ hrange

private theorem cj_exists_avoid {G : Type*} [Group G] [Finite G] (hG : IsPGroup 3 G)
    (s : Finset (Fin 6)) (hs : s.card ≤ 3) (H : Fin 6 → Subgroup G) (hH : ∀ i ∈ s, H i ≠ ⊤) :
    ∃ g : G, ∀ i ∈ s, g ∉ H i := by
  classical
  by_contra hcon
  push Not at hcon
  haveI := Fintype.ofFinite G
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hG
  have hHcard : ∀ i ∈ s, 3 * Nat.card (H i) ≤ Nat.card G := by
    intro i hi
    have hmul := Subgroup.card_mul_index (H i)
    have hidx1 : (H i).index ≠ 1 := fun h1 => hH i hi (Subgroup.index_eq_one.1 h1)
    have hdvd : (H i).index ∣ 3 ^ k := hk ▸ Subgroup.index_dvd_card (H i)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hidx1 (by simpa using hj)
    have h3 : 3 ≤ (H i).index := by
      rw [hj]
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hj0)
    rw [← hmul, mul_comm]
    exact Nat.mul_le_mul_left _ h3
  have hsub : (Finset.univ : Finset G).erase 1 ⊆
      s.biUnion (fun i => ((H i : Set G).toFinset).erase 1) := by
    intro g hg
    obtain ⟨i, hi, hgi⟩ := hcon g
    rw [Finset.mem_biUnion]
    refine ⟨i, hi, ?_⟩
    rw [Finset.mem_erase] at hg ⊢
    exact ⟨hg.1, by simpa using hgi⟩
  have hc1 := Finset.card_le_card hsub
  have hc2 := Finset.card_biUnion_le (s := s) (t := fun i => ((H i : Set G).toFinset).erase 1)
  have hc3 : ∀ i ∈ s, (((H i : Set G).toFinset).erase 1).card + 1 = Nat.card (H i) := by
    intro i _
    rw [Finset.card_erase_of_mem (by simp), Set.toFinset_card, Nat.sub_add_cancel]
    · rw [Nat.card_eq_fintype_card]; rfl
    · exact Fintype.card_pos
  have hG1 : 1 ≤ Nat.card G := Nat.card_pos
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ← Nat.card_eq_fintype_card]
    at hc1
  have hsum : 3 * ∑ i ∈ s, (((H i : Set G).toFinset).erase 1).card ≤ s.card * (Nat.card G - 3) := by
    rw [Finset.mul_sum]
    calc ∑ i ∈ s, 3 * (((H i : Set G).toFinset).erase 1).card ≤ ∑ _i ∈ s, (Nat.card G - 3) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have := hc3 i hi
          have := hHcard i hi
          omega
      _ = s.card * (Nat.card G - 3) := by rw [Finset.sum_const, smul_eq_mul]
  rcases s.eq_empty_or_nonempty with hs0 | ⟨i₀, hi₀⟩
  · obtain ⟨i, hi, -⟩ := hcon 1
    rw [hs0] at hi
    exact absurd hi (Finset.notMem_empty i)
  · have h3G : 3 ≤ Nat.card G := by
      have := hHcard i₀ hi₀
      have : 1 ≤ Nat.card (H i₀) := Nat.card_pos
      omega
    have : s.card * (Nat.card G - 3) ≤ 3 * (Nat.card G - 3) := Nat.mul_le_mul_right _ hs
    omega

theorem u6MatConcl_of_diag [Finite K] (h : UnitaryFieldData 2 n K) (hn : Odd n) (hn1 : 1 < n)
    {Δ : Subgroup (primeFormUnitary h (idGram K 6))}
    (hdiag : ∀ X ∈ Δ, ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag)
    (hcube : ∀ X ∈ Δ, X ^ 3 = 1) {a b : Fin 6} (hab : a ≠ b)
    (ha : ∀ X ∈ Δ, ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) a a = 1)
    (hb : ∀ X ∈ Δ, ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) b b = 1)
    (hcard : 27 ≤ Nat.card Δ) :
    U6MatConcl h (Δ.map (primeFormConjHom h (idGram K 6))) := by
  classical
  have := h.finite
  set c := primeFormConjHom h (idGram K 6) with hc
  have hM1 : ∀ X : primeFormUnitary h (idGram K 6),
      ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 → X = 1 := by
    intro X hX
    exact Subtype.ext (Units.ext hX)
  have h6 : ¬(6 = 3 ∧ 2 ^ n = 2) := fun h' => by omega
  have hinjΔ : ∀ X ∈ Δ, c X = 1 → X = 1 := by
    intro X hX hcX
    obtain ⟨u, -, hu⟩ := (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.primeFormConjHom_eq_one_iff h
      (by norm_num) h6 X).1 hcX
    have hua : (u : K) = 1 := by
      have e := ha X hX
      rw [hu, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at e
      exact e
    apply Subtype.ext
    rw [hu, Subgroup.coe_one, show u = 1 from Units.ext hua, map_one]
  have hcinj : Function.Injective (c.comp Δ.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro X hX
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hX
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hinjΔ X X.2 hX)
  have hcardmap : ∀ D : Subgroup (primeFormUnitary h (idGram K 6)), D ≤ Δ →
      Nat.card (D.map c) = Nat.card D := by
    intro D hD
    have e : D.map c = (D.subgroupOf Δ).map (c.comp Δ.subtype) := by
      ext Y
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.coe_comp, Function.comp_apply,
        Subgroup.coe_subtype]
      constructor
      · rintro ⟨X, hX, rfl⟩
        exact ⟨⟨X, hD hX⟩, hX, rfl⟩
      · rintro ⟨X, hX, rfl⟩
        exact ⟨X, hX, rfl⟩
    rw [e, Subgroup.card_map_of_injective hcinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD).toEquiv
  obtain ⟨X₀, hX₀, c₀, hX₀c⟩ : ∃ X₀ ∈ Δ, ∃ c₀ : Fin 6,
      ((X₀ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) c₀ c₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ X ∈ Δ, X = 1 := by
      intro X hX
      apply hM1
      rw [← (hdiag X hX).diagonal_diag]
      ext i j
      simp only [Matrix.diag, hcon X hX, Matrix.diagonal_apply, Matrix.one_apply]
    have hbot : Δ = ⊥ := (Subgroup.eq_bot_iff_forall Δ).2 hall
    have : Nat.card Δ = 1 := by rw [hbot, Subgroup.card_bot]
    omega
  have hca : c₀ ≠ a := fun h' => hX₀c (h' ▸ ha X₀ hX₀)
  have hcb : c₀ ≠ b := fun h' => hX₀c (h' ▸ hb X₀ hX₀)
  set Δ₀ := cj_coordKer Δ hdiag c₀ with hΔ₀def
  have hΔ₀Δ : Δ₀ ≤ Δ := fun X hX => (cj_mem_coordKer.1 hX).1
  have hΔ₀diag : ∀ X ∈ Δ₀, ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag :=
    fun X hX => hdiag X (hΔ₀Δ hX)
  have hΔ₀3 : ∀ X ∈ Δ₀, X ^ 3 = 1 := fun X hX => hcube X (hΔ₀Δ hX)
  have hidx : Nat.card Δ ≤ 3 * Nat.card Δ₀ := cj_card_le_three_mul Δ hdiag hcube c₀
  have hΔ₀card : 9 ≤ Nat.card Δ₀ := by omega
  set I₀ : Finset (Fin 6) := Finset.univ.filter
    (fun l => ∀ X ∈ Δ₀, ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) l l = 1) with hI₀def
  have hmemI₀ : ∀ l, l ∈ I₀ ↔ ∀ X ∈ Δ₀, ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) l l = 1 := by
    intro l
    simp [hI₀def]
  have haI : a ∈ I₀ := (hmemI₀ a).2 fun X hX => ha X (hΔ₀Δ hX)
  have hbI : b ∈ I₀ := (hmemI₀ b).2 fun X hX => hb X (hΔ₀Δ hX)
  have hcI : c₀ ∈ I₀ := (hmemI₀ c₀).2 fun X hX => (cj_mem_coordKer.1 hX).2
  have hI3 : 3 ≤ I₀.card := by
    have hsub : ({a, b, c₀} : Finset (Fin 6)) ⊆ I₀ := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact haI
      · exact hbI
      · exact hcI
    have h3 : ({a, b, c₀} : Finset (Fin 6)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hab, hca.symm]), Finset.card_pair hcb.symm]
    exact h3 ▸ Finset.card_le_card hsub
  have hI6 : I₀.card < 6 := by
    by_contra hcon
    have hI : I₀ = Finset.univ :=
      Finset.eq_univ_of_card I₀ (by rw [Fintype.card_fin]; have := Finset.card_le_univ I₀; simp at this; omega)
    have hall : ∀ X ∈ Δ₀, X = 1 := by
      intro X hX
      apply hM1
      rw [← (hΔ₀diag X hX).diagonal_diag]
      ext i j
      have hi := (hmemI₀ i).1 (hI ▸ Finset.mem_univ i) X hX
      simp only [Matrix.diag, hi, Matrix.diagonal_apply, Matrix.one_apply]
    have hbot : Δ₀ = ⊥ := (Subgroup.eq_bot_iff_forall Δ₀).2 hall
    have : Nat.card Δ₀ = 1 := by rw [hbot, Subgroup.card_bot]
    omega
  have hΔ₀p : IsPGroup 3 Δ₀ := by
    intro X
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hΔ₀3 X X.2
  let H : Fin 6 → Subgroup Δ₀ := fun l => (cj_coordKer Δ₀ hΔ₀diag l).subgroupOf Δ₀
  have hH : ∀ l ∈ I₀ᶜ, H l ≠ ⊤ := by
    intro l hl htop
    apply Finset.mem_compl.1 hl
    refine (hmemI₀ l).2 fun X hX => ?_
    have h1 := (Subgroup.eq_top_iff' _).1 htop ⟨X, hX⟩
    rw [Subgroup.mem_subgroupOf] at h1
    exact (cj_mem_coordKer.1 h1).2
  have hs : I₀ᶜ.card ≤ 3 := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨Y, hY⟩ := cj_exists_avoid hΔ₀p I₀ᶜ hs H hH
  have hYI : ∀ i, (((Y : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) i i = 1 ↔ i ∈ I₀ := by
    intro i
    constructor
    · intro h1
      by_contra hi
      exact hY i (Finset.mem_compl.2 hi) (by
        rw [Subgroup.mem_subgroupOf]
        exact cj_mem_coordKer.2 ⟨Y.2, h1⟩)
    · intro hi
      exact (hmemI₀ i).1 hi Y Y.2
  have hY1 : (Y : primeFormUnitary h (idGram K 6)) ≠ 1 := by
    obtain ⟨l, hl⟩ : ∃ l, l ∉ I₀ := by
      by_contra hcon
      push Not at hcon
      have : I₀ = Finset.univ := Finset.eq_univ_iff_forall.2 hcon
      rw [this, Finset.card_univ, Fintype.card_fin] at hI6
      omega
    intro h1
    apply hl
    rw [← hYI l, h1]
    simp
  obtain ⟨Jb, hJb, hJbE, hJbcat⟩ := u6_block_props h hn hn1 hI3 hI6 (Y : primeFormUnitary h (idGram K 6))
    (hΔ₀diag _ Y.2) (hΔ₀3 _ Y.2) hYI (Δ₀ : Set (primeFormUnitary h (idGram K 6))) hΔ₀diag
    (fun X hX i hi => (hmemI₀ i).1 hi X hX)
  obtain ⟨Tb', hTb2, hTbfix, hTbN, hTbA, hTbcard⟩ := u6_root_props h hn hn1 hdiag hcube hab hca.symm
    hcb.symm ha hb (Y : primeFormUnitary h (idGram K 6)) (hΔ₀diag _ Y.2) (ha _ (hΔ₀Δ Y.2))
    (hb _ (hΔ₀Δ Y.2)) (cj_mem_coordKer.1 Y.2).2 hX₀ hX₀c
  refine ⟨Δ₀.map c, c Y, Subgroup.map_mono hΔ₀Δ, ?_, Subgroup.mem_map_of_mem c Y.2, ?_,
    ⟨Jb, hJb, ?_, hJbcat⟩, Tb', hTb2, hTbfix, ?_, ?_, hTbcard⟩
  · rw [hcardmap Δ le_rfl, hcardmap Δ₀ hΔ₀Δ]
    exact hidx
  · intro h1
    exact hY1 (hinjΔ Y (hΔ₀Δ Y.2) h1)
  · rintro _ ⟨X, hX, rfl⟩
    exact hJbE X hX
  · rintro _ ⟨X, hX, rfl⟩
    exact hTbN X hX
  · obtain ⟨t, ht, hmove⟩ := hTbA
    exact ⟨c X₀, Subgroup.mem_map_of_mem c hX₀, t, ht, hmove⟩

private noncomputable def eig_res {U : Subgroup (GL (Fin 6) K)} (A : Subgroup U)
    (W : Submodule K (Fin 6 → K))
    (hW : ∀ X ∈ A, ∀ w ∈ W, (((X : U) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ w ∈ W) :
    A →* Module.End K W where
  toFun X := LinearMap.restrict
    (Matrix.mulVecLin ((((X : A) : U) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))
    (fun w hw => hW X.1 X.2 w hw)
  map_one' := by
    ext w
    simp
  map_mul' X Y := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    exact (Matrix.mulVec_mulVec (w : Fin 6 → K) _ _).symm

private theorem eig_res_apply {U : Subgroup (GL (Fin 6) K)} (A : Subgroup U)
    (W : Submodule K (Fin 6 → K))
    (hW : ∀ X ∈ A, ∀ w ∈ W, (((X : U) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ w ∈ W)
    (X : A) (w : W) :
    ((eig_res A W hW X w : W) : Fin 6 → K) =
      ((((X : A) : U) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ (w : Fin 6 → K) :=
  rfl

private theorem eig_scalar_mulVec (a : K) (v : Fin 6 → K) :
    Matrix.scalar (Fin 6) a *ᵥ v = a • v := by
  funext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

private theorem eig_two_pow_mod (hn : Odd n) : ∃ k : ℕ, 2 ^ n = 3 * k + 2 := by
  obtain ⟨m, rfl⟩ := hn
  refine ⟨2 ^ (2 * m + 1) / 3, ?_⟩
  have h1 : 2 ^ (2 * m + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * m + 1) = x at h1 ⊢
  omega

private theorem eig_finrank_le_three {p f : ℕ} (h : UnitaryFieldData p f K)
    {W : Submodule K (Fin 6 → K)} (hiso : W ≤ W.orthogonalBilin (idForm h 6)) :
    Module.finrank K W ≤ 3 := by
  have hσ : Function.Surjective h.bar := fun c => ⟨h.bar c, UnitaryFieldData.bar_bar h c⟩
  have h1 := CFSG.HardMathSupport.Curtis.UnitaryLevi.finrank_orthogonalBilin_eq hσ
    (CFSG.RankThree.PartOne.KCUnitaryModel.idForm_separatingLeft h 6) W
  have h2 := Submodule.finrank_mono hiso
  rw [Module.finrank_fin_fun] at h1
  omega

private theorem eig_orth_le {p f : ℕ} (h : UnitaryFieldData p f K) {W : Submodule K (Fin 6 → K)}
    (hiso : W ≤ W.orthogonalBilin (idForm h 6)) (hd : Module.finrank K W = 3) :
    W.orthogonalBilin (idForm h 6) ≤ W := by
  have hσ : Function.Surjective h.bar := fun c => ⟨h.bar c, UnitaryFieldData.bar_bar h c⟩
  have h1 := CFSG.HardMathSupport.Curtis.UnitaryLevi.finrank_orthogonalBilin_eq hσ
    (CFSG.RankThree.PartOne.KCUnitaryModel.idForm_separatingLeft h 6) W
  rw [Module.finrank_fin_fun] at h1
  have heq : W = W.orthogonalBilin (idForm h 6) :=
    Submodule.eq_of_le_of_finrank_eq hiso (by omega)
  exact heq.symm.le

private theorem eig_sq_of_scalar [CharP K 2] {p f : ℕ} (h : UnitaryFieldData p f K)
    {X : GL (Fin 6) K} (hX : X ∈ primeFormUnitary h (idGram K 6)) {W : Submodule K (Fin 6 → K)}
    (hWW : W.orthogonalBilin (idForm h 6) ≤ W) {μ : K} (hμN : h.norm μ = 1)
    (hfix : ∀ u ∈ W, (X : Matrix (Fin 6) (Fin 6) K) *ᵥ u = μ • u) (v : Fin 6 → K) :
    (X : Matrix (Fin 6) (Fin 6) K) *ᵥ ((X : Matrix (Fin 6) (Fin 6) K) *ᵥ v) = (μ ^ 2) • v := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hN : μ * h.bar μ = 1 := hμN
  have hy : ((X : Matrix (Fin 6) (Fin 6) K) *ᵥ v - μ • v) ∈ W.orthogonalBilin (idForm h 6) := by
    rw [Submodule.mem_orthogonalBilin_iff]
    intro u hu
    have e := CFSG.LocalAnalysis.GLTheoremA.HDescUniRes.idForm_mulVec_of_mem_primeFormUnitary hX u v
    rw [hfix u hu, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at e
    rw [map_sub, map_smul, smul_eq_mul]
    linear_combination μ * e - (idForm h 6 u ((X : Matrix (Fin 6) (Fin 6) K) *ᵥ v)) * hN
  have h3 := hfix _ (hWW hy)
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul] at h3
  funext i
  have h4 := congrFun h3 i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h4 ⊢
  linear_combination h4 + (μ * ((X : Matrix (Fin 6) (Fin 6) K) *ᵥ v) i - μ ^ 2 * v i) * h2

private theorem eig_conj_eq_one_of_scalar [Finite K] (h : UnitaryFieldData 2 n K) (hn : Odd n)
    (X : primeFormUnitary h (idGram K 6)) (hX3 : primeFormConjHom h (idGram K 6) X ^ 3 = 1)
    {W : Submodule K (Fin 6 → K)} (hW : W ≠ ⊥) (hWW : W.orthogonalBilin (idForm h 6) ≤ W)
    {μ : K} (hμ : ∀ w ∈ W, ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ w = μ • w) :
    primeFormConjHom h (idGram K 6) X = 1 := by
  have := h.charP
  have hq : ¬(6 = 3 ∧ 2 ^ n = 2) := fun h' => absurd h'.1 (by norm_num)
  rw [← map_pow] at hX3
  obtain ⟨l, hlN, hl⟩ :=
    (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.primeFormConjHom_eq_one_iff h (n := 6)
      (by norm_num) hq (X ^ 3)).1 hX3
  set M := ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) with hM
  have hM3 : M ^ 3 = Matrix.scalar (Fin 6) (l : K) := by
    have e := congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) hl
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar] at e
    exact e
  have hM3v : ∀ v, M *ᵥ (M *ᵥ (M *ᵥ v)) = (l : K) • v := by
    intro v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← pow_three', hM3, eig_scalar_mulVec]
  obtain ⟨w₀, hw₀, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hμl : μ ^ 3 = l := by
    have e := hM3v w₀
    rw [hμ w₀ hw₀, Matrix.mulVec_smul, hμ w₀ hw₀, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hμ w₀ hw₀, smul_smul, smul_smul] at e
    have e' : (μ ^ 3) • w₀ = (l : K) • w₀ := by
      rw [← e]
      ring_nf
    exact smul_left_injective K hw₀0 e'
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num)] at hμl
    exact l.ne_zero hμl.symm
  obtain ⟨k, hk⟩ := eig_two_pow_mod hn
  letI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = (3 * k + 2) ^ 2 := by
    rw [← Nat.card_eq_fintype_card, h.card_eq_sq, hk]
  have hμpow : μ ^ ((3 * k + 3) * (3 * k + 1)) = 1 := by
    have e := FiniteField.pow_card_sub_one_eq_one μ hμ0
    rw [hcardK] at e
    have e2 : (3 * k + 2) ^ 2 - 1 = (3 * k + 3) * (3 * k + 1) := by
      have : (3 * k + 2) ^ 2 = (3 * k + 3) * (3 * k + 1) + 1 := by ring
      omega
    rw [e2] at e
    exact e
  have hlq : (l : K) ^ (3 * k + 3) = 1 := by
    rw [h.norm_eq_pow, hk] at hlN
    exact hlN
  set t := μ ^ (3 * k + 3) with ht
  have ht3 : t ^ 3 = 1 := by
    rw [ht, ← pow_mul, mul_comm, pow_mul, hμl, hlq]
  have htq : t ^ (3 * k + 1) = 1 := by
    rw [ht, ← pow_mul]
    exact hμpow
  have ht1 : t = 1 := by
    have e : t ^ (3 * k + 1) = (t ^ 3) ^ k * t := by ring
    rw [ht3, one_pow, one_mul, htq] at e
    exact e.symm
  have hμN : h.norm μ = 1 := by
    rw [h.norm_eq_pow, hk]
    exact ht1
  have hsq := eig_sq_of_scalar h X.2 hWW hμN hμ
  have hXv : ∀ v, M *ᵥ v = μ • v := by
    intro v
    have e1 : μ ^ 2 • (M *ᵥ v) = μ ^ 2 • (μ • v) := by
      rw [← hsq (M *ᵥ v), hM3v v, ← hμl, smul_smul]
      ring_nf
    exact smul_right_injective (Fin 6 → K) (pow_ne_zero 2 hμ0) e1
  have hXμ : M = Matrix.scalar (Fin 6) μ := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [hXv v, eig_scalar_mulVec]
  apply (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.primeFormConjHom_eq_one_iff h (n := 6)
    (by norm_num) hq X).2
  refine ⟨Units.mk0 μ hμ0, by rw [Units.val_mk0]; exact hμN, ?_⟩
  apply Units.ext
  rw [GeneralLinearGroup.coe_scalar, Units.val_mk0]
  exact hXμ

private theorem eig_not_three [Finite K] (h : UnitaryFieldData 2 n K) (hn : Odd n)
    {Ah : Subgroup (primeFormUnitary h (idGram K 6))}
    (hAbel : IsElemAbelian 3 (Ah.map (primeFormConjHom h (idGram K 6))))
    (hcard : 27 ≤ Nat.card (Ah.map (primeFormConjHom h (idGram K 6))))
    {W : Submodule K (Fin 6 → K)} (hW : W ≠ ⊥) (hiso : W ≤ W.orthogonalBilin (idForm h 6))
    (hWAh : ∀ X ∈ Ah, ∀ w ∈ W, ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ w ∈ W)
    (h3 : Module.finrank K W = 3) : False := by
  classical
  have hWW := eig_orth_le h hiso h3
  have hq : ¬(6 = 3 ∧ 2 ^ n = 2) := fun h' => absurd h'.1 (by norm_num)
  set c := primeFormConjHom h (idGram K 6) with hc
  let b := Module.finBasisOfFinrankEq K W h3
  let e : (Module.End K W)ˣ ≃* GL (Fin 3) K :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv
  let r : Ah →* GL (Fin 3) K := e.toMonoidHom.comp (eig_res Ah W hWAh).toHomUnits
  have hr : ∀ X : Ah, ((r X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      LinearMap.toMatrixAlgEquiv b (eig_res Ah W hWAh X) := fun X => rfl
  have hkey : ∀ X : Ah, c X = 1 ↔ r X ∈ Subgroup.center (GL (Fin 3) K) := by
    intro X
    rw [CFSG.HardMathSupport.Timmesfeld.LinearRank.mem_center_iff]
    constructor
    · intro hX
      obtain ⟨s, -, hs⟩ :=
        (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.primeFormConjHom_eq_one_iff h (n := 6)
          (by norm_num) hq (X : primeFormUnitary h (idGram K 6))).1 hX
      have hres : eig_res Ah W hWAh X = algebraMap K (Module.End K W) (s : K) := by
        refine LinearMap.ext fun w => Subtype.ext ?_
        rw [eig_res_apply, Module.algebraMap_end_apply, Submodule.coe_smul, hs,
          GeneralLinearGroup.coe_scalar, eig_scalar_mulVec]
      refine ⟨s, Units.ext ?_⟩
      rw [hr, hres, AlgEquiv.commutes, GeneralLinearGroup.coe_scalar]
      rfl
    · rintro ⟨s, hs⟩
      have hres : eig_res Ah W hWAh X = algebraMap K (Module.End K W) (s : K) := by
        apply (LinearMap.toMatrixAlgEquiv b).injective
        rw [← hr, hs, AlgEquiv.commutes, GeneralLinearGroup.coe_scalar]
        rfl
      refine eig_conj_eq_one_of_scalar h hn (X : primeFormUnitary h (idGram K 6))
        (hAbel.2 _ (Subgroup.mem_map_of_mem c X.2)) hW hWW (μ := (s : K)) fun w hw => ?_
      have e := congrArg (fun φ : Module.End K W => ((φ ⟨w, hw⟩ : W) : Fin 6 → K)) hres
      simp only [eig_res_apply, Module.algebraMap_end_apply, Submodule.coe_smul] at e
      exact e
  have hker : r.rangeRestrict.ker ≤ (c.comp Ah.subtype).ker := by
    intro X hX
    rw [MonoidHom.mem_ker] at hX ⊢
    have hX' : r X = 1 := congrArg Subtype.val hX
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, hkey X, hX']
    exact Subgroup.one_mem _
  let ρ : r.range →* MulAut (primeFormP h (idGram K 6)) :=
    r.rangeRestrict.liftOfSurjective r.rangeRestrict_surjective ⟨c.comp Ah.subtype, hker⟩
  have hρ : ∀ X : Ah, ρ (r.rangeRestrict X) = c X := fun X =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ X
  have hρker : ∀ A : r.range, ρ A = 1 ↔ (A : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) := by
    intro A
    obtain ⟨X, rfl⟩ := r.rangeRestrict_surjective A
    rw [hρ X, MonoidHom.coe_rangeRestrict]
    exact hkey X
  have hle : Ah.map c ≤ ρ.range := by
    rintro _ ⟨X, hX, rfl⟩
    exact ⟨r.rangeRestrict ⟨X, hX⟩, hρ ⟨X, hX⟩⟩
  obtain ⟨k, hk⟩ := eig_two_pow_mod hn
  have hpK : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card_eq_sq, hk]
    refine ⟨3 * k ^ 2 + 4 * k + 1, ?_⟩
    have : (3 * k + 2) ^ 2 = 3 * (3 * k ^ 2 + 4 * k + 1) + 1 := by ring
    omega
  have hb := CFSG.HardMathSupport.Timmesfeld.LinearRank.card_le_of_scalar_kernel (n := 3)
    Nat.prime_three (by norm_num) hpK (by norm_num) r.range ρ hρker (Ah.map c) hle hAbel
  rw [show (3 : ℕ) ^ (3 - 1) = 9 by norm_num] at hb
  omega

private theorem eig_small [Finite K] (h : UnitaryFieldData 2 n K)
    {Ah : Subgroup (primeFormUnitary h (idGram K 6))}
    (hAbel : IsElemAbelian 3 (Ah.map (primeFormConjHom h (idGram K 6))))
    {W : Submodule K (Fin 6 → K)}
    (hWAh : ∀ X ∈ Ah, ∀ w ∈ W, ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ w ∈ W)
    (hnd : ¬ 3 ∣ Nat.card (Projectivization K W)) :
    ∃ w : Fin 6 → K, w ≠ 0 ∧ w ∈ W ∧
      ∀ X ∈ Ah, ∃ μ : K, ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ w = μ • w := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : ¬(6 = 3 ∧ 2 ^ n = 2) := fun h' => absurd h'.1 (by norm_num)
  set c := primeFormConjHom h (idGram K 6) with hc
  let f := c.subgroupMap Ah
  have hf : Function.Surjective f := c.subgroupMap_surjective Ah
  let g : Ah →* Equiv.Perm (Projectivization K W) :=
    (MulAction.toPermHom (LinearMap.GeneralLinearGroup K W) (Projectivization K W)).comp
      (eig_res Ah W hWAh).toHomUnits
  have hg : ∀ (X : Ah) (x : Projectivization K W), g X x = (eig_res Ah W hWAh).toHomUnits X • x :=
    fun X x => rfl
  have hker : f.ker ≤ g.ker := by
    intro X hX
    rw [MonoidHom.mem_ker] at hX ⊢
    have hcX : c X = 1 := by
      have := congrArg Subtype.val hX
      rwa [MonoidHom.subgroupMap_apply_coe] at this
    obtain ⟨s, -, hs⟩ :=
      (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.primeFormConjHom_eq_one_iff h (n := 6)
        (by norm_num) hq (X : primeFormUnitary h (idGram K 6))).1 hcX
    refine Equiv.ext fun x => ?_
    rw [hg, Equiv.Perm.coe_one, id]
    rw [← Projectivization.mk_rep x, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
    refine ⟨(s : K), Subtype.ext ?_⟩
    change (s : K) • (x.rep : Fin 6 → K) = ((eig_res Ah W hWAh X x.rep : W) : Fin 6 → K)
    rw [eig_res_apply, hs, GeneralLinearGroup.coe_scalar, eig_scalar_mulVec]
  let L := f.liftOfSurjective hf ⟨g, hker⟩
  have hL : ∀ X : Ah, L (f X) = g X := fun X =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ X
  letI : MulAction (Ah.map c) (Projectivization K W) := MulAction.compHom _ L
  have hP : IsPGroup 3 (Ah.map c) := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hAbel.2 x x.2)⟩
  obtain ⟨x, hx⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card (Projectivization K W) hnd
  refine ⟨(x.rep : Fin 6 → K), fun h0 => x.rep_nonzero (Subtype.ext h0), x.rep.2, fun X hX => ?_⟩
  have hgx : g ⟨X, hX⟩ x = x := by
    rw [← hL]
    exact MulAction.mem_fixedPoints.mp hx (f ⟨X, hX⟩)
  rw [hg] at hgx
  rw [← Projectivization.mk_rep x, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff'] at hgx
  obtain ⟨a, ha⟩ := hgx
  refine ⟨a, ?_⟩
  have e := congrArg Subtype.val ha
  exact e.symm

theorem u6_exists_common_eigenvector [Finite K] (h : UnitaryFieldData 2 n K) (hn : Odd n)
    (hn1 : 1 < n)
    {Ah : Subgroup (primeFormUnitary h (idGram K 6))}
    (hAbel : IsElemAbelian 3 (Ah.map (primeFormConjHom h (idGram K 6))))
    (hcard : 27 ≤ Nat.card (Ah.map (primeFormConjHom h (idGram K 6))))
    {W : Submodule K (Fin 6 → K)} (hW : W ≠ ⊥) (hiso : W ≤ W.orthogonalBilin (idForm h 6))
    (hWAh : ∀ X ∈ Ah, ∀ w ∈ W, ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ w ∈ W) :
    ∃ w : Fin 6 → K, w ≠ 0 ∧ w ∈ W ∧
      ∀ X ∈ Ah, ∃ μ : K, ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ w = μ • w := by
  have hd3 := eig_finrank_le_three h hiso
  have hd1 : 1 ≤ Module.finrank K W := Submodule.one_le_finrank_iff.mpr hW
  by_cases h3 : Module.finrank K W = 3
  · exact (eig_not_three h hn hAbel hcard hW hiso hWAh h3).elim
  · refine eig_small h hAbel hWAh ?_
    have hd : Module.finrank K W = 1 ∨ Module.finrank K W = 2 := by omega
    have h4 : 2 ^ (2 * n) % 3 = 1 := by
      rw [pow_mul, Nat.pow_mod]
      norm_num
    rcases hd with hd | hd
    · rw [Projectivization.card_of_finrank K W hd]
      norm_num
    · rw [Projectivization.card_of_finrank K W hd, h.card]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add]
      omega

private theorem cj_two_pow_mod_three (hn : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

private theorem cj_three_dvd (hn : Odd n) : 3 ∣ 2 ^ n + 1 := by
  have := cj_two_pow_mod_three hn
  omega

private theorem cj_coprime_three (hn : Odd n) : Nat.Coprime 3 (2 ^ n - 1) := by
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  have := cj_two_pow_mod_three hn
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

private theorem cj_pow_q_add_one [Finite K] (h : UnitaryFieldData 2 n K) (hn : Odd n) {μ : K}
    (hμ : μ ≠ 0) (h3 : (μ ^ 3) ^ (2 ^ n + 1) = 1) : μ ^ (2 ^ n + 1) = 1 := by
  have := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ n * 2 ^ n := by
    rw [← Nat.card_eq_fintype_card, h.card, two_mul, pow_add]
  have hq1 : μ ^ (Fintype.card K - 1) = 1 := FiniteField.pow_card_sub_one_eq_one μ hμ
  have hν3 : (μ ^ (2 ^ n + 1)) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact h3
  have hνq : (μ ^ (2 ^ n + 1)) ^ (2 ^ n - 1) = 1 := by
    rw [← pow_mul]
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ n * 2 ^ n := Nat.one_le_iff_ne_zero.2 (by positivity)
    have e : (2 ^ n + 1) * (2 ^ n - 1) = Fintype.card K - 1 := by
      rw [hcard]
      zify [h1, h2]
      ring
    rw [e]
    exact hq1
  exact (pow_eq_one_iff_of_coprime (cj_coprime_three hn)).1 ⟨hν3, hνq⟩

private theorem cj_exists_two_ne_zero (h : UnitaryFieldData 2 n K) {v : Fin 6 → K} (hv : v ≠ 0)
    (hiso : idForm h 6 v v = 0) : ∃ a b : Fin 6, a ≠ b ∧ v a ≠ 0 ∧ v b ≠ 0 := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, v a ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv (funext hc)
  by_contra hcon
  push Not at hcon
  have hsum : idForm h 6 v v = h.bar (v a) * v a := by
    show gramForm h (idGram K 6) v v = _
    rw [gramForm_apply, idGram, Units.val_one, Matrix.one_mulVec, dotProduct,
      Finset.sum_eq_single a]
    · intro b _ hba
      rw [hcon a b (Ne.symm hba) ha, mul_zero]
    · simp
  rw [hsum] at hiso
  have hbar : h.bar (v a) ≠ 0 := (map_ne_zero h.bar).2 ha
  exact mul_ne_zero hbar ha hiso

theorem u6MatConcl_of_twoGroup [Finite K] (h : UnitaryFieldData 2 n K) (hn : Odd n) (hn1 : 1 < n)
    {Ab : Subgroup (MulAut (primeFormP h (idGram K 6)))}
    (hAbD : Ab ≤ primeFormD h (idGram K 6)) (hAbel : IsElemAbelian 3 Ab) (hAbcard : 27 ≤ Nat.card Ab)
    {Tb : Subgroup (primeFormP h (idGram K 6))} (hTb2 : IsPGroup 2 Tb)
    (hTbN : ∀ α ∈ Ab, Tb.map α.toMonoidHom = Tb) (hTbA : ∃ α ∈ Ab, ∃ t ∈ Tb, α t ≠ t) :
    U6MatConcl h Ab := by
  classical
  have := h.finite
  haveI : CharP K 2 := h.charP
  set c := primeFormConjHom h (idGram K 6) with hc
  have h6 : ¬(6 = 3 ∧ 2 ^ n = 2) := fun h' => absurd h'.1 (by norm_num)
  have hker : ∀ X : primeFormUnitary h (idGram K 6), c X = 1 →
      ∃ u : Kˣ, h.norm (u : K) = 1 ∧ (X : GL (Fin 6) K) = Matrix.GeneralLinearGroup.scalar (Fin 6) u :=
    fun X hX => (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.primeFormConjHom_eq_one_iff h
      (by norm_num) h6 X).1 hX
  have hscalar_c : ∀ (u : Kˣ) (hu : h.norm (u : K) = 1),
      c ⟨Matrix.GeneralLinearGroup.scalar (Fin 6) u, scalar_mem_primeFormUnitary_one h hu⟩ = 1 :=
    fun u hu => (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.primeFormConjHom_eq_one_iff h
      (by norm_num) h6 _).2 ⟨u, hu, rfl⟩
  have hsmul : ∀ (u : Kˣ) (v : Fin 6 → K), ((Matrix.GeneralLinearGroup.scalar (Fin 6) u :
      GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ v = (u : K) • v := by
    intro u v
    funext i
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal]
    rfl
  set Ah := Ab.comap c with hAhdef
  have hAbrange : Ab ≤ c.range := hAbD
  have hAhmap : Ah.map c = Ab := Subgroup.map_comap_eq_self hAbrange
  have hTbne : Tb ≠ ⊥ := by
    obtain ⟨α, -, t, ht, hαt⟩ := hTbA
    intro hbot
    rw [hbot, Subgroup.mem_bot] at ht
    exact hαt (by rw [ht, map_one])
  obtain ⟨T₂, hT₂2, hT₂ne, hT₂U, hT₂N⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.HDescUniRes.exists_sylow_two_lift h hTb2 hTbne (Â := Ah)
      (fun X hX => hTbN (c X) hX)
  obtain ⟨W, hW, hiso, hWstab⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.HDescUniRes.exists_isotropic_stable h hT₂2 hT₂ne hT₂U
      (Â := Ah.map (primeFormUnitary h (idGram K 6)).subtype) (by rintro _ ⟨X, -, rfl⟩; exact X.2)
      (by rintro _ ⟨X, hX, rfl⟩ t ht; exact hT₂N X hX t ht)
  obtain ⟨w, hw0, hwW, hweig⟩ := u6_exists_common_eigenvector h hn hn1 (Ah := Ah)
    (by rw [hAhmap]; exact hAbel) (by rw [hAhmap]; exact hAbcard) hW hiso
    (fun X hX v hv => hWstab _ ⟨X, hX, rfl⟩ v hv)
  obtain ⟨i₀, hi₀⟩ : ∃ i, w i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw0 (funext hcon)
  have hscal_w : ∀ u : Kˣ, (u : K) • w = w → u = 1 := by
    intro u hu
    have h1 := congrFun hu i₀
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    exact Units.ext (by simpa using mul_right_cancel₀ hi₀ (h1.trans (one_mul _).symm))
  let Ah1 : Subgroup (primeFormUnitary h (idGram K 6)) :=
    { carrier := {X | X ∈ Ah ∧ ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ w = w}
      one_mem' := ⟨Ah.one_mem, by simp⟩
      mul_mem' := by
        rintro X Y ⟨hX, hXw⟩ ⟨hY, hYw⟩
        refine ⟨Ah.mul_mem hX hY, ?_⟩
        show (((X * Y : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) *ᵥ w = w
        rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hYw, hXw]
      inv_mem' := by
        rintro X ⟨hX, hXw⟩
        refine ⟨Ah.inv_mem hX, ?_⟩
        show (((X⁻¹ : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) *ᵥ w = w
        conv_lhs => rw [← hXw]
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel,
          Subgroup.coe_one, Units.val_one, Matrix.one_mulVec] }
  have hAh1 : ∀ X, X ∈ Ah1 ↔ X ∈ Ah ∧ ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ w = w :=
    fun X => Iff.rfl
  have hfix_scalar : ∀ X : primeFormUnitary h (idGram K 6), c X = 1 →
      ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ w = w → X = 1 := by
    intro X hX hXw
    obtain ⟨u, -, hu⟩ := hker X hX
    rw [hu, hsmul] at hXw
    apply Subtype.ext
    rw [hu, hscal_w u hXw, map_one, Subgroup.coe_one]
  have hpow : ∀ X ∈ Ah1, X ^ 3 = 1 := by
    intro X hX
    have hc3 : c (X ^ 3) = 1 := by rw [map_pow]; exact hAbel.2 (c X) ((hAh1 X).1 hX).1
    refine hfix_scalar _ hc3 ?_
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, pow_succ, pow_succ, pow_one,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ((hAh1 X).1 hX).2, ((hAh1 X).1 hX).2,
      ((hAh1 X).1 hX).2]
  have hcomm : ∀ X ∈ Ah1, ∀ Y ∈ Ah1, X * Y = Y * X := by
    intro X hX Y hY
    have hc1 : c (X * Y * X⁻¹ * Y⁻¹) = 1 := by
      have hXY : c X * c Y = c Y * c X := by
        have := hAbel.1.is_comm.comm ⟨c X, ((hAh1 X).1 hX).1⟩ ⟨c Y, ((hAh1 Y).1 hY).1⟩
        simpa using congrArg Subtype.val this
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hXY]
      group
    have hw1 : (((X * Y * X⁻¹ * Y⁻¹ : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) *ᵥ w = w :=
      ((hAh1 _).1 (Ah1.mul_mem (Ah1.mul_mem (Ah1.mul_mem hX hY) (Ah1.inv_mem hX))
        (Ah1.inv_mem hY))).2
    have h1 := hfix_scalar _ hc1 hw1
    calc X * Y = X * Y * X⁻¹ * Y⁻¹ * (Y * X) := by group
      _ = Y * X := by rw [h1, one_mul]
  have hsurj : Ah1.map c = Ab := by
    apply le_antisymm
    · rintro _ ⟨X, hX, rfl⟩
      exact ((hAh1 X).1 hX).1
    · intro α hα
      rw [← hAhmap] at hα
      obtain ⟨X, hX, rfl⟩ := hα
      obtain ⟨μ, hμ⟩ := hweig X hX
      have hμ0 : μ ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hμ
        apply hw0
        have h1 := congrArg (fun v => (((X⁻¹ : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) *ᵥ v) hμ
        simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h1
        rwa [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one,
          Matrix.one_mulVec] at h1
      obtain ⟨l, hl, hXl⟩ := hker (X ^ 3) (by rw [map_pow]; exact hAbel.2 (c X) hX)
      have hX3w : (((X ^ 3 : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) *ᵥ w = (μ ^ 3) • w := by
        rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, pow_succ, pow_succ, pow_one,
          ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hμ, Matrix.mulVec_smul, hμ,
          Matrix.mulVec_smul, Matrix.mulVec_smul, hμ, smul_smul, smul_smul]
        congr 1
        ring
      have hμl : μ ^ 3 = (l : K) := by
        rw [hXl, hsmul] at hX3w
        have h1 := congrFun hX3w i₀
        simp only [Pi.smul_apply, smul_eq_mul] at h1
        exact (mul_right_cancel₀ hi₀ h1).symm
      have hμq : μ ^ (2 ^ n + 1) = 1 := by
        apply cj_pow_q_add_one h hn hμ0
        rw [hμl]
        have h1 := hl
        rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply] at h1
        rw [pow_succ']
        exact h1
      set μu : Kˣ := Units.mk0 μ hμ0 with hμu
      have hnorm : h.norm ((μu⁻¹ : Kˣ) : K) = 1 := by
        rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, hμu, Units.val_inv_eq_inv_val,
          Units.val_mk0, inv_pow, ← mul_inv, ← pow_succ', hμq, inv_one]
      let Sc : primeFormUnitary h (idGram K 6) :=
        ⟨Matrix.GeneralLinearGroup.scalar (Fin 6) μu⁻¹, scalar_mem_primeFormUnitary_one h hnorm⟩
      have hcSc : c Sc = 1 := hscalar_c _ hnorm
      refine ⟨Sc * X, (hAh1 _).2 ⟨?_, ?_⟩, ?_⟩
      · show c (Sc * X) ∈ Ab
        rw [map_mul, hcSc, one_mul]
        exact hX
      · rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hμ]
        show ((Matrix.GeneralLinearGroup.scalar (Fin 6) μu⁻¹ : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) *ᵥ (μ • w) = w
        rw [hsmul, smul_smul, hμu, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ hμ0,
          one_smul]
      · show c (Sc * X) = c X
        rw [map_mul, hcSc, one_mul]
  have hinj1 : Function.Injective (c.comp Ah1.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro X hX
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hX
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hfix_scalar _ hX ((hAh1 _).1 X.2).2)
  have hcard1 : Nat.card Ah1 = Nat.card Ab := by
    rw [← hsurj, show Ah1.map c = (c.comp Ah1.subtype).range by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]]
    exact Nat.card_congr (MonoidHom.ofInjective hinj1).toEquiv
  obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag h Nat.prime_three
    (cj_three_dvd hn) Ah1 hcomm hpow
  set Δ := Ah1.map (MulAut.conj P⁻¹).toMonoidHom with hΔdef
  have hΔmem : ∀ Y, Y ∈ Δ → ∃ X ∈ Ah1, Y = P⁻¹ * X * P := by
    rintro Y ⟨X, hX, rfl⟩
    exact ⟨X, hX, by simp [MulAut.conj_apply]⟩
  have hdiagΔ : ∀ Y ∈ Δ, ((Y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag := by
    intro Y hY
    obtain ⟨X, hX, rfl⟩ := hΔmem Y hY
    exact hP X hX
  have hcubeΔ : ∀ Y ∈ Δ, Y ^ 3 = 1 := by
    intro Y hY
    obtain ⟨X, hX, rfl⟩ := hΔmem Y hY
    have e : P⁻¹ * X * P = P⁻¹ * X * P⁻¹⁻¹ := by rw [inv_inv]
    rw [e, conj_pow, hpow X hX, mul_one, mul_inv_cancel]
  set w' := (((P⁻¹ : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ w
    with hw'def
  have hPP : ∀ v : Fin 6 → K, ((P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ
      ((((P⁻¹ : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
      Units.val_one, Matrix.one_mulVec]
  have hw'fix : ∀ Y ∈ Δ, ((Y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ w' = w' := by
    intro Y hY
    obtain ⟨X, hX, rfl⟩ := hΔmem Y hY
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hw'def, hPP, ((hAh1 X).1 hX).2]
  have hw'0 : w' ≠ 0 := by
    intro h0
    apply hw0
    rw [← hPP w, ← hw'def, h0, Matrix.mulVec_zero]
  have hw'iso : idForm h 6 w' w' = 0 := by
    rw [hw'def, CFSG.LocalAnalysis.GLTheoremA.HDescUniRes.idForm_mulVec_of_mem_primeFormUnitary
      (P⁻¹).2]
    exact (Submodule.mem_orthogonalBilin_iff.1 (hiso hwW)) w hwW
  obtain ⟨a, b, hab, ha0, hb0⟩ := cj_exists_two_ne_zero h hw'0 hw'iso
  have hentry : ∀ i, w' i ≠ 0 → ∀ Y ∈ Δ, ((Y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i i = 1 := by
    intro i hi Y hY
    have h1 := congrFun (hw'fix Y hY) i
    rw [← (hdiagΔ Y hY).diagonal_diag, Matrix.mulVec_diagonal] at h1
    exact mul_right_cancel₀ hi (h1.trans (one_mul _).symm)
  have hcardΔ : 27 ≤ Nat.card Δ := by
    rw [hΔdef, Subgroup.card_map_of_injective (MulAut.conj P⁻¹).injective, hcard1]
    exact hAbcard
  have hconcl := u6MatConcl_of_diag h hn hn1 hdiagΔ hcubeΔ hab (hentry a ha0) (hentry b hb0) hcardΔ
  have hmapΔ : Δ.map c = Ab.map (MulAut.conj (c P⁻¹)).toMonoidHom := by
    rw [hΔdef, Subgroup.map_map, ← hsurj, Subgroup.map_map]
    congr 1
    ext X : 1
    show c (MulAut.conj P⁻¹ X) = MulAut.conj (c P⁻¹) (c X)
    rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, map_inv, map_inv]
  have hfinal := u6MatConcl_map_conj h (c P) hconcl
  rw [hmapΔ, Subgroup.map_map] at hfinal
  have hid : (MulAut.conj (c P)).toMonoidHom.comp (MulAut.conj (c P⁻¹)).toMonoidHom =
      MonoidHom.id _ := by
    ext α : 1
    show MulAut.conj (c P) (MulAut.conj (c P⁻¹) α) = α
    rw [MulAut.conj_apply, MulAut.conj_apply, map_inv]
    group
  rwa [hid, Subgroup.map_id] at hfinal

end CFSG.LocalAnalysis.GLTheoremA.T266U6

end
