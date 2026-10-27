module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.UniAut
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.YS04LUPSU

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b (isCyclic_unitaryD_quotient exists_ne_one_inf_of_cyclic succ_dvd_sq_sub_one)
open Matrix

section Adjoint

variable {F : Type} [Field F] {m : ℕ}

abbrev adjM (bar : F →+* F) (X : Matrix (Fin m) (Fin m) F) : Matrix (Fin m) (Fin m) F :=
  (X.map bar)ᵀ

theorem adjM_mul (bar : F →+* F) (X Y : Matrix (Fin m) (Fin m) F) :
    adjM bar (X * Y) = adjM bar Y * adjM bar X := by
  simp [adjM, Matrix.map_mul, Matrix.transpose_mul]

theorem adjM_one (bar : F →+* F) : adjM bar (1 : Matrix (Fin m) (Fin m) F) = 1 := by
  simp [adjM, Matrix.map_one _ (map_zero bar) (map_one bar)]

theorem adjM_inv_of_sim (bar : F →+* F) {G : Matrix (Fin m) (Fin m) F} {μ : F}
    (hG : IsUnit G.det) (hs : adjM bar G * G = μ • 1) :
    μ • (adjM bar G⁻¹ * G⁻¹) = 1 := by
  calc μ • (adjM bar G⁻¹ * G⁻¹) = adjM bar G⁻¹ * (μ • 1) * G⁻¹ := by
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    _ = adjM bar G⁻¹ * (adjM bar G * G) * G⁻¹ := by rw [hs]
    _ = adjM bar (G * G⁻¹) * (G * G⁻¹) := by
        rw [adjM_mul]
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Matrix.mul_nonsing_inv G hG, adjM_one, Matrix.mul_one]

theorem adjM_conj_of_sim (bar : F →+* F) {G N : Matrix (Fin m) (Fin m) F} {μ : F}
    (hG : IsUnit G.det) (hs : adjM bar G * G = μ • 1) (hN : adjM bar N * N = 1) :
    adjM bar (G * N * G⁻¹) * (G * N * G⁻¹) = 1 := by
  have hM := adjM_inv_of_sim bar hG hs
  calc adjM bar (G * N * G⁻¹) * (G * N * G⁻¹)
      = adjM bar G⁻¹ * adjM bar N * (adjM bar G * G) * N * G⁻¹ := by
        rw [adjM_mul, adjM_mul]
        simp only [Matrix.mul_assoc]
    _ = adjM bar G⁻¹ * adjM bar N * (μ • 1) * N * G⁻¹ := by rw [hs]
    _ = μ • (adjM bar G⁻¹ * (adjM bar N * N) * G⁻¹) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
    _ = μ • (adjM bar G⁻¹ * G⁻¹) := by rw [hN, Matrix.mul_one]
    _ = 1 := hM

theorem adjM_smul_mul (bar : F →+* F) (u : F) {A : Matrix (Fin m) (Fin m) F}
    (hA : adjM bar A * A = 1) : adjM bar (u • A) * (u • A) = (bar u * u) • 1 := by
  have h1 : adjM bar (u • A) = bar u • adjM bar A := by
    ext i j
    simp [adjM, Matrix.map_apply]
  rw [h1, Matrix.smul_mul, Matrix.mul_smul, hA, smul_smul]

theorem adjM_map_subtype {K : Type} [Field K] {k : Subfield K} (bar : K →+* K) (bar₀ : k →+* k)
    (hbar : ∀ c : k, ((bar₀ c : k) : K) = bar c) (M : Matrix (Fin m) (Fin m) k) :
    (adjM bar₀ M).map k.subtype = adjM bar (M.map k.subtype) := by
  ext i j
  simp [adjM, Matrix.map_apply, hbar]

end Adjoint

theorem dvd_add_one_of_pow_eq {p a b : ℕ} (hp : p.Prime) (hb : b = a ^ p) (hpb : p ∣ b + 1) :
    p ∣ a + 1 := by
  haveI := Fact.mk hp
  have h1 : (b : ZMod p) + 1 = 0 := by
    have h0 : ((b + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpb
    simpa using h0
  have h2 : (a : ZMod p) = (b : ZMod p) := by
    rw [hb, Nat.cast_pow, ZMod.pow_card]
  have h3 : ((a + 1 : ℕ) : ZMod p) = 0 := by
    push_cast
    rw [h2]
    exact h1
  exact (ZMod.natCast_eq_zero_iff _ _).1 h3

theorem exists_orderOf_prime_primeFormP {ℓ e : ℕ} {K₀ : Type} [Field K₀] [Finite K₀]
    (h₀ : UnitaryFieldData ℓ e K₀) {n : ℕ} (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ ℓ ^ e + 1) :
    ∃ x : primeFormP h₀ ((1 : GL (Fin n) K₀) : Matrix (Fin n) (Fin n) K₀), orderOf x = p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card K₀ = (ℓ ^ e) ^ 2 := by rw [h₀.card, ← pow_mul, mul_comm]
  have hq1 : 1 ≤ ℓ ^ e := Nat.one_le_pow _ _ h₀.prime.pos
  have hdvd : p ∣ Nat.card K₀ˣ := by
    rw [Nat.card_units, hcard]
    exact hpq.trans (succ_dvd_sq_sub_one hq1)
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hζq : ζ ^ (ℓ ^ e + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hζ ▸ hpq)
  have hζ1 : ζ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hζ
    exact hp.one_lt.ne hζ
  have hnorm : h₀.norm (ζ : K₀) = 1 := by
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, ← pow_succ', ← Units.val_pow_eq_pow_val,
      hζq, Units.val_one]
  have hn1 : 1 < n := by omega
  obtain ⟨hd, hdet⟩ := pairDiag_norm_prod h₀ hnorm (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n)
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set i1 : Fin n := ⟨1, by omega⟩ with hi1
  set i2 : Fin n := ⟨2, by omega⟩ with hi2
  have hi01 : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
  have hi20 : i2 ≠ i0 := by simp [hi0, hi2, Fin.ext_iff]
  have hi21 : i2 ≠ i1 := by simp [hi1, hi2, Fin.ext_iff]
  let d : Fin n → K₀ˣ := Pi.mulSingle i0 ζ * Pi.mulSingle i1 ζ⁻¹
  have hdpow : ∀ i, (d i) ^ p = 1 := by
    intro i
    simp only [d, Pi.mul_apply]
    by_cases h0 : i = i0
    · subst h0
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hi01, mul_one, hζp]
    · by_cases h1 : i = i1
      · subst h1
        rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (Ne.symm hi01), one_mul, inv_pow, hζp,
          inv_one]
      · rw [Pi.mulSingle_eq_of_ne h0, Pi.mulSingle_eq_of_ne h1, mul_one, one_pow]
  let x₁ : ↥(gramSU h₀ ((1 : GL (Fin n) K₀) : Matrix (Fin n) (Fin n) K₀)) :=
    ⟨unitaryDiagGL d, unitaryDiagGL_mem_gramSU h₀ hd hdet⟩
  have hcoe : ((unitaryDiagGL d : GL (Fin n) K₀) : Matrix (Fin n) (Fin n) K₀) =
      Matrix.diagonal fun i => ((d i : K₀ˣ) : K₀) := coe_unitaryDiagGL d
  have hx1p : x₁ ^ p = 1 := by
    refine Subtype.ext (Units.ext ?_)
    change ((unitaryDiagGL d : GL (Fin n) K₀) ^ p : GL (Fin n) K₀).val = _
    rw [Units.val_pow_eq_pow_val, hcoe, Matrix.diagonal_pow]
    have hfp : (fun i => ((d i : K₀ˣ) : K₀)) ^ p = 1 := by
      funext i
      simp only [Pi.pow_apply, Pi.one_apply]
      rw [← Units.val_pow_eq_pow_val, hdpow i, Units.val_one]
    rw [hfp]
    ext i j
    simp [Matrix.one_apply, Matrix.diagonal_apply]
  refine ⟨((x₁ : gramSU h₀ _) : primeFormP h₀ _), orderOf_eq_prime ?_ ?_⟩
  · rw [← QuotientGroup.mk_pow, hx1p, QuotientGroup.mk_one]
  · intro hc
    rw [QuotientGroup.eq_one_iff] at hc
    obtain ⟨c, -, -, hcG⟩ := hc
    have e0 := congrFun (congrFun (congrArg (fun X : GL (Fin n) K₀ =>
      (X : Matrix (Fin n) (Fin n) K₀)) hcG) i0) i0
    have e2 := congrFun (congrFun (congrArg (fun X : GL (Fin n) K₀ =>
      (X : Matrix (Fin n) (Fin n) K₀)) hcG) i2) i2
    rw [coe_unitaryDiagGL] at e0 e2
    simp only [Matrix.diagonal_apply_eq, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
      at e0 e2
    have hd0 : d i0 = ζ := by
      simp only [d, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hi01, mul_one]
    have hd2 : d i2 = 1 := by
      simp only [d, Pi.mul_apply, Pi.mulSingle_eq_of_ne hi20, Pi.mulSingle_eq_of_ne hi21, mul_one]
    rw [hd0] at e0
    rw [hd2] at e2
    apply hζ1
    have h1 : ((ζ : K₀ˣ) : K₀) = 1 := by
      rw [e0, ← e2]
      simp
    exact Units.ext h1

theorem exists_ne_zero_entry_det_one {F : Type} [Field F] {n : ℕ} (hn : 3 ≤ n)
    (M : Matrix (Fin n) (Fin n) F) (hM : M.det = 1) : ∃ i j, M i j ≠ 0 := by
  by_contra hall
  push Not at hall
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have h0 : M = 0 := Matrix.ext fun i j => hall i j
  simp [h0] at hM

theorem psu_normalizes {ℓ f : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData ℓ f K)
    {n : ℕ} (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {σ : K ≃+* K}
    (hσ : orderOf σ = p)
    (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hg : primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ g = g)
    (z : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hz : z ∈ (primeSubfieldPSU h hp hp2 hσ n).range) :
    g * z * g⁻¹ ∈ (primeSubfieldPSU h hp hp2 hσ n).range := by
  classical
  have hK : Finite K := h.finite
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨w, rfl⟩ := MonoidHom.mem_range.1 hz
  obtain ⟨N, rfl⟩ := QuotientGroup.mk_surjective w
  have hA := mem_gramSU.1 A.2
  have hAdj0 : adjM h.bar ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    simpa only [Units.val_one, Matrix.mul_one] using hA.1
  have hg' : (((primeFormFieldSU h isPrimeFormGram_one σ A) :
      gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
      primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      ((A : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
      primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    rw [← primeFormFieldAut_mk]
    exact hg
  obtain ⟨c, -, -, hc⟩ := QuotientGroup.eq.1 hg'
  have hc' : (glAut σ (A : GL (Fin n) K))⁻¹ * (A : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) c := hc
  have hσA : glAut σ (A : GL (Fin n) K) =
      (A : GL (Fin n) K) * (GeneralLinearGroup.scalar (Fin n) c)⁻¹ := by
    apply eq_mul_inv_of_mul_eq
    rw [← hc', mul_inv_cancel_left]
  have hσA' : glAut σ (A : GL (Fin n) K) =
      (A : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) c⁻¹ := by
    rw [hσA, map_inv]
  have hσAe : ∀ a b, σ (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b) =
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b * (c : K)⁻¹ := by
    intro a b
    have := congrArg (fun X : GL (Fin n) K => (X : Matrix (Fin n) (Fin n) K) a b) hσA'
    simp only [coe_glAut, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.mul_diagonal, Units.val_inv_eq_inv_val, Matrix.map_apply] at this
    exact this
  obtain ⟨i₀, j₀, hne⟩ := exists_ne_zero_entry_det_one hn _ hA.2
  set Am : Matrix (Fin n) (Fin n) K := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAm
  set u : K := (Am i₀ j₀)⁻¹ with hu
  have hu0 : u ≠ 0 := inv_ne_zero hne
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  have hσu : σ u = u * (c : K) := by
    rw [hu, map_inv₀, hσAe i₀ j₀, mul_inv, inv_inv]
  have hBfix : ∀ a b, σ (u * Am a b) = u * Am a b := by
    intro a b
    rw [map_mul, hσu, hσAe a b]
    field_simp
  have hdetAm : Am.det = 1 := hA.2
  have hdetB : (u • Am).det = u ^ n := by
    rw [Matrix.det_smul, hdetAm, mul_one, Fintype.card_fin]
  have hBunit : IsUnit (u • Am).det := by
    rw [hdetB]
    exact isUnit_iff_ne_zero.2 (pow_ne_zero _ hu0)
  let Bu : GL (Fin n) K :=
    ⟨u • Am, (u • Am)⁻¹, Matrix.mul_nonsing_inv _ hBunit, Matrix.nonsing_inv_mul _ hBunit⟩
  have hBu : (Bu : Matrix (Fin n) (Fin n) K) = u • Am := rfl
  have hBufix : glAut σ Bu = Bu := Units.ext (Matrix.ext fun a b => hBfix a b)
  obtain ⟨g₀, hg₀⟩ := exists_subfieldGL_eq_of_fixed n hBufix
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  have hG0 : ((g₀ : GL (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ)).map
        (CFSG.LieType.Chevalley.fixSubfield σ).subtype = u • Am := by
    have := congrArg (fun X : GL (Fin n) K => (X : Matrix (Fin n) (Fin n) K)) hg₀
    rw [coe_subfieldGL] at this
    rw [this]
  have hAdj : adjM h.bar Am * Am = 1 := hAdj0
  have hN := mem_gramSU.1 N.2
  have hNadj : adjM (fixSubfield_unitaryFieldData h hp hp2 hσ).bar
      ((N : GL (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ)) :
        Matrix (Fin n) (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ)) *
      ((N : GL (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ)) :
        Matrix (Fin n) (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ)) = 1 := by
    simpa only [Units.val_one, Matrix.mul_one] using hN.1
  have hNdet : ((N : GL (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ)).det = 1 := hN.2
  generalize hG0def : ((g₀ : GL (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ)) = G0 at hG0
  generalize hN0def : ((N : GL (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ)) = N0 at hNadj hNdet
  have hsimK : (adjM (fixSubfield_unitaryFieldData h hp hp2 hσ).bar G0 * G0).map
      (CFSG.LieType.Chevalley.fixSubfield σ).subtype = (h.bar u * u) • 1 := by
    rw [Matrix.map_mul, adjM_map_subtype h.bar _ hbar, hG0, adjM_smul_mul h.bar u hAdj]
  obtain ⟨μ₀, hsim⟩ : ∃ μ₀ : CFSG.LieType.Chevalley.fixSubfield σ,
      adjM (fixSubfield_unitaryFieldData h hp hp2 hσ).bar G0 * G0 = μ₀ • 1 := by
    refine ⟨(adjM (fixSubfield_unitaryFieldData h hp hp2 hσ).bar G0 * G0) ⟨0, by omega⟩
      ⟨0, by omega⟩, ?_⟩
    apply Matrix.map_injective Subtype.val_injective
    ext i j
    have e1 := congrFun (congrFun hsimK i) j
    have e0 := congrFun (congrFun hsimK ⟨0, by omega⟩) ⟨0, by omega⟩
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at e1 e0 ⊢
    by_cases hij : i = j
    · subst hij
      simp only [if_true, mul_one, mul_zero, ite_true] at e1 e0 ⊢
      exact e1.trans e0.symm
    · simpa [hij] using e1
  have hunitG0 : IsUnit G0.det := by
    have h1 : (CFSG.LieType.Chevalley.fixSubfield σ).subtype G0.det = (u • Am).det := by
      rw [← hG0, RingHom.map_det]
      rfl
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, map_zero, hdetB] at h1
    exact pow_ne_zero n hu0 h1.symm
  have hPadj := adjM_conj_of_sim (fixSubfield_unitaryFieldData h hp hp2 hσ).bar hunitG0 hsim hNadj
  have hdetP : (G0 * N0 * G0⁻¹).det = 1 := by
    have h2 : G0.det * G0⁻¹.det = 1 := by
      rw [← Matrix.det_mul, Matrix.mul_nonsing_inv _ hunitG0, Matrix.det_one]
    rw [Matrix.det_mul, Matrix.det_mul, hNdet, mul_one]
    linear_combination h2
  let Pg : GL (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ) := g₀ * N * g₀⁻¹
  have hPg : ((Pg : GL (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ)) = G0 * N0 * G0⁻¹ := by
    rw [← hG0def, ← hN0def]
    simp only [Pg, Units.val_mul, Matrix.coe_units_inv]
  have hPmem : Pg ∈ gramSU (fixSubfield_unitaryFieldData h hp hp2 hσ)
      ((1 : GL (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ)) :
        Matrix (Fin n) (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ)) := by
    rw [mem_gramSU]
    refine ⟨?_, ?_⟩
    · rw [Units.val_one, Matrix.mul_one, hPg]
      exact hPadj
    · rw [hPg]
      exact hdetP
  let s : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) (Units.mk0 u hu0)
  have hBus : Bu = s * (A : GL (Fin n) K) := by
    apply Units.ext
    rw [Units.val_mul]
    ext i j
    simp [s, Bu, Am, Matrix.scalar_apply, Matrix.diagonal_mul]
  have hcomm : ∀ Y : GL (Fin n) K, Y * s = s * Y := fun Y => (commute_scalar _ Y).eq
  have hconjBu : ∀ X : GL (Fin n) K, Bu * X * Bu⁻¹ = (A : GL (Fin n) K) * X * (A : GL (Fin n) K)⁻¹ := by
    intro X
    rw [hBus]
    have hY := hcomm ((A : GL (Fin n) K) * X * (A : GL (Fin n) K)⁻¹)
    calc s * (A : GL (Fin n) K) * X * (s * (A : GL (Fin n) K))⁻¹
        = s * ((A : GL (Fin n) K) * X * (A : GL (Fin n) K)⁻¹) * s⁻¹ := by group
      _ = (A : GL (Fin n) K) * X * (A : GL (Fin n) K)⁻¹ := by
        rw [← hY, mul_inv_cancel_right]
  have hconjGL : (A : GL (Fin n) K) * (subfieldGL (CFSG.LieType.Chevalley.fixSubfield σ) n
      (N : GL (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ))) * (A : GL (Fin n) K)⁻¹ =
      subfieldGL (CFSG.LieType.Chevalley.fixSubfield σ) n Pg := by
    rw [← hconjBu, ← hg₀, map_mul, map_mul, map_inv]
  have hconj : (A : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
      primeSubfieldSU h hp hp2 hσ n N * (A : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))⁻¹ =
      primeSubfieldSU h hp hp2 hσ n ⟨Pg, hPmem⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_subfieldSU]
    exact hconjGL
  have hfinal : (QuotientGroup.mk A : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
      primeSubfieldPSU h hp hp2 hσ n (QuotientGroup.mk N) *
      (QuotientGroup.mk A)⁻¹ =
      primeSubfieldPSU h hp hp2 hσ n (QuotientGroup.mk ⟨Pg, hPmem⟩) := by
    rw [subfieldPSU_mk, subfieldPSU_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, hconj]
  rw [hfinal]
  exact MonoidHom.mem_range.2 ⟨_, rfl⟩

end CFSG.LocalAnalysis.GLTheoremA.YS04LUPSU
