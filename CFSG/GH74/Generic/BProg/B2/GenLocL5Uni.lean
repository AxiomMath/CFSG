module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherFourGroupAntiunitary
public import CFSG.GH74.Generic.BProg.B2.GenLocL5Sign
public import CFSG.GH74.Generic.BProg.B2.GenLocL5Gen

public section

namespace CFSG.GH74.Generic.BProg.B2.GenLocL5Uni

open Matrix Module CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.FourGroupOddBilinear (isometrySL mem_isometrySL)

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem exists_E16_group_of_antiunitary (h : UnitaryFieldData p f K) (hp : p ≠ 2)
    (hn : 2 * r + ε = 5) {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε) {c : K}
    (hc0 : c ≠ 0) (hAc : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar = c • 1) :
    ∃ V : Subgroup (hypPSU h r ε), CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 16 ∧
      ∀ x ∈ V, ∃ g : hypSU h r ε, hypProj h r ε g = x ∧
        (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
          ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar =
            ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
              (A : Matrix (HypIndex r ε) (HypIndex r ε) K) := by
  have : CharP K p := h.charP
  have : Finite K := h.finite
  obtain ⟨b, t, s, ht, hs0, hττ, hfin, B, hBs, hBnd, hBsym⟩ :=
    exists_descended_form h hp (by omega) hA hc0 hAc
  obtain ⟨Hm, Wm, C₀, R, hHW, hWH, hW, hRC, hRdet, hRsym, hcol⟩ :=
    exists_fixed_transport h hp hττ ht t.ne_zero hfin hBs hBnd hBsym
  have hk : ringChar h.fixedField ≠ 2 := by
    rw [ringChar.eq h.fixedField p]
    exact hp
  have hRsymm : Rᵀ = R := by
    rcases hRsym with h1 | h1
    · exact h1
    · exfalso
      have h2 := congrArg Matrix.det h1
      rw [det_transpose, det_neg, Fintype.card_fin] at h2
      have hpow : (-1 : h.fixedField) ^ (2 * r + ε) = -1 := by rw [hn]; norm_num
      rw [hpow] at h2
      have h3 : (2 : h.fixedField) * R.det = 0 := by linear_combination h2
      exact hRdet ((mul_eq_zero.1 h3).resolve_left (Ring.two_ne_zero hk))
  obtain ⟨V₄, hV₄le, hV₄ab, hV₄card⟩ := GenLocL5Sign.exists_E16_isometry hn hk
    (Matrix.GeneralLinearGroup.mkOfDetNeZero R hRdet) hRsymm
  have hR0 : R ≠ 0 := fun h0 => by
    have : Nonempty (Fin (2 * r + ε)) := ⟨⟨0, by omega⟩⟩
    exact hRdet (by rw [h0, Matrix.det_zero])
  set ρ := (LinearFlag.proj (2 * r + ε) h.fixedField).comp (isometrySL R).subtype with hρdef
  set φ : isometrySL R →* hypPSU h r ε := (gramHypProjEquiv h C₀ hW).toMonoidHom.comp
    ((QuotientGroup.mk' _).comp (isometryToGramSU h hs0 hRC)) with hφdef
  have hker : ρ.ker = φ.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change LinearFlag.proj _ _ (g : Matrix.SpecialLinearGroup (Fin (2 * r + ε)) h.fixedField) = 1 ↔
      gramHypProjEquiv h C₀ hW (QuotientGroup.mk (isometryToGramSU h hs0 hRC g)) = 1
    rw [LinearFlag.proj_eq_one_iff, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
    exact mem_scalars_iff_mem_normOneScalars h hs0 hRC (by omega) hR0 g
  have hV₄le' : V₄ ≤ ρ.range := by
    rw [hρdef, MonoidHom.range_comp, Subgroup.range_subtype]
    exact hV₄le
  have : CFSG.IsElementaryAbelian 2 V₄ := hV₄ab
  obtain ⟨V, hVab, hVcard, hVmem⟩ := exists_subgroup_of_ker_eq (p := 2) ρ φ hker V₄ hV₄le'
  have hAH : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * Hm.map h.bar =
      ((b : K)⁻¹) • Hm := by
    refine Matrix.ext fun a j => ?_
    have h3 := congrFun (hcol j) a
    change (b : K) * ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
      fun k => h.bar (Hm k j)) a = Hm a j at h3
    rw [Matrix.smul_apply, smul_eq_mul, ← h3, ← mul_assoc, inv_mul_cancel₀ b.ne_zero, one_mul]
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  have hgramInv : gramHypInv h C₀ Wm = Hm := by
    calc gramHypInv h C₀ Wm = gramHypInv h C₀ Wm * (Wm * Hm) := by rw [hWH, Matrix.mul_one]
      _ = Hm := by rw [← Matrix.mul_assoc, gramHypInv_mul hW, Matrix.one_mul]
  refine ⟨V, hVab, hVcard.trans hV₄card, fun x hx => ?_⟩
  obtain ⟨g, rfl⟩ := hVmem x hx
  refine ⟨gramHypEquiv h C₀ hW (isometryToGramSU h hs0 hRC g),
    (gramHypProjEquiv_mk hW (isometryToGramSU h hs0 hRC g)).symm, ?_⟩
  rw [coe_gramHypEquiv, hgramInv]
  refine mul_map_bar_conj_eq h hHW hWH hAH ?_
  rw [coe_isometryToGramSU]
  exact Matrix.ext fun i j => h.mem_fixedField.mp (((g : Matrix.SpecialLinearGroup
    (Fin (2 * r + ε)) h.fixedField) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) h.fixedField) i
      j).2


theorem exists_scalar_mul_mem_hypSU (h : UnitaryFieldData p f K) (hodd : Odd (2 * r + ε))
    {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε) {c : Kˣ} (hcN : h.norm (c : K) = 1)
    (hAc : A * A = Matrix.GeneralLinearGroup.scalar (HypIndex r ε) c) :
    ∃ μ : Kˣ, Matrix.GeneralLinearGroup.scalar (HypIndex r ε) μ * A ∈ hypSU h r ε := by
  classical
  obtain ⟨m, hm⟩ := hodd
  have hcard : Fintype.card (HypIndex r ε) = 2 * m + 1 := by rw [card_hypIndex, hm]
  set d : Kˣ := Matrix.GeneralLinearGroup.det A with hd
  have hdc : d ^ 2 = c ^ (2 * m + 1) := by
    have h2 := congrArg (Matrix.GeneralLinearGroup.det) hAc
    rw [map_mul, ← pow_two] at h2
    rw [hd, h2]
    ext
    simp [hcard]
  have hNd : h.norm (d : K) = 1 := by
    have h1 := congrArg Matrix.det (mem_hypUnitary.1 hA)
    rw [det_mul, det_mul, det_transpose] at h1
    have hbar : ((A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar).det = h.bar (d : K) := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      simp [hd]
    rw [hbar] at h1
    have hJ := det_hypGram_ne_zero (r := r) (ε := ε) (K := K)
    have hdA : (A : Matrix (HypIndex r ε) (HypIndex r ε) K).det = (d : K) := by simp [hd]
    rw [hdA] at h1
    have h2 : h.norm (d : K) * (hypGram r ε K).det = (hypGram r ε K).det := by
      rw [UnitaryFieldData.norm]
      linear_combination h1
    exact mul_right_cancel₀ hJ (h2.trans (one_mul _).symm)
  set e : Kˣ := d * (c ^ m)⁻¹ with he
  have hen : e ^ (2 * m + 1) = d := by
    have h3 : d ^ (2 * m + 1) = d * (c ^ (2 * m + 1)) ^ m := by
      rw [pow_succ, pow_mul, hdc, mul_comm]
    have h4 : (c ^ m) ^ (2 * m + 1) = (c ^ (2 * m + 1)) ^ m := by
      rw [← pow_mul, ← pow_mul, mul_comm]
    rw [he, mul_pow, inv_pow, h3, h4, mul_inv_cancel_right]
  have hNe : h.norm ((e⁻¹ : Kˣ) : K) = 1 := by
    have hcU : c ^ (p ^ f + 1) = 1 := by
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, ← UnitaryFieldData.norm_eq_pow]
      exact hcN
    have hdU : d ^ (p ^ f + 1) = 1 := by
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, ← UnitaryFieldData.norm_eq_pow]
      exact hNd
    have hU : (e⁻¹) ^ (p ^ f + 1) = 1 := by
      rw [inv_pow, he, mul_pow, inv_pow, hdU,
        show (c ^ m) ^ (p ^ f + 1) = (c ^ (p ^ f + 1)) ^ m by
          rw [← pow_mul, ← pow_mul, mul_comm], hcU]
      simp
    rw [UnitaryFieldData.norm_eq_pow, ← Units.val_pow_eq_pow_val, hU, Units.val_one]
  refine ⟨e⁻¹, ?_⟩
  have hsc : Matrix.GeneralLinearGroup.scalar (HypIndex r ε) e⁻¹ ∈ hypUnitary h r ε := by
    rw [mem_hypUnitary, Matrix.GeneralLinearGroup.coe_scalar, scalar_gram, hNe, one_smul]
  have hs : Matrix.GeneralLinearGroup.scalar (HypIndex r ε) e⁻¹ * A ∈ hypUnitary h r ε :=
    mul_mem hsc hA
  rw [mem_hypSU]
  refine ⟨mem_hypUnitary.1 hs, ?_⟩
  have hdet : Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.scalar (HypIndex r ε) e⁻¹ * A) = 1 := by
    rw [map_mul]
    have hs' : Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.scalar (HypIndex r ε) e⁻¹ : GL (HypIndex r ε) K) =
        e⁻¹ ^ (2 * m + 1) := by
      ext
      simp [hcard]
    rw [hs', inv_pow, hen, inv_mul_cancel]
  have := congrArg Units.val hdet
  simpa using this


theorem exists_fixed_E16_hyp (h : UnitaryFieldData p f K) (hp : p ≠ 2) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (hn : 2 * r + ε = 5) (β : MulAut (hypPSU h r ε)) (hβ : β * β = 1)
    (hβi : β ∉ (MulAut.conj : hypPSU h r ε →* MulAut (hypPSU h r ε)).range) :
    ∃ V : Subgroup (hypPSU h r ε), (∀ x ∈ V, β x = x) ∧ CFSG.IsElementaryAbelian 2 ↥V ∧
      Nat.card ↥V = 16 := by
  have hβ1 : β ≠ 1 := fun h1 => hβi ⟨1, by rw [h1, map_one]⟩
  have hord : orderOf β = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq]; exact hβ) hβ1
  obtain ⟨hΦapply, -, -, hrep⟩ :=
    odd_unitary_automorphism_semilinear_representation h hp hr hε (by omega)
  obtain ⟨A, σ, hx, hA, hΦ, hσ, hid, hbar⟩ := hrep β hord
  rcases hσ with hσ1 | hσbar
  ·
    exfalso
    have h1 := hid hσ1
    have h2 : (QuotientGroup.mk ⟨A, hA⟩ : hypUnitaryMod h r ε) ^ 2 = 1 := by
      rw [← h1, pow_orderOf_eq_one]
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h2
    obtain ⟨c, hcN, -, hc⟩ := h2
    have hAc : A * A = GeneralLinearGroup.scalar (HypIndex r ε) c := by
      rw [← hc, sq]
      rfl
    obtain ⟨μ, hμ⟩ := exists_scalar_mul_mem_hypSU h (by rw [hn]; decide) hA hcN hAc
    apply hβi
    refine ⟨hypProj h r ε ⟨_, hμ⟩, ?_⟩
    ext y
    obtain ⟨g, rfl⟩ := hypProj_surjective h r ε y
    rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, ← hΦ, hΦapply]
    congr 1
    apply Subtype.ext
    change GeneralLinearGroup.scalar (HypIndex r ε) μ * A * (g : GL (HypIndex r ε) K) *
        (GeneralLinearGroup.scalar (HypIndex r ε) μ * A)⁻¹ =
      A * glAut σ (g : GL (HypIndex r ε) K) * A⁻¹
    rw [hσ1, show RingEquiv.refl K = (1 : K ≃+* K) from rfl, map_one, MulAut.one_apply]
    have hcen : ∀ X : GL (HypIndex r ε) K,
        GeneralLinearGroup.scalar (HypIndex r ε) μ * X = X * GeneralLinearGroup.scalar (HypIndex r ε) μ :=
      fun X => (commute_scalar μ X).symm.eq
    calc GeneralLinearGroup.scalar (HypIndex r ε) μ * A * (g : GL (HypIndex r ε) K) *
          (GeneralLinearGroup.scalar (HypIndex r ε) μ * A)⁻¹
        = GeneralLinearGroup.scalar (HypIndex r ε) μ * (A * (g : GL (HypIndex r ε) K) * A⁻¹) *
          (GeneralLinearGroup.scalar (HypIndex r ε) μ)⁻¹ := by group
      _ = (A * (g : GL (HypIndex r ε) K) * A⁻¹) * GeneralLinearGroup.scalar (HypIndex r ε) μ *
          (GeneralLinearGroup.scalar (HypIndex r ε) μ)⁻¹ := by rw [hcen]
      _ = A * (g : GL (HypIndex r ε) K) * A⁻¹ := by rw [mul_inv_cancel_right]
  ·
    obtain ⟨c, hc0, hAc⟩ := hbar hσbar
    obtain ⟨V, hVab, hVcard, hVmem⟩ := exists_E16_group_of_antiunitary h hp hn hA hc0 hAc
    refine ⟨V, fun x hx => ?_, hVab, hVcard⟩
    obtain ⟨g, rfl, hg⟩ := hVmem x hx
    have hg' : A * glAut σ (g : GL (HypIndex r ε) K) = (g : GL (HypIndex r ε) K) * A := by
      refine Units.ext ?_
      rw [Units.val_mul, Units.val_mul, coe_glAut]
      have hmap : ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map σ =
          ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar :=
        Matrix.ext fun i j => hσbar _
      rw [hmap]
      exact hg
    rw [← hΦ, hΦapply]
    congr 1
    apply Subtype.ext
    change A * glAut σ (g : GL (HypIndex r ε) K) * A⁻¹ = g
    rw [hg', mul_inv_cancel_right]


theorem out16_of_stated {J : Type} [Group J] {p f : ℕ} (hp2 : p ≠ 2)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel J .PSU 5 p f) : GenLocL5Gen.Out16 J := by
  obtain ⟨⟨hprime, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hU : UnitaryFieldData p f K := ⟨hprime, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 1) hU
  let ψ : J ≃* hypPSU hU 2 1 := e.trans (hypPSUEquivStatedProj hU hR (by omega)).symm
  exact GenLocL5Gen.Out16.of_mulEquiv ψ.symm fun β hβ hβi =>
    exists_fixed_E16_hyp hU hp2 (by omega) (by omega) (by omega) β hβ hβi

end CFSG.GH74.Generic.BProg.B2.GenLocL5Uni
