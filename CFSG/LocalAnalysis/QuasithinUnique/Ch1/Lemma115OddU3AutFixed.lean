module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherFourGroupAntiunitary
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3AutCard

public section

namespace CFSG.QuasithinUnique.Ch1

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.FourGroupOddBilinear (isometrySL mem_isometrySL)

variable {p f : ℕ} {K : Type} [Field K]

theorem exists_commuting_rep_of_fixed (h : UnitaryFieldData p f K) {r ε : ℕ} (hr : 1 ≤ r)
    (hε : ε ≤ 1) (hn3 : 2 * r + ε = 3) {A : GL (HypIndex r ε) K} {σ : K ≃+* K}
    (hσ : ∀ c, σ c = h.bar c) (hx : (⟨A, σ⟩ : SemiGL (HypIndex r ε) K) ∈ semilinearSimilitudes h r ε)
    {y : hypPSU h r ε} (hy : semilinearAutHom h hr hε ⟨_, hx⟩ y = y) :
    ∃ g : hypSU h r ε, hypProj h r ε g = y ∧
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
          ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar =
        ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
          (A : Matrix (HypIndex r ε) (HypIndex r ε) K) := by
  obtain ⟨g, rfl⟩ := hypProj_surjective h r ε y
  rw [semilinearAutHom_apply] at hy
  set g' : hypSU h r ε :=
    ⟨A * glAut σ (g : GL (HypIndex r ε) K) * A⁻¹, conj_mem_hypSU hx g⟩ with hg'
  have hz : g'⁻¹ * g ∈ hypScalars h r ε := by
    rw [← ker_hypProj, MonoidHom.mem_ker, map_mul, map_inv, hy, inv_mul_cancel]
  have hz' := hz
  obtain ⟨ζ, hζN, hζ3, hζ⟩ := hz'
  rw [hn3] at hζ3
  have hζ3' : (ζ : K) ^ 3 = 1 := by
    have := congrArg Units.val hζ3
    simpa using this
  set s : GL (HypIndex r ε) K := GeneralLinearGroup.scalar (HypIndex r ε) ζ with hs
  have h1 : (g : GL (HypIndex r ε) K) = A * glAut σ (g : GL (HypIndex r ε) K) * A⁻¹ * s :=
    inv_mul_eq_iff_eq_mul.1 hζ
  have hcomm' : A⁻¹ * s * A = s := by
    rw [(commute_scalar ζ A⁻¹).eq, mul_assoc, inv_mul_cancel, mul_one]
  have h2 : (g : GL (HypIndex r ε) K) * A = A * glAut σ (g : GL (HypIndex r ε) K) * s := by
    calc (g : GL (HypIndex r ε) K) * A
        = A * glAut σ (g : GL (HypIndex r ε) K) * A⁻¹ * s * A := by rw [← h1]
      _ = A * glAut σ (g : GL (HypIndex r ε) K) * (A⁻¹ * s * A) := by simp only [mul_assoc]
      _ = A * glAut σ (g : GL (HypIndex r ε) K) * s := by rw [hcomm']
  have hmap : ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map σ =
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar :=
    Matrix.ext fun i j => hσ _
  have hmat : ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        (A : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      (ζ : K) • ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar) := by
    have h3 := congrArg (fun X : GL (HypIndex r ε) K => (X : Matrix (HypIndex r ε) (HypIndex r ε) K)) h2
    simp only [Units.val_mul, coe_glAut, hs, GeneralLinearGroup.coe_scalar, hmap] at h3
    rw [h3, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  have hN : (ζ : K) * h.bar (ζ : K) = 1 := hζN
  have hbar : h.bar (ζ : K) = (ζ : K) * (ζ : K) := by
    linear_combination (-(h.bar (ζ : K))) * hζ3' + ((ζ : K) * (ζ : K)) * hN
  have hπz : hypProj h r ε (g'⁻¹ * g) = 1 := by
    rw [← MonoidHom.mem_ker, ker_hypProj]
    exact hz
  refine ⟨(g'⁻¹ * g) * g, ?_, ?_⟩
  · rw [map_mul, hπz, one_mul]
  · have hzg : (((g'⁻¹ * g) * g : hypSU h r ε) : GL (HypIndex r ε) K) =
        s * (g : GL (HypIndex r ε) K) := by
      rw [Subgroup.coe_mul, hζ]
    have hzgm : ((((g'⁻¹ * g) * g : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) =
        (ζ : K) • ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) := by
      rw [hzg, hs, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
    have hmapsmul : ((ζ : K) • ((g : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K)).map h.bar =
        h.bar (ζ : K) • ((g : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar := by
      ext i j
      simp [Matrix.smul_apply]
    rw [hzgm, hmapsmul, Matrix.mul_smul, hbar, Matrix.smul_mul, hmat, smul_smul]

theorem exists_fixed_embedding (h : UnitaryFieldData p f K) (hp : p ≠ 2) {r ε : ℕ}
    (hn : 3 ≤ 2 * r + ε) {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε) {c : K}
    (hc0 : c ≠ 0) (hAc : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar = c • 1) :
    ∃ (R : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) h.fixedField)
      (φ : isometrySL R →* hypPSU h r ε),
      R.det ≠ 0 ∧ (Rᵀ = R ∨ Rᵀ = -R) ∧
      ((LinearFlag.proj (2 * r + ε) h.fixedField).comp (isometrySL R).subtype).ker = φ.ker ∧
      ∀ g : hypSU h r ε,
        (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
            ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar =
          ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
            (A : Matrix (HypIndex r ε) (HypIndex r ε) K) →
        hypProj h r ε g ∈ φ.range := by
  have : CharP K p := h.charP
  have : Finite K := h.finite
  obtain ⟨b, t, s, ht, hs0, hττ, hfin, B, hBs, hBnd, hBsym⟩ :=
    exists_descended_form h hp (by omega) hA hc0 hAc
  obtain ⟨Hm, Wm, C₀, R, hHW, hWH, hW, hRC, hRdet, hRsym, hcol⟩ :=
    exists_fixed_transport h hp hττ ht t.ne_zero hfin hBs hBnd hBsym
  have hR0 : R ≠ 0 := fun h0 => by
    have : Nonempty (Fin (2 * r + ε)) := ⟨⟨0, by omega⟩⟩
    exact hRdet (by rw [h0, Matrix.det_zero])
  set φ : isometrySL R →* hypPSU h r ε := (gramHypProjEquiv h C₀ hW).toMonoidHom.comp
    ((QuotientGroup.mk' _).comp (isometryToGramSU h hs0 hRC)) with hφdef
  refine ⟨R, φ, hRdet, hRsym, ?_, ?_⟩
  · ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change LinearFlag.proj _ _ (g : Matrix.SpecialLinearGroup (Fin (2 * r + ε)) h.fixedField) = 1 ↔
      gramHypProjEquiv h C₀ hW (QuotientGroup.mk (isometryToGramSU h hs0 hRC g)) = 1
    rw [LinearFlag.proj_eq_one_iff, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
    exact mem_scalars_iff_mem_normOneScalars h hs0 hRC (by omega) hR0 g
  · intro g hg
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
    have hWA : Wm * (A : Matrix (HypIndex r ε) (HypIndex r ε) K) =
        ((b : K)⁻¹) • Wm.map h.bar := by
      have h1 : Wm * (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * Hm.map h.bar =
          ((b : K)⁻¹) • (1 : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) := by
        rw [Matrix.mul_assoc, hAH, Matrix.mul_smul, hWH]
      have h3 : Hm.map h.bar * Wm.map h.bar = 1 := by
        rw [← Matrix.map_mul, hHW, Matrix.map_one _ (map_zero h.bar) (map_one h.bar)]
      calc Wm * (A : Matrix (HypIndex r ε) (HypIndex r ε) K)
          = Wm * (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * (Hm.map h.bar * Wm.map h.bar) := by
            rw [h3, Matrix.mul_one]
        _ = ((b : K)⁻¹) • Wm.map h.bar := by
            rw [← Matrix.mul_assoc, h1, Matrix.smul_mul, Matrix.one_mul]
    have hWb : Wm.map h.bar =
        (b : K) • (Wm * (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) := by
      rw [hWA, smul_smul, mul_inv_cancel₀ b.ne_zero, one_smul]
    set G : gramSU h C₀ := (gramHypEquiv h C₀ hW).symm g with hGdef
    have hGm : ((G : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) =
        Wm * ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) * Hm := by
      change Wm * ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        gramHypInv h C₀ Wm = _
      rw [hgramInv]
    have hbarG : ((G : GL (Fin (2 * r + ε)) K) :
        Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K).map h.bar =
        ((G : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) := by
      rw [hGm, Matrix.map_mul, Matrix.map_mul, hWb]
      calc ((b : K) • (Wm * (A : Matrix (HypIndex r ε) (HypIndex r ε) K))) *
            ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar *
              Hm.map h.bar
          = (b : K) • (Wm * ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
              ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar) *
                Hm.map h.bar) := by
            rw [Matrix.smul_mul, Matrix.smul_mul]
            congr 1
            simp only [Matrix.mul_assoc]
        _ = (b : K) • (Wm * (((g : GL (HypIndex r ε) K) :
              Matrix (HypIndex r ε) (HypIndex r ε) K) *
                (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) * Hm.map h.bar) := by rw [hg]
        _ = (b : K) • (Wm * ((g : GL (HypIndex r ε) K) :
              Matrix (HypIndex r ε) (HypIndex r ε) K) *
                ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) * Hm.map h.bar)) := by
            congr 1
            simp only [Matrix.mul_assoc]
        _ = Wm * ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) * Hm := by
            rw [hAH, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ b.ne_zero, one_smul]
    let Gf : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) h.fixedField :=
      Matrix.of fun i j => ⟨((G : GL (Fin (2 * r + ε)) K) :
        Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) i j,
          h.mem_fixedField.mpr (congrFun (congrFun hbarG i) j)⟩
    have hGfmap : Gf.map h.fixedField.subtype =
        ((G : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) :=
      Matrix.ext fun i j => rfl
    have hdetGf : Gf.det = 1 := by
      apply h.fixedField.subtype.injective
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hGfmap, map_one]
      exact G.2.2
    have hGC : ((G : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)ᵀ *
        C₀ * ((G : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) =
          C₀ := by
      have := G.2.1
      rwa [hbarG] at this
    have hiso : Gfᵀ * R * Gf = R := by
      apply Matrix.map_injective h.fixedField.subtype.injective
      beta_reduce
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hRC, hGfmap, Matrix.mul_smul,
        Matrix.smul_mul, hGC]
    refine ⟨⟨⟨Gf, hdetGf⟩, mem_isometrySL.mpr hiso⟩, ?_⟩
    have hiG : isometryToGramSU h hs0 hRC ⟨⟨Gf, hdetGf⟩, mem_isometrySL.mpr hiso⟩ = G :=
      Subtype.ext (Units.ext hGfmap)
    change gramHypProjEquiv h C₀ hW (QuotientGroup.mk (isometryToGramSU h hs0 hRC
      ⟨⟨Gf, hdetGf⟩, mem_isometrySL.mpr hiso⟩)) = hypProj h r ε g
    rw [hiG, gramHypProjEquiv_mk, hGdef, MulEquiv.apply_symm_apply]
    rfl

theorem card_dvd_of_fixed (h : UnitaryFieldData p 1 K) (hp : p ≠ 2) {A : GL (HypIndex 1 1) K}
    (hA : A ∈ hypUnitary h 1 1) {c : K} (hc0 : c ≠ 0)
    (hAc : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
      (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map h.bar = c • 1)
    {σ : K ≃+* K} (hσ : ∀ x, σ x = h.bar x)
    (hx : (⟨A, σ⟩ : SemiGL (HypIndex 1 1) K) ∈ semilinearSimilitudes h 1 1)
    (Q : Subgroup (hypPSU h 1 1))
    (hQ : ∀ y ∈ Q, semilinearAutHom h (le_refl 1) (le_refl 1) ⟨_, hx⟩ y = y) :
    Nat.card Q ∣ p * (p ^ 2 - 1) := by
  have : CharP K p := h.charP
  have : Finite K := h.finite
  obtain ⟨R, φ, hRdet, hRsym, hker, hfix⟩ :=
    exists_fixed_embedding h hp (r := 1) (ε := 1) (by norm_num) hA hc0 hAc
  have hk : ringChar h.fixedField ≠ 2 := by
    rw [ringChar.eq h.fixedField p]
    exact hp
  have hRs : Rᵀ = R := by
    rcases hRsym with hs | hneg
    · exact hs
    · exfalso
      have hdet := congrArg Matrix.det hneg
      rw [Matrix.det_transpose, Matrix.det_neg, Fintype.card_fin] at hdet
      have h3 : (2 : h.fixedField) * R.det = 0 := by linear_combination hdet
      exact hRdet ((mul_eq_zero.mp h3).resolve_left (Ring.two_ne_zero hk))
  have hR0 : R ≠ 0 := fun h0 => hRdet (by rw [h0, Matrix.det_zero])
  have hρinj : Function.Injective (soProj R) := soProj_injective hR0
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, ← hker, MonoidHom.ker_eq_bot_iff]
    exact hρinj
  have hle : Q ≤ φ.range := fun y hy => by
    obtain ⟨g, rfl, hg⟩ := exists_commuting_rep_of_fixed h (le_refl 1) (le_refl 1) (by norm_num)
      hσ hx (hQ y hy)
    exact hfix g hg
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv] at hdvd
  have hcard := card_soForm hk (Matrix.GeneralLinearGroup.mkOfDetNeZero R hRdet) hRs
  have hF : Nat.card h.fixedField = p := by rw [h.card_fixedField, pow_one]
  rw [hF] at hcard
  exact hcard ▸ hdvd

end CFSG.QuasithinUnique.Ch1
