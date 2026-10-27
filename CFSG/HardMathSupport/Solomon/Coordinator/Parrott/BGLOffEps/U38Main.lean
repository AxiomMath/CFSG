module

public import CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.U38Core
public import CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.U38Data
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLUTMain
public import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoU8Core
public import CFSG.RankThree.PartTwo.KFacts.AutPSUScalar
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.U38

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.HeisSmall HuppertU38F
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open Matrix

variable {F : Type} [Field F]

section Field

theorem exists_eq_frobenius_pow [Finite F] [CharP F 2] (φ : F ≃+* F) :
    ∃ k : ℕ, ∀ c : F, φ c = c ^ 2 ^ k := by
  classical
  letI : Algebra (ZMod 2) F := ZMod.algebra _ _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : FiniteDimensional (ZMod 2) F := Module.Finite.of_finite
  let φa : F ≃ₐ[ZMod 2] F := AlgEquiv.ofRingEquiv (f := φ) (fun x => by
    have := RingHom.ext_zmod ((φ : F →+* F).comp (algebraMap (ZMod 2) F)) (algebraMap (ZMod 2) F)
    exact DFunLike.congr_fun this x)
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod 2) F).2 φa
  refine ⟨n.1, fun c => ?_⟩
  have h1 : (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F ^ n.1) c = φa c := by
    rw [← hn]
  have h2 : φ c = φa c := rfl
  rw [h2, ← h1, AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  simp

theorem frob_cases (h : UnitaryFieldData 2 3 F) {σ : F ≃+* F} (hσ : orderOf σ = 3) :
    (∀ c, σ c = c ^ 4) ∨ ∀ c, σ c = c ^ 16 := by
  have := h.finite
  have : CharP F 2 := h.charP
  obtain ⟨k, hk⟩ := exists_eq_frobenius_pow σ
  have h64 : ∀ c : F, c ^ 64 = c := by
    intro c
    have := Fintype.ofFinite F
    have hc : Fintype.card F = 64 := by rw [← Nat.card_eq_fintype_card, h.card]; norm_num
    rw [← hc]
    exact FiniteField.pow_card c
  have hper : ∀ (m : ℕ) (c : F), c ^ 2 ^ (6 * m) = c := by
    intro m c
    induction m with
    | zero => simp
    | succ n ih =>
      rw [show 6 * (n + 1) = 6 * n + 6 by ring, pow_add, pow_mul, ih,
        show (2 : ℕ) ^ 6 = 64 by norm_num, h64]
  have hr : ∀ c : F, σ c = c ^ 2 ^ (k % 6) := by
    intro c
    have e : 2 ^ k = 2 ^ (6 * (k / 6)) * 2 ^ (k % 6) := by rw [← pow_add, Nat.div_add_mod]
    rw [hk, e, pow_mul, hper]
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have h3 : ∀ c : F, σ (σ (σ c)) = c := fun c => DFunLike.congr_fun hσ3 c
  have hbar : ∃ c : F, c ^ 8 ≠ c := by
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    exact ⟨c, by rwa [h.bar_apply] at hc⟩
  have h8 : ∀ c : F, c ^ 512 = c ^ 8 := fun c => by
    rw [show 512 = 64 * 8 by norm_num, pow_mul, h64]
  have hlt : k % 6 < 6 := Nat.mod_lt _ (by norm_num)
  generalize k % 6 = r at hr hlt
  interval_cases r
  · exfalso
    have : σ = 1 := RingEquiv.ext fun c => by rw [hr c]; simp
    rw [this, orderOf_one] at hσ
    norm_num at hσ
  · exfalso
    obtain ⟨c, hc⟩ := hbar
    apply hc
    have := h3 c
    rw [hr, hr, hr] at this
    calc c ^ 8 = ((c ^ 2 ^ 1) ^ 2 ^ 1) ^ 2 ^ 1 := by ring
      _ = c := this
  · left
    intro c
    rw [hr c]
    norm_num
  · exfalso
    obtain ⟨c, hc⟩ := hbar
    apply hc
    have := h3 c
    rw [hr, hr, hr] at this
    calc c ^ 8 = c ^ 512 := (h8 c).symm
      _ = ((c ^ 2 ^ 3) ^ 2 ^ 3) ^ 2 ^ 3 := by ring
      _ = c := this
  · right
    intro c
    rw [hr c]
    norm_num
  · exfalso
    obtain ⟨c, hc⟩ := hbar
    apply hc
    have := h3 c
    rw [hr, hr, hr] at this
    calc c ^ 8 = c ^ 512 := (h8 c).symm
      _ = (c ^ 64) ^ 512 := by rw [h64]
      _ = ((c ^ 2 ^ 5) ^ 2 ^ 5) ^ 2 ^ 5 := by ring
      _ = c := this

theorem prime_pow_eq_eight {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (h : p ^ e = 8) :
    p = 2 ∧ e = 3 := by
  have h2 : p ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← h]
    exact dvd_pow_self p (by omega)
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2)
  subst hp2
  exact ⟨rfl, Nat.pow_right_injective (le_refl 2) (show 2 ^ e = 2 ^ 3 by norm_num [h])⟩

end Field

section Model


theorem top_le_fixJoin_four (h : UnitaryFieldData 2 3 F) {σ : F ≃+* F} (hσ4 : ∀ c, σ c = c ^ 4)
    (A : unitaryIsom3 h) (hcomm : psuConj h A * psuField h σ = psuField h σ * psuConj h A)
    (h3 : psuConj h A ^ 3 = 1) (hA1 : psuConj h A ≠ 1) :
    (⊤ : Subgroup (unitaryPSU h 3)) ≤ fixJoin (psuField h σ) (psuConj h A) := by
  classical
  have := h.finite
  have hq : (2 : ℕ) ^ 3 = 8 := by norm_num
  have hK3 : 3 ∣ Nat.card F - 1 := by rw [h.card]; norm_num
  obtain ⟨ω, hω⟩ := CFSG.RankThree.PartTwo.Sec19.Item19Res5Proof.exists_isPrimitiveRoot_three hK3
  obtain ⟨ι, hι, hιω⟩ := exists_ringHom_omega (L := Q8) h (by norm_num)
    (by rw [card_q8]; norm_num) CFSG.RankThree.PartTwo.Sec19.U38F.isPrimitiveRoot_w0 hω
  have hσω : σ (ι w0) = ι w0 := by
    rw [hσ4, ← map_pow]
    congr 1
  have hσA : ∃ c : F, ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map σ =
      c • ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    have h1 : psuConj h ⟨glAut σ (A : GL (Fin 3) F), glAut_mem_unitaryIsom3 σ A.2⟩ =
        psuConj h A := by
      rw [← psuField_mul_psuConj_mul_inv, ← hcomm, mul_inv_cancel_right]
    have h2 : psuConj h (A⁻¹ * ⟨glAut σ (A : GL (Fin 3) F), glAut_mem_unitaryIsom3 σ A.2⟩) *
        psuField h 1 = 1 := by
      rw [map_one, mul_one, map_mul, map_inv, h1, inv_mul_cancel]
    obtain ⟨-, c, -, hc⟩ := eq_one_of_psuConj_mul_psuField_eq_one _ _ h2
    refine ⟨c, ?_⟩
    have e : glAut σ (A : GL (Fin 3) F) =
        (A : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) c := by
      rw [← hc, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    have e' := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) e
    simp only [coe_glAut, Units.val_mul, GeneralLinearGroup.coe_scalar] at e'
    rw [e', Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  have hA3 : ∃ c : F, ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = c • 1 := by
    have h1 : psuConj h (A ^ 3) * psuField h 1 = 1 := by rw [map_one, mul_one, map_pow, h3]
    obtain ⟨-, c, -, hc⟩ := eq_one_of_psuConj_mul_psuField_eq_one _ _ h1
    refine ⟨c, ?_⟩
    have e : ((A ^ 3 : unitaryIsom3 h) : GL (Fin 3) F) = A * A * A := by
      rw [Subgroup.coe_pow, pow_three']
    rw [← Units.val_mul, ← Units.val_mul, ← e, hc, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hAn : ¬ ∃ c : F, ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = c • 1 := by
    rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      have h1 : ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          (((A : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [hc, zero_smul, Matrix.zero_mul] at h1
      exact zero_ne_one h1
    apply hA1
    refine psuConj_eq_one_of_coe_eq_scalar (c := Units.mk0 c hc0) (Units.ext ?_)
    rw [hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.val_mk0,
      Matrix.smul_one_eq_diagonal]
  obtain ⟨M, hMdef⟩ : ∃ M : Matrix (Fin 3) (Fin 3) F,
      M = ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := ⟨_, rfl⟩
  rw [← hMdef] at hσA hA3 hAn
  have hMu : (M.map h.bar)ᵀ * M = 1 := by rw [hMdef]; exact A.2
  obtain ⟨i0, j0, hb⟩ := CFSG.RankThree.PartTwo.Sec19.U38F.exists_ne_zero_entry hAn
  obtain ⟨c, hc⟩ := hσA
  have hcb : σ (M i0 j0) = c * M i0 j0 := by
    have := congrFun (congrFun hc i0) j0
    simpa [Matrix.map_apply, Matrix.smul_apply] using this
  obtain ⟨B', hB'⟩ : ∃ B' : Matrix (Fin 3) (Fin 3) F, B' = (M i0 j0)⁻¹ • M := ⟨_, rfl⟩
  have hMB' : M = M i0 j0 • B' := by rw [hB', smul_inv_smul₀ hb]
  have hc0 : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_mul] at hcb
    exact hb (σ.injective (by rw [hcb, map_zero]))
  have hfix : ∀ i j, σ (B' i j) = B' i j := by
    intro i j
    have hij := congrFun (congrFun hc i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hij
    rw [hB']
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, hij, hcb]
    field_simp
  have hfour : ∀ i j, B' i j ^ 4 = B' i j := fun i j => by rw [← hσ4, hfix]
  have hu : (B'.map h.bar)ᵀ * B' = 1 :=
    CFSG.RankThree.PartTwo.Sec19.U38F.unitary_normalize h hb hB' hMu hfour
  obtain ⟨Ym, hYe, hYm⟩ := CFSG.RankThree.PartTwo.Sec19.U38F.exists_model_matrix ι hιω hω hfour
  have hYu : unitaryOk Ym = true := by
    apply decide_eq_true
    apply CFSG.RankThree.PartTwo.Sec19.U38F.toMat_inj ι
    rw [toMat_mul, toMat_one]
    have h1 := toMat_transpose_map h ι Ym
    rw [hq] at h1
    rw [h1, hYm, hu]
  have hYns : isScalar Ym = false := by
    by_contra hcon
    have h1 := CFSG.RankThree.PartTwo.Sec19.U38F.toMat_scalar_of_isScalar ι
      (Bool.eq_true_of_not_eq_false hcon)
    apply hAn
    refine ⟨M i0 j0 * ι Ym.a00, ?_⟩
    calc M = M i0 j0 • B' := hMB'
      _ = (M i0 j0 * ι Ym.a00) • 1 := by rw [← hYm, h1, smul_smul]
  have hY3 : isScalar (Ym * Ym * Ym) = true := by
    obtain ⟨c3, hc3⟩ := hA3
    apply CFSG.RankThree.PartTwo.Sec19.U38F.isScalar_of_toMat ι (d := (M i0 j0)⁻¹ ^ 3 * c3)
    rw [toMat_mul, toMat_mul, hYm, hB']
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hc3, smul_smul]
    ring_nf
  obtain ⟨e, he, g, -, ⟨hgE, hgU⟩, l, -, hYme⟩ :=
    CFSG.RankThree.PartTwo.Sec19.U38F.class_sound Certificates.certificate188005 hYe hYu hYns
      hY3
  obtain ⟨D, hDY, hD⟩ := exists_liftData he
  obtain ⟨hYst, -, -, -⟩ := LiftData.check_spec hD
  have hYuu : ((toMat ι D.Y).map h.bar)ᵀ * toMat ι D.Y = 1 := by
    rw [← toMat_mstar h ι, ← toMat_mul, hYst, toMat_one]
  let Yu0 : GL (Fin 3) F :=
    ⟨toMat ι D.Y, ((toMat ι D.Y).map h.bar)ᵀ, mul_eq_one_comm.2 hYuu, hYuu⟩
  let Yu : unitaryIsom3 h := ⟨Yu0, hYuu⟩
  have hGu : ((toMat ι g).map h.bar)ᵀ * toMat ι g = 1 := by
    have h1 := toMat_transpose_map h ι g
    rw [hq] at h1
    rw [← h1, ← toMat_mul, of_decide_eq_true hgU, toMat_one]
  let gU0 : GL (Fin 3) F := ⟨toMat ι g, ((toMat ι g).map h.bar)ᵀ, mul_eq_one_comm.2 hGu, hGu⟩
  let gU : unitaryIsom3 h := ⟨gU0, hGu⟩
  have hgUfix : glAut σ (gU : GL (Fin 3) F) = gU := by
    apply Units.ext
    rw [coe_glAut]
    exact CFSG.RankThree.PartTwo.Sec19.U38F.map_toMat_fixed ι hσω hgE
  set κ := psuConj h gU with hκ
  have hgUinv : (((gU⁻¹ : unitaryIsom3 h) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      toMat ι (gstar g) := by
    rw [CFSG.RankThree.PartTwo.Sec19.U38F.toMat_gstar h hq ι]
    rfl
  have hX : psuConj h A = κ * psuConj h Yu * κ⁻¹ := by
    set X : unitaryIsom3 h := gU * Yu * gU⁻¹ with hXdef
    have hXm : ((X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        toMat ι g * toMat ι e.Y * toMat ι (gstar g) := by
      rw [hXdef, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hgUinv, ← hDY]
    have hAX : ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        (M i0 j0 * ι l) • ((X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      calc ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = M := hMdef.symm
        _ = M i0 j0 • toMat ι Ym := by rw [hYm]; exact hMB'
        _ = (M i0 j0 * ι l) • ((X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
          rw [hYme, toMat_smul, toMat_mul, toMat_mul, hXm, smul_smul]
    have hcl : M i0 j0 * ι l ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hAX
      apply hAn
      exact ⟨0, by rw [hMdef, hAX, zero_smul]⟩
    have hAX' : ((A * X⁻¹ : unitaryIsom3 h) : GL (Fin 3) F) =
        GeneralLinearGroup.scalar (Fin 3) (Units.mk0 _ hcl) := by
      apply Units.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, hAX, Matrix.smul_mul,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, Units.val_mk0, Matrix.smul_one_eq_diagonal]
    have h1 : psuConj h (A * X⁻¹) = 1 := psuConj_eq_one_of_coe_eq_scalar hAX'
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    rw [h1, hXdef, map_mul, map_mul, map_inv]
  have hκf : psuField h σ = κ * psuField h σ * κ⁻¹ := by
    have h1 := psuField_mul_psuConj_mul_inv σ gU
    have h2 : (⟨glAut σ (gU : GL (Fin 3) F), glAut_mem_unitaryIsom3 σ gU.2⟩ : unitaryIsom3 h) =
        gU := Subtype.ext hgUfix
    rw [h2, ← hκ, mul_inv_eq_iff_eq_mul] at h1
    rw [← h1, mul_inv_cancel_right]
  have hcore := top_le_fixJoin_of_check h ι hι hσ4 hD Yu rfl
  rw [hX, hκf, fixJoin_conj]
  calc (⊤ : Subgroup (unitaryPSU h 3)) = (⊤ : Subgroup (unitaryPSU h 3)).map κ.toMonoidHom :=
        (Subgroup.map_top_of_surjective _ κ.surjective).symm
    _ ≤ _ := Subgroup.map_mono hcore

theorem top_le_fixJoin_model (h : UnitaryFieldData 2 3 F) {σ : F ≃+* F} (hσ : orderOf σ = 3)
    (A : unitaryIsom3 h) (hcomm : psuConj h A * psuField h σ = psuField h σ * psuConj h A)
    (h3 : psuConj h A ^ 3 = 1) (hA1 : psuConj h A ≠ 1) :
    (⊤ : Subgroup (unitaryPSU h 3)) ≤ fixJoin (psuField h σ) (psuConj h A) := by
  rcases frob_cases h hσ with h4 | h16
  · exact top_le_fixJoin_four h h4 A hcomm h3 hA1
  · have := h.finite
    have h64 : ∀ c : F, c ^ 64 = c := by
      intro c
      have := Fintype.ofFinite F
      have hc : Fintype.card F = 64 := by rw [← Nat.card_eq_fintype_card, h.card]; norm_num
      rw [← hc]
      exact FiniteField.pow_card c
    have h4' : ∀ c, σ⁻¹ c = c ^ 4 := by
      intro c
      apply σ.injective
      change σ (σ.symm c) = σ (c ^ 4)
      rw [RingEquiv.apply_symm_apply, h16, ← pow_mul, h64]
    have hcomm' : psuConj h A * psuField h σ⁻¹ = psuField h σ⁻¹ * psuConj h A := by
      rw [map_inv]
      exact (Commute.inv_right (show Commute (psuConj h A) (psuField h σ) from hcomm)).eq
    have := top_le_fixJoin_four h h4' A hcomm' h3 hA1
    rw [map_inv] at this
    exact this.trans (fixJoin_inv_le _ _ hcomm.symm h3)

end Model

end CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.U38

namespace CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.RankThree.PartTwo.KFacts CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
open CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.U38


theorem bglOffEpsU38_holds : BGLOffEpsU38 := by
  intro K _ _ hK hU8 f x hf hf1 hf3 hx hx1 hx3 hfx
  obtain ⟨F0, hF0, hfin0, hcard0, ⟨e0⟩⟩ := hU8
  obtain ⟨p, e, F, hFf, hF, η, σ, A, hσ, -, hηf, hηx⟩ :=
    bglu_data hK ⟨F0, hF0, hfin0, 8, hcard0, ⟨e0⟩⟩ hf hf1 hf3 hx
  have h8 : 8 = p ^ e := bglu_q_eq ⟨F0, hF0, hfin0, hcard0, ⟨e0⟩⟩
    ⟨F, hFf, hF.finite, hF.card_eq_sq, ⟨η.trans (psuO hF)⟩⟩
  obtain ⟨rfl, rfl⟩ := prime_pow_eq_eight hF.prime hF.one_le h8.symm
  have hcomm : psuConj hF A * psuField hF σ = psuField hF σ * psuConj hF A := by
    have := congrArg (fun z : MulAut K => MulAut.congr η (centerDescend K z)) hfx
    simp only [map_mul] at this
    rw [hηf, hηx] at this
    exact this.symm
  have h3 : psuConj hF A ^ 3 = 1 := by
    rw [← hηx, ← map_pow, ← map_pow, hx3, map_one, map_one]
  have hA1 : psuConj hF A ≠ 1 := by
    intro h1
    apply hx1
    refine eq_one_of_centerDescend_eq_one hK ?_
    apply (MulAut.congr η).injective
    rw [hηx, h1, map_one]
  have hQ := top_le_fixJoin_model hF hσ A hcomm h3 hA1
  have hK1 : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ := by
    have := hK.1
    rwa [commutator_def] at this
  let π : K →* unitaryPSU hF 3 := η.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hker : π.ker ≤ Subgroup.center K := by
    intro k hk
    have h1 : η (QuotientGroup.mk' (Subgroup.center K) k) = 1 := hk
    rw [map_eq_one_iff _ η.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hπ : Function.Surjective π := fun y => by
    obtain ⟨q, rfl⟩ := η.surjective y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) q
    exact ⟨k, rfl⟩
  have hcompat : ∀ (α : MulAut K) (β : MulAut (unitaryPSU hF 3)),
      MulAut.congr η (centerDescend K α) = β → ∀ k, π (α k) = β (π k) := by
    intro α β hαβ k
    rw [← hαβ]
    change η ((α k : K) : K ⧸ Subgroup.center K) =
      η (centerDescend K α (η.symm (η (k : K ⧸ Subgroup.center K))))
    rw [MulEquiv.symm_apply_apply, centerDescend_mk]
  exact top_le_of_fixJoin π hker hπ hK1 f x _ _ (hcompat f _ hηf) (hcompat x _ hηx) hQ

end CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps
