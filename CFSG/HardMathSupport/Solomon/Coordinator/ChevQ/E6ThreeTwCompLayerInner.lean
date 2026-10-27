module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCompFrame
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCompTorus

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KE6 CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Lang.SeitzPlane CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE (diagGL3 conjDiag3 toGL_conjDiag3)

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary)

open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

open CFSG.RankThree.PartTwo.KFacts (unitaryIsom3 mem_unitaryIsom3 unitarySU_le_unitaryIsom3
  suConj coe_suConj psuConj psuConj_mk eq_one_of_psuConj_mul_psuField_eq_one)

open CFSG.RankThree.PartTwo.Sec4.E27 (coe_conj_eq_of_eq_smul)

open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

section Group

variable {G : Type*} [Group G]

theorem twConj_inv_mul_eq {a b v : G} (h : a * v * a⁻¹ = b * v * b⁻¹) :
    b⁻¹ * a * v * (b⁻¹ * a)⁻¹ = v :=
  calc b⁻¹ * a * v * (b⁻¹ * a)⁻¹ = b⁻¹ * (a * v * a⁻¹) * b := by group
    _ = b⁻¹ * (b * v * b⁻¹) * b := by rw [h]
    _ = v := by group

end Group

section Unitary

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

theorem twMem_unitaryIsom3_of_mem {X : GL (Fin 3) K}
    (hX : X ∈ primeFormUnitary h (idGram K 3)) : X ∈ unitaryIsom3 h := by
  have h1 := UnitaryHigher.mem_primeFormUnitary.1 hX
  rw [show idGram K 3 = 1 from rfl, Matrix.mul_one] at h1
  exact mem_unitaryIsom3.2 h1

theorem twExists_unitarySU_conj_eq_pow_three (P : primeFormUnitary h (idGram K 3)) :
    ∃ B : unitarySU ℓ f K 3, ∀ w : unitarySU ℓ f K 3,
      B * w * B⁻¹ = conjSU h P (conjSU h P (conjSU h P w)) := by
  have hPi := mem_unitaryIsom3.1 (twMem_unitaryIsom3_of_mem h P.2)
  obtain ⟨δ, hδ⟩ : ∃ δ : Kˣ, δ = Matrix.GeneralLinearGroup.det (P : GL (Fin 3) K) := ⟨_, rfl⟩
  have hdn : h.bar (δ : K) * δ = 1 := by
    have h2 := congrArg Matrix.det hPi
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det] at h2
    rwa [hδ, Matrix.GeneralLinearGroup.val_det_apply]
  obtain ⟨s, hs⟩ : ∃ s : GL (Fin 3) K, s = Matrix.GeneralLinearGroup.scalar (Fin 3) δ⁻¹ :=
    ⟨_, rfl⟩
  have hsu : s ∈ primeFormUnitary h (idGram K 3) := by
    have hn : h.bar ((δ⁻¹ : Kˣ) : K) * ((δ⁻¹ : Kˣ) : K) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, hdn, inv_one]
    rw [UnitaryHigher.mem_primeFormUnitary, show idGram K 3 = 1 from rfl, Matrix.mul_one, hs,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _),
      Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, hn, Matrix.diagonal_one]
  have hB : s * (P : GL (Fin 3) K) ^ 3 ∈ unitarySU ℓ f K 3 := by
    refine (mem_unitarySU_iff h).2 ⟨?_, ?_⟩
    · rw [← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_pow, hs,
        Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, ← hδ, inv_pow, inv_mul_cancel,
        Units.val_one]
    · exact mem_unitaryIsom3.1 (twMem_unitaryIsom3_of_mem h (mul_mem hsu (pow_mem P.2 3)))
  have hc : ∀ M : GL (Fin 3) K, s * M * s⁻¹ = M := fun M => by
    rw [hs, Matrix.GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]
  refine ⟨⟨_, hB⟩, fun w => Subtype.ext ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_conjSU, coe_conjSU, coe_conjSU]
  calc s * (P : GL (Fin 3) K) ^ 3 * (w : GL (Fin 3) K) * (s * (P : GL (Fin 3) K) ^ 3)⁻¹
      = s * ((P : GL (Fin 3) K) ^ 3 * w * ((P : GL (Fin 3) K) ^ 3)⁻¹) * s⁻¹ := by group
    _ = (P : GL (Fin 3) K) ^ 3 * w * ((P : GL (Fin 3) K) ^ 3)⁻¹ := hc _
    _ = P * (P * (P * w * (P : GL (Fin 3) K)⁻¹) * (P : GL (Fin 3) K)⁻¹) *
        (P : GL (Fin 3) K)⁻¹ := by
      rw [pow_three]
      group

variable {h}

theorem twExists_smul_one_of_conj_eq {X : GL (Fin 3) K} (hX : X ∈ unitaryIsom3 h)
    (hc : ∀ w : unitarySU ℓ f K 3, X * w * X⁻¹ = w) :
    ∃ c : K, c ≠ 0 ∧ (X : Matrix (Fin 3) (Fin 3) K) = c • 1 := by
  have hsu : suConj h ⟨X, hX⟩ = 1 :=
    MulEquiv.ext fun g => Subtype.ext ((coe_suConj _ g).trans (hc g))
  have hpsu : psuConj h ⟨X, hX⟩ = 1 := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H g => rw [psuConj_mk, hsu]; rfl
  obtain ⟨-, c, -, hcX⟩ :=
    eq_one_of_psuConj_mul_psuField_eq_one ⟨X, hX⟩ 1 (by rw [map_one, mul_one]; exact hpsu)
  have hX' : X = Matrix.GeneralLinearGroup.scalar (Fin 3) c := hcX
  refine ⟨c, c.ne_zero, ?_⟩
  rw [hX']
  simp [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]

end Unitary

section Realize

variable {ℓ f : ℕ} {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]

theorem TwDiagRealizes.twOf_smul {Hc : SL(3, Ω)} {d : Fin 3 → Ωˣ} {B B' : GL (Fin 3) K} {c : K}
    (hB : TwDiagRealizes Hc d B) (hc : c ≠ 0)
    (hBB' : (B : Matrix (Fin 3) (Fin 3) K) = c • (B' : Matrix (Fin 3) (Fin 3) K)) :
    TwDiagRealizes Hc d B' := by
  obtain ⟨c', hc', hN⟩ := hB
  refine ⟨c' * algebraMap K Ω c, mul_ne_zero hc' ((map_ne_zero _).2 hc), ?_⟩
  rw [hN, hBB', Matrix.map_smul' (algebraMap K Ω) c _ (map_mul _), smul_smul]

theorem TwDiagRealizes.twDiag_eq_smul (h : UnitaryFieldData ℓ f K) {Hc : SL(3, Ω)}
    {d : Fin 3 → Ωˣ} {x : unitarySU ℓ f K 3} (hx : TwDiagRealizes Hc d (x : GL (Fin 3) K)) :
    ∃ c : Ω, c ≠ 0 ∧ ((diagGL3 d : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
      c • ((Matrix.SpecialLinearGroup.toGL (twUnitaryFrame h Hc x) : GL (Fin 3) Ω) :
        Matrix (Fin 3) (Fin 3) Ω) := by
  obtain ⟨c, hc, hN⟩ := hx
  refine ⟨c, hc, ?_⟩
  have e : diagGL3 d = Matrix.SpecialLinearGroup.toGL Hc * twFrameDiag Hc d *
      (Matrix.SpecialLinearGroup.toGL Hc)⁻¹ := by
    unfold twFrameDiag
    group
  rw [e, toGL_twUnitaryFrame]
  simp only [Units.val_mul]
  rw [hN, coe_gl3Emb, Matrix.mul_smul, Matrix.smul_mul]

theorem TwDiagRealizes.twUnitaryFrame_offDiag (h : UnitaryFieldData ℓ f K) {Hc : SL(3, Ω)}
    {d : Fin 3 → Ωˣ} {x : unitarySU ℓ f K 3} (hx : TwDiagRealizes Hc d (x : GL (Fin 3) K)) :
    ∀ j k, j ≠ k → ((twUnitaryFrame h Hc x : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) j k = 0 := by
  intro j k hjk
  obtain ⟨c, hc, he⟩ := hx.twDiag_eq_smul h
  have h1 := congrFun (congrFun he j) k
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at h1
  have h2 : ((diagGL3 d : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) j k = 0 :=
    Matrix.diagonal_apply_ne _ hjk
  rw [h2] at h1
  exact (mul_eq_zero.1 h1.symm).resolve_left hc

theorem TwDiagRealizes.twConjDiag3_eq (h : UnitaryFieldData ℓ f K) {Hc : SL(3, Ω)}
    {d : Fin 3 → Ωˣ} {x : unitarySU ℓ f K 3} (hx : TwDiagRealizes Hc d (x : GL (Fin 3) K))
    (Z : SL(3, Ω)) :
    conjDiag3 d Z = twUnitaryFrame h Hc x * Z * (twUnitaryFrame h Hc x)⁻¹ := by
  obtain ⟨c, hc, he⟩ := hx.twDiag_eq_smul h
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [toGL_conjDiag3, map_mul, map_mul, map_inv]
  apply Units.ext
  simp only [Units.val_mul]
  refine coe_conj_eq_of_eq_smul (diagGL3 d) _ _ c hc he ?_ _
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

end Realize

section Blocks


variable {ℓ f : ℕ} {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]

theorem twBlockProd_mem_torusGroup_of_realizes (h : UnitaryFieldData ℓ f K)
    {Hc : Fin 3 → SL(3, Ω)} {x : Fin 3 → unitarySU ℓ f K 3} {d : Fin 3 → Fin 3 → Ωˣ}
    (hx : ∀ i, TwDiagRealizes (Hc i) (d i) (x i : GL (Fin 3) K)) :
    twBlockProd Ω (fun j => twUnitaryFrame h (Hc j) (x j)) ∈ torusGroup Tag.E6 Ω := by
  rw [twBlockProd_apply]
  exact mul_mem (mul_mem (twFrame_diag_mem_torusGroup 0 ((hx 0).twUnitaryFrame_offDiag h))
    (twFrame_diag_mem_torusGroup 1 ((hx 1).twUnitaryFrame_offDiag h)))
    (twFrame_diag_mem_torusGroup 2 ((hx 2).twUnitaryFrame_offDiag h))

theorem twBlockProd_conj_of_realizes (h : UnitaryFieldData ℓ f K) {Hc : Fin 3 → SL(3, Ω)}
    {x : Fin 3 → unitarySU ℓ f K 3} {d : Fin 3 → Fin 3 → Ωˣ}
    (hx : ∀ i, TwDiagRealizes (Hc i) (d i) (x i : GL (Fin 3) K)) (i : Fin 3) (Z : SL(3, Ω)) :
    twBlockProd Ω (fun j => twUnitaryFrame h (Hc j) (x j)) * twFrame Ω i Z *
      (twBlockProd Ω (fun j => twUnitaryFrame h (Hc j) (x j)))⁻¹ =
        twFrame Ω i (conjDiag3 (d i) Z) := by
  rw [(hx i).twConjDiag3_eq h Z]
  exact commProd3_conj_apply (twFrame Ω) twFrame_commute _ i Z

end Blocks

section Package


variable {K : Type} [Field K] {σ : K ≃+* K} {h₀ : ModGL TwistTag.E6.tag K}
  {L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K)} {T : Subgroup (ModGL TwistTag.E6.tag K)}
  {n : ModGL TwistTag.E6.tag K} {ℓ f : ℕ} {hU : UnitaryFieldData ℓ f K}
  {Fr : AlgebraicClosure K →+* AlgebraicClosure K} {g₀ : ModGL Tag.E6 (AlgebraicClosure K)}
  {Hc : Fin 3 → SL(3, AlgebraicClosure K)}
  {ρ : Fin 3 → unitarySU ℓ f K 3 →* twistedE6RootGroup K σ}
  {A : Fin 3 → ModGL TwistTag.E6.tag K → primeFormUnitary hU (idGram K 3)}

theorem TwCompFrames.pow_three_inner (F : TwCompFrames K σ h₀ L T n hU Fr g₀ Hc ρ A)
    {τ : ModGL TwistTag.E6.tag K} (hτ : τ ∈ twTorusHat K σ g₀) (i : Fin 3) :
    ∃ B : unitarySU ℓ f K 3, ∀ w : unitarySU ℓ f K 3,
      τ ^ 3 * ((ρ i w : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * (τ ^ 3)⁻¹ =
        ((ρ i (B * w * B⁻¹) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) := by
  obtain ⟨B, hB⟩ := twExists_unitarySU_conj_eq_pow_three hU (A i τ)
  refine ⟨B, fun w => ?_⟩
  rw [hB w, ← F.act i τ hτ, ← F.act i τ hτ, ← F.act i τ hτ, pow_three]
  group

theorem TwCompFrames.twRealizes_of_inner (F : TwCompFrames K σ h₀ L T n hU Fr g₀ Hc ρ A)
    {τ : ModGL TwistTag.E6.tag K} (hτ : τ ∈ twTorusHat K σ g₀) {i : Fin 3}
    {B : unitarySU ℓ f K 3}
    (hB : ∀ w : unitarySU ℓ f K 3,
      τ * ((ρ i w : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * τ⁻¹ =
        ((ρ i (B * w * B⁻¹) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K)) :
    ∃ d : Fin 3 → (AlgebraicClosure K)ˣ,
      (∀ X, twLinePsi K g₀ τ * twFrame (AlgebraicClosure K) i X * (twLinePsi K g₀ τ)⁻¹ =
        twFrame (AlgebraicClosure K) i (conjDiag3 d X)) ∧
        TwDiagRealizes (Hc i) d (B : GL (Fin 3) K) := by
  obtain ⟨d, hd, hdr⟩ := F.realizes i τ hτ
  refine ⟨d, hd, ?_⟩
  have hconj : ∀ w, conjSU hU (A i τ) w = B * w * B⁻¹ := fun w =>
    F.injective i (Subtype.ext ((F.act i τ hτ w).symm.trans (hB w)))
  obtain ⟨c, hc, hcX⟩ := twExists_smul_one_of_conj_eq
    (mul_mem (inv_mem (unitarySU_le_unitaryIsom3 (h := hU) B.2))
      (twMem_unitaryIsom3_of_mem hU (A i τ).2)) fun w => by
      have h1 := congrArg Subtype.val (hconj w)
      rw [coe_conjSU, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h1
      exact twConj_inv_mul_eq h1
  refine hdr.twOf_smul hc ?_
  have e : (A i τ : GL (Fin 3) K) =
      (B : GL (Fin 3) K) * ((B : GL (Fin 3) K)⁻¹ * (A i τ : GL (Fin 3) K)) := by
    group
  rw [e, Units.val_mul, hcX, Matrix.mul_smul, Matrix.mul_one]

theorem TwCompFrames.mem_layer_of_inner (F : TwCompFrames K σ h₀ L T n hU Fr g₀ Hc ρ A)
    (hl : TwE6ThreeA2Line K σ h₀ L T n) {τ : ModGL TwistTag.E6.tag K}
    (hτ : τ ∈ twTorusHat K σ g₀)
    (hinn : ∀ i, ∃ B : unitarySU ℓ f K 3, ∀ w : unitarySU ℓ f K 3,
      τ * ((ρ i w : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * τ⁻¹ =
        ((ρ i (B * w * B⁻¹) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K)) :
    τ ∈ ⨆ i, L i := by
  choose B hB using hinn
  choose d hd hdr using fun i => F.twRealizes_of_inner hτ (hB i)
  obtain ⟨m, hm⟩ : ∃ m, m = (twLayerProd ρ B)⁻¹ * τ := ⟨_, rfl⟩
  have hψm : twLinePsi K g₀ m = (twBlockProd (AlgebraicClosure K)
      (fun j => twUnitaryFrame hU (Hc j) (B j)))⁻¹ * twLinePsi K g₀ τ := by
    rw [hm, map_mul, map_inv, F.psi_layerProd]
  have hmH : twLinePsi K g₀ m ∈ torusGroup Tag.E6 (AlgebraicClosure K) := by
    rw [hψm]
    exact mul_mem (inv_mem (twBlockProd_mem_torusGroup_of_realizes hU hdr))
      (mem_twTorusHat.1 hτ).2
  have hmc : ∀ i, ∀ y ∈ rootSpan Tag.E6 (AlgebraicClosure K) (twE6FrameS i),
      twLinePsi K g₀ m * y = y * twLinePsi K g₀ m := by
    intro i y hy
    obtain ⟨Z, rfl⟩ := exists_twFrame_eq i hy
    rw [hψm]
    exact mul_inv_eq_iff_eq_mul.1
      (twConj_inv_mul_eq ((hd i Z).trans (twBlockProd_conj_of_realizes hU hdr i Z).symm))
  obtain ⟨ω, hω3, hω1, hψh⟩ := F.pic.h₀_image
  have hz := twTorus_mem_zpowers_of_commute hω3 hω1 hmH hmc
  rw [← hψh] at hz
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hmk : m = h₀ ^ k := twLinePsi_injective K g₀ (by rw [map_zpow, hk])
  have hLB : ∀ j, ((ρ j (B j) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) ∈ ⨆ i, L i :=
    fun j => Subgroup.mem_iSup_of_mem j (by rw [← F.range j]; exact ⟨ρ j (B j), ⟨B j, rfl⟩, rfl⟩)
  have hP : twLayerProd ρ B ∈ ⨆ i, L i := mul_mem (mul_mem (hLB 0) (hLB 1)) (hLB 2)
  have hτm : τ = twLayerProd ρ B * m := by rw [hm, mul_inv_cancel_left]
  rw [hτm, hmk]
  exact mul_mem hP (Subgroup.mem_iSup_of_mem 0 (zpow_mem (hl.h₀_mem_L 0) k))

end Package

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
