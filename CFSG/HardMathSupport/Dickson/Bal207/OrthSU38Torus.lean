module

public import CFSG.HardMathSupport.Dickson.Bal207.SU38Block
public import CFSG.HardMathSupport.Dickson.Bal207.SpFCFrame
public import CFSG.HardMathSupport.Dickson.Bal207.UniNormalAut
import CFSG.HardMathSupport.Dickson.Bal207.OrthSemilinLift
public import CFSG.HardMathSupport.Dickson.Bal207.OrthFixedType
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Unit

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.OrthFix

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Dickson.Bal207.Uni
  CFSG.HardMathSupport.Dickson.I271 CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.RankThree.PartOne.KCOrthogonalAut

theorem uniAut_fix_of_eq_conj {F : Type} [Field F] [Finite F] [CharP F 2] {d : ℕ}
    {Q : QuadraticForm F (Fin d → F)} {G : Type} [Group G] {K B : Subgroup G}
    (hB : IsSCp 3 ⊤ B) (hBK : B ≤ Subgroup.normalizer (K : Set G)) (_hd : 0 < d)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule F (Fin d → F), Module.finrank F U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ProjOrthDerived Q) {a : G} (haB : a ∈ B)
    {t : ProjOrthDerived Q} (ha : uniAut e ⟨a, hBK haB⟩ = MulAut.conj t) (b : ↥B) :
    uniAut e ⟨b, hBK b.2⟩ t = t := by
  have hZ := CFSG.RankThree.PartOne.KCOrthogonalD4.center_projOrthDerived_eq_bot Q hQ hT
  have hab : (⟨a, hBK haB⟩ : ↥(Subgroup.normalizer (K : Set G))) * ⟨b, hBK b.2⟩ =
      ⟨b, hBK b.2⟩ * ⟨a, hBK haB⟩ :=
    Subtype.ext (show a * (b : G) = b * a from
      congrArg Subtype.val (hB.2.1.1.is_comm.comm ⟨a, haB⟩ b))
  have hc := congrArg (uniAut e) hab
  rw [map_mul, map_mul, ha] at hc
  obtain ⟨β, hβ⟩ : ∃ β, β = uniAut e ⟨b, hBK b.2⟩ := ⟨_, rfl⟩
  rw [← hβ] at hc ⊢
  have hcen : (β t)⁻¹ * t ∈ Subgroup.center (ProjOrthDerived Q) := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h1 := congrArg (fun φ : MulAut (ProjOrthDerived Q) => φ (β.symm z)) hc
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply] at h1
    calc z * ((β t)⁻¹ * t) = (β t)⁻¹ * (β t * z * (β t)⁻¹) * t := by group
      _ = (β t)⁻¹ * (t * z * t⁻¹) * t := by rw [h1]
      _ = (β t)⁻¹ * t * z := by group
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hcen
  exact hcen

section Semilin

open CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] {σ : F ≃+* F}
  {S : V ≃+ V} {xe : V ≃ₗ[F] V}

theorem phi_map_ringEquiv {φ : F[X]} (hφ : φ = X ^ 2 + X + 1) (τ : F ≃+* F) :
    φ.map (τ : F →+* F) = φ := by
  subst hφ
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]

theorem polar_semilin {Q : QuadraticForm F V} (hSQ : ∀ v, Q (S v) = σ (Q v)) (u w : V) :
    polar Q (S u) (S w) = σ (polar Q u w) := by
  rw [polar, polar, ← map_add S u w, hSQ, hSQ, hSQ, map_sub, map_sub]

theorem semilin_aeval (hS : ∀ (c : F) (v : V), S (c • v) = σ c • S v)
    (hSx : ∀ v, S (xe v) = xe (S v)) (p : F[X]) (v : V) :
    S (aeval xe.toLinearMap p v) = aeval xe.toLinearMap (p.map (σ : F →+* F)) (S v) := by
  have hpow : ∀ (n : ℕ) (w : V), S ((xe.toLinearMap ^ n) w) = (xe.toLinearMap ^ n) (S w) := by
    intro n
    induction n with
    | zero => intro w; rw [pow_zero, Module.End.one_apply, Module.End.one_apply]
    | succ n ih =>
      intro w
      rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      exact congrArg (fun u => (xe.toLinearMap ^ n) u) (hSx w)
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.map_add, LinearMap.add_apply, hp, hq]
  | monomial n c =>
    simp only [aeval_monomial, Polynomial.map_monomial, Module.End.mul_apply,
      Module.algebraMap_end_apply, hS, hpow, RingEquiv.coe_toRingHom]

theorem semilin_mem_primaryComponent (hS : ∀ (c : F) (v : V), S (c • v) = σ c • S v)
    (hSx : ∀ v, S (xe v) = xe (S v)) {φ : F[X]} (hφ : φ.map (σ : F →+* F) = φ) {v : V}
    (hv : v ∈ primaryComponent xe.toLinearMap φ) : S v ∈ primaryComponent xe.toLinearMap φ := by
  rw [mem_primaryComponent] at hv ⊢
  rw [← hφ, ← semilin_aeval hS hSx, hv, map_zero]

theorem semilin_comm_symm (hSx : ∀ v, S (xe v) = xe (S v)) (v : V) :
    S.symm (xe v) = xe (S.symm v) := by
  refine S.injective ?_
  rw [S.apply_symm_apply, hSx, S.apply_symm_apply]

theorem phi_map_symm {φ : F[X]} (hφ : φ.map (σ : F →+* F) = φ) :
    φ.map (σ.symm : F →+* F) = φ := by
  have h := congrArg (Polynomial.map (σ.symm : F →+* F)) hφ
  rw [Polynomial.map_map] at h
  have hcomp : ((σ.symm : F →+* F).comp (σ : F →+* F)) = RingHom.id F := by
    ext c
    exact σ.symm_apply_apply c
  rw [hcomp, Polynomial.map_id] at h
  exact h.symm

@[expose] def semilinRestrict (hS : ∀ (c : F) (v : V), S (c • v) = σ c • S v)
    (hSx : ∀ v, S (xe v) = xe (S v)) {φ : F[X]} (hφ : φ.map (σ : F →+* F) = φ) :
    primaryComponent xe.toLinearMap φ ≃+ primaryComponent xe.toLinearMap φ where
  toFun v := ⟨S (v : V), semilin_mem_primaryComponent hS hSx hφ v.2⟩
  invFun v := ⟨S.symm (v : V), semilin_mem_primaryComponent
    (semilin_symm_smul S σ hS) (semilin_comm_symm hSx) (phi_map_symm hφ) v.2⟩
  left_inv v := Subtype.ext (S.symm_apply_apply (v : V))
  right_inv v := Subtype.ext (S.apply_symm_apply (v : V))
  map_add' u v := Subtype.ext (map_add S (u : V) (v : V))

theorem coe_semilinRestrict (hS : ∀ (c : F) (v : V), S (c • v) = σ c • S v)
    (hSx : ∀ v, S (xe v) = xe (S v)) {φ : F[X]} (hφ : φ.map (σ : F →+* F) = φ)
    (v : primaryComponent xe.toLinearMap φ) :
    (semilinRestrict hS hSx hφ v : V) = S (v : V) := rfl

theorem coe_semilinRestrict_symm (hS : ∀ (c : F) (v : V), S (c • v) = σ c • S v)
    (hSx : ∀ v, S (xe v) = xe (S v)) {φ : F[X]} (hφ : φ.map (σ : F →+* F) = φ)
    (v : primaryComponent xe.toLinearMap φ) :
    ((semilinRestrict hS hSx hφ).symm v : V) = S.symm (v : V) := rfl

theorem semilinRestrict_smul (hS : ∀ (c : F) (v : V), S (c • v) = σ c • S v)
    (hSx : ∀ v, S (xe v) = xe (S v)) {φ : F[X]} (hφ : φ.map (σ : F →+* F) = φ)
    (c : AdjoinRoot φ) (v : primaryComponent xe.toLinearMap φ) :
    semilinRestrict hS hSx hφ (c • v) = extAut φ σ hφ c • semilinRestrict hS hSx hφ v := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective c
  refine Subtype.ext ?_
  rw [coe_semilinRestrict, coe_mk_smul_primaryComponent, semilin_aeval hS hSx, extAut_mk,
    coe_mk_smul_primaryComponent, coe_semilinRestrict]

theorem herm_semilinRestrict (hS : ∀ (c : F) (v : V), S (c • v) = σ c • S v)
    (hSx : ∀ v, S (xe v) = xe (S v)) {Q : QuadraticForm F V} (hSQ : ∀ v, Q (S v) = σ (Q v))
    {φ : F[X]} [Fact (Irreducible φ)] (hφ' : φ = X ^ 2 + X + 1) (hφ : φ.map (σ : F →+* F) = φ)
    {H : primaryComponent xe.toLinearMap φ → primaryComponent xe.toLinearMap φ → AdjoinRoot φ}
    (htr : ∀ u w c, Algebra.trace F (AdjoinRoot φ) (H u w * c) =
      polar Q (u : V) ((c • w : primaryComponent xe.toLinearMap φ) : V))
    (u w : primaryComponent xe.toLinearMap φ) :
    H (semilinRestrict hS hSx hφ u) (semilinRestrict hS hSx hφ w) = extAut φ σ hφ (H u w) := by
  refine eq_of_forall_trace_mul_eq hφ' fun c => ?_
  have hc : c • semilinRestrict hS hSx hφ w =
      semilinRestrict hS hSx hφ ((extAut φ σ hφ).symm c • w) := by
    rw [semilinRestrict_smul, RingEquiv.apply_symm_apply]
  rw [mul_comm c, htr, hc, coe_semilinRestrict, coe_semilinRestrict, polar_semilin hSQ, ← htr,
    ← trace_extAut hφ' hφ, map_mul (extAut φ σ hφ), RingEquiv.apply_symm_apply, mul_comm c]

theorem herm_semilinRestrict_finite [Finite F]
    (hS : ∀ (c : F) (v : V), S (c • v) = σ c • S v)
    (hSx : ∀ v, S (xe v) = xe (S v)) {Q : QuadraticForm F V}
    (hSQ : ∀ v, Q (S v) = σ (Q v)) {φ : F[X]} [Fact (Irreducible φ)]
    (hφ : φ.map (σ : F →+* F) = φ)
    {H : primaryComponent xe.toLinearMap φ → primaryComponent xe.toLinearMap φ → AdjoinRoot φ}
    (htr : ∀ u w c, Algebra.trace F (AdjoinRoot φ) (H u w * c) =
      polar Q (u : V) ((c • w : primaryComponent xe.toLinearMap φ) : V))
    (u w : primaryComponent xe.toLinearMap φ) :
    H (semilinRestrict hS hSx hφ u) (semilinRestrict hS hSx hφ w) =
      extAut φ σ hφ (H u w) := by
  letI : Finite (AdjoinRoot φ) := Module.finite_of_finite F
  exact traceTransfer_semilin F (AdjoinRoot φ) σ (extAut φ σ hφ)
    (fun c => extAut_of hφ c) (semilinRestrict hS hSx hφ)
    (semilinRestrict_smul hS hSx hφ)
    (fun u w => polar Q (u : V) (w : V))
    (fun u w => polar_semilin hSQ (u : V) (w : V)) H htr u w

end Semilin

section BlockSquare

open CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
  {Q : QuadraticForm F V} {x : V ≃ₗ[F] V} {φ : F[X]} {σ : F ≃+* F} {S : V ≃+ V}

theorem blockGL_semilinRestrict_square
    (hS : ∀ (c : F) (v : V), S (c • v) = σ c • S v)
    (hSx : ∀ v, S (x v) = x (S v)) (hφ : φ.map (σ : F →+* F) = φ)
    {g g' : ↥(supportedBlock Q x φ)}
    (hgg' : ∀ v : V, (g' : V ≃ₗ[F] V) v = S ((g : V ≃ₗ[F] V) (S.symm v)))
    (w : primaryComponent x.toLinearMap φ) :
    ((blockGL Q x φ g' : BlockGL x φ) : Module.End (AdjoinRoot φ)
      (primaryComponent x.toLinearMap φ)) w =
      semilinRestrict hS hSx hφ
        (((blockGL Q x φ g : BlockGL x φ) : Module.End (AdjoinRoot φ)
          (primaryComponent x.toLinearMap φ)) ((semilinRestrict hS hSx hφ).symm w)) := by
  apply Subtype.ext
  rw [coe_semilinRestrict, coe_blockGL, coe_blockGL, coe_semilinRestrict_symm]
  exact hgg' (w : V)

variable [FiniteDimensional F V]

end BlockSquare

section Frame

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {x : V ≃ₗ[F] V}

theorem exists_phiFrame {f : ℕ} (hFf : Nat.card F = 2 ^ f) (hf1 : 1 ≤ f)
    (hx : OddOrderIsometry Q 3 x) {φ : F[X]} [Fact (Irreducible φ)] (hφ : φ = X ^ 2 + X + 1)
    (hmem : φ ∈ primaryFactors x.toLinearMap) {m : ℕ}
    (hm : primaryMultiplicity x.toLinearMap φ = m) (hm3 : 3 ≤ m) (hmq : ¬(m = 3 ∧ 2 ^ f = 2)) :
    ∃ (hU : UnitaryFieldData 2 f (AdjoinRoot φ))
      (H : primaryComponent x.toLinearMap φ →ₛₗ[hU.bar]
        primaryComponent x.toLinearMap φ →ₗ[AdjoinRoot φ] AdjoinRoot φ)
      (b : Module.Basis (Fin m) (AdjoinRoot φ) (primaryComponent x.toLinearMap φ)),
      (∀ u w c, Algebra.trace F (AdjoinRoot φ) (H u w * c) =
        polar Q (u : V) ((c • w : primaryComponent x.toLinearMap φ) : V)) ∧
      (∀ i j, H (b i) (b j) = if i = j then 1 else 0) ∧
      (blockGL Q x φ).range = sesqUnitaryGroup H ∧ specialBlock Q x φ ≤ orthDerived Q := by
  classical
  have hirr : Irreducible φ := Fact.out
  have hne1 : φ ≠ X - 1 := by rw [hφ]; exact phi_ne
  have hself : φ = reciprocalPolynomial φ := by
    rw [hφ]; exact (CFSG.HardMathSupport.Timmesfeld.CrossChar.reciprocal_cyc3 F).symm
  obtain ⟨d, H, hdeg, -, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian ⟨1, rfl⟩ hmem hne1 hself
  have hd1 : d = 1 := by
    have h2 : φ.natDegree = 2 := by rw [hφ]; exact monic_phi.2
    omega
  subst hd1
  have : Module.Finite F (AdjoinRoot φ) := (AdjoinRoot.powerBasis hirr.ne_zero).finite
  have hcardE : Nat.card (AdjoinRoot φ) = 2 ^ (2 * f) := by
    rw [Module.natCard_eq_pow_finrank (K := F), (AdjoinRoot.powerBasis hirr.ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, hdeg, hFf, ← pow_mul]
    ring_nf
  have hU : UnitaryFieldData 2 f (AdjoinRoot φ) := ⟨Nat.prime_two, hf1, hcardE⟩
  have hbar' : ∀ z, frobPow F (AdjoinRoot φ) 1 z = hU.bar z := fun z => by
    rw [frobPow_apply, UnitaryFieldData.bar_apply, hFf, pow_one]
  let B : primaryComponent x.toLinearMap φ →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap φ →ₗ[AdjoinRoot φ] AdjoinRoot φ :=
    LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
      (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
      (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
  have hBH : ∀ u w, B u w = H u w := fun u w => rfl
  have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
  have hBl : B.SeparatingLeft := by
    intro u hu
    refine Subtype.ext (hx.eq_zero_of_polar_selfdual hmem hself u.2 fun w hw => ?_)
    have h1 := hH u ⟨w, hw⟩ 1
    rw [mul_one, one_smul] at h1
    have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
    rw [h2, map_zero] at h1
    exact h1.symm
  have hrange : (blockGL Q x φ).range = sesqUnitaryGroup B := by
    ext γ
    rw [hx.mem_range_blockGL_selfDual_iff hmem hne1 hself H hH, mem_sesqUnitaryGroup]
    exact Iff.rfl
  have hrangeSU : (specialBlockGL Q x φ).range = sesqSpecialUnitaryGroup B := by
    rw [range_specialBlockGL, sesqSpecialUnitaryGroup, hrange]
  have e₁ : ↥(specialBlock Q x φ) ≃* ↥(sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hmem)).trans
      (MulEquiv.subgroupCongr hrangeSU)
  have hfin : finrank (AdjoinRoot φ) (primaryComponent x.toLinearMap φ) = m := hm
  have hq : CFSG.IsQuasisimple ↥(specialBlock Q x φ) := by
    refine CFSG.LocalCores.isQuasisimple_of_mulEquiv e₁.symm
      (isQuasisimple_sesqSpecialUnitaryGroup_of_three_le hU hBsymm hBl (by omega) fun h' => ?_)
    have h3 : finrank (AdjoinRoot φ) (primaryComponent x.toLinearMap φ) = 3 :=
      congrArg Prod.fst h'
    exact hmq ⟨by omega, congrArg Prod.snd h'⟩
  have hspec : specialBlock Q x φ ≤ orthDerived Q :=
    specialBlock_le_orthDerived_of_perfect hq.1
      ((specialBlock_le_isometryCentralizer φ).trans fun _ hg => (Subgroup.mem_inf.mp hg).1)
  obtain ⟨b₀, hb₀⟩ := hU.exists_orthonormal_basis hBsymm hBl
  refine ⟨hU, B, b₀.reindex (finCongr hfin), hH, fun i j => ?_, hrange, hspec⟩
  simp [Module.Basis.reindex_apply, hb₀, Equiv.apply_eq_iff_eq]

theorem supportedBlock_le_orthDerived (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule F V, finrank F U = 3 ∧ ∀ u ∈ U, Q u = 0) {f m : ℕ} {φ : F[X]}
    [Fact (Irreducible φ)] (hU : UnitaryFieldData 2 f (AdjoinRoot φ))
    {H : primaryComponent x.toLinearMap φ →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap φ →ₗ[AdjoinRoot φ] AdjoinRoot φ}
    (b : Module.Basis (Fin m) (AdjoinRoot φ) (primaryComponent x.toLinearMap φ))
    (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0)
    (hrange : (blockGL Q x φ).range = sesqUnitaryGroup H)
    (hspec : specialBlock Q x φ ≤ orthDerived Q) :
    supportedBlock Q x φ ≤ orthDerived Q := by
  intro g hg
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg).1).1
  have hg2 : g ^ 2 ∈ orthDerived Q :=
    (CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ
      hT).2.2.2.2.2.1 g hgO
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ f = 2 * k := ⟨2 ^ (f - 1), by
    rw [← pow_succ']
    congr 1
    have := hU.one_le
    omega⟩
  have hγ : blockGL Q x φ ⟨g, hg⟩ ∈ sesqUnitaryGroup H := by
    rw [← hrange]
    exact ⟨⟨g, hg⟩, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : GL (Fin m) (AdjoinRoot φ),
      Matrix.GeneralLinearGroup.toLin' b M = blockGL Q x φ ⟨g, hg⟩ :=
    ⟨(Matrix.GeneralLinearGroup.toLin' b).symm _, MulEquiv.apply_symm_apply _ _⟩
  have hMU : M ∈ primeFormUnitary hU (oneGram (AdjoinRoot φ) m) :=
    (toLin'_mem_sesqUnitaryGroup_iff b hU hb M).1 (hM ▸ hγ)
  have hdet : (M : Matrix (Fin m) (Fin m) (AdjoinRoot φ)).det ^ (2 ^ f + 1) = 1 := by
    have h1 := congrArg Matrix.det (mem_primeFormUnitary.mp hMU)
    have h2 : ((M : Matrix (Fin m) (Fin m) (AdjoinRoot φ)).map hU.bar).det =
        hU.bar (M : Matrix (Fin m) (Fin m) (AdjoinRoot φ)).det := by
      rw [RingHom.map_det]
      rfl
    simp only [oneGram, Units.val_one, Matrix.mul_one, Matrix.det_mul, Matrix.det_transpose,
      Matrix.det_one, h2, UnitaryFieldData.bar_apply] at h1
    rw [pow_succ]
    exact h1
  have hgq : g ^ (2 * k + 1) ∈ specialBlock Q x φ := by
    have hs : g ^ (2 * k + 1) ∈ supportedBlock Q x φ := pow_mem hg _
    refine mem_specialBlock.mpr ⟨hs, ?_⟩
    have h1 : (⟨g ^ (2 * k + 1), hs⟩ : ↥(supportedBlock Q x φ)) = ⟨g, hg⟩ ^ (2 * k + 1) := rfl
    rw [h1, map_pow, blockDet_apply, ← hM, CFSG.RankThree.CentralLift.det_toLin'_basis, ← hk]
    exact hdet
  have hgg : ((g ^ 2)⁻¹) ^ k * g ^ (2 * k + 1) = g := by
    rw [inv_pow, ← pow_mul, pow_succ, ← mul_assoc, inv_mul_cancel, one_mul]
  have h := mul_mem (pow_mem (inv_mem hg2) k) (hspec hgq)
  rwa [hgg] at h

end Frame

section Block

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V} {x : V ≃ₗ[F] V} {p f m : ℕ}

@[expose] noncomputable def phiBlockEquiv {φ : F[X]} [Fact (Irreducible φ)]
    (hx : OddOrderIsometry Q p x) (hmem : φ ∈ primaryFactors x.toLinearMap)
    (hU : UnitaryFieldData 2 f (AdjoinRoot φ))
    {H : primaryComponent x.toLinearMap φ →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap φ →ₗ[AdjoinRoot φ] AdjoinRoot φ}
    (b : Module.Basis (Fin m) (AdjoinRoot φ) (primaryComponent x.toLinearMap φ))
    (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0)
    (hrange : (blockGL Q x φ).range = sesqUnitaryGroup H) :
    ↥(primeFormUnitary hU (oneGram (AdjoinRoot φ) m)) ≃* ↥(supportedBlock Q x φ) :=
  (unitaryEquivOfBasis b hU hb).trans ((MulEquiv.subgroupCongr hrange).symm.trans
    (MonoidHom.ofInjective (hx.blockGL_injective hmem)).symm)

theorem blockGL_phiBlockEquiv {φ : F[X]} [Fact (Irreducible φ)]
    (hx : OddOrderIsometry Q p x) (hmem : φ ∈ primaryFactors x.toLinearMap)
    (hU : UnitaryFieldData 2 f (AdjoinRoot φ))
    {H : primaryComponent x.toLinearMap φ →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap φ →ₗ[AdjoinRoot φ] AdjoinRoot φ}
    (b : Module.Basis (Fin m) (AdjoinRoot φ) (primaryComponent x.toLinearMap φ))
    (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0)
    (hrange : (blockGL Q x φ).range = sesqUnitaryGroup H)
    (M : ↥(primeFormUnitary hU (oneGram (AdjoinRoot φ) m))) :
    blockGL Q x φ (phiBlockEquiv hx hmem hU b hb hrange M) =
      Matrix.GeneralLinearGroup.toLin' b (M : GL (Fin m) (AdjoinRoot φ)) :=
  MonoidHom.apply_ofInjective_symm (hx.blockGL_injective hmem) _

theorem phiBlockEquiv_apply {φ : F[X]} [Fact (Irreducible φ)]
    (hx : OddOrderIsometry Q p x) (hmem : φ ∈ primaryFactors x.toLinearMap)
    (hU : UnitaryFieldData 2 f (AdjoinRoot φ))
    {H : primaryComponent x.toLinearMap φ →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap φ →ₗ[AdjoinRoot φ] AdjoinRoot φ}
    (b : Module.Basis (Fin m) (AdjoinRoot φ) (primaryComponent x.toLinearMap φ))
    (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0)
    (hrange : (blockGL Q x φ).range = sesqUnitaryGroup H)
    (M : ↥(primeFormUnitary hU (oneGram (AdjoinRoot φ) m)))
    (v : primaryComponent x.toLinearMap φ) :
    (phiBlockEquiv hx hmem hU b hb hrange M : V ≃ₗ[F] V) v =
      ((((Matrix.GeneralLinearGroup.toLin' b (M : GL (Fin m) (AdjoinRoot φ)) :
        LinearMap.GeneralLinearGroup (AdjoinRoot φ) (primaryComponent x.toLinearMap φ)) :
          primaryComponent x.toLinearMap φ →ₗ[AdjoinRoot φ] primaryComponent x.toLinearMap φ)
            v : primaryComponent x.toLinearMap φ) : V) := by
  rw [← blockGL_phiBlockEquiv hx hmem hU b hb hrange M, coe_blockGL]

theorem map_blockSU_phiBlockEquiv {φ : F[X]} [Fact (Irreducible φ)]
    (hx : OddOrderIsometry Q p x) (hmem : φ ∈ primaryFactors x.toLinearMap)
    (hU : UnitaryFieldData 2 f (AdjoinRoot φ))
    {H : primaryComponent x.toLinearMap φ →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap φ →ₗ[AdjoinRoot φ] AdjoinRoot φ}
    (b : Module.Basis (Fin m) (AdjoinRoot φ) (primaryComponent x.toLinearMap φ))
    (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0)
    (hrange : (blockGL Q x φ).range = sesqUnitaryGroup H)
    (hsupp : supportedBlock Q x φ ≤ orthDerived Q) :
    (blockSU hU m).map ((Subgroup.inclusion hsupp).comp
      (phiBlockEquiv hx hmem hU b hb hrange).toMonoidHom) =
      (specialBlock Q x φ).subgroupOf (orthDerived Q) := by
  have hdet : ∀ M, blockDet Q x φ (phiBlockEquiv hx hmem hU b hb hrange M) =
      ((M : GL (Fin m) (AdjoinRoot φ)) : Matrix (Fin m) (Fin m) (AdjoinRoot φ)).det := fun M => by
    rw [blockDet_apply, blockGL_phiBlockEquiv, CFSG.RankThree.CentralLift.det_toLin'_basis]
  ext g
  constructor
  · rintro ⟨M, hM, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr (mem_specialBlock.mpr
      ⟨(phiBlockEquiv hx hmem hU b hb hrange M).2,
        (hdet M).trans ((mem_gramSU_iff_unitary hU).mp (Subgroup.mem_subgroupOf.mp hM)).2⟩)
  · intro hg
    obtain ⟨hgs, hg1⟩ := mem_specialBlock.mp (Subgroup.mem_subgroupOf.mp hg)
    refine ⟨(phiBlockEquiv hx hmem hU b hb hrange).symm ⟨(g : V ≃ₗ[F] V), hgs⟩,
      Subgroup.mem_subgroupOf.mpr ((mem_gramSU_iff_unitary hU).mpr
        ⟨((phiBlockEquiv hx hmem hU b hb hrange).symm ⟨(g : V ≃ₗ[F] V), hgs⟩).2, ?_⟩), ?_⟩
    · rw [← hdet, MulEquiv.apply_symm_apply]
      exact hg1
    · apply Subtype.ext
      change ((phiBlockEquiv hx hmem hU b hb hrange ((phiBlockEquiv hx hmem hU b hb hrange).symm
        ⟨(g : V ≃ₗ[F] V), hgs⟩) : V ≃ₗ[F] V)) = g
      rw [MulEquiv.apply_symm_apply]

theorem apply_fixed_of_mem_supportedBlock [Finite F] [CharP F 2] {φ : F[X]}
    (hφ : φ = X ^ 2 + X + 1) {g : V ≃ₗ[F] V} (hg : g ∈ supportedBlock Q x φ) {v : V}
    (hv : v ∈ fixedSpace x) : g v = v := by
  by_cases h1 : (X - 1 : F[X]) ∈ primaryFactors x.toLinearMap
  · subst hφ
    refine apply_eq_of_mem_supportedBlock hg h1 phi_ne.symm ?_ ?_
    · have hr : reciprocalPolynomial (X ^ 2 + X + 1 : F[X]) = X ^ 2 + X + 1 :=
        CFSG.HardMathSupport.Timmesfeld.CrossChar.reciprocal_cyc3 F
      rw [hr]
      exact phi_ne.symm
    · rwa [← fixedSpace_eq_primaryComponent]
  · rw [fixedSpace_eq_bot_of_not_mem h1, Submodule.mem_bot] at hv
    rw [hv, map_zero]

end Block

section Gamma

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

variable {E : Type} [Field E] {ℓ f : ℕ} (h : UnitaryFieldData ℓ f E) {W : Type*}
  [AddCommGroup W] [Module E W] {n : ℕ} (b : Module.Basis (Fin n) E W)

theorem toLin'_conj_semGamma {τ : E ≃+* E} {T : W →+ W}
    (hT : ∀ (c : E) (v : W), T (c • v) = τ c • T v)
    (hM : ((semMat b T).map h.bar)ᵀ * semMat b T = 1) (g : primeFormUnitary h (oneGram E n))
    (v : W) :
    ((Matrix.GeneralLinearGroup.toLin' b (((semGamma b h hM τ * SemidirectProduct.inl g *
      (semGamma b h hM τ)⁻¹).left : primeFormUnitary h (oneGram E n)) : GL (Fin n) E) :
        LinearMap.GeneralLinearGroup E W) : W →ₗ[E] W) (T v) =
      T (((Matrix.GeneralLinearGroup.toLin' b (g : GL (Fin n) E) :
        LinearMap.GeneralLinearGroup E W) : W →ₗ[E] W) v) := by
  apply b.equivFun.injective
  have hA : ∀ w : Fin n → E, ((((semU b h hM)⁻¹ : primeFormUnitary h (oneGram E n)) :
      GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ (semMat b T *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, ← coe_semU b h hM, Subgroup.coe_inv, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [CFSG.RankThree.CentralLift.equivFun_toLin'_basis_apply,
    repr_semilin b (τ := (τ : E →+* E)) hT, repr_semilin b (τ := (τ : E →+* E)) hT,
    CFSG.RankThree.CentralLift.equivFun_toLin'_basis_apply, uni_conj_inl_left,
    show (semGamma b h hM τ).left = semU b h hM from rfl,
    show (semGamma b h hM τ).right = τ from rfl, Subgroup.coe_mul, Subgroup.coe_mul,
    Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA,
    coe_primeFormFieldU, CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.coe_glAut, coe_semU]
  congr 1
  funext i
  exact (RingHom.map_mulVec (τ : E →+* E) _ _ i).symm

end Gamma

section Core

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.HardMathSupport.Dickson.Bal207.FirstClaim
open scoped Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {x : V ≃ₗ[F] V} {f m : ℕ}

theorem phiBlockEquiv_conj_semilin {φ : F[X]} [Fact (Irreducible φ)] (hφ : φ = X ^ 2 + X + 1)
    (hx : OddOrderIsometry Q 3 x) (hpq : 3 ∣ Nat.card F + 1)
    (hmem : φ ∈ primaryFactors x.toLinearMap) (hU : UnitaryFieldData 2 f (AdjoinRoot φ))
    {H : primaryComponent x.toLinearMap φ →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap φ →ₗ[AdjoinRoot φ] AdjoinRoot φ}
    (b : Module.Basis (Fin m) (AdjoinRoot φ) (primaryComponent x.toLinearMap φ))
    (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0)
    (hrange : (blockGL Q x φ).range = sesqUnitaryGroup H)
    {σ : F ≃+* F} {S : V ≃+ V} (hS : ∀ (c : F) (v : V), S (c • v) = σ c • S v)
    (hSx : ∀ v, S (x v) = x (S v)) (hσ : φ.map (σ : F →+* F) = φ)
    (hM : ((semMat b (semilinRestrict hS hSx hσ)).map hU.bar)ᵀ *
      semMat b (semilinRestrict hS hSx hσ) = 1)
    (M : ↥(primeFormUnitary hU (oneGram (AdjoinRoot φ) m))) (v : V) :
    (phiBlockEquiv hx hmem hU b hb hrange ((semGamma b hU hM (extAut φ σ hσ) *
      SemidirectProduct.inl M * (semGamma b hU hM (extAut φ σ hσ))⁻¹).left) : V ≃ₗ[F] V)
        (S v) = S ((phiBlockEquiv hx hmem hU b hb hrange M : V ≃ₗ[F] V) v) := by
  classical
  obtain ⟨u₁, u₂, hu₁, hu₂, rfl⟩ :=
    Submodule.codisjoint_iff_exists_add_eq.mp hx.fixed_others.1.codisjoint v
  have hoth : othersSpace x.toLinearMap (X - 1) = primaryComponent x.toLinearMap φ := by
    rw [hφ]
    exact othersSpace_eq hx hpq (hφ ▸ hmem)
  rw [hoth] at hu₂
  obtain ⟨w, rfl⟩ : ∃ w : primaryComponent x.toLinearMap φ, (w : V) = u₂ := ⟨⟨u₂, hu₂⟩, rfl⟩
  have hSu₁ : S u₁ ∈ fixedSpace x := by
    rw [mem_fixedSpace] at hu₁ ⊢
    rw [← hSx, hu₁]
  have h3 := toLin'_conj_semGamma hU b (τ := extAut φ σ hσ)
    (T := semilinRestrict hS hSx hσ) (fun c v => semilinRestrict_smul hS hSx hσ c v) hM M w
  have h3' :
      ((Matrix.GeneralLinearGroup.toLin' b (((semGamma b hU hM (extAut φ σ hσ) *
        SemidirectProduct.inl M * (semGamma b hU hM (extAut φ σ hσ))⁻¹).left :
          primeFormUnitary hU (oneGram (AdjoinRoot φ) m)) : GL (Fin m) (AdjoinRoot φ)) :
        LinearMap.GeneralLinearGroup (AdjoinRoot φ)
          (primaryComponent x.toLinearMap φ)) : primaryComponent x.toLinearMap φ →ₗ[AdjoinRoot φ]
            primaryComponent x.toLinearMap φ) (semilinRestrict hS hSx hσ w) =
      semilinRestrict hS hSx hσ
        (((Matrix.GeneralLinearGroup.toLin' b (M : GL (Fin m) (AdjoinRoot φ)) :
          LinearMap.GeneralLinearGroup (AdjoinRoot φ)
            (primaryComponent x.toLinearMap φ)) : primaryComponent x.toLinearMap φ →ₗ[AdjoinRoot φ]
              primaryComponent x.toLinearMap φ) w) :=
    h3
  simp only [map_add]
  rw [apply_fixed_of_mem_supportedBlock hφ (phiBlockEquiv hx hmem hU b hb hrange _).2 hSu₁,
    apply_fixed_of_mem_supportedBlock hφ (phiBlockEquiv hx hmem hU b hb hrange _).2 hu₁,
    ← coe_semilinRestrict hS hSx hσ w, phiBlockEquiv_apply, phiBlockEquiv_apply, h3',
    coe_semilinRestrict]

theorem exists_phiBlockData_of_semilin [Nontrivial V] {G : Type} [Group G] {K B J : Subgroup G}
    (hB : IsSCp 3 ⊤ B) (hBK : B ≤ Subgroup.normalizer (K : Set G)) (hFf : Nat.card F = 2 ^ f)
    (hf : f = 1 ∨ f = 3) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule F V, Module.finrank F U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ProjOrthDerived Q) (hx : OddOrderIsometry Q 3 x)
    (hmem : (X ^ 2 + X + 1 : F[X]) ∈ primaryFactors x.toLinearMap)
    (hm : primaryMultiplicity x.toLinearMap (X ^ 2 + X + 1) = m) (hm3 : 3 ≤ m)
    (hmq : ¬(m = 3 ∧ 2 ^ f = 2))
    (hJx : (J.comap K.subtype).map (uniMap e) = componentImage Q x (X ^ 2 + X + 1))
    (S : ↥B → V ≃+ V) (σ : ↥B →* (F ≃+* F)) (hSsl : ∀ b c v, S b (c • v) = σ b c • S b v)
    (hSmul : ∀ b b' v, S (b * b') v = S b (S b' v)) (hSQ : ∀ b v, Q (S b v) = σ b (Q v))
    (hSx : ∀ b v, S b (x v) = x (S b v))
    (hSact : ∀ b (g g' : orthDerived Q), (∀ v, (g' : V ≃ₗ[F] V) v =
      S b ((g : V ≃ₗ[F] V) ((S b).symm v))) → uniAut e ⟨b, hBK b.2⟩ (piOrth Q g) = piOrth Q g') :
    ∃ (E : Type) (_ : Field E) (h : UnitaryFieldData 2 f E)
      (ι : ↥(primeFormUnitary h (oneGram E m)) →* ProjOrthDerived Q), Function.Injective ι ∧
      (J.comap K.subtype).map (uniMap e) = (blockSU h m).map ι ∧
      ∃ xb : ↥B → blockGamma h m,
        (∀ (b : ↥B) (g : ↥(primeFormUnitary h (oneGram E m))),
          uniAut e ⟨b, hBK b.2⟩ (ι g) = ι ((xb b * SemidirectProduct.inl g * (xb b)⁻¹).left)) ∧
        ∃ P : ↥(primeFormUnitary h (oneGram E m)), ∀ b : ↥B,
          ∃ D : ↥(primeFormUnitary h (oneGram E m)),
            ((D : GL (Fin m) E) : Matrix (Fin m) (Fin m) E).IsDiag ∧ ∃ φ : E ≃+* E,
              (∀ c : E, c ^ 3 = 1 → φ c = c) ∧
                (SemidirectProduct.inl P)⁻¹ * xb b * SemidirectProduct.inl P =
                  SemidirectProduct.inl D * SemidirectProduct.inr φ := by
  classical
  obtain ⟨φ, hφ⟩ : ∃ φ : F[X], φ = X ^ 2 + X + 1 := ⟨_, rfl⟩
  rw [← hφ] at hmem hm hJx
  haveI : Fact (Irreducible φ) := ⟨irreducible_of_mem_primaryFactors hmem⟩
  obtain ⟨hU, H, b, htr, hb, hrange, hspec⟩ :=
    exists_phiFrame hFf (by omega) hx hφ hmem hm hm3 hmq
  have hsupp := supportedBlock_le_orthDerived hQ hT hU b hb hrange hspec
  have hpq : 3 ∣ Nat.card F + 1 := by
    rw [hFf]
    rcases hf with rfl | rfl <;> norm_num
  have hσ : ∀ β : ↥B, φ.map (σ β : F →+* F) = φ := fun β => phi_map_ringEquiv hφ (σ β)
  have hM : ∀ β, ((semMat b (semilinRestrict (hSsl β) (hSx β) (hσ β))).map hU.bar)ᵀ *
      semMat b (semilinRestrict (hSsl β) (hSx β) (hσ β)) = 1 := fun β =>
    semMat_unitary b hU hb fun i j => by
      rw [herm_semilinRestrict (hSsl β) (hSx β) (hSQ β) hφ (hσ β) htr, hb]
      split_ifs <;> simp only [map_one, map_zero]
  have hTmul : ∀ β β' v, semilinRestrict (hSsl (β * β')) (hSx (β * β')) (hσ (β * β')) v =
      semilinRestrict (hSsl β) (hSx β) (hσ β) (semilinRestrict (hSsl β') (hSx β') (hσ β') v) :=
    fun β β' v => Subtype.ext (hSmul β β' v)
  have hext : ∀ (τ τ' : F ≃+* F) (hτ : φ.map (τ : F →+* F) = φ)
      (hτ' : φ.map (τ' : F →+* F) = φ), τ = τ' → extAut φ τ hτ = extAut φ τ' hτ' := by
    rintro τ _ hτ hτ' rfl
    rfl
  obtain ⟨xb, hxb⟩ : ∃ xb : ↥B →* blockGamma hU m,
      ∀ β, xb β = semGamma b hU (hM β) (extAut φ (σ β) (hσ β)) := by
    refine ⟨MonoidHom.mk' (fun β => semGamma b hU (hM β) (extAut φ (σ β) (hσ β)))
      fun β β' => ?_, fun β => rfl⟩
    show semGamma b hU (hM (β * β')) (extAut φ (σ (β * β')) (hσ (β * β'))) =
      semGamma b hU (hM β) (extAut φ (σ β) (hσ β)) *
        semGamma b hU (hM β') (extAut φ (σ β') (hσ β'))
    rw [(hext _ _ _ (phi_map_ringEquiv hφ _) (map_mul σ β β')).trans
      (extAut_mul (hσ β) (hσ β') _)]
    exact semGamma_mul b hU
      (T := (semilinRestrict (hSsl β) (hSx β) (hσ β)).toAddMonoidHom)
      (fun c v => semilinRestrict_smul (hSsl β) (hSx β) (hσ β) c v)
      (hTmul β β') (hM β) (hM β') (hM (β * β'))
  obtain ⟨ι, hιdef⟩ : ∃ ι, ι = (piOrth Q).comp ((Subgroup.inclusion hsupp).comp
      (phiBlockEquiv hx hmem hU b hb hrange).toMonoidHom) := ⟨_, rfl⟩
  have hιapp : ∀ M, ι M = piOrth Q (Subgroup.inclusion hsupp
      (phiBlockEquiv hx hmem hU b hb hrange M)) := fun M => by rw [hιdef]; rfl
  have hι : Function.Injective ι := by
    rw [hιdef]
    exact (piOrth_injective hQ).comp ((Subgroup.inclusion_injective hsupp).comp
      (phiBlockEquiv hx hmem hU b hb hrange).injective)
  have hJι : (J.comap K.subtype).map (uniMap e) = (blockSU hU m).map ι := by
    rw [hJx, hιdef, ← Subgroup.map_map, map_blockSU_phiBlockEquiv hx hmem hU b hb hrange hsupp]
    rfl
  have hact : ∀ (β : ↥B) (M : ↥(primeFormUnitary hU (oneGram (AdjoinRoot φ) m))),
      uniAut e ⟨β, hBK β.2⟩ (ι M) = ι ((xb β * SemidirectProduct.inl M * (xb β)⁻¹).left) := by
    intro β M
    rw [hιapp, hιapp, hxb]
    refine hSact β _ _ fun v => ?_
    obtain ⟨u, rfl⟩ := (S β).surjective v
    rw [Subgroup.coe_inclusion, Subgroup.coe_inclusion, AddEquiv.symm_apply_apply]
    exact phiBlockEquiv_conj_semilin hφ hx hpq hmem hU b hb hrange (hSsl β) (hSx β) (hσ β)
      (hM β) M u
  have hc : ∀ u ∈ Set.range xb, ∀ w ∈ Set.range xb, u * w = w * u := by
    rintro _ ⟨c, rfl⟩ _ ⟨c', rfl⟩
    rw [← map_mul, ← map_mul, hB.2.1.1.is_comm.comm c c']
  have hcube : ∀ u ∈ Set.range xb, u ^ 3 = 1 := by
    rintro _ ⟨c, rfl⟩
    have hc3 : c ^ 3 = 1 := Subtype.ext (hB.2.1.2 c c.2)
    rw [← map_pow, hc3, map_one]
  have h3 : 3 ∣ 2 ^ f + 1 := by rcases hf with rfl | rfl <;> norm_num
  obtain ⟨P, τ₀, hτ₀, hP⟩ := uni_normal_form_mat (n := m) hU h3 (Set.range xb) hc hcube
  refine ⟨AdjoinRoot φ, inferInstance, hU, ι, hι, hJι, xb, hact, P, fun c => ?_⟩
  obtain ⟨D, hD, -, k, hk⟩ := hP (xb c) ⟨c, rfl⟩
  have hτk : (τ₀ ^ k) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hτ₀, one_pow]
  exact ⟨D, hD, τ₀ ^ k, fun z hz => uni_fix_cube_root hτk hz, hk⟩

end Core

section Frames

open CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

theorem blockFrame_of_mem_E {F : Type} [Field F] [Finite F] [CharP F 2] {d : ℕ}
    {Q : QuadraticForm F (Fin d → F)} {G : Type} [Group G] {K B J : Subgroup G}
    (hB : IsSCp 3 ⊤ B) (hBK : B ≤ Subgroup.normalizer (K : Set G))
    (hF : Nat.card F = 2 ∨ Nat.card F = 8) (hd : 0 < d) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule F (Fin d → F), Module.finrank F U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hker : ∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g = 1 →
      g.val.right = 1 ∧ ∃ a : Fˣ, g.val.left = Matrix.GeneralLinearGroup.scalar (Fin d) a)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ProjOrthDerived Q)
    (hE : ∀ b : ↥B, MulAut.congr (coordBridge Q hd).symm (uniAut e ⟨b, hBK b.2⟩) ∈
      matrixProjectiveImage Q)
    (x : orthDerived Q) (hx3 : orderOf x = 3)
    (hmem : (X ^ 2 + X + 1 : F[X]) ∈
      primaryFactors (x : (Fin d → F) ≃ₗ[F] (Fin d → F)).toLinearMap)
    (hm3 : 3 ≤ primaryMultiplicity (x : (Fin d → F) ≃ₗ[F] (Fin d → F)).toLinearMap
      (X ^ 2 + X + 1))
    (hmq : ¬(primaryMultiplicity (x : (Fin d → F) ≃ₗ[F] (Fin d → F)).toLinearMap
      (X ^ 2 + X + 1) = 3 ∧ Nat.card F = 2))
    (hJx : (J.comap K.subtype).map (uniMap e) =
      componentImage Q (x : (Fin d → F) ≃ₗ[F] (Fin d → F)) (X ^ 2 + X + 1))
    (hBx : ∀ b : ↥B, uniAut e ⟨b, hBK b.2⟩ (piOrth Q x) = piOrth Q x) :
    BlockFrame e B J hBK := by
  obtain ⟨f, hFf, hf⟩ : ∃ f, Nat.card F = 2 ^ f ∧ (f = 1 ∨ f = 3) := by
    rcases hF with hF | hF
    · exact ⟨1, by rw [hF]; norm_num, Or.inl rfl⟩
    · exact ⟨3, by rw [hF]; norm_num, Or.inr rfl⟩
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hpl : 3 ≠ ringChar F := by
    rw [ringChar.eq F 2]
    norm_num
  obtain ⟨S, σ, hSsl, hSmul, hSQ, hSx, hSact⟩ := exists_semilin_of_mem_E hBK hd hQ hker e hE x hBx
  have hmq' : ¬(primaryMultiplicity (x : (Fin d → F) ≃ₗ[F] (Fin d → F)).toLinearMap
      (X ^ 2 + X + 1) = 3 ∧ 2 ^ f = 2) := by
    rwa [← hFf]
  obtain ⟨E, _, h, ι, hι, hJι, xb, hx, P, hP⟩ := exists_phiBlockData_of_semilin hB hBK hFf hf hQ
    hT e (oddOrderIsometry_of_orthDerived Nat.prime_three hpl hQ x hx3) hmem rfl hm3 hmq' hJx S σ
    hSsl hSmul hSQ hSx hSact
  exact ⟨E, inferInstance, f, h, _, hf, hm3, hmq', ι, hι, hJι, xb, hx, P, hP⟩

theorem su38Toral_of_mem_E {F : Type} [Field F] [Finite F] [CharP F 2] {d : ℕ}
    {Q : QuadraticForm F (Fin d → F)} {G : Type} [Group G] {K B J : Subgroup G} [Finite G]
    (hB : IsSCp 3 ⊤ B) (hBK : B ≤ Subgroup.normalizer (K : Set G))
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center ↥K))) (hF8 : Nat.card F = 8) (hd : 0 < d)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule F (Fin d → F), Module.finrank F U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hker : ∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g = 1 →
      g.val.right = 1 ∧ ∃ a : Fˣ, g.val.left = Matrix.GeneralLinearGroup.scalar (Fin d) a)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ProjOrthDerived Q)
    (hE : ∀ b : ↥B, MulAut.congr (coordBridge Q hd).symm (uniAut e ⟨b, hBK b.2⟩) ∈
      matrixProjectiveImage Q)
    (hJ : CFSG.Open.IsQuasisimple ↥J) (hJK : J ≤ K) (hBJ : B ≤ Subgroup.normalizer (J : Set G))
    (x : orthDerived Q) (hx3 : orderOf x = 3)
    (hmem : (X ^ 2 + X + 1 : F[X]) ∈
      primaryFactors (x : (Fin d → F) ≃ₗ[F] (Fin d → F)).toLinearMap)
    (hm3 : primaryMultiplicity (x : (Fin d → F) ≃ₗ[F] (Fin d → F)).toLinearMap
      (X ^ 2 + X + 1) = 3)
    (hJx : (J.comap K.subtype).map (uniMap e) =
      componentImage Q (x : (Fin d → F) ≃ₗ[F] (Fin d → F)) (X ^ 2 + X + 1))
    (hBx : ∀ b : ↥B, uniAut e ⟨b, hBK b.2⟩ (piOrth Q x) = piOrth Q x) :
    SU38Toral B J := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hpl : 3 ≠ ringChar F := by
    rw [ringChar.eq F 2]
    norm_num
  obtain ⟨S, σ, hSsl, hSmul, hSQ, hSx, hSact⟩ := exists_semilin_of_mem_E hBK hd hQ hker e hE x hBx
  obtain ⟨E, _, h, ι, hι, hJι, xb, hx, P, hP⟩ := exists_phiBlockData_of_semilin (f := 3) hB hBK
    (by rw [hF8]; norm_num) (Or.inr rfl) hQ hT e
    (oddOrderIsometry_of_orthDerived Nat.prime_three hpl hQ x hx3) hmem hm3 le_rfl
    (by norm_num) hJx S σ hSsl hSmul hSQ hSx hSact
  exact su38Toral_of_block hB hBK hZ e hJ hJK hBJ h rfl (Or.inr rfl) (by norm_num) hι hJι xb hx
    P hP

end Frames

end CFSG.HardMathSupport.Dickson.Bal207.OrthFix

end
