module

import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq2
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeKillAux2
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartOne.KC.OrthogonalSelfDualBlock
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryField

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Polynomial Module Matrix CFSG.Open

private abbrev FT (K : Type) [Field K] (p : ℕ) (ζ : K) : Type := AdjoinRoot (X ^ p - C ζ)

private theorem matrixToLin'_scalar_apply {K : Type} [Field K] {N : ℕ} (u : Kˣ)
    (v : Fin N → K) :
    Matrix.toLin' (((Matrix.GeneralLinearGroup.scalar (Fin N) u : GL (Fin N) K) :
      Matrix (Fin N) (Fin N) K)) v = u • v := by
  rw [Matrix.toLin'_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  have hmv : (Matrix.diagonal (fun _ => (u : K)) *ᵥ v) = (u : K) • v := by
    funext i
    rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  rw [hmv, Units.smul_def]

private theorem toLin'_scalar_apply {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (μ : Kˣ) (v : V) :
    ((Matrix.GeneralLinearGroup.toLin' b) (Matrix.GeneralLinearGroup.scalar ι μ)).toLinearEquiv v =
      μ • v := by
  rw [Matrix.GeneralLinearGroup.toLin'_apply, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply]
  have hmv : (Matrix.diagonal (fun _ => (μ : K)) *ᵥ (⇑(b.repr v))) =
      (μ : K) • ⇑(b.repr v) := by
    funext i
    rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  rw [hmv, map_smul, Fintype.linearCombination_apply, b.sum_repr, Units.smul_def]

theorem card_le_pow_centralizer_of_scalar_pow {K : Type} [Field K] [Finite K] {p N : ℕ}
    (hp : p.Prime) (hN : 0 < N) {D : GL (Fin N) K} {lam : Kˣ}
    (hDp : D ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) lam)
    (hlam : ∀ c : Kˣ, c ^ p ≠ lam) (hpK : (p : K) ≠ 0) (hp2 : p ≠ 2)
    (E : Subgroup (StatedProj (Subgroup.centralizer ({D} : Set (GL (Fin N) K)))))
    (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ (N / p) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hζ : ∀ b : K, b ^ p ≠ (lam : K) := by
    intro b hb
    by_cases hb0 : b = 0
    · subst hb0
      rw [zero_pow hp.pos.ne'] at hb
      exact lam.ne_zero hb.symm
    · exact hlam (Units.mk0 b hb0) (Units.ext (by rwa [Units.val_pow_eq_pow_val, Units.val_mk0]))
  haveI : Fact (Irreducible (X ^ p - C (lam : K) : K[X])) :=
    ⟨X_pow_sub_C_irreducible_of_prime hp hζ⟩
  let x : Module.End K (Fin N → K) :=
    Matrix.toLin' ((D : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
  have hxl : aeval x (X ^ p - C (lam : K) : K[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, ← Matrix.toLin'_pow, sub_eq_zero]
    have hmat : ((D : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) ^ p =
        Matrix.scalar (Fin N) (lam : K) := by
      rw [← Units.val_pow_eq_pow_val, hDp, Matrix.GeneralLinearGroup.coe_scalar]
    rw [hmat]
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.scalar_apply]
    have hmv : (Matrix.diagonal (fun _ => (lam : K)) *ᵥ v) = (lam : K) • v := by
      funext i
      rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    rw [hmv, Algebra.smul_def]
    rfl
  let φ : FT K p (lam : K) →+* Module.End K (Fin N → K) :=
    Ideal.Quotient.lift (Ideal.span {(X ^ p - C (lam : K) : K[X])})
      (aeval x : K[X] →ₐ[K] Module.End K (Fin N → K)).toRingHom
      (fun a ha => by
        obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.1 ha
        change aeval x ((X ^ p - C (lam : K)) * g) = 0
        rw [map_mul, hxl, zero_mul])
  have hφmk : ∀ g : K[X], φ (AdjoinRoot.mk (X ^ p - C (lam : K)) g) = aeval x g := fun g => rfl
  letI : Module (FT K p (lam : K)) (Fin N → K) := Module.compHom (Fin N → K) φ
  have hsmul : ∀ (e : FT K p (lam : K)) (v : Fin N → K), e • v = φ e v := fun e v => rfl
  haveI : IsScalarTower K (FT K p (lam : K)) (Fin N → K) := by
    refine IsScalarTower.of_algebraMap_smul fun r v => ?_
    rw [hsmul, AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, hφmk, aeval_C]
    rfl
  haveI : Module.Finite K (Fin N → K) := inferInstance
  haveI : Module.Finite (FT K p (lam : K)) (Fin N → K) :=
    Module.Finite.of_restrictScalars_finite K _ _
  haveI : Module.Free (FT K p (lam : K)) (Fin N → K) := Module.Free.of_divisionRing _ _
  have hfinV : Module.finrank K (Fin N → K) = N := Module.finrank_fin_fun K
  have hf0 : (X ^ p - C (lam : K) : K[X]) ≠ 0 :=
    (monic_X_pow_sub_C (lam : K) hp.ne_zero).ne_zero
  have hfinF : Module.finrank K (FT K p (lam : K)) = p := by
    rw [(AdjoinRoot.powerBasis hf0).finrank]
    simp [AdjoinRoot.powerBasis, natDegree_X_pow_sub_C]
  have htower : Module.finrank K (FT K p (lam : K)) *
      Module.finrank (FT K p (lam : K)) (Fin N → K) = Module.finrank K (Fin N → K) :=
    Module.finrank_mul_finrank K _ _
  have hNp : p * Module.finrank (FT K p (lam : K)) (Fin N → K) = N := by
    calc p * Module.finrank (FT K p (lam : K)) (Fin N → K)
        = Module.finrank K (FT K p (lam : K)) *
            Module.finrank (FT K p (lam : K)) (Fin N → K) := by rw [hfinF]
      _ = Module.finrank K (Fin N → K) := htower
      _ = N := hfinV
  have hrpos : 0 < Module.finrank (FT K p (lam : K)) (Fin N → K) := by
    rcases Nat.eq_zero_or_pos (Module.finrank (FT K p (lam : K)) (Fin N → K)) with h0 | h
    · rw [h0, mul_zero] at hNp
      omega
    · exact h
  have hNdiv : N / p = Module.finrank (FT K p (lam : K)) (Fin N → K) := by
    have h := Nat.mul_div_right (Module.finrank (FT K p (lam : K)) (Fin N → K)) hp.pos
    rwa [hNp] at h
  let C : Subgroup (GL (Fin N) K) := Subgroup.centralizer ({D} : Set (GL (Fin N) K))
  have hEnd_mul (a b : C) :
      Matrix.toLin' (((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) *
        Matrix.toLin' (((b : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) =
      Matrix.toLin' ((((a * b : C) : GL (Fin N) K)) : Matrix (Fin N) (Fin N) K) := by
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul]
    rfl
  have hEnd_one :
      Matrix.toLin' ((((1 : C) : GL (Fin N) K)) : Matrix (Fin N) (Fin N) K) =
        LinearMap.id := by
    rw [show ((((1 : C) : GL (Fin N) K)) : Matrix (Fin N) (Fin N) K) = 1 by simp]
    rw [Matrix.toLin'_one]
  have hcommD (h : C) :
      Matrix.toLin' (((h : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) * x =
        x * Matrix.toLin' (((h : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) := by
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp h.2
    have h2 := congrArg (fun g : Matrix (Fin N) (Fin N) K => Matrix.toLin' g)
      (congrArg (fun g : GL (Fin N) K => (g : Matrix (Fin N) (Fin N) K)) h1)
    rw [Units.val_mul, Units.val_mul, Matrix.toLin'_mul, Matrix.toLin'_mul] at h2
    exact h2
  have hxcent (h : C) :
      x ∈ Subalgebra.centralizer K
        ({Matrix.toLin' (((h : GL (Fin N) K) : Matrix (Fin N) (Fin N) K))} :
          Set (Module.End K (Fin N → K))) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hcommD h
  have hcomm_aeval (h : C) (g : K[X]) :
      Matrix.toLin' (((h : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) * aeval x g =
        aeval x g * Matrix.toLin' (((h : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) := by
    have hadj : Algebra.adjoin K ({x} : Set (Module.End K (Fin N → K))) ≤
        Subalgebra.centralizer K
          ({Matrix.toLin' (((h : GL (Fin N) K) : Matrix (Fin N) (Fin N) K))} :
            Set (Module.End K (Fin N → K))) :=
      Algebra.adjoin_le (by rw [Set.singleton_subset_iff]; exact hxcent h)
    have hmem : aeval x g ∈ Algebra.adjoin K ({x} : Set (Module.End K (Fin N → K))) := by
      rw [Algebra.adjoin_singleton_eq_range_aeval]
      exact ⟨g, rfl⟩
    exact (Subalgebra.mem_centralizer_iff K).mp (hadj hmem) _ (Set.mem_singleton _)
  have hcommF (h : C) (f : FT K p (lam : K)) :
      Matrix.toLin' (((h : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) * φ f =
        φ f * Matrix.toLin' (((h : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) := by
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective f
    exact hcomm_aeval h g
  let linF (h : C) : (Fin N → K) →ₗ[FT K p (lam : K)] (Fin N → K) :=
    { toFun := fun v => Matrix.toLin' (((h : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) v
      map_add' := fun u v => (Matrix.toLin' _).map_add u v
      map_smul' := fun c v => by
        have h := congrArg (fun m : Module.End K (Fin N → K) => m v) (hcommF h c)
        rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.comp_apply,
          LinearMap.comp_apply] at h
        simpa only [hsmul, RingHom.id_apply] using h }
  have hlinF_apply (h : C) (v : Fin N → K) :
      linF h v =
        Matrix.toLin' (((h : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) v := rfl
  have hlinF_mul (a b : C) : linF a * linF b = linF (a * b) := by
    refine LinearMap.ext fun v => ?_
    rw [Module.End.mul_eq_comp, LinearMap.comp_apply, hlinF_apply, hlinF_apply, hlinF_apply]
    change (Matrix.toLin' (((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) *
      Matrix.toLin' (((b : GL (Fin N) K) : Matrix (Fin N) (Fin N) K))) v = _
    rw [hEnd_mul]
  have hlinF_one : linF (1 : C) = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    rw [hlinF_apply]
    show Matrix.toLin' ((((1 : C) : GL (Fin N) K)) : Matrix (Fin N) (Fin N) K) v = v
    rw [show ((((1 : C) : GL (Fin N) K)) : Matrix (Fin N) (Fin N) K) = 1 by simp]
    rw [Matrix.toLin'_one]
    rfl
  have hleft (h : C) : (linF h) ∘ₗ (linF h⁻¹) = LinearMap.id := by
    rw [← Module.End.mul_eq_comp, hlinF_mul, mul_inv_cancel, hlinF_one]
  have hright (h : C) : (linF h⁻¹) ∘ₗ (linF h) = LinearMap.id := by
    rw [← Module.End.mul_eq_comp, hlinF_mul, inv_mul_cancel, hlinF_one]
  let eF (h : C) : (Fin N → K) ≃ₗ[FT K p (lam : K)] (Fin N → K) :=
    LinearEquiv.ofLinearMap (linF h) (linF h⁻¹) (hleft h) (hright h)
  let ψ₀ : C →* ((Fin N → K) ≃ₗ[FT K p (lam : K)] (Fin N → K)) :=
    { toFun := eF
      map_one' := by
        refine LinearEquiv.ext fun v => ?_
        rw [LinearEquiv.coe_ofLinearMap, hlinF_one, LinearEquiv.coe_one]
        rfl
      map_mul' := fun a b => by
        refine LinearEquiv.ext fun v => ?_
        rw [LinearEquiv.mul_apply, LinearEquiv.coe_ofLinearMap,
          LinearEquiv.coe_ofLinearMap, LinearEquiv.coe_ofLinearMap, ← hlinF_mul]
        rw [Module.End.mul_eq_comp, LinearMap.comp_apply] }
  let bF : Module.Basis (Fin (Module.finrank (FT K p (lam : K)) (Fin N → K)))
      (FT K p (lam : K)) (Fin N → K) := Module.finBasis _ _
  let ψ : C →* GL (Fin (Module.finrank (FT K p (lam : K)) (Fin N → K))) (FT K p (lam : K)) :=
    (Matrix.GeneralLinearGroup.toLin' bF).symm.toMonoidHom.comp
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv (FT K p (lam : K))
        (Fin N → K)).symm.toMonoidHom.comp ψ₀)
  have eF_apply (g : C) (v : Fin N → K) : eF g v = linF g v := by
    change (LinearEquiv.ofLinearMap (linF g) (linF g⁻¹) (hleft g) (hright g)) v = linF g v
    rw [LinearEquiv.coe_ofLinearMap]
  have hψ_apply (g : C) : (LinearMap.GeneralLinearGroup.generalLinearEquiv
      (FT K p (lam : K)) (Fin N → K))
        ((Matrix.GeneralLinearGroup.toLin' bF) (ψ g)) = ψ₀ g := by
    dsimp only [ψ, MonoidHom.comp_apply]
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  have hψ_inj : Function.Injective ψ := by
    intro a b hab
    have h1 : ψ₀ a = ψ₀ b := by
      have h := congrArg (fun g => (LinearMap.GeneralLinearGroup.generalLinearEquiv
        (FT K p (lam : K)) (Fin N → K)) ((Matrix.GeneralLinearGroup.toLin' bF) g)) hab
      rw [hψ_apply a, hψ_apply b] at h
      exact h
    have h2 : linF a = linF b := by
      refine LinearMap.ext fun v => ?_
      have h := congrArg (fun e : (Fin N → K) ≃ₗ[FT K p (lam : K)] (Fin N → K) => e v) h1
      have hcoe : ∀ (g : C) (w : Fin N → K), eF g w = linF g w := by
        intro g w
        dsimp only [eF]
        rw [LinearEquiv.coe_ofLinearMap]
      change eF a v = eF b v at h
      rw [hcoe, hcoe] at h
      exact h
    have h3 : Matrix.toLin' (((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) =
        Matrix.toLin' (((b : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) := by
      refine LinearMap.ext fun v => ?_
      have h := congrArg (fun m : (Fin N → K) →ₗ[FT K p (lam : K)] (Fin N → K) => m v) h2
      rwa [hlinF_apply, hlinF_apply] at h
    exact Subtype.ext (Units.ext (Matrix.toLin'.injective h3))
  have hgen_scalar_apply (μ : (FT K p (lam : K))ˣ) (v : Fin N → K) :
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv (FT K p (lam : K)) (Fin N → K))
        ((Matrix.GeneralLinearGroup.toLin' bF)
          (Matrix.GeneralLinearGroup.scalar
            (Fin (Module.finrank (FT K p (lam : K)) (Fin N → K))) μ))) v = μ • v := by
    exact toLin'_scalar_apply bF μ v
  have halg_inj : Function.Injective (algebraMap K (FT K p (lam : K))) :=
    (algebraMap K (FT K p (lam : K))).injective
  let Kunit : Kˣ →* (FT K p (lam : K))ˣ :=
    { toFun := fun u => Units.mk0 (algebraMap K (FT K p (lam : K)) (u : K)) (by
        intro h
        exact u.ne_zero (halg_inj (by simpa using h)))
      map_one' := by
        ext
        simp
      map_mul' := fun a b => by
        ext
        simp [map_mul] }
  have hKunit_val (u : Kˣ) : ((Kunit u : (FT K p (lam : K))ˣ) : FT K p (lam : K)) =
      algebraMap K (FT K p (lam : K)) (u : K) := by
    dsimp only [Kunit]
    rfl
  have hψ_scalar (c : C) {u : Kˣ}
      (hu : (c : GL (Fin N) K) = Matrix.GeneralLinearGroup.scalar (Fin N) u) :
      ψ c = Matrix.GeneralLinearGroup.scalar
        (Fin (Module.finrank (FT K p (lam : K)) (Fin N → K)))
        (Kunit u) := by
    apply (Matrix.GeneralLinearGroup.toLin' bF).injective
    apply (LinearMap.GeneralLinearGroup.generalLinearEquiv (FT K p (lam : K)) (Fin N → K)).injective
    refine LinearEquiv.ext fun v => ?_
    rw [hψ_apply]
    change eF c v = _
    have hum : (((c : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) =
        (((Matrix.GeneralLinearGroup.scalar (Fin N) u : GL (Fin N) K) :
          Matrix (Fin N) (Fin N) K)) := congrArg (fun g : GL (Fin N) K =>
            (g : Matrix (Fin N) (Fin N) K)) hu
    rw [eF_apply, hlinF_apply, hum, matrixToLin'_scalar_apply, hgen_scalar_apply]
    simp only [Units.smul_def]
    change (u : K) • v = (algebraMap K (FT K p (lam : K)) (u : K)) • v
    rw [IsScalarTower.algebraMap_smul (FT K p (lam : K)) (u : K) v]
  have hψ_scalar_mem (c : C) {u : Kˣ}
      (h : ψ c = Matrix.GeneralLinearGroup.scalar
        (Fin (Module.finrank (FT K p (lam : K)) (Fin N → K)))
        (Kunit u)) :
      (c : GL (Fin N) K) ∈ StatedScalars (Fin N) K := by
    have hfun : ∀ v : Fin N → K,
        Matrix.toLin' (((c : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) v = (u : K) • v := by
      intro v
      have h1 := congrArg (fun e : (Fin N → K) ≃ₗ[FT K p (lam : K)] (Fin N → K) => e v)
        (hψ_apply c)
      rw [h] at h1
      rw [hgen_scalar_apply] at h1
      simp only [Units.smul_def] at h1
      change (algebraMap K (FT K p (lam : K)) (u : K)) • v = (ψ₀ c) v at h1
      rw [IsScalarTower.algebraMap_smul (FT K p (lam : K)) (u : K) v] at h1
      change (u : K) • v = eF c v at h1
      rw [eF_apply, hlinF_apply] at h1
      exact h1.symm
    rw [StatedScalars]
    refine ⟨u, Units.ext ?_⟩
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [hfun v, matrixToLin'_scalar_apply, Units.smul_def]
  let S : Subgroup C := (StatedScalars (Fin N) K).subgroupOf C
  let mkS : C →* StatedProj C := QuotientGroup.mk' S
  let E₀ : Subgroup C := Subgroup.comap mkS E
  have hS_le_E₀ : S ≤ E₀ := by
    intro c hc
    rw [Subgroup.mem_comap]
    change (QuotientGroup.mk c : StatedProj C) ∈ E
    have hzero : (QuotientGroup.mk c : StatedProj C) = 1 :=
      (QuotientGroup.eq_one_iff c).mpr (Subgroup.mem_subgroupOf.mp hc)
    rw [hzero]
    exact E.one_mem
  have hS_le_comap : S ≤ Subgroup.comap ψ (StatedScalars
      (Fin (Module.finrank (FT K p (lam : K)) (Fin N → K))) (FT K p (lam : K))) := by
    intro c hc
    rw [Subgroup.mem_comap]
    have hc' : ∃ u : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin N) u = (c : GL (Fin N) K) := by
      simpa only [StatedScalars, MonoidHom.mem_range] using Subgroup.mem_subgroupOf.mp hc
    obtain ⟨u, hu⟩ := hc'
    rw [hψ_scalar c hu.symm]
    exact ⟨Kunit u, rfl⟩
  let W : Subgroup C := E₀ ⊓ Subgroup.comap ψ (StatedScalars
    (Fin (Module.finrank (FT K p (lam : K)) (Fin N → K))) (FT K p (lam : K)))
  have hS_le_W : S ≤ W := le_inf hS_le_E₀ hS_le_comap
  haveI : Nonempty (Fin (Module.finrank (FT K p (lam : K)) (Fin N → K))) :=
    ⟨⟨0, hrpos⟩⟩
  have hscalar_inj : Function.Injective
      (Matrix.GeneralLinearGroup.scalar
        (Fin (Module.finrank (FT K p (lam : K)) (Fin N → K))) :
        (FT K p (lam : K))ˣ →* GL (Fin (Module.finrank (FT K p (lam : K)) (Fin N → K)))
          (FT K p (lam : K))) := by
    intro a b hab
    apply Units.ext
    have h := congrArg (fun g : GL (Fin (Module.finrank (FT K p (lam : K)) (Fin N → K)))
      (FT K p (lam : K)) => (g : Matrix (Fin (Module.finrank (FT K p (lam : K)) (Fin N → K)))
        (Fin (Module.finrank (FT K p (lam : K)) (Fin N → K))) (FT K p (lam : K)))) hab
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.coe_scalar] at h
    exact Matrix.scalar_inj.mp h
  let βs : W →* StatedScalars (Fin (Module.finrank (FT K p (lam : K)) (Fin N → K)))
      (FT K p (lam : K)) :=
    (ψ.comp W.subtype).codRestrict _ (fun w => by
      exact (inf_le_right : W ≤ Subgroup.comap ψ (StatedScalars
        (Fin (Module.finrank (FT K p (lam : K)) (Fin N → K))) (FT K p (lam : K)))) w.2)
  let β : W →* (FT K p (lam : K))ˣ :=
    (MonoidHom.ofInjective hscalar_inj).symm.toMonoidHom.comp βs
  have hβ_spec (w : W) : (Matrix.GeneralLinearGroup.scalar
      (Fin (Module.finrank (FT K p (lam : K)) (Fin N → K))) (β w) :
        GL (Fin (Module.finrank (FT K p (lam : K)) (Fin N → K))) (FT K p (lam : K))) =
      ψ w := by
    have h := MonoidHom.ofInjective_apply hscalar_inj (x := β w)
    have h2 : (MonoidHom.ofInjective hscalar_inj) (β w) = βs w := by
      have h' := (MonoidHom.ofInjective hscalar_inj).apply_symm_apply (βs w)
      change (MonoidHom.ofInjective hscalar_inj)
        ((MonoidHom.ofInjective hscalar_inj).symm (βs w)) = βs w
      exact h'
    rw [h2] at h
    exact h.symm
  let Kscal : Subgroup (FT K p (lam : K))ˣ := Kunit.range
  let γ : W →* (FT K p (lam : K))ˣ ⧸ Kscal := (QuotientGroup.mk' Kscal).comp β
  have hγker : γ.ker = S.subgroupOf W := by
    ext w
    rw [MonoidHom.mem_ker]
    constructor
    · intro hw
      rw [Subgroup.mem_subgroupOf]
      have hmem : β w ∈ Kscal := (QuotientGroup.eq_one_iff (β w)).mp hw
      obtain ⟨u, hu⟩ := hmem
      apply hψ_scalar_mem (w : C)
      rw [← hβ_spec w, ← hu]
    · intro hw
      have hS : (w : C) ∈ S := Subgroup.mem_subgroupOf.mp hw
      have hS' : ∃ u : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin N) u = (w : GL (Fin N) K) := by
        simpa only [StatedScalars, MonoidHom.mem_range] using Subgroup.mem_subgroupOf.mp hS
      obtain ⟨u, hu⟩ := hS'
      have hβeq : β w = Kunit u := by
        apply hscalar_inj
        rw [hβ_spec w, hψ_scalar (w : C) hu.symm]
      have hmem : β w ∈ Kscal := ⟨u, hβeq.symm⟩
      exact (QuotientGroup.eq_one_iff (β w)).mpr hmem
  haveI : Finite (FT K p (lam : K)) := by
    haveI : Module.Finite K (FT K p (lam : K)) := (AdjoinRoot.powerBasis hf0).finite
    exact Module.finite_of_finite K
  have hγ_cyc : IsCyclic γ.range := by
    haveI : IsCyclic (FT K p (lam : K))ˣ := inferInstance
    have hquot : IsCyclic ((FT K p (lam : K))ˣ ⧸ Kscal) :=
      isCyclic_of_surjective (QuotientGroup.mk' Kscal) (QuotientGroup.mk'_surjective Kscal)
    exact Subgroup.isCyclic γ.range
  have hγ_exp : ∀ x ∈ γ.range, x ^ p = 1 := by
    rintro x ⟨w, rfl⟩
    have hwE : (mkS (w : C) : StatedProj C) ∈ E :=
      Subgroup.mem_comap.mp ((inf_le_left : W ≤ E₀) w.2)
    have hpowS : ((w : C) ^ p) ∈ S := by
      rw [← QuotientGroup.eq_one_iff]
      show (QuotientGroup.mk ((w : C) ^ p) : StatedProj C) = 1
      rw [QuotientGroup.mk_pow]
      exact hE.2 _ hwE
    have hmemW : ((w : C) ^ p) ∈ W := hS_le_W hpowS
    have hmemker : (⟨(w : C) ^ p, hmemW⟩ : W) ∈ γ.ker := by
      rw [hγker]
      exact Subgroup.mem_subgroupOf.mpr hpowS
    have hker : γ ⟨(w : C) ^ p, hmemW⟩ = 1 := MonoidHom.mem_ker.mp hmemker
    rw [← map_pow]
    change γ (w ^ p) = 1
    rw [show w ^ p = ⟨(w : C) ^ p, hmemW⟩ from Subtype.ext rfl]
    exact hker
  have hγ_card : Nat.card γ.range ≤ p :=
    CFSG.AGLEmbedding.card_le_of_isCyclic_of_pow_eq_one γ.range hγ_exp
  let ψE₀ : E₀ →* ψ.range :=
    (ψ.comp E₀.subtype).codRestrict ψ.range (fun x => ⟨x, rfl⟩)
  let SF : Subgroup ψ.range := (StatedScalars
    (Fin (Module.finrank (FT K p (lam : K)) (Fin N → K))) (FT K p (lam : K))).subgroupOf ψ.range
  let g : E₀ →* StatedProj ψ.range := (QuotientGroup.mk' SF).comp ψE₀
  have hgker : g.ker = W.subgroupOf E₀ := by
    ext x
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk ((ψE₀ x : ψ.range)) : StatedProj ψ.range) = 1 ↔ x ∈ W.subgroupOf E₀
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rw [Subgroup.mem_inf, Subgroup.mem_comap]
    constructor
    · intro h
      exact ⟨x.2, h⟩
    · rintro ⟨-, h⟩
      exact h
  have hfE_ker : ((mkS.comp E₀.subtype).ker) = S.subgroupOf E₀ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change (QuotientGroup.mk (x : C) : StatedProj C) = 1 ↔ (x : C) ∈ S
    exact QuotientGroup.eq_one_iff (x : C)
  have hfE_range : (mkS.comp E₀.subtype).range = E := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact Subgroup.mem_comap.mp x.2
    · intro hy
      obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective S y
      exact ⟨⟨c, (Subgroup.mem_comap.mpr (hc ▸ hy))⟩, hc⟩
  let e : (E₀ ⧸ S.subgroupOf E₀) ≃* E :=
    (QuotientGroup.quotientMulEquivOfEq hfE_ker.symm).trans
      ((QuotientGroup.quotientKerEquivRange (mkS.comp E₀.subtype)).trans
        (MulEquiv.subgroupCongr hfE_range))
  let Q := E₀ ⧸ S.subgroupOf E₀
  have hEquot : IsElemAbelian p (⊤ : Subgroup Q) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · have h : e (x * y) = e (y * x) := by
        rw [map_mul, map_mul]
        exact hE.1.is_comm.comm (e x) (e y)
      exact Subtype.ext (e.injective h)
    · have h : e (x ^ p) = e 1 := by
        rw [map_pow, map_one]
        exact Subtype.ext (hE.2 (e x) (e x).2)
      exact e.injective h
  have hS_ker_g : S.subgroupOf E₀ ≤ g.ker := by
    rw [hgker]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨x.2, hS_le_comap (Subgroup.mem_subgroupOf.mp hx)⟩
  let gq : (E₀ ⧸ S.subgroupOf E₀) →* StatedProj ψ.range :=
    QuotientGroup.lift (S.subgroupOf E₀) g hS_ker_g
  have hgq_range : gq.range = g.range := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (S.subgroupOf E₀) y
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨QuotientGroup.mk a, rfl⟩
  have hg_elem : IsElemAbelian p g.range := by
    rw [← hgq_range]
    simpa only [MonoidHom.range_eq_map] using IsElemAbelian.map hEquot gq
  have hpF : (p : FT K p (lam : K)) ≠ 0 := by
    intro h
    apply hpK
    have h1 : algebraMap K (FT K p (lam : K)) (p : K) = 0 := by
      simpa only [map_natCast] using h
    exact (algebraMap K (FT K p (lam : K))).injective (by simpa using h1)
  have hg_card : Nat.card g.range ≤ p ^ (Module.finrank (FT K p (lam : K)) (Fin N → K) - 1) :=
    CFSG.LocalAnalysis.GLTheoremA.card_le_pow_statedProj hp hp2 hpF hrpos ψ.range g.range hg_elem
  have hcardE₀ : Nat.card E * Nat.card S = Nat.card E₀ := by
    have h := Subgroup.card_ker_mul_card_range (mkS.comp E₀.subtype)
    rw [hfE_ker, hfE_range] at h
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS_le_E₀).toEquiv] at h
    rw [mul_comm] at h
    exact h
  have hcardg : Nat.card g.range * Nat.card W = Nat.card E₀ := by
    have h := Subgroup.card_ker_mul_card_range g
    rw [hgker] at h
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : W ≤ E₀)).toEquiv] at h
    rw [mul_comm] at h
    exact h
  have hcardγ : Nat.card γ.range * Nat.card S = Nat.card W := by
    have h := Subgroup.card_ker_mul_card_range γ
    rw [hγker] at h
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS_le_W).toEquiv] at h
    rw [mul_comm] at h
    exact h
  haveI : Nonempty S := ⟨1⟩
  have hSp : 0 < Nat.card S := Nat.card_pos
  have hmain : Nat.card E = Nat.card g.range * Nat.card γ.range := by
    have h1 : Nat.card E * Nat.card S = Nat.card g.range * Nat.card γ.range * Nat.card S := by
      calc Nat.card E * Nat.card S = Nat.card E₀ := hcardE₀
        _ = Nat.card g.range * Nat.card W := hcardg.symm
        _ = Nat.card g.range * (Nat.card γ.range * Nat.card S) := by rw [hcardγ]
        _ = Nat.card g.range * Nat.card γ.range * Nat.card S := by ring
    exact Nat.eq_of_mul_eq_mul_right hSp h1
  rw [hNdiv, hmain]
  calc Nat.card g.range * Nat.card γ.range
      ≤ p ^ (Module.finrank (FT K p (lam : K)) (Fin N → K) - 1) * p :=
        Nat.mul_le_mul hg_card hγ_card
    _ = p ^ Module.finrank (FT K p (lam : K)) (Fin N → K) := by
        rw [← pow_succ, Nat.sub_add_cancel hrpos]

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
