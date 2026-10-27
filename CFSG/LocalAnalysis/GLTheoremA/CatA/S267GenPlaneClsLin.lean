module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsLinLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsNoComp
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnAut
import CFSG.GroupTheory.PrimeField.SteinbergBNNoncyclicFixedVector
import CFSG.LocalAnalysis.ComponentClassification.SolMaxCoverSwap
import CFSG.GroupTheory.Fitting.LayerProjection
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInner
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
public import CFSG.RankThree.PartOne.KC.OrthogonalSelfDualBlock

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open CFSG.RankThree.CALinearPrimary CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.LocalAnalysis.ComponentInitial CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement Matrix

theorem aeval_apply_eq_eval_one_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {T : Module.End R M} {u : M} (hu : T u = u) (q : R[X]) : aeval T q u = q.eval 1 • u := by
  by_cases h0 : u = 0
  · simp [h0]
  · exact Module.End.aeval_apply_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.2 (by rw [one_smul]; exact hu), h0⟩

variable {n : ℕ} {K : Type} [Field K]

theorem scalar_eq_one_of_mulVec_eq {c : Kˣ} {w : Fin n → K} (hw : w ≠ 0)
    (h : ((Matrix.GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) *ᵥ w = w) : c = 1 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  have h1 : (c : K) * w i = 1 * w i := by
    have := congrFun h i
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal] at this
    rw [one_mul]
    exact this
  exact Units.ext (mul_right_cancel₀ hi h1)

theorem primaryComponent_le_of_specialFactor_eq [Finite K] {p : ℕ} (hpk : (p : K) ≠ 0)
    {A B : GL (Fin n) K} {c d : Kˣ} (hA : A ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    (hB : B ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) d) {h h' : K[X]}
    (hh : h ∈ primaryFactors (glA A : Module.End K (Fin n → K))) (hgood : IsGoodFactor A h)
    (hh' : h' ∈ primaryFactors (glA B : Module.End K (Fin n → K)))
    (heq : specialFactor A h = specialFactor B h') :
    primaryComponent (glA A : Module.End K (Fin n → K)) h ≤
      primaryComponent (glA B : Module.End K (Fin n → K)) h' := by
  intro w hw
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hsqA := squarefree_minpoly_glA hpk hA
  have hsqB := squarefree_minpoly_glA hpk hB
  have hm : 2 ≤ finrank (AdjoinRoot h) (primaryComponent (glA A : Module.End K (Fin n → K)) h) := by
    rcases hgood with h3 | ⟨h2, -⟩
    · exact le_trans (by norm_num) h3
    · exact h2
  obtain ⟨f, v, hfw, hfv⟩ := exists_dual_eq_zero_eq_one hm ⟨w, hw⟩
  obtain ⟨g, hg, hgv⟩ := exists_mem_linearSpecialBlock_transvection hsqA hh hfw
  have hle : linearSpecialBlock (glA A) h ≤ (slGL n K).range := fun _ hg =>
    mem_range_slGL (det_eq_one_of_mem_linearSpecialBlock hsqA hh hg)
  obtain ⟨g₀, rfl⟩ := hle hg
  have hg₀ : g₀ ∈ specialFactor B h' := heq ▸ (hg : g₀ ∈ specialFactor A h)
  have h1 : (slGL n K g₀ : Module.End K (Fin n → K)) v = (v : Fin n → K) + w := by
    rw [hgv v, hfv, one_smul]
    rfl
  have h2 : w = (slGL n K g₀ : Module.End K (Fin n → K)) v - v := by rw [h1]; abel
  rw [h2]
  exact sub_mem_primaryComponent_of_mem_linearSpecialBlock hsqB hh' hg₀ _

theorem exists_unitsHom_of_smul {E : Type*} [Field E] {W : Submodule K (Fin n → K)}
    [Module E W] (hW : ∃ w : W, w ≠ 0) (S : Subgroup (GL (Fin n) K))
    (h : ∀ B ∈ S, ∃ e : E, ∀ w : W,
      (B : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = ((e • w : W) : Fin n → K)) :
    ∃ ρ : ↥S →* Eˣ, ∀ (B : ↥S) (w : W), ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (w : Fin n → K) = (((ρ B : E) • w : W) : Fin n → K) := by
  choose e he using fun B : ↥S => h B B.2
  obtain ⟨w₀, hw₀⟩ := hW
  have huniq : ∀ a b : E, ((a • w₀ : W) : Fin n → K) = ((b • w₀ : W) : Fin n → K) → a = b :=
    fun a b hab => smul_left_injective E hw₀ (Subtype.ext hab)
  have hne : ∀ B : ↥S, e B ≠ 0 := by
    intro B h0
    have h1 := he B w₀
    rw [h0, zero_smul, Submodule.coe_zero] at h1
    apply hw₀
    apply Subtype.ext
    have h2 : (((B : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        (((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (w₀ : Fin n → K)) = w₀ := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [h1, Matrix.mulVec_zero] at h2
    rw [← h2, Submodule.coe_zero]
  refine ⟨{ toFun := fun B => Units.mk0 (e B) (hne B), map_one' := ?_, map_mul' := ?_ },
    fun B w => he B w⟩
  · apply Units.ext
    rw [Units.val_mk0, Units.val_one]
    apply huniq
    rw [← he 1 w₀, one_smul]
    simp
  · intro B₁ B₂
    apply Units.ext
    rw [Units.val_mk0, Units.val_mul, Units.val_mk0, Units.val_mk0]
    apply huniq
    rw [← he (B₁ * B₂) w₀, mul_smul, ← he B₁ (e B₂ • w₀), ← he B₂ w₀, Subgroup.coe_mul,
      Units.val_mul, Matrix.mulVec_mulVec]

theorem glA_apply_eq_mulVec (B : GL (Fin n) K) (v : Fin n → K) :
    (glA B : Module.End K (Fin n → K)) v = (B : Matrix (Fin n) (Fin n) K) *ᵥ v :=
  Matrix.toLin'_apply _ _

theorem glScalar_mulVec (u : Kˣ) (v : Fin n → K) :
    ((Matrix.GeneralLinearGroup.scalar (Fin n) u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      v = (u : K) • v := by
  ext i
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal]
  rfl

theorem eq_one_of_mulVec_eq_self {B : GL (Fin n) K}
    (h : ∀ v : Fin n → K, (B : Matrix (Fin n) (Fin n) K) *ᵥ v = v) : B = 1 := by
  apply Units.ext
  rw [Units.val_one]
  have h1 : Matrix.toLin' (B : Matrix (Fin n) (Fin n) K) = Matrix.toLin' 1 := by
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, h, Matrix.toLin'_one, LinearMap.id_apply]
  exact Matrix.toLin'.injective h1

variable [Finite K]

theorem planeNoComp_projectiveSL (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : (p : K) ≠ 0) : PlaneNoComp p (LinearFlag.projectiveSL n K) := by
  classical
  intro P hP hcard J hJ
  haveI : Fact p.Prime := ⟨hp⟩
  have hscal : ∀ B : GL (Fin n) K, LinearFlag.conjAut n K B = 1 →
      ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin n) c = B := fun B hB =>
    (LinearFlag.eq_one_of_conjAut_mul_fieldAut_eq_one hn B 1 (by rw [map_one, mul_one, hB])).2
  have hpow : ∀ B : GL (Fin n) K, LinearFlag.conjAut n K B ∈ P →
      ∃ c : Kˣ, B ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
    intro B hB
    obtain ⟨c, hc⟩ := hscal (B ^ p) (by rw [map_pow]; exact hP.2 _ hB)
    exact ⟨c, hc.symm⟩
  have hcompOf : ∀ B : GL (Fin n) K, LinearFlag.conjAut n K B ∈ P →
      LinearFlag.conjAut n K B ≠ 1 → ∃ (c : Kˣ) (h : K[X]),
        B ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c ∧
        h ∈ primaryFactors (glA B : Module.End K (Fin n → K)) ∧ IsGoodFactor B h ∧
        J = (specialFactor B h).map (LinearFlag.proj n K) := by
    intro B hB hB1
    obtain ⟨c, hc⟩ := hpow B hB
    have hJB := hJ _ hB hB1
    have hperfJ : ⁅J, J⁆ = J := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJB
    have hcomp := (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer
      hJB (perfectInLayer_conjAut hpK hc J hJB.1 hperfJ)).1
    obtain ⟨⟨⟨h, hh⟩, hgood⟩, hJeq⟩ := linear_inner_components hpK hc J hcomp
    exact ⟨c, h, hc, hh, hgood, hJeq⟩
  have hVE : ∀ α ∈ P, α ∈ LinearFlag.semilinearAutGroup n K := fun α hα =>
    LinearFlag.mem_semilinearAutGroup_iff.2
      (CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.exists_conj_field_of_odd hn (hp.odd_of_ne_two hp2)
        (hP.2 α hα))
  haveI hVe : IsElementaryAbelian p ↥P :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p P).2 hP
  obtain ⟨x₀, hx₀P, hx₀1, A, rfl⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.exists_inner_diag_of_elem hn hVe hcard hVE
  obtain ⟨c, h, hc, hh, hgood, hJeq⟩ := hcompOf A hx₀P hx₀1
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hsqA := squarefree_minpoly_glA hpK hc
  set F := specialFactor A h with hFdef
  have hperfF : ⁅F, F⁆ = F := by
    haveI := (isQuasisimple_specialFactor hsqA hh hgood).1
    exact CFSG.GroupTheory.commutator_eq_self_of_isPerfect_subgroup
  set W := primaryComponent (glA A : Module.End K (Fin n → K)) h with hWdef
  have hm : 2 ≤ finrank (AdjoinRoot h) W := by
    rcases hgood with h3 | ⟨h2, -⟩
    · exact le_trans (by norm_num) h3
    · exact h2
  obtain ⟨w₀, hw₀⟩ : ∃ w : W, w ≠ 0 := by
    have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := AdjoinRoot h) (by omega)
    exact exists_ne 0
  have hw₀' : (w₀ : Fin n → K) ≠ 0 := fun h0 => hw₀ (Subtype.ext h0)
  have hker : (LinearFlag.proj n K).ker ≤ Subgroup.center _ := by
    rw [LinearFlag.ker_proj]
    exact LinearFlag.scalars_le_center n K
  have hfixF : ∀ z ∈ P, ∀ g ∈ F, z (LinearFlag.proj n K g) = LinearFlag.proj n K g := by
    intro z hz g hg
    by_cases hz1 : z = 1
    · rw [hz1]
      rfl
    · have hmem : LinearFlag.proj n K g ∈ J := by
        rw [hJeq]
        exact ⟨g, hg, rfl⟩
      exact (hJ z hz hz1).1 hmem
  have hinner : ∀ z ∈ P, ∃ B : GL (Fin n) K, LinearFlag.conjAut n K B = z := by
    intro z hz
    obtain ⟨B, σ, hzB⟩ := LinearFlag.mem_semilinearAutGroup_iff.1 (hVE z hz)
    have hσ := eq_one_of_fix_specialFactor hpK hc hh hgood B σ (fun g hg => by
      rw [← hzB]
      exact hfixF z hz g hg)
    exact ⟨B, by rw [hzB, hσ, map_one, mul_one]⟩
  have hsmulB : ∀ B ∈ P.comap (LinearFlag.conjAut n K), ∃ e : AdjoinRoot h, ∀ w : W,
      (B : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = ((e • w : W) : Fin n → K) := by
    intro B hB
    obtain ⟨e, he⟩ := exists_smul_of_fix_specialFactor hpK hc hh hgood B 1 (fun g hg => by
      rw [map_one, mul_one]
      exact hfixF _ hB g hg)
    exact ⟨e, fun w => by rw [← he w, plSemiVec_apply]; rfl⟩
  obtain ⟨ρ, hρ⟩ := exists_unitsHom_of_smul ⟨w₀, hw₀⟩ (P.comap (LinearFlag.conjAut n K)) hsmulB
  have hexB : ∃ B : GL (Fin n) K, LinearFlag.conjAut n K B ∈ P ∧ LinearFlag.conjAut n K B ≠ 1 ∧
      ∀ w : W, (B : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = w := by
    by_contra hcon
    push Not at hcon
    obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := ↥ρ.range)
    obtain ⟨g₀, hg₀⟩ := γ.2
    refine IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hcard ?_
    have hle : P ≤ Subgroup.zpowers (LinearFlag.conjAut n K (g₀ : GL (Fin n) K)) := by
      intro z hz
      obtain ⟨B, rfl⟩ := hinner z hz
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hγ ⟨ρ ⟨B, hz⟩, ⟨B, hz⟩, rfl⟩)
      have hk' : ρ (g₀ ^ k) = ρ ⟨B, hz⟩ := by
        rw [map_zpow, hg₀]
        have := congrArg Subtype.val hk
        rwa [Subgroup.coe_zpow] at this
      set B' : ↥(P.comap (LinearFlag.conjAut n K)) := ⟨B, hz⟩ * (g₀ ^ k)⁻¹ with hB'
      have hρB' : ρ B' = 1 := by rw [hB', map_mul, map_inv, hk', mul_inv_cancel]
      have hfixB' : ∀ w : W, ((B' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          (w : Fin n → K) = w := by
        intro w
        rw [hρ B' w, hρB', Units.val_one, one_smul]
      have hB'1 : LinearFlag.conjAut n K (B' : GL (Fin n) K) = 1 := by
        by_contra hne
        obtain ⟨w, hw⟩ := hcon (B' : GL (Fin n) K) B'.2 hne
        exact hw (hfixB' w)
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      have h1 : LinearFlag.conjAut n K (B' : GL (Fin n) K) = LinearFlag.conjAut n K B *
          (LinearFlag.conjAut n K (g₀ : GL (Fin n) K) ^ k)⁻¹ := by
        rw [hB', Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow, map_mul, map_inv,
          map_zpow]
      rw [hB'1] at h1
      exact (mul_inv_eq_one.1 h1.symm).symm
    exact isCyclic_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  obtain ⟨B, hBP, hB1, hBfix⟩ := hexB
  have hdata : ∀ B' : GL (Fin n) K, LinearFlag.conjAut n K B' ∈ P →
      LinearFlag.conjAut n K B' ≠ 1 →
      (∀ w : W, (B' : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = w) →
      ∃ (d : Kˣ) (h' : K[X]), B' ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) d ∧
        h' ∈ primaryFactors (glA B' : Module.End K (Fin n → K)) ∧ IsGoodFactor B' h' ∧
        specialFactor B' h' = F ∧
        primaryComponent (glA B' : Module.End K (Fin n → K)) h' = W ∧ h'.eval 1 = 0 := by
    intro B' hB'P hB'1 hB'fix
    obtain ⟨d, h', hd, hh', hgood', hJeq'⟩ := hcompOf B' hB'P hB'1
    have hsqB := squarefree_minpoly_glA hpK hd
    have hperf' : ⁅specialFactor B' h', specialFactor B' h'⁆ = specialFactor B' h' := by
      haveI := (isQuasisimple_specialFactor hsqB hh' hgood').1
      exact CFSG.GroupTheory.commutator_eq_self_of_isPerfect_subgroup
    have hFeq : specialFactor B' h' = F := le_antisymm
      (CFSG.ComponentClassification.SolMax.le_of_map_le_of_perfect _ hker hperf'
        (by rw [← hJeq', ← hJeq]))
      (CFSG.ComponentClassification.SolMax.le_of_map_le_of_perfect _ hker hperfF
        (by rw [← hJeq', ← hJeq]))
    have hWeq : primaryComponent (glA B' : Module.End K (Fin n → K)) h' = W := le_antisymm
      (primaryComponent_le_of_specialFactor_eq hpK hd hc hh' hgood' hh hFeq)
      (primaryComponent_le_of_specialFactor_eq hpK hc hd hh hgood hh' hFeq.symm)
    have hev : h'.eval 1 = 0 := by
      have hmem : (w₀ : Fin n → K) ∈ primaryComponent (glA B' : Module.End K (Fin n → K)) h' := by
        rw [hWeq]
        exact w₀.2
      have h1 := mem_primaryComponent.mp hmem
      rw [aeval_apply_eq_eval_one_smul (by rw [glA_apply_eq_mulVec]; exact hB'fix w₀) h'] at h1
      exact (smul_eq_zero.mp h1).resolve_right hw₀'
    exact ⟨d, h', hd, hh', hgood', hFeq, hWeq, hev⟩
  have hfixW : ∀ B' : GL (Fin n) K, LinearFlag.conjAut n K B' ∈ P →
      LinearFlag.conjAut n K B' ≠ 1 →
      (∀ w : W, (B' : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = w) →
      ∀ u : Fin n → K, (B' : Matrix (Fin n) (Fin n) K) *ᵥ u = u → u ∈ W := by
    intro B' hB'P hB'1 hB'fix u hu
    obtain ⟨d, h', -, -, -, -, hWeq, hev⟩ := hdata B' hB'P hB'1 hB'fix
    rw [← hWeq, mem_primaryComponent,
      aeval_apply_eq_eval_one_smul (by rw [glA_apply_eq_mulVec]; exact hu) h', hev, zero_smul]
  obtain ⟨dB, hB', hdB, hhB, hgoodB, hFB, hWB, hevB⟩ := hdata B hBP hB1 hBfix
  have hsqB := squarefree_minpoly_glA hpK hdB
  have hnorm : ∀ z ∈ P, ∃ B₂ : GL (Fin n) K, LinearFlag.conjAut n K B₂ = z ∧
      ∀ w : W, (B₂ : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = w := by
    intro z hz
    obtain ⟨B₂', rfl⟩ := hinner z hz
    obtain ⟨e, he⟩ := exists_smul_of_fix_specialFactor hpK hdB hhB hgoodB B₂' 1 (fun g hg => by
      rw [map_one, mul_one]
      rw [hFB] at hg
      exact hfixF _ hz g hg)
    obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective e
    have hact : ∀ w : W, (B₂' : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) =
        f.eval 1 • (w : Fin n → K) := by
      intro w
      have hwB : (w : Fin n → K) ∈ primaryComponent (glA B : Module.End K (Fin n → K)) hB' := by
        rw [hWB]
        exact w.2
      have h1 := he ⟨w, hwB⟩
      rw [plSemiVec_apply, coe_mk_smul_primaryComponent,
        aeval_apply_eq_eval_one_smul (by rw [glA_apply_eq_mulVec]; exact hBfix w) f] at h1
      exact h1
    have ha0 : f.eval 1 ≠ 0 := by
      intro h0
      have h1 := hact w₀
      rw [h0, zero_smul] at h1
      apply hw₀'
      have h2 : ((B₂'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          ((B₂' : Matrix (Fin n) (Fin n) K) *ᵥ (w₀ : Fin n → K)) = w₀ := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]
      rw [h1, Matrix.mulVec_zero] at h2
      exact h2.symm
    refine ⟨Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 (f.eval 1) ha0)⁻¹ * B₂', ?_, ?_⟩
    · rw [map_mul, CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.conjAut_scalar', one_mul]
    · intro w
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, hact w, glScalar_mulVec, smul_smul,
        Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ ha0, one_smul]
  let S1 : Subgroup (GL (Fin n) K) :=
    { carrier := {B' | LinearFlag.conjAut n K B' ∈ P ∧
        ∀ w : W, (B' : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = w}
      mul_mem' := by
        rintro a b ⟨haP, haW⟩ ⟨hbP, hbW⟩
        refine ⟨by rw [map_mul]; exact mul_mem haP hbP, fun w => ?_⟩
        rw [Units.val_mul, ← Matrix.mulVec_mulVec, hbW w, haW w]
      one_mem' := ⟨by rw [map_one]; exact one_mem P, fun w => by
        rw [Units.val_one, Matrix.one_mulVec]⟩
      inv_mem' := by
        rintro a ⟨haP, haW⟩
        refine ⟨by rw [map_inv]; exact inv_mem haP, fun w => ?_⟩
        conv_lhs => rw [← haW w]
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec] }
  have hcommP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hP.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hscal1 : ∀ B' : GL (Fin n) K, LinearFlag.conjAut n K B' = 1 →
      (∀ w : W, (B' : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = w) → B' = 1 := by
    intro B' h1 hW'
    obtain ⟨s, rfl⟩ := hscal B' h1
    rw [scalar_eq_one_of_mulVec_eq hw₀' (hW' w₀), map_one]
  have hcomm : ∀ a ∈ S1, ∀ b ∈ S1, a * b = b * a := by
    intro a ha b hb
    have hc1 : LinearFlag.conjAut n K (a * b * a⁻¹ * b⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcommP _ ha.1 _ hb.1]
      group
    have hmem : a * b * a⁻¹ * b⁻¹ ∈ S1 :=
      S1.mul_mem (S1.mul_mem (S1.mul_mem ha hb) (S1.inv_mem ha)) (S1.inv_mem hb)
    have h1 := hscal1 _ hc1 hmem.2
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [h1, one_mul]
  set π := primaryProjection (glA B : Module.End K (Fin n → K)) hB' with hπ
  set U : Submodule K (Fin n → K) := LinearMap.ker π with hU
  have hBS : B ∈ S1 := ⟨hBP, hBfix⟩
  have hπcomm : ∀ a ∈ S1, Commute (glA a : Module.End K (Fin n → K)) π := by
    intro a ha
    have h1 : Commute (glA a : Module.End K (Fin n → K)) (glA B : Module.End K (Fin n → K)) := by
      have := hcomm a ha B hBS
      change (glA a : Module.End K (Fin n → K)) * (glA B : Module.End K (Fin n → K)) =
        (glA B : Module.End K (Fin n → K)) * (glA a : Module.End K (Fin n → K))
      rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, this]
    exact commute_aeval h1 _
  have hUinv : ∀ a ∈ S1, ∀ u ∈ U, (glA a : Module.End K (Fin n → K)) u ∈ U := by
    intro a ha u hu
    rw [hU, LinearMap.mem_ker] at hu ⊢
    rw [← Module.End.mul_apply, ← (hπcomm a ha).eq, Module.End.mul_apply, hu, map_zero]
  letI : CommGroup ↥S1 :=
    { (inferInstance : Group ↥S1) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  let ρU : Representation K ↥S1 ↥U :=
    { toFun := fun a => (glA (a : GL (Fin n) K) : Module.End K (Fin n → K)).restrict
        (hUinv a a.2)
      map_one' := by
        refine LinearMap.ext fun u => Subtype.ext ?_
        rw [LinearMap.restrict_coe_apply, glA_apply_eq_mulVec, OneMemClass.coe_one, Units.val_one,
          Matrix.one_mulVec]
        rfl
      map_mul' := fun a b => by
        refine LinearMap.ext fun u => Subtype.ext ?_
        rw [LinearMap.restrict_coe_apply, glA_apply_eq_mulVec, Subgroup.coe_mul, Units.val_mul,
          ← Matrix.mulVec_mulVec, Module.End.mul_apply, LinearMap.restrict_coe_apply,
          LinearMap.restrict_coe_apply, glA_apply_eq_mulVec, glA_apply_eq_mulVec] }
  have hUne : U ≠ ⊥ := by
    intro hbot
    apply hB1
    have hfixall : ∀ v : Fin n → K, (B : Matrix (Fin n) (Fin n) K) *ᵥ v = v := by
      intro v
      have hvπ : v - π v ∈ U := by
        rw [hU, LinearMap.mem_ker, map_sub,
          primaryProjection_of_mem hsqB hhB (primaryProjection_mem hsqB hhB v), sub_self]
      rw [hbot, Submodule.mem_bot, sub_eq_zero] at hvπ
      have hvW : v ∈ W := by
        rw [← hWB, hvπ]
        exact primaryProjection_mem hsqB hhB v
      exact hBfix ⟨v, hvW⟩
    rw [eq_one_of_mulVec_eq_self hfixall, map_one]
  haveI : Nontrivial ↥U := Submodule.nontrivial_iff_ne_bot.2 hUne
  have hWU : ∀ u : Fin n → K, u ∈ U → u ∈ W → u = 0 := by
    intro u huU huW
    have h1 : π u = u := primaryProjection_of_mem hsqB hhB (by rw [hWB]; exact huW)
    rw [← h1]
    exact huU
  obtain ⟨z₂, hz₂P, hz₂⟩ : ∃ z₂ ∈ P, z₂ ∉ Subgroup.zpowers (LinearFlag.conjAut n K B) := by
    by_contra hcon
    push Not at hcon
    have hle : Nat.card P ≤ Nat.card (Subgroup.zpowers (LinearFlag.conjAut n K B)) :=
      Subgroup.card_le_of_le hcon
    rw [Nat.card_zpowers, hcard] at hle
    have h2 : orderOf (LinearFlag.conjAut n K B) ≤ p :=
      orderOf_le_of_pow_eq_one hp.pos (hP.2 _ hBP)
    have h3 := hle.trans h2
    nlinarith [hp.two_le]
  obtain ⟨B₂, hB₂z, hB₂W⟩ := hnorm z₂ hz₂P
  have hB₂S : B₂ ∈ S1 := ⟨by rw [hB₂z]; exact hz₂P, hB₂W⟩
  have hpow1 : ∀ a ∈ S1, a ^ p = 1 := by
    intro a ha
    obtain ⟨d, hd⟩ := hpow a ha.1
    have hmem : a ^ p ∈ S1 := S1.pow_mem ha p
    have h1 := scalar_eq_one_of_mulVec_eq hw₀' (by rw [← hd]; exact hmem.2 w₀)
    rw [hd, h1, map_one]
  have hy : (⟨B, hBS⟩ : ↥S1) ^ p = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow]
    exact hpow1 B hBS)
  have hx : (⟨B₂, hB₂S⟩ : ↥S1) ^ p = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow]
    exact hpow1 B₂ hB₂S)
  have hy1 : (⟨B, hBS⟩ : ↥S1) ≠ 1 := by
    intro h1
    apply hB1
    have h2 : B = 1 := congrArg Subtype.val h1
    rw [h2, map_one]
  have hxy : (⟨B₂, hB₂S⟩ : ↥S1) ∉ Subgroup.zpowers (⟨B, hBS⟩ : ↥S1) := by
    rintro ⟨k, hk⟩
    apply hz₂
    refine ⟨k, ?_⟩
    have h1 := congrArg (fun a : ↥S1 => LinearFlag.conjAut n K (a : GL (Fin n) K)) hk
    simp only [SubgroupClass.coe_zpow, map_zpow] at h1
    rw [← hB₂z, ← h1]
  obtain ⟨a, ha1, v, hv0, hav⟩ :=
    CFSG.GroupTheory.PrimeField.exists_fixed_of_pow_eq_one ρU hp hpK hx hy hy1 hxy
  have hav' : (glA (a : GL (Fin n) K) : Module.End K (Fin n → K)) (v : Fin n → K) = v :=
    congrArg Subtype.val hav
  rw [glA_apply_eq_mulVec] at hav'
  have ha1' : LinearFlag.conjAut n K (a : GL (Fin n) K) ≠ 1 := by
    intro h1
    exact ha1 (Subtype.ext (hscal1 _ h1 a.2.2))
  have hvW := hfixW _ a.2.1 ha1' a.2.2 _ hav'
  exact hv0 (Subtype.ext (hWU _ v.2 hvW))

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
