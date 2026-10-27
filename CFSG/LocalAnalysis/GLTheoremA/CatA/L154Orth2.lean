module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Orth
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockQuasisimple
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryTransvectionGeneration
public import CFSG.Models.PGLSimple
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GCenterQuot
public import CFSG.CharacterTheory.Burnside
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryNorm
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticNormalForms
public import CFSG.RankThree.PartOne.K159.RowFourFixed
public import CFSG.RankThree.PartOne.S11d.OrthCaseH
public import CFSG.RankThree.PartOne.K159.Klein
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Glue
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.LayerModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155XOr

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.K155X
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
open Polynomial

section Realize

variable {G₀ : Type} [Group G₀] {ι : Type} [Fintype ι] [DecidableEq ι] {E : Type} [Field E]

theorem orth_realize_of_model {J₀ M : Subgroup G₀} (hJM : J₀ ≤ M)
    (hMn : ∀ L ∈ M, ∀ ω ∈ J₀, L * ω * L⁻¹ ∈ J₀) {H : Subgroup (GL ι E)} {S : Set (GL ι E)}
    (κ : ↥M →* GL ι E) (hκH : ∀ ω (hω : ω ∈ J₀), κ ⟨ω, hJM hω⟩ ∈ H)
    (hκs : ∀ g ∈ H, ∃ ω, ∃ hω : ω ∈ J₀, κ ⟨ω, hJM hω⟩ = g)
    (hκi : ∀ ω ω' (hω : ω ∈ J₀) (hω' : ω' ∈ J₀), κ ⟨ω, hJM hω⟩ = κ ⟨ω', hJM hω'⟩ → ω = ω')
    (hS : ∀ A ∈ S, ∃ L, ∃ hL : L ∈ M, ∀ g ∈ H, κ ⟨L, hL⟩ * g * (κ ⟨L, hL⟩)⁻¹ = A * g * A⁻¹) :
    ∃ Θ₁ : ↥J₀ →* LargeEvenProj H, Function.Surjective Θ₁ ∧ Θ₁.ker ≤ Subgroup.center ↥J₀ ∧
      ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk H) S, ∃ L : G₀, ∃ hL : ∀ ω ∈ J₀, L * ω * L⁻¹ ∈ J₀,
        ∀ ω : ↥J₀, φ (Θ₁ ω) = Θ₁ ⟨L * ω * L⁻¹, hL ω ω.2⟩ := by
  set κ₀ : ↥J₀ →* ↥H := MonoidHom.codRestrict (κ.comp (Subgroup.inclusion hJM)) H
    (fun ω => hκH ω.1 ω.2) with hκ₀
  have hκ₀v : ∀ ω : ↥J₀, ((κ₀ ω : ↥H) : GL ι E) = κ ⟨ω, hJM ω.2⟩ := fun _ => rfl
  have hbij : Function.Bijective κ₀ := by
    refine ⟨fun ω ω' h => Subtype.ext (hκi ω ω' ω.2 ω'.2 ?_), fun g => ?_⟩
    · have := congrArg Subtype.val h
      exact this
    · obtain ⟨ω, hω, hωg⟩ := hκs g g.2
      exact ⟨⟨ω, hω⟩, Subtype.ext hωg⟩
  set e : ↥J₀ ≃* ↥H := MulEquiv.ofBijective κ₀ hbij with he
  refine ⟨(LargeEvenProjMk H).comp e.toMonoidHom, (QuotientGroup.mk'_surjective _).comp e.surjective,
    orth_ker_mk'_comp_le_center e _ (orth_statedScalars_subgroupOf_le_center H), ?_⟩
  rintro φ ⟨A, hA, hφ⟩
  obtain ⟨L, hLM, hLconj⟩ := hS A hA
  refine ⟨L, hMn L hLM, fun ω => ?_⟩
  show φ (LargeEvenProjMk H (κ₀ ω)) = LargeEvenProjMk H (κ₀ ⟨L * ω * L⁻¹, hMn L hLM ω ω.2⟩)
  apply hφ
  rw [hκ₀v, hκ₀v]
  have e1 : (⟨L * ω * L⁻¹, hJM (hMn L hLM ω ω.2)⟩ : ↥M) = ⟨L, hLM⟩ * ⟨ω, hJM ω.2⟩ * ⟨L, hLM⟩⁻¹ := rfl
  rw [e1, map_mul, map_mul, map_inv]
  exact hLconj _ (hκH ω ω.2)

end Realize

section Unipotent

variable {E W : Type*} [Field E] [AddCommGroup W] [Module E W]

@[expose] noncomputable def orthUnipotent (T : W →ₗ[E] W) (hT : ∀ w, T (T w) = 0) (a : E) :
    LinearMap.GeneralLinearGroup E W where
  val := 1 + a • T
  inv := 1 - a • T
  val_inv := LinearMap.ext fun w => by
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.smul_apply, map_sub, map_smul, hT, smul_zero, sub_zero]
    abel
  inv_val := LinearMap.ext fun w => by
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.smul_apply, map_add, map_smul, hT, smul_zero, add_zero]
    abel

theorem orthUnipotent_apply (T : W →ₗ[E] W) (hT : ∀ w, T (T w) = 0) (a : E) (w : W) :
    ((orthUnipotent T hT a : LinearMap.GeneralLinearGroup E W) : W →ₗ[E] W) w = w + a • T w := rfl

theorem orthUnipotent_apply_sub (T : W →ₗ[E] W) (hT : ∀ w, T (T w) = 0) (a : E) (w : W) :
    ((orthUnipotent T hT a : LinearMap.GeneralLinearGroup E W) : W →ₗ[E] W) (w - a • T w) = w := by
  rw [orthUnipotent_apply, map_sub, map_smul, hT, smul_zero, sub_zero, sub_add_cancel]

theorem det_orthUnipotent [CharP E 2] [Module.Free E W] [Module.Finite E W] (T : W →ₗ[E] W)
    (hT : ∀ w, T (T w) = 0) (a : E) :
    LinearMap.det ((orthUnipotent T hT a : LinearMap.GeneralLinearGroup E W) : W →ₗ[E] W) = 1 := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hsq : ((orthUnipotent T hT a : LinearMap.GeneralLinearGroup E W) : W →ₗ[E] W) *
      ((orthUnipotent T hT a : LinearMap.GeneralLinearGroup E W) : W →ₗ[E] W) = 1 := by
    refine LinearMap.ext fun w => ?_
    rw [Module.End.mul_apply, orthUnipotent_apply, orthUnipotent_apply, map_add, map_smul, hT, smul_zero,
      add_zero, Module.End.one_apply, add_assoc, ← two_smul E (a • T w), h2, zero_smul, add_zero]
  have h1 := congrArg LinearMap.det hsq
  rw [map_mul, map_one] at h1
  set δ := LinearMap.det ((orthUnipotent T hT a : LinearMap.GeneralLinearGroup E W) : W →ₗ[E] W)
  have : (δ - 1) * (δ - 1) = 0 := by linear_combination h1 - δ * h2 + h2
  exact sub_eq_zero.1 (mul_self_eq_zero.1 this)

end Unipotent

section Decomp

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem orth_linearMap_ext_orbit (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) {f₁ f₂ : V →ₗ[K] V}
    (h1 : ∀ u ∈ primaryComponent x.toLinearMap h, f₁ u = f₂ u)
    (h2 : ∀ w ∈ primaryComponent x.toLinearMap (reciprocalPolynomial h), f₁ w = f₂ w)
    (h3 : ∀ r ∈ othersSpace x.toLinearMap h, f₁ r = f₂ r) : f₁ = f₂ := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨o, ho, r, hr, rfl⟩ := exists_add_of_isCompl (hx.isCompl_orbit_others hh) v
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp ho
  rw [map_add, map_add, map_add, map_add, h1 u hu, h2 w hw, h3 r hr]

end Decomp

section KLine

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem orth_kline_of_unipotent (hx : OddOrderIsometry Q p x) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap)
    (T : primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] primaryComponent x.toLinearMap h)
    (hT : ∀ w, T (T w) = 0) (hT0 : T ≠ 0)
    (g : K → ↥(supportedBlock Q x h))
    (hg : ∀ c, blockGL Q x h (g c) = orthUnipotent T hT (algebraMap K (AdjoinRoot h) c))
    (hdet : ∀ c, blockDet Q x h (g c) = 1) :
    ∃ N : V →ₗ[K] V, N ≠ 0 ∧ ∀ c : K, ∃ ω ∈ specialBlock Q x h, ∀ v, ω v = v + c • N v := by
  have hVh : ∀ (c : K) (w : primaryComponent x.toLinearMap h),
      ((g c : V ≃ₗ[K] V) (w : V)) = (w : V) + c • ((T w : primaryComponent x.toLinearMap h) : V) := by
    intro c w
    have h1 := coe_blockGL h (g c) w
    rw [hg c, orthUnipotent_apply] at h1
    rw [← h1, Submodule.coe_add, coe_algebraMap_smul_primaryComponent]
  set N : V →ₗ[K] V := ((g 1 : V ≃ₗ[K] V) : V →ₗ[K] V) - LinearMap.id with hN
  have hNh : ∀ w : primaryComponent x.toLinearMap h,
      N (w : V) = ((T w : primaryComponent x.toLinearMap h) : V) := by
    intro w
    rw [hN, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, hVh 1 w, one_smul,
      add_sub_cancel_left]
  refine ⟨N, ?_, fun c => ⟨(g c : V ≃ₗ[K] V), mem_specialBlock.mpr ⟨(g c).2, hdet c⟩, fun v => ?_⟩⟩
  · intro hN0
    apply hT0
    refine LinearMap.ext fun w => Subtype.ext ?_
    rw [← hNh w, hN0]
    rfl
  have key : ((g c : V ≃ₗ[K] V) : V →ₗ[K] V) = LinearMap.id + c • N := by
    refine orth_linearMap_ext_orbit hx hh ?_ ?_ ?_
    · intro u hu
      rw [LinearEquiv.coe_coe, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply]
      have := hVh c ⟨u, hu⟩
      rw [hNh ⟨u, hu⟩]
      exact this
    · intro w hw
      rw [LinearEquiv.coe_coe, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply]
      have hcc : ∀ c' : K, (g c' : V ≃ₗ[K] V) ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) :=
        fun c' => supportedBlock_le_centralizer h (g c').2
      have hO : ∀ c' : K, (g c' : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
        fun c' => (Subgroup.mem_inf.mp (supportedBlock_le_isometryCentralizer h (g c').2)).1
      have hmem : ∀ c' : K, (g c' : V ≃ₗ[K] V) w ∈ primaryComponent x.toLinearMap (reciprocalPolynomial h) :=
        fun c' => apply_mem_primaryComponent_of_mem_centralizer (hcc c') hw
      have hpol : ∀ (c' : K) (u : primaryComponent x.toLinearMap h),
          QuadraticMap.polar Q (u : V) ((g c' : V ≃ₗ[K] V) w) =
            QuadraticMap.polar Q (u : V) w - c' * QuadraticMap.polar Q
              ((T u : primaryComponent x.toLinearMap h) : V) w := by
        intro c' u
        have hz := orthUnipotent_apply_sub T hT (algebraMap K (AdjoinRoot h) c') u
        set z : primaryComponent x.toLinearMap h := u - algebraMap K (AdjoinRoot h) c' • T u with hzdef
        have hgz : (g c' : V ≃ₗ[K] V) (z : V) = (u : V) := by
          have h1 := coe_blockGL h (g c') z
          rw [hg c', hz] at h1
          exact h1.symm
        have hiso := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hO c') (z : V) w
        rw [hgz] at hiso
        rw [hiso, hzdef, Submodule.coe_sub, coe_algebraMap_smul_primaryComponent,
          QuadraticMap.polar_sub_left, QuadraticMap.polar_smul_left, smul_eq_mul]
      set D : V := (g c : V ≃ₗ[K] V) w - w - c • ((g 1 : V ≃ₗ[K] V) w - w) with hD
      have hDmem : D ∈ primaryComponent x.toLinearMap (reciprocalPolynomial h) :=
        Submodule.sub_mem _ (Submodule.sub_mem _ (hmem c) hw)
          (Submodule.smul_mem _ c (Submodule.sub_mem _ (hmem 1) hw))
      have hD0 : D = 0 := by
        refine hx.eq_zero_of_polar_paired_right hh hDmem fun u hu => ?_
        rw [hD, QuadraticMap.polar_sub_right, QuadraticMap.polar_sub_right, QuadraticMap.polar_smul_right,
          QuadraticMap.polar_sub_right, hpol c ⟨u, hu⟩, hpol 1 ⟨u, hu⟩, smul_eq_mul]
        ring
      have hNw : N w = (g 1 : V ≃ₗ[K] V) w - w := by
        rw [hN, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
      rw [hNw]
      have h3 : (g c : V ≃ₗ[K] V) w - w = c • ((g 1 : V ≃ₗ[K] V) w - w) := sub_eq_zero.1 hD0
      rw [← h3]
      abel
    · intro r hr
      have h1 : (g c : V ≃ₗ[K] V) r = r := (mem_supportedBlock.mp (g c).2).2 r hr
      have h2 : (g 1 : V ≃ₗ[K] V) r = r := (mem_supportedBlock.mp (g 1).2).2 r hr
      rw [LinearEquiv.coe_coe, h1, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply, hN,
        LinearMap.sub_apply, LinearEquiv.coe_coe, h2, LinearMap.id_apply, sub_self, smul_zero, add_zero]
  have := congrArg (fun F : V →ₗ[K] V => F v) key
  simpa using this

end KLine

end CFSG.LocalAnalysis.GLTheoremA.K155XOr

namespace CFSG.LocalAnalysis.GLTheoremA.K155XOr

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.K155X
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
open Polynomial

section Matrix

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {x : V ≃ₗ[K] V}

@[expose] noncomputable def orthBlockMatrix {h : K[X]} [Fact (Irreducible h)] {n : ℕ}
    (β : Module.Basis (Fin n) (AdjoinRoot h) (primaryComponent x.toLinearMap h)) :
    ↥(supportedBlock Q x h) →* GL (Fin n) (AdjoinRoot h) :=
  (Matrix.GeneralLinearGroup.toLin' β).symm.toMonoidHom.comp (blockGL Q x h)

theorem toLin'_orthBlockMatrix {h : K[X]} [Fact (Irreducible h)] {n : ℕ}
    (β : Module.Basis (Fin n) (AdjoinRoot h) (primaryComponent x.toLinearMap h))
    (g : ↥(supportedBlock Q x h)) :
    Matrix.GeneralLinearGroup.toLin' β (orthBlockMatrix β g) = blockGL Q x h g :=
  MulEquiv.apply_symm_apply _ _

theorem det_orthBlockMatrix {h : K[X]} [Fact (Irreducible h)] {n : ℕ}
    (β : Module.Basis (Fin n) (AdjoinRoot h) (primaryComponent x.toLinearMap h))
    (g : ↥(supportedBlock Q x h)) :
    ((orthBlockMatrix β g : GL (Fin n) (AdjoinRoot h)) : Matrix (Fin n) (Fin n) (AdjoinRoot h)).det =
      blockDet Q x h g := by
  rw [← CFSG.LocalAnalysis.ComponentInitial.det_toLin' β, toLin'_orthBlockMatrix, blockDet_apply]

end Matrix

section Paired

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem orthBlockData_paired (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) (hne : h ≠ reciprocalPolynomial h)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h)) : OrthBlockData p (specialBlock Q x h) := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : CharP (AdjoinRoot h) 2 := charP_two_of_algebra (K := K)
  haveI : Finite (AdjoinRoot h) := finite_adjoinRoot_of_fact h
  set n := primaryMultiplicity x.toLinearMap h with hn
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hpos := hx.primaryMultiplicity_pos hh
    exact ne_bot_of_isQuasisimple hq (hx.specialBlock_eq_bot_of_finrank_eq_one hh (by omega))
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hE4 : 4 ≤ Nat.card (AdjoinRoot h) := by
    have := hx.p_lt_card_adjoinRoot hp hh hne1
    omega
  obtain ⟨f', hf'⟩ : ∃ f' : ℕ, Nat.card (AdjoinRoot h) = 2 ^ f' := by
    haveI := Fintype.ofFinite (AdjoinRoot h)
    obtain ⟨m, -, hm⟩ := FiniteField.card (AdjoinRoot h) 2
    exact ⟨m, by rw [Nat.card_eq_fintype_card, hm]⟩
  have hf'2 : 2 ≤ f' := by
    by_contra hlt
    have : 2 ^ f' ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hfin : Module.finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) = n - 1 + 1 := by
    have : Module.finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) = n := rfl
    omega
  set β : Module.Basis (Fin (n - 1 + 1)) (AdjoinRoot h) (primaryComponent x.toLinearMap h) :=
    Module.finBasisOfFinrankEq _ _ hfin with hβ
  set κ : ↥(supportedBlock Q x h) →* GL (Fin (n - 1 + 1)) (AdjoinRoot h) := orthBlockMatrix β with hκ
  have hκsurj : ∀ A : GL (Fin (n - 1 + 1)) (AdjoinRoot h), ∃ L : ↥(supportedBlock Q x h), κ L = A := by
    intro A
    refine ⟨(pairedBlockEquiv hx hh hne).symm (Matrix.GeneralLinearGroup.toLin' β A), ?_⟩
    rw [hκ, orthBlockMatrix, MonoidHom.comp_apply]
    have h1 : blockGL Q x h ((pairedBlockEquiv hx hh hne).symm (Matrix.GeneralLinearGroup.toLin' β A)) =
        Matrix.GeneralLinearGroup.toLin' β A := (pairedBlockEquiv hx hh hne).apply_symm_apply _
    rw [h1]
    exact (Matrix.GeneralLinearGroup.toLin' β).symm_apply_apply A
  have hlab : LargeEvenInLambda2 ⟨.A, n - 1, f'⟩ := by
    show 1 ≤ f' ∧ 1 ≤ n - 1 ∧ (n - 1 = 1 → 2 ≤ f')
    exact ⟨by omega, by omega, fun _ => hf'2⟩
  refine ⟨⟨⟨.A, n - 1, f'⟩, hlab, (show LargeEvenLieTag.A ≠ .triD4 by decide),
    fun h => absurd h.1 (show LargeEvenLieTag.A ≠ .D by decide), ?_⟩, Or.inl ?_⟩
  ·
    have hs : IsSimpleGroup (LargeEvenProj (LargeEvenSLGroup (Fin (n - 1 + 1)) (AdjoinRoot h))) := by
      rw [largeEvenSLGroup_eq_statedSL]
      exact CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL _ (by omega) (Or.inr (by omega))
        (Or.inr (by omega))
    obtain ⟨Θ₁, hΘs, hΘk, hreal⟩ := orth_realize_of_model (specialBlock_le_supportedBlock h)
      (fun L hL ω hω => conj_mem_specialBlock (supportedBlock_le_isometryCentralizer h hL) hω)
      (H := LargeEvenSLGroup (Fin (n - 1 + 1)) (AdjoinRoot h)) (S := Set.univ) κ
      (fun ω hω => by
        rw [largeEvenSLGroup_eq_statedSL, CFSG.Open.StatedAPI.mem_statedSL_iff, hκ, det_orthBlockMatrix]
        exact blockDet_eq_one_of_mem_specialBlock hω)
      (fun g hg => by
        obtain ⟨L, hL⟩ := hκsurj g
        have hdet : blockDet Q x h L = 1 := by
          rw [← det_orthBlockMatrix β, ← hκ, hL]
          rw [largeEvenSLGroup_eq_statedSL, CFSG.Open.StatedAPI.mem_statedSL_iff] at hg
          exact hg
        exact ⟨L.1, mem_specialBlock.mpr ⟨L.2, hdet⟩, hL⟩)
      (fun ω ω' hω hω' hωω' => by
        have h1 : blockGL Q x h ⟨ω, specialBlock_le_supportedBlock h hω⟩ =
            blockGL Q x h ⟨ω', specialBlock_le_supportedBlock h hω'⟩ := by
          rw [← toLin'_orthBlockMatrix β, ← toLin'_orthBlockMatrix β]
          exact congrArg _ hωω'
        exact congrArg Subtype.val (hx.blockGL_injective hh h1))
      (fun A _ => by
        obtain ⟨L, hL⟩ := hκsurj A
        exact ⟨L.1, L.2, fun g _ => by rw [show (⟨L.1, L.2⟩ : ↥(supportedBlock Q x h)) = L from rfl, hL]⟩)
    unfold OrthRealized CFSG.Assembly.LargeEvenRawDatum
    dsimp only
    unfold LargeEvenRecipeLinear
    haveI := hs
    exact ⟨AdjoinRoot h, inferInstance, inferInstance, hf', hs,
      orth_exists_noncomm_of_surjective hq.1 Θ₁ hΘs, Θ₁, hΘs, hΘk, hreal⟩
  ·
    set i0 : Fin (n - 1 + 1) := ⟨0, by omega⟩ with hi0
    set i1 : Fin (n - 1 + 1) := ⟨1, by omega⟩ with hi1
    have hi : i0 ≠ i1 := by
      rw [hi0, hi1]
      exact fun h01 => absurd (congrArg Fin.val h01) (by simp)
    set T : primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] primaryComponent x.toLinearMap h :=
      (β.coord i1).smulRight (β i0) with hT
    have hTT : ∀ w, T (T w) = 0 := by
      intro w
      simp [hT, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, hi]
    have hT0 : T ≠ 0 := by
      intro h0
      have h1 : T (β i1) = β i0 := by simp [hT]
      rw [h0, LinearMap.zero_apply] at h1
      exact β.ne_zero i0 h1.symm
    set g : K → ↥(supportedBlock Q x h) := fun c =>
      (pairedBlockEquiv hx hh hne).symm (orthUnipotent T hTT (algebraMap K (AdjoinRoot h) c)) with hg
    have hgv : ∀ c, blockGL Q x h (g c) = orthUnipotent T hTT (algebraMap K (AdjoinRoot h) c) :=
      fun c => (pairedBlockEquiv hx hh hne).apply_symm_apply _
    exact orth_kline_of_unipotent hx hh T hTT hT0 g hgv fun c => by
      rw [blockDet_apply, hgv c]
      exact det_orthUnipotent T hTT _

end Paired

end CFSG.LocalAnalysis.GLTheoremA.K155XOr

namespace CFSG.LocalAnalysis.GLTheoremA.K155XOr

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.K155X
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
open Polynomial

theorem orth_not_isSolvable_of_isQuasisimple {G : Type*} [Group G] (hG : CFSG.IsQuasisimple G) :
    ¬ Group.IsSolvable G := by
  intro hsolv
  obtain ⟨-, hsimple, a, b, hab⟩ := hG
  have hsolv' : Group.IsSolvable (G ⧸ Subgroup.center G) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (Subgroup.center G))
  exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hsolv') a b)

theorem orth_largeEvenProj_congr {ι : Type} [Fintype ι] [DecidableEq ι] {E : Type} [Field E]
    {H₁ H₂ : Subgroup (GL ι E)} (h : H₁ = H₂) : Nonempty (LargeEvenProj H₁ ≃* LargeEvenProj H₂) := by
  subst h
  exact ⟨MulEquiv.refl _⟩

section SelfDualSetting

open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem orth_selfDual_setting (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) :
    ∃ (f₀ : ℕ) (hU : UnitaryFieldData 2 f₀ (AdjoinRoot h))
      (B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
        primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h),
      B.IsSymm ∧ B.SeparatingLeft ∧ p ∣ 2 ^ f₀ + 1 ∧
      (∀ z : AdjoinRoot h, hU.bar z = z ^ 2 ^ f₀) ∧
      (∀ c : K, hU.bar (algebraMap K (AdjoinRoot h) c) = algebraMap K (AdjoinRoot h) c) ∧
      (∀ γ : BlockGL x h, γ ∈ (blockGL Q x h).range ↔
        ∀ u w, B ((γ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) u)
          ((γ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) w) = B u w) ∧
      (specialBlockGL Q x h).range = sesqSpecialUnitaryGroup B := by
  classical
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hirr := irreducible_of_mem_primaryFactors hh
  obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian hpodd hh hne1 hself
  have hd : Module.finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨ℓ, f, hU, hqK, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot h) hd
  have hbar' : ∀ z, frobPow K (AdjoinRoot h) d z = hU.bar z := fun z => by
    rw [hbar, frobPow_apply]
  obtain ⟨f₂, hf₂⟩ : ∃ f₂ : ℕ, Nat.card K = 2 ^ f₂ := by
    haveI := Fintype.ofFinite K
    obtain ⟨m, -, hm⟩ := FiniteField.card K 2
    exact ⟨m, by rw [Nat.card_eq_fintype_card, hm]⟩
  have hℓ2 : ℓ = 2 := by
    have hf1 : 1 ≤ f := by
      by_contra hlt
      have : f = 0 := by omega
      rw [this, pow_zero] at hqK
      have := Finite.one_lt_card (α := K)
      omega
    have hdvd : ℓ ∣ 2 ^ f₂ := by
      rw [← hf₂, hqK]
      exact dvd_pow_self ℓ (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hU.prime Nat.prime_two).1 (hU.prime.dvd_of_dvd_pow hdvd)
  subst hℓ2
  let B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
    LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
      (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
      (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
  have hBH : ∀ u w, B u w = H u w := fun u w => rfl
  have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
  have hBl : B.SeparatingLeft := by
    intro u hu
    refine Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => ?_)
    have h1 := hH u ⟨w, hw⟩ 1
    rw [mul_one, one_smul] at h1
    have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
    rw [h2, map_zero] at h1
    exact h1.symm
  have hrange : (specialBlockGL Q x h).range = sesqSpecialUnitaryGroup B := by
    rw [range_specialBlockGL, sesqSpecialUnitaryGroup]
    congr 1
    ext γ
    rw [hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH, mem_sesqUnitaryGroup]
    exact Iff.rfl
  have hqd : Nat.card K ^ d = 2 ^ (f * d) := by rw [hqK, pow_mul]
  refine ⟨f * d, hU, B, hBsymm, hBl, ?_, fun z => by rw [hbar, hqd], fun c => ?_,
    fun γ => hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH γ, hrange⟩
  · rw [← hqd]
    exact hx.dvd_card_pow_add_one hp hh hne1 hroot
  · rw [← hbar', AlgEquiv.commutes]

end SelfDualSetting

section SelfDual

open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem orth_kline_selfDual (hx : OddOrderIsometry Q p x) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) {f₀ : ℕ} (hU : UnitaryFieldData 2 f₀ (AdjoinRoot h))
    (B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h)
    (hBsymm : B.IsSymm) (hBl : B.SeparatingLeft)
    (hbarK : ∀ c : K, hU.bar (algebraMap K (AdjoinRoot h) c) = algebraMap K (AdjoinRoot h) c)
    (hrangeB : ∀ γ : BlockGL x h, γ ∈ (blockGL Q x h).range ↔
      ∀ u w, B ((γ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) u)
        ((γ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) w) = B u w)
    (hn2 : 2 ≤ Module.finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h)) :
    ∃ N : V →ₗ[K] V, N ≠ 0 ∧ ∀ c : K, ∃ ω ∈ specialBlock Q x h, ∀ v, ω v = v + c • N v := by
  classical
  haveI : CharP (AdjoinRoot h) 2 := charP_two_of_algebra (K := K)
  have h2 : (2 : AdjoinRoot h) = 0 := CharTwo.two_eq_zero
  obtain ⟨e, he⟩ := hU.exists_orthonormal_basis hBsymm hBl
  set i0 : Fin (Module.finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h)) := ⟨0, by omega⟩ with hi0
  set i1 : Fin (Module.finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h)) := ⟨1, by omega⟩ with hi1
  have hi : i0 ≠ i1 := by
    rw [hi0, hi1]
    exact fun h01 => absurd (congrArg Fin.val h01) (by simp)
  set u₀ := e i0 + e i1 with hu₀
  have hB00 : B u₀ u₀ = 0 := by
    simp only [hu₀, map_add, LinearMap.add_apply, he, ↓reduceIte, hi, hi.symm, if_false]
    linear_combination h2
  have hB0 : B u₀ (e i0) = 1 := by
    simp only [hu₀, map_add, LinearMap.add_apply, he, ↓reduceIte, hi.symm, if_false, add_zero]
  set T : primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] primaryComponent x.toLinearMap h :=
    (B u₀).smulRight u₀ with hT
  have hTv : ∀ w, T w = B u₀ w • u₀ := fun w => rfl
  have hTT : ∀ w, T (T w) = 0 := by
    intro w
    rw [hTv, hTv, map_smul, hB00, smul_zero, zero_smul]
  have hT0 : T ≠ 0 := by
    intro h0
    have h1 : T (e i0) = u₀ := by rw [hTv, hB0, one_smul]
    rw [h0, LinearMap.zero_apply] at h1
    have h3 : B u₀ (e i0) = 0 := by rw [← h1, map_zero, LinearMap.zero_apply]
    rw [hB0] at h3
    exact one_ne_zero h3
  have hpres : ∀ c : K, orthUnipotent T hTT (algebraMap K (AdjoinRoot h) c) ∈ (blockGL Q x h).range := by
    intro c
    rw [hrangeB]
    intro u w
    rw [orthUnipotent_apply, orthUnipotent_apply, hTv, hTv]
    set a := algebraMap K (AdjoinRoot h) c with ha
    have hba : hU.bar a = a := hbarK c
    have hsym : hU.bar (B u₀ u) = B u u₀ := hBsymm.eq u₀ u
    simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, map_smul,
      hba, hsym, hB00]
    linear_combination (a * B u₀ w * B u u₀) * h2
  set g : K → ↥(supportedBlock Q x h) := fun c => (hpres c).choose with hg
  have hgv : ∀ c, blockGL Q x h (g c) = orthUnipotent T hTT (algebraMap K (AdjoinRoot h) c) :=
    fun c => (hpres c).choose_spec
  exact orth_kline_of_unipotent hx hh T hTT hT0 g hgv fun c => by
    rw [blockDet_apply, hgv c]
    exact det_orthUnipotent T hTT _

theorem orthBlockData_selfDual (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) (hself : h = reciprocalPolynomial h)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h)) : OrthBlockData p (specialBlock Q x h) := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : CharP (AdjoinRoot h) 2 := charP_two_of_algebra (K := K)
  haveI : Finite (AdjoinRoot h) := finite_adjoinRoot_of_fact h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f₀, hU, B, hBsymm, hBl, -, hbarq, hbarK, hrangeB, hrange⟩ :=
    orth_selfDual_setting hx hp hp2 hh hne1 hself
  set n := primaryMultiplicity x.toLinearMap h with hn
  have hnW : Module.finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) = n := rfl
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hpos := hx.primaryMultiplicity_pos hh
    exact ne_bot_of_isQuasisimple hq (hx.specialBlock_eq_bot_of_finrank_eq_one hh (by omega))
  have hf1 : 1 ≤ f₀ := hU.one_le
  have hE : Nat.card (AdjoinRoot h) = (2 ^ f₀) ^ 2 := by rw [hU.card, ← pow_mul, mul_comm]
  set e₁ : ↥(specialBlock Q x h) ≃* ↥(sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans (MulEquiv.subgroupCongr hrange) with he₁
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hsmall : ¬ (f₀ = 1 ∧ (n = 2 ∨ n = 3)) := by
    rintro ⟨hf, hn23⟩
    have hcard := (CFSG.LinearGroups.unitary_full_group_order hU hBsymm hBl hnW (by omega)).2.1
    apply orth_not_isSolvable_of_isQuasisimple hq
    haveI := Fintype.ofFinite ↥(specialBlock Q x h)
    rcases hn23 with h2' | h3'
    · rw [h2', show (2 : ℕ) ^ f₀ = 2 ^ 1 by rw [hf]] at hcard
      have e : ((2 ^ 1 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
          ∏ i ∈ Finset.Icc 2 2, (((2 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) = 6 := by decide +kernel
      have h6 : Nat.card ↥(specialBlock Q x h) = 2 ^ 1 * 3 ^ 1 := by
        rw [Nat.card_congr e₁.toEquiv]
        exact_mod_cast hcard.trans e
      exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
        Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact h6)
    · rw [h3', show (2 : ℕ) ^ f₀ = 2 ^ 1 by rw [hf]] at hcard
      have e : ((2 ^ 1 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
          ∏ i ∈ Finset.Icc 2 3, (((2 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) = 216 := by decide +kernel
      have h216 : Nat.card ↥(specialBlock Q x h) = 2 ^ 3 * 3 ^ 3 := by
        rw [Nat.card_congr e₁.toEquiv]
        exact_mod_cast hcard.trans e
      exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
        Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact h216)
  refine ⟨?_, Or.inl (orth_kline_selfDual hx hh hU B hBsymm hBl hbarK hrangeB (by rw [hnW]; exact hn2))⟩
  rcases Nat.lt_or_ge n 3 with hlt | hge
  ·
    have hn2' : n = 2 := by omega
    have hf2 : 2 ≤ f₀ := by
      by_contra hlt'
      exact hsmall ⟨by omega, Or.inl hn2'⟩
    obtain ⟨eSL⟩ := CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hU hBsymm hBl
      (by rw [hnW, hn2'])
    haveI : CharP ↥hU.fixedField 2 :=
      ((algebraMap ↥hU.fixedField (AdjoinRoot h)).charP_iff_charP 2).2 inferInstance
    obtain ⟨eZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sl 2 (e₁.trans eSL)
    have hlab : LargeEvenInLambda2 ⟨.A, 1, f₀⟩ := by
      show 1 ≤ f₀ ∧ 1 ≤ 1 ∧ (1 = 1 → 2 ≤ f₀)
      exact ⟨hf1, le_rfl, fun _ => hf2⟩
    refine ⟨⟨.A, 1, f₀⟩, hlab, (show LargeEvenLieTag.A ≠ .triD4 by decide),
      fun h => absurd h.1 (show LargeEvenLieTag.A ≠ .D by decide), orthRealized_of_centerQuot hq ?_⟩
    unfold CFSG.Assembly.LargeEvenRawDatum
    dsimp only
    unfold LargeEvenRecipeLinear
    refine ⟨↥hU.fixedField, inferInstance, inferInstance, hU.card_fixedField, ?_, ?_⟩
    · exact ⟨eZ.trans (orth_largeEvenProj_congr (largeEvenSLGroup_eq_statedSL 2).symm).some⟩
    · exact orth_matConj_SL_sub_inn fun c hc => by
        obtain ⟨c', hc', hc'2⟩ := orth_exists_pow_two_pow 1 c hc
        exact ⟨c', hc', by simpa using hc'2⟩
  ·
    have hnq : (n - 1 + 1, 2 ^ f₀) ≠ (3, 2) := by
      intro h32
      have h1 := Prod.mk.inj h32
      have hf : f₀ = 1 := by
        have h2 : 2 ^ f₀ = 2 ^ 1 := by rw [h1.2]; norm_num
        exact Nat.pow_right_injective (le_refl 2) h2
      exact hsmall ⟨hf, Or.inr (by omega)⟩
    have hlab : LargeEvenInLambda2 ⟨.twA, n - 1, f₀⟩ := by
      show 1 ≤ f₀ ∧ 2 ≤ n - 1 ∧ (n - 1 = 2 → 2 ≤ f₀)
      refine ⟨hf1, by omega, fun h2' => ?_⟩
      by_contra hlt'
      exact hsmall ⟨by omega, Or.inr (by omega)⟩
    obtain ⟨e₀, he₀⟩ := hU.exists_orthonormal_basis hBsymm hBl
    have hfin : Module.finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) = n - 1 + 1 := by
      rw [hnW]
      omega
    set e := e₀.reindex (finCongr hfin) with he
    have he' : ∀ i j, B (e i) (e j) = if i = j then 1 else 0 := by
      intro i j
      rw [he, Module.Basis.reindex_apply, Module.Basis.reindex_apply, he₀]
      simp only [EmbeddingLike.apply_eq_iff_eq]
    set κ : ↥(supportedBlock Q x h) →* GL (Fin (n - 1 + 1)) (AdjoinRoot h) := orthBlockMatrix e with hκ
    have hSU : ∀ M : GL (Fin (n - 1 + 1)) (AdjoinRoot h),
        M ∈ LargeEvenSUGroup (Fin (n - 1 + 1)) (AdjoinRoot h) (2 ^ f₀) ↔
          Matrix.GeneralLinearGroup.toLin' e M ∈ sesqSpecialUnitaryGroup B := by
      intro M
      rw [toLin'_mem_sesqSpecialUnitaryGroup_iff hU e he', largeEvenSUGroup_eq_statedSU,
        ← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hE,
        ← CFSG.RankThree.CentralLiftU.barEquiv_eq_unitaryInvolution hU]
    have hs : IsSimpleGroup (LargeEvenProj (LargeEvenSUGroup (Fin (n - 1 + 1)) (AdjoinRoot h) (2 ^ f₀))) := by
      rw [largeEvenSUGroup_eq_statedSU]
      exact CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU _ 2 f₀ hE _ (by omega) hnq
    obtain ⟨Θ₁, hΘs, hΘk, hreal⟩ := orth_realize_of_model (specialBlock_le_supportedBlock h)
      (fun L hL ω hω => conj_mem_specialBlock (supportedBlock_le_isometryCentralizer h hL) hω)
      (H := LargeEvenSUGroup (Fin (n - 1 + 1)) (AdjoinRoot h) (2 ^ f₀))
      (S := LargeEvenGUSet (Fin (n - 1 + 1)) (AdjoinRoot h) (2 ^ f₀)) κ
      (fun ω hω => by
        rw [hSU, hκ, toLin'_orthBlockMatrix, ← hrange]
        exact ⟨⟨ω, hω⟩, rfl⟩)
      (fun g hg => by
        rw [hSU, ← hrange] at hg
        obtain ⟨⟨ω, hω⟩, hωg⟩ := hg
        refine ⟨ω, hω, ?_⟩
        apply (Matrix.GeneralLinearGroup.toLin' e).injective
        rw [hκ, toLin'_orthBlockMatrix]
        exact hωg)
      (fun ω ω' hω hω' hωω' => by
        have h1 : blockGL Q x h ⟨ω, specialBlock_le_supportedBlock h hω⟩ =
            blockGL Q x h ⟨ω', specialBlock_le_supportedBlock h hω'⟩ := by
          rw [← toLin'_orthBlockMatrix e, ← toLin'_orthBlockMatrix e]
          exact congrArg _ hωω'
        exact congrArg Subtype.val (hx.blockGL_injective hh h1))
      (fun A hA => by
        obtain ⟨μ, hμ0, hμq, hAμ⟩ := hA
        have hq2 : 2 ≤ 2 ^ f₀ := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) hf1
        obtain ⟨c, hc0, hcq⟩ := orth_exists_norm_eq hq2 hE hμ0 hμq
        set s : GL (Fin (n - 1 + 1)) (AdjoinRoot h) :=
          Matrix.GeneralLinearGroup.scalar (Fin (n - 1 + 1)) (Units.mk0 c hc0)⁻¹ with hs
        set A' : GL (Fin (n - 1 + 1)) (AdjoinRoot h) := s * A with hA'
        have hA'val : (A' : Matrix (Fin (n - 1 + 1)) (Fin (n - 1 + 1)) (AdjoinRoot h)) =
            c⁻¹ • (A : Matrix (Fin (n - 1 + 1)) (Fin (n - 1 + 1)) (AdjoinRoot h)) := by
          rw [hA', hs, Units.val_mul]
          simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_eq_diagonal_mul]
        have hconj : CFSG.LieType.Universal.Unitary.conjTr hU.barEquiv
            (A' : Matrix (Fin (n - 1 + 1)) (Fin (n - 1 + 1)) (AdjoinRoot h)) *
              (A' : Matrix (Fin (n - 1 + 1)) (Fin (n - 1 + 1)) (AdjoinRoot h)) = 1 := by
          unfold CFSG.LieType.Universal.Unitary.conjTr
          have hmap : (A' : Matrix (Fin (n - 1 + 1)) (Fin (n - 1 + 1)) (AdjoinRoot h)).map hU.barEquiv =
              (c⁻¹) ^ 2 ^ f₀ • (A : Matrix (Fin (n - 1 + 1)) (Fin (n - 1 + 1)) (AdjoinRoot h)).map
                (· ^ 2 ^ f₀) := by
            ext i j
            simp [hA'val, UnitaryFieldData.barEquiv_apply, hbarq, mul_pow]
          rw [hmap, Matrix.transpose_smul, Matrix.smul_mul, hA'val, Matrix.mul_smul, hAμ, smul_smul,
            smul_smul, ← pow_succ, inv_pow, hcq, inv_mul_cancel₀ hμ0, one_smul]
        have hpresA : ∀ u w, B (((Matrix.GeneralLinearGroup.toLin' e A' :
            LinearMap.GeneralLinearGroup (AdjoinRoot h) (primaryComponent x.toLinearMap h)) :
              Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) u)
            (((Matrix.GeneralLinearGroup.toLin' e A' :
              LinearMap.GeneralLinearGroup (AdjoinRoot h) (primaryComponent x.toLinearMap h)) :
                Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) w) = B u w := by
          intro u w
          rw [form_eq_herm hU e he', form_eq_herm hU e he', equivFun_toLin'_apply, equivFun_toLin'_apply,
            CFSG.ClassicalGroups.Unitary.herm_mulVec, hconj, Matrix.one_mulVec]
        obtain ⟨L, hL⟩ := (hrangeB _).2 hpresA
        refine ⟨L.1, L.2, fun g _ => ?_⟩
        have hκL : κ ⟨L.1, L.2⟩ = A' := by
          apply (Matrix.GeneralLinearGroup.toLin' e).injective
          rw [hκ, toLin'_orthBlockMatrix]
          exact hL
        rw [hκL, hA', mul_inv_rev]
        have hsc : ∀ X : GL (Fin (n - 1 + 1)) (AdjoinRoot h), s * X = X * s := fun X =>
          CFSG.LieType.SemisimpleCentralizers.HeldLang.scalar_mul_comm _ X
        calc s * A * g * (A⁻¹ * s⁻¹) = s * (A * g * A⁻¹) * s⁻¹ := by group
          _ = A * g * A⁻¹ := by rw [hsc (A * g * A⁻¹), mul_inv_cancel_right])
    refine ⟨⟨.twA, n - 1, f₀⟩, hlab, (show LargeEvenLieTag.twA ≠ .triD4 by decide),
      fun h => absurd h.1 (show LargeEvenLieTag.twA ≠ .D by decide), ?_⟩
    unfold OrthRealized CFSG.Assembly.LargeEvenRawDatum
    dsimp only
    unfold LargeEvenRecipeUnitary
    haveI := hs
    exact ⟨AdjoinRoot h, inferInstance, inferInstance, hE, hs, orth_exists_noncomm_of_surjective hq.1 Θ₁ hΘs,
      Θ₁, hΘs, hΘk, hreal⟩

end SelfDual

end CFSG.LocalAnalysis.GLTheoremA.K155XOr

namespace CFSG.LocalAnalysis.GLTheoremA.K155XOr

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.K155X
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.LieType.Universal.Spin (quadPlus quadMinus quadPlus_apply quadMinus_apply polar_quadPlus polar_quadMinus)
open Polynomial QuadraticMap

section FixedLine

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem orth_kline_fixed (hx : OddOrderIsometry Q p x) {F : Subgroup (V ≃ₗ[K] V)}
    (T : fixedSpace x →ₗ[K] fixedSpace x) (hT0 : T ≠ 0) (g : K → V ≃ₗ[K] V) (hgF : ∀ c, g c ∈ F)
    (hgS : ∀ c, g c ∈ supportedBlock Q x (X - 1))
    (hgW : ∀ (c : K) (w : fixedSpace x), g c (w : V) = (w : V) + c • ((T w : fixedSpace x) : V)) :
    ∃ N : V →ₗ[K] V, N ≠ 0 ∧ ∀ c : K, ∃ ω ∈ F, ∀ v, ω v = v + c • N v := by
  set N : V →ₗ[K] V := ((g 1 : V ≃ₗ[K] V) : V →ₗ[K] V) - LinearMap.id with hN
  have hNW : ∀ w : fixedSpace x, N (w : V) = ((T w : fixedSpace x) : V) := by
    intro w
    rw [hN, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, hgW 1 w, one_smul,
      add_sub_cancel_left]
  have hNr : ∀ r ∈ othersSpace x.toLinearMap (X - 1), N r = 0 := by
    intro r hr
    rw [hN, LinearMap.sub_apply, LinearEquiv.coe_coe, (mem_supportedBlock.mp (hgS 1)).2 r hr,
      LinearMap.id_apply, sub_self]
  refine ⟨N, fun hN0 => hT0 (LinearMap.ext fun w => Subtype.ext ?_), fun c => ⟨g c, hgF c, fun v => ?_⟩⟩
  · rw [← hNW w, hN0]
    rfl
  obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hx.fixed_others.1 v
  rw [map_add, map_add, smul_add, (mem_supportedBlock.mp (hgS c)).2 r hr, hNr r hr, smul_zero, add_zero]
  have h1 := hgW c ⟨w, hw⟩
  have h2 := hNW ⟨w, hw⟩
  simp only at h1 h2
  rw [h1, h2]
  abel

end FixedLine

section Hyperbolic

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem orth_exists_hyperbolic_fixed (hx : OddOrderIsometry Q p x) {s : ℕ} (hs : 2 ≤ s)
    (hdim : Module.finrank K (fixedSpace x) = 2 * s) :
    ∃ e f : V, e ∈ fixedSpace x ∧ f ∈ fixedSpace x ∧ Q e = 0 ∧ Q f = 0 ∧ polar Q e f = 1 := by
  rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus (Q.comp (fixedSpace x).subtype)
    hx.polarBilin_fixed_nondegenerate (by omega) hdim with hψ | ⟨b, c, -, hψ⟩
  · obtain ⟨ψ⟩ := hψ
    set i0 : Fin s := ⟨0, by omega⟩
    set e' : Fin s ⊕ Fin s → K := Pi.single (Sum.inl i0) 1 with he'
    set f' : Fin s ⊕ Fin s → K := Pi.single (Sum.inr i0) 1 with hf'
    refine ⟨(ψ.symm e' : fixedSpace x), (ψ.symm f' : fixedSpace x), (ψ.symm e').2, (ψ.symm f').2, ?_, ?_, ?_⟩
    · have := ψ.symm.map_app e'
      rw [QuadraticMap.comp_apply, Submodule.subtype_apply] at this
      rw [this, quadPlus_apply]
      simp [he']
    · have := ψ.symm.map_app f'
      rw [QuadraticMap.comp_apply, Submodule.subtype_apply] at this
      rw [this, quadPlus_apply]
      simp [hf']
    · have h1 : polar Q ((ψ.symm e' : fixedSpace x) : V) ((ψ.symm f' : fixedSpace x) : V) =
          polar (Q.comp (fixedSpace x).subtype) (ψ.symm e') (ψ.symm f') := rfl
      have h2 : polar (Q.comp (fixedSpace x).subtype) (ψ.symm e') (ψ.symm f') = polar (quadPlus s K) e' f' := by
        simp only [polar, ← map_add, ψ.symm.map_app]
      rw [h1, h2, polar_quadPlus, Finset.sum_eq_single i0]
      · simp [he', hf']
      · intro i _ hi
        simp [he', hf', Pi.single_apply, hi]
      · simp
  · obtain ⟨ψ⟩ := hψ
    set i0 : Fin (s - 1) := ⟨0, by omega⟩
    set e' : Fin (s - 1) ⊕ Fin (s - 1) ⊕ Fin 2 → K := Pi.single (Sum.inl i0) 1 with he'
    set f' : Fin (s - 1) ⊕ Fin (s - 1) ⊕ Fin 2 → K := Pi.single (Sum.inr (Sum.inl i0)) 1 with hf'
    refine ⟨(ψ.symm e' : fixedSpace x), (ψ.symm f' : fixedSpace x), (ψ.symm e').2, (ψ.symm f').2, ?_, ?_, ?_⟩
    · have := ψ.symm.map_app e'
      rw [QuadraticMap.comp_apply, Submodule.subtype_apply] at this
      rw [this, quadMinus_apply]
      simp [he']
    · have := ψ.symm.map_app f'
      rw [QuadraticMap.comp_apply, Submodule.subtype_apply] at this
      rw [this, quadMinus_apply]
      simp [hf']
    · have h1 : polar Q ((ψ.symm e' : fixedSpace x) : V) ((ψ.symm f' : fixedSpace x) : V) =
          polar (Q.comp (fixedSpace x).subtype) (ψ.symm e') (ψ.symm f') := rfl
      have h2 : polar (Q.comp (fixedSpace x).subtype) (ψ.symm e') (ψ.symm f') =
          polar (quadMinus s K b c) e' f' := by
        simp only [polar, ← map_add, ψ.symm.map_app]
      rw [h1, h2, polar_quadMinus, Finset.sum_eq_single i0]
      · simp [he', hf']
      · intro i _ hi
        simp [he', hf', Pi.single_apply, hi]
      · simp

theorem orth_obstruction_fixed [CharP K 2] (hx : OddOrderIsometry Q p x) (hQ : (polarBilin Q).Nondegenerate)
    {s : ℕ} (hs : 2 ≤ s) (hdim : Module.finrank K (fixedSpace x) = 2 * s) :
    OrthObstruction (supportedFixedDerived Q x) := by
  obtain ⟨e, f, heW, hfW, he, hf, hef⟩ := orth_exists_hyperbolic_fixed hx hs hdim
  exact Or.inr fun μ hμ => orth_trace_witness_fixed hx he hf hef heW hfW
    (CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Q hQ) μ hμ

end Hyperbolic

section InnRecipes

variable {G₀ : Type} [Group G₀] {J₀ : Subgroup G₀}

theorem orth_not_isQuasisimple_of_comm {G : Type*} [Group G] (h : ∀ a b : G, a * b = b * a) :
    ¬ CFSG.IsQuasisimple G := by
  rintro ⟨-, -, a, b, hab⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem orth_linear_inn_data (hq : CFSG.IsQuasisimple ↥J₀) {E : Type} [Field E] [Finite E] [CharP E 2]
    {d j N : ℕ} (hdj : d = 2 ^ j) (hd2 : 2 ≤ d) (h22 : d ≠ 2 ∨ Nat.card E ≠ 2) (hN : Nat.card E = N)
    (e : ↥J₀ ≃* ↥(StatedSL d E)) :
    LargeEvenRecipeLinear d N fun R _ I _ => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      I ⊆ LargeEvenInnSet R ∧ ∃ Θ₁ : ↥J₀ →* R, Function.Surjective Θ₁ ∧ Θ₁.ker ≤ Subgroup.center ↥J₀ := by
  have h3 : Nat.card E ≠ 3 := by
    haveI := Fintype.ofFinite E
    obtain ⟨m, -, hm⟩ := FiniteField.card E 2
    rw [Nat.card_eq_fintype_card, hm]
    intro h
    have h2 : 2 ∣ 3 := h ▸ dvd_pow_self 2 m.ne_zero
    omega
  set e' : ↥J₀ ≃* ↥(LargeEvenSLGroup (Fin d) E) :=
    e.trans (MulEquiv.subgroupCongr (largeEvenSLGroup_eq_statedSL d).symm) with he'
  have hs : IsSimpleGroup (LargeEvenProj (LargeEvenSLGroup (Fin d) E)) := by
    rw [largeEvenSLGroup_eq_statedSL]
    exact CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL E hd2 h22 (Or.inr h3)
  haveI := hs
  set Θ₁ : ↥J₀ →* LargeEvenProj (LargeEvenSLGroup (Fin d) E) :=
    (LargeEvenProjMk _).comp e'.toMonoidHom with hΘ₁
  have hΘs : Function.Surjective Θ₁ := (QuotientGroup.mk'_surjective _).comp e'.surjective
  refine ⟨E, inferInstance, inferInstance, hN, hs, orth_exists_noncomm_of_surjective hq.1 Θ₁ hΘs,
    orth_matConj_SL_sub_inn fun c hc => ?_, Θ₁, hΘs,
    orth_ker_mk'_comp_le_center e' _ (orth_statedScalars_subgroupOf_le_center _)⟩
  obtain ⟨c', hc', hc'j⟩ := orth_exists_pow_two_pow j c hc
  exact ⟨c', hc', by rw [hdj]; exact hc'j⟩

theorem orth_unitary4_inn_data (hq : CFSG.IsQuasisimple ↥J₀) {E : Type} [Field E] [Finite E] [CharP E 2]
    {f : ℕ} (hf : 1 ≤ f) (hE : Nat.card E = (2 ^ f) ^ 2) (e : ↥J₀ ≃* ↥(StatedSU 4 (2 ^ f) E)) :
    LargeEvenRecipeUnitary 4 (2 ^ f) fun R _ I _ => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      I ⊆ LargeEvenInnSet R ∧ ∃ Θ₁ : ↥J₀ →* R, Function.Surjective Θ₁ ∧ Θ₁.ker ≤ Subgroup.center ↥J₀ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup (LargeEvenProj (LargeEvenSUGroup (Fin 4) E (2 ^ f))) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU E 2 f hE 4 (by norm_num)
      (fun h => absurd (congrArg Prod.fst h) (by norm_num))
  haveI := hs
  set e' : ↥J₀ ≃* ↥(LargeEvenSUGroup (Fin 4) E (2 ^ f)) :=
    e.trans (MulEquiv.subgroupCongr (largeEvenSUGroup_eq_statedSU 4 (2 ^ f)).symm) with he'
  set Θ₁ : ↥J₀ →* LargeEvenProj (LargeEvenSUGroup (Fin 4) E (2 ^ f)) :=
    (LargeEvenProjMk _).comp e'.toMonoidHom with hΘ₁
  have hΘs : Function.Surjective Θ₁ := (QuotientGroup.mk'_surjective _).comp e'.surjective
  exact ⟨E, inferInstance, inferInstance, hE, hs, orth_exists_noncomm_of_surjective hq.1 Θ₁ hΘs,
    orth_matConj_SU_sub_inn rfl hf hE, Θ₁, hΘs,
    orth_ker_mk'_comp_le_center e' _ (orth_statedScalars_subgroupOf_le_center _)⟩

end InnRecipes

section DetFactor

open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] [CharP K 2]

theorem orth_nonempty_mulEquiv_determinantFactor (F : Subgroup (DeterminantIsometries K))
    (hF : F = determinantLeftFactor K ∨ F = determinantRightFactor K) :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) K ≃* ↥F) := by
  have hsq : ∀ c : Kˣ, c ^ 2 = 1 → c = 1 := by
    intro c hc
    have h1 : ((c : K) - 1) ^ 2 = 0 := by
      have h2 : (c : K) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
      have h3 : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination h2 - (c : K) * h3 + h3
    exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h1))
  rcases hF with rfl | rfl
  · have hinj : Function.Injective ((specialRho (K := K)).comp (MonoidHom.inl _ _)) := by
      rw [injective_iff_map_eq_one]
      intro A hA
      obtain ⟨c, hc2, hcA, -⟩ := (specialRho_eq_one_iff (A, (1 : Matrix.SpecialLinearGroup (Fin 2) K))).1 hA
      rw [hsq c hc2, map_one] at hcA
      exact Matrix.SpecialLinearGroup.toGL_injective (hcA.trans (map_one _).symm)
    exact ⟨MonoidHom.ofInjective hinj⟩
  · have hinj : Function.Injective ((specialRho (K := K)).comp (MonoidHom.inr _ _)) := by
      rw [injective_iff_map_eq_one]
      intro A hA
      obtain ⟨c, hc2, -, hcA⟩ := (specialRho_eq_one_iff ((1 : Matrix.SpecialLinearGroup (Fin 2) K), A)).1 hA
      rw [hsq c hc2, map_one] at hcA
      exact Matrix.SpecialLinearGroup.toGL_injective (hcA.trans (map_one _).symm)
    exact ⟨MonoidHom.ofInjective hinj⟩

end DetFactor

section Split

open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem orthBlockData_fixed_split (hx : OddOrderIsometry Q p x) (hlist : FixedLayerListed Q x)
    {F : Subgroup (V ≃ₗ[K] V)} (hFq : CFSG.IsQuasisimple ↥F) (hFle : F ≤ supportedFixedDerived Q x)
    (hFn : (F.subgroupOf (supportedFixedDerived Q x)).Normal)
    (hsplit : Module.finrank K (fixedSpace x) = 4 ∧ ∃ S : Submodule K (fixedSpace x),
      Module.finrank K S = 2 ∧ ∀ y ∈ S, (Q.comp (fixedSpace x).subtype) y = 0)
    {f : ℕ} (hK : Nat.card K = 2 ^ f) : OrthBlockData p F := by
  classical
  set R := Q.comp (fixedSpace x).subtype with hRdef
  have hR := hx.polarBilin_fixed_nondegenerate
  have hK2 : Nat.card K ≠ 2 := fun h => hlist.2 (Or.inr ⟨hsplit, Or.inl h⟩)
  have hK3 : Nat.card K ≠ 3 := fun h => hlist.2 (Or.inr ⟨hsplit, Or.inr h⟩)
  have hf2 : 2 ≤ f := by
    by_contra hlt
    interval_cases f
    · have := Finite.one_lt_card (α := K)
      rw [hK] at this
      norm_num at this
    · exact hK2 (by rw [hK]; norm_num)
  obtain ⟨ψ, e, -, he, hsup, hLq', hRq', hLn', hRn', -, -, -⟩ :=
    orthogonal_split_four_derived hK2 hK3 R hR hsplit.1 hsplit.2
  have hSFD : (commutator ↥(supportedBlock Q x (X - 1))).map
      (supportedBlock Q x (X - 1)).subtype = supportedFixedDerived Q x := by
    rw [Subgroup.map_subtype_commutator, hx.supportedFixedDerived_eq]
  have hFB : F ≤ supportedBlock Q x (X - 1) :=
    hFle.trans supportedFixedDerived_le_supportedBlock
  have hCB : ∀ g : ↥(supportedBlock Q x (X - 1)), (g : V ≃ₗ[K] V) ∈ supportedFixedDerived Q x →
      g ∈ commutator ↥(supportedBlock Q x (X - 1)) := by
    intro g hg
    rw [← hSFD] at hg
    obtain ⟨g', hg', hgg⟩ := hg
    rwa [show g = g' from Subtype.ext hgg.symm]
  have hmapC : (commutator ↥(supportedBlock Q x (X - 1))).map (fixedBlockEquiv hx).toMonoidHom =
      commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      (MonoidHom.range_eq_top (f := (fixedBlockEquiv hx).toMonoidHom)).2
        (fixedBlockEquiv hx).surjective]
  set L : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup R) :=
    (F.subgroupOf (supportedBlock Q x (X - 1))).map (fixedBlockEquiv hx).toMonoidHom with hL
  have hLle : L ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [← hmapC]
    exact ⟨g, hCB g (hFle hg), rfl⟩
  have hLn : (L.subgroupOf (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hLle]
    rintro _ k ⟨g, hg, rfl⟩ hk
    rw [← hmapC] at hk
    obtain ⟨c, hc, rfl⟩ := hk
    refine ⟨c * g * c⁻¹, ?_, by simp⟩
    have hcS : (c : V ≃ₗ[K] V) ∈ supportedFixedDerived Q x := hSFD ▸ ⟨c, hc, rfl⟩
    exact (Subgroup.normal_subgroupOf_iff hFle).1 hFn _ _ hg hcS
  set eFL : ↥F ≃* ↥L := (Subgroup.subgroupOfEquivOfLe hFB).symm.trans
    ((F.subgroupOf (supportedBlock Q x (X - 1))).equivMapOfInjective
      (fixedBlockEquiv hx).toMonoidHom (fixedBlockEquiv hx).injective) with heFL
  have hLq : CFSG.IsQuasisimple ↥L := CFSG.LocalCores.isQuasisimple_of_mulEquiv eFL hFq
  haveI : Finite (fixedSpace x) := Module.finite_of_finite K
  haveI : Finite ((fixedSpace x) ≃ₗ[K] (fixedSpace x)) :=
    Finite.of_injective (fun g : (fixedSpace x) ≃ₗ[K] (fixedSpace x) => (g : fixedSpace x → fixedSpace x))
      fun g₁ g₂ h => LinearEquiv.ext (congrFun h)
  set Lf := (determinantLeftFactor K).map e.symm.toMonoidHom with hLf
  set Rf := (determinantRightFactor K).map e.symm.toMonoidHom with hRf
  have hLfC : Lf ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
    rw [hsup]
    exact le_sup_left
  have hRfC : Rf ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
    rw [hsup]
    exact le_sup_right
  have hFc : ∀ i, CFSG.Open.IsComponentOf (![Lf, Rf] i)
      (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)) := by
    intro i
    fin_cases i
    · exact ⟨hLfC, CFSG.Open.IsSubnormal.step hLfC hLn' (CFSG.Open.IsSubnormal.refl _),
        CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hLq'⟩
    · exact ⟨hRfC, CFSG.Open.IsSubnormal.step hRfC hRn' (CFSG.Open.IsSubnormal.refl _),
        CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hRq'⟩
  have hperf : ∀ P : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup R),
      P ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) → commutator ↥P = ⊤ →
      P ≤ ⨆ i, ![Lf, Rf] i := by
    intro P hP _
    refine hP.trans (hsup.le.trans (sup_le ?_ ?_))
    · exact le_iSup (fun i => ![Lf, Rf] i) 0
    · exact le_iSup (fun i => ![Lf, Rf] i) 1
  have hLc : CFSG.Open.IsComponentOf L (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)) :=
    ⟨hLle, CFSG.Open.IsSubnormal.step hLle hLn (CFSG.Open.IsSubnormal.refl _),
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hLq⟩
  obtain ⟨i, hi⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.component_mem_named_factors _ hFc hperf hLc
  have hact : ∀ (z : DeterminantIsometries K) (w : fixedSpace x),
      (((e.symm z : TauCeti.QuadraticMap.orthogonalGroup R) : fixedSpace x ≃ₗ[K] fixedSpace x) w) =
        ψ.symm (z.val (ψ w)) := by
    intro z w
    have h := he (e.symm z) (ψ w)
    rw [MulEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at h
    rw [h, LinearEquiv.symm_apply_apply]
  have key : ∀ Fac : Subgroup (DeterminantIsometries K),
      (Fac = determinantLeftFactor K ∨ Fac = determinantRightFactor K) → L = Fac.map e.symm.toMonoidHom →
      (∃ M : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K, M ≠ 0 ∧
        ∀ c : K, ∃ z ∈ Fac, ∀ X, z.val X = X + c • M X) → OrthBlockData p F := by
    intro Fac hFac hLFac ⟨M, hM0, hline⟩
    set eLFac : ↥L ≃* ↥Fac := (MulEquiv.subgroupCongr hLFac).trans
      (Fac.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm with heLFac
    set eF : ↥F ≃* ↥(StatedSL 2 K) := eFL.trans (eLFac.trans
      ((orth_nonempty_mulEquiv_determinantFactor Fac hFac).some.symm.trans
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K))) with heF
    have hlab : LargeEvenInLambda2 ⟨.A, 1, f⟩ := by
      show 1 ≤ f ∧ 1 ≤ 1 ∧ (1 = 1 → 2 ≤ f)
      exact ⟨by omega, le_rfl, fun _ => hf2⟩
    refine ⟨⟨⟨.A, 1, f⟩, hlab, (show LargeEvenLieTag.A ≠ .triD4 by decide),
      fun h => absurd h.1 (show LargeEvenLieTag.A ≠ .D by decide), orthRealized_of_inn ?_⟩, Or.inl ?_⟩
    · unfold CFSG.Assembly.LargeEvenRawDatum
      dsimp only
      exact orth_linear_inn_data hFq (d := 1 + 1) (j := 1) rfl le_rfl (Or.inr hK2) hK eF
    ·
      set T : fixedSpace x →ₗ[K] fixedSpace x :=
        ψ.symm.toLinearMap ∘ₗ M ∘ₗ ψ.toLinearMap with hT
      have hT0 : T ≠ 0 := by
        intro h0
        apply hM0
        refine LinearMap.ext fun X => ?_
        have h1 := congrArg (fun F' : fixedSpace x →ₗ[K] fixedSpace x => ψ (F' (ψ.symm X))) h0
        simpa [hT] using h1
      choose z hzFac hz using hline
      set g : K → V ≃ₗ[K] V := fun c =>
        (((fixedBlockEquiv hx).symm (e.symm (⟨z c, hzFac c⟩ : ↥Fac) :
          TauCeti.QuadraticMap.orthogonalGroup R) : ↥(supportedBlock Q x (X - 1))) : V ≃ₗ[K] V) with hg
      refine orth_kline_fixed hx T hT0 g (fun c => ?_) (fun c => ((fixedBlockEquiv hx).symm _).2)
        (fun c w => ?_)
      · have hmemL : (e.symm (z c) : TauCeti.QuadraticMap.orthogonalGroup R) ∈ L := by
          rw [hLFac]
          exact ⟨z c, hzFac c, rfl⟩
        rw [hL, Subgroup.mem_map_equiv] at hmemL
        exact hmemL
      · have h1 := coe_fixedBlockEquiv hx ((fixedBlockEquiv hx).symm (e.symm (z c))) w
        rw [MulEquiv.apply_symm_apply, hact] at h1
        rw [hg]
        simp only
        rw [← h1, hz c (ψ w), map_add, map_smul, LinearEquiv.symm_apply_apply, Submodule.coe_add,
          Submodule.coe_smul]
        rfl
  fin_cases i
  · refine key _ (Or.inl rfl) hi ⟨LinearMap.mulLeft K !![0, 1; 0, 0], ?_, fun c => ?_⟩
    · intro h0
      have := congrArg (fun F' : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K =>
        F' 1 0 1) h0
      simp at this
    · refine ⟨specialRho (⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two]⟩, 1),
        ⟨_, rfl⟩, fun X => ?_⟩
      rw [specialRho_apply]
      dsimp only
      rw [inv_one, Matrix.SpecialLinearGroup.coe_one, mul_one, LinearMap.mulLeft_apply]
      have hA : (!![1, c; 0, 1] : Matrix (Fin 2) (Fin 2) K) = 1 + c • !![0, 1; 0, 0] := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp
      show !![1, c; 0, 1] * X = X + c • (!![0, 1; 0, 0] * X)
      rw [hA, add_mul, one_mul, smul_mul_assoc]
  · refine key _ (Or.inr rfl) hi ⟨LinearMap.mulRight K (-!![0, 1; 0, 0]), ?_, fun c => ?_⟩
    · intro h0
      have := congrArg (fun F' : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K =>
        F' 1 0 1) h0
      simp at this
    · refine ⟨specialRho (1, (⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two]⟩ :
        Matrix.SpecialLinearGroup (Fin 2) K)), ⟨_, rfl⟩, fun X => ?_⟩
      rw [specialRho_apply]
      dsimp only
      rw [Matrix.SpecialLinearGroup.coe_one, one_mul, LinearMap.mulRight_apply]
      show X * Matrix.adjugate !![1, c; 0, 1] = X + c • (X * -!![0, 1; 0, 0])
      rw [Matrix.adjugate_fin_two_of]
      have hB : (!![1, -c; -0, 1] : Matrix (Fin 2) (Fin 2) K) = 1 + c • -!![0, 1; 0, 0] := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp
      rw [hB, mul_add, mul_one, mul_smul_comm]

end Split

section Klein

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

theorem orth_klein_commutator_six (R : QuadraticForm K W) (hR : (polarBilin R).Nondegenerate)
    (hd : Module.finrank K W = 6) (hts : ∃ U : Submodule K W, Module.finrank K U = 3 ∧ ∀ u ∈ U, R u = 0) :
    Nonempty (commutator (TauCeti.QuadraticMap.orthogonalGroup R) ≃* StatedSL 4 K) := by
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.K159.Klein.exists_isometry_quadPlus_three R hR hd hts
  obtain ⟨hs, hp⟩ := CFSG.RankThree.PartOne.K159.Klein.sl4_isSimpleGroup_and_perfect (K := K)
  have hρinj := transportHom_injective e
    (CFSG.RankThree.PartOne.K159.Klein.rho : Matrix.SpecialLinearGroup (Fin 4) K →* _)
    CFSG.RankThree.PartOne.K159.Klein.rho_injective
  have hρmem := transportHom_mem e
    (CFSG.RankThree.PartOne.K159.Klein.rho : Matrix.SpecialLinearGroup (Fin 4) K →* _)
    CFSG.RankThree.PartOne.K159.Klein.rho_mem
  set O := TauCeti.QuadraticMap.orthogonalGroup R with hO
  set ρ := transportHom e
    (CFSG.RankThree.PartOne.K159.Klein.rho : Matrix.SpecialLinearGroup (Fin 4) K →* _) with hρ
  have hle : ρ.range ≤ O := by
    rintro _ ⟨g, rfl⟩
    exact hρmem g
  have hcard : Nat.card O = 2 * Nat.card (Matrix.SpecialLinearGroup (Fin 4) K) := by
    rw [CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_congr e,
      CFSG.RankThree.PartOne.K159.Klein.card_orthogonalGroup_quadPlus_three]
  obtain ⟨-, -, -, -, -, -, hcomm, -⟩ := derived_of_index_two_model O ρ hρinj hle hcard
  have h1 : (commutator ↥O).map O.subtype = ρ.range := by
    rw [Subgroup.map_subtype_commutator, hcomm]
  let e1 : commutator ↥O ≃* ρ.range :=
    (Subgroup.equivMapOfInjective _ O.subtype O.subtype_injective).trans (MulEquiv.subgroupCongr h1)
  let e2 : ρ.range ≃* Matrix.SpecialLinearGroup (Fin 4) K := (MonoidHom.ofInjective hρinj).symm
  exact ⟨e1.trans (e2.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 K))⟩

end Klein

section FixedMain

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem orth_eq_supportedFixedDerived (hx : OddOrderIsometry Q p x) {F : Subgroup (V ≃ₗ[K] V)}
    (hFq : CFSG.IsQuasisimple ↥F) (hFle : F ≤ supportedFixedDerived Q x)
    (hFn : (F.subgroupOf (supportedFixedDerived Q x)).Normal)
    (hC : CFSG.IsQuasisimple
      ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)))) :
    F = supportedFixedDerived Q x := by
  have hsq : CFSG.IsQuasisimple ↥(supportedFixedDerived Q x) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((CFSG.RankThree.PartOne.orthDerivedEquivCommutator _).trans (supportedFixedDerivedEquiv hx).symm) hC
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hsq hFn with h | h
  · exact le_antisymm hFle (Subgroup.subgroupOf_eq_top.1 h)
  · exfalso
    refine orth_not_isQuasisimple_of_comm (fun a b => ?_) hFq
    have ha : (⟨a.1, hFle a.2⟩ : ↥(supportedFixedDerived Q x)) ∈
        F.subgroupOf (supportedFixedDerived Q x) := Subgroup.mem_subgroupOf.2 a.2
    have hc := Subgroup.mem_center_iff.1 (h ha) ⟨b.1, hFle b.2⟩
    exact Subtype.ext (congrArg Subtype.val hc).symm

theorem orthBlockData_fixed (hx : OddOrderIsometry Q p x) (hQ : (polarBilin Q).Nondegenerate)
    (hlist : FixedLayerListed Q x) {F : Subgroup (V ≃ₗ[K] V)}
    (hFq : CFSG.IsQuasisimple ↥F) (hFle : F ≤ supportedFixedDerived Q x)
    (hFn : (F.subgroupOf (supportedFixedDerived Q x)).Normal) :
    OrthBlockDataW F ∧ (OrthBlockData p F ∨
      (p = 3 ∧ F = supportedFixedDerived Q x ∧
        Nonempty ((Q.comp (fixedSpace x).subtype).IsometryEquiv (quadPlus 4 K)))) := by
  classical
  set R := Q.comp (fixedSpace x).subtype with hRdef
  have hR := hx.polarBilin_fixed_nondegenerate
  obtain ⟨s, hs⟩ : ∃ s, Module.finrank K (fixedSpace x) = 2 * s := by
    obtain ⟨r, hr⟩ := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo R hR
    exact ⟨r, by omega⟩
  have hs2 : 2 ≤ s := by
    have := hlist.1
    omega
  obtain ⟨f, hK⟩ : ∃ f : ℕ, Nat.card K = 2 ^ f := by
    haveI := Fintype.ofFinite K
    obtain ⟨m, -, hm⟩ := FiniteField.card K 2
    exact ⟨m, by rw [Nat.card_eq_fintype_card, hm]⟩
  have hf1 : 1 ≤ f := by
    by_contra hlt
    have h1 := Finite.one_lt_card (α := K)
    rw [hK, show f = 0 by omega, pow_zero] at h1
    exact lt_irrefl 1 h1
  by_cases hsplit : Module.finrank K (fixedSpace x) = 4 ∧ ∃ S : Submodule K (fixedSpace x),
      Module.finrank K S = 2 ∧ ∀ y ∈ S, R y = 0
  · have hB := orthBlockData_fixed_split (p := p) hx hlist hFq hFle hFn hsplit hK
    exact ⟨orthBlockDataW_of_orthBlockData hB, Or.inl hB⟩
  have hC := orthogonal_regular_space_derived_quasisimple R hR hlist.1 hlist.2 hsplit
  have hF := orth_eq_supportedFixedDerived hx hFq hFle hFn hC
  subst hF
  have hobs := orth_obstruction_fixed hx hQ hs2 hs
  have finish : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag ≠ .triD4 →
      ¬ (lab.tag = .D ∧ lab.rank = 4 ∧ p = 3) → OrthRealized lab (supportedFixedDerived Q x) →
      OrthBlockDataW (supportedFixedDerived Q x) ∧ (OrthBlockData p (supportedFixedDerived Q x) ∨
        (p = 3 ∧ supportedFixedDerived Q x = supportedFixedDerived Q x ∧
          Nonempty ((Q.comp (fixedSpace x).subtype).IsometryEquiv (quadPlus 4 K)))) :=
    fun lab hlab htri hD hraw => ⟨⟨⟨lab, hlab, htri, hraw⟩, hobs⟩,
      Or.inl ⟨⟨lab, hlab, htri, hD, hraw⟩, hobs⟩⟩
  rcases Nat.lt_or_ge s 4 with hs4 | hs4
  · rcases Nat.lt_or_ge s 3 with hs3 | hs3
    ·
      have hs22 : s = 2 := by omega
      have hts : ∀ U : Submodule K (fixedSpace x), Module.finrank K U = 2 → ∃ u ∈ U, R u ≠ 0 := by
        intro U hU
        by_contra hcon
        push Not at hcon
        exact hsplit ⟨by omega, U, hU, hcon⟩
      obtain ⟨E, _, _, _, hE, ⟨eSL⟩⟩ :=
        CFSG.RankThree.PartOne.K159.exists_orthDerived_four_sl2 R hR (by omega) hts
      have hE' : Nat.card E = (2 ^ f) ^ 2 := by rw [hE, hK]
      have hE2 : Nat.card E ≠ 2 := by
        rw [hE']
        have : 2 ^ 1 < (2 ^ f) ^ 2 := by
          calc 2 ^ 1 < 2 ^ (2 * f) := Nat.pow_lt_pow_right (by norm_num) (by omega)
            _ = (2 ^ f) ^ 2 := by rw [← pow_mul, mul_comm]
        omega
      refine finish ⟨.twD, 2, f⟩ (by show 1 ≤ f ∧ 2 ≤ 2; exact ⟨hf1, le_rfl⟩)
        (show LargeEvenLieTag.twD ≠ .triD4 by decide)
        (fun h => absurd h.1 (show LargeEvenLieTag.twD ≠ .D by decide)) (orthRealized_of_inn ?_)
      unfold CFSG.Assembly.LargeEvenRawDatum
      dsimp only
      simp only [↓reduceIte]
      exact orth_linear_inn_data hFq (d := 2) (j := 1) rfl le_rfl (Or.inr hE2) hE'
        ((supportedFixedDerivedEquiv hx).trans
          (eSL.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 E)))
    · have hs33 : s = 3 := by omega
      by_cases hT : ∃ U : Submodule K (fixedSpace x), Module.finrank K U = 3 ∧ ∀ u ∈ U, R u = 0
      ·
        obtain ⟨κ⟩ := orth_klein_commutator_six R hR (by omega) hT
        refine finish ⟨.D, 3, f⟩ (by show 1 ≤ f ∧ 3 ≤ 3; exact ⟨hf1, le_rfl⟩)
          (show LargeEvenLieTag.D ≠ .triD4 by decide)
          (fun h => absurd h.2.1 (show (3 : ℕ) ≠ 4 by decide)) (orthRealized_of_inn ?_)
        unfold CFSG.Assembly.LargeEvenRawDatum
        dsimp only
        simp only [↓reduceIte]
        exact orth_linear_inn_data hFq (d := 4) (j := 2) rfl (by norm_num) (Or.inl (by norm_num)) hK
          ((supportedFixedDerivedEquiv hx).trans ((CFSG.RankThree.PartOne.orthDerivedEquivCommutator R).symm.trans κ))
      ·
        have hts : ∀ U : Submodule K (fixedSpace x), Module.finrank K U = 3 → ∃ u ∈ U, R u ≠ 0 := by
          intro U hU
          by_contra hcon
          push Not at hcon
          exact hT ⟨U, hU, hcon⟩
        obtain ⟨E, _, _, D, ψ, hψ⟩ := exists_evenMinus_model R hR (n := 3) (by norm_num) (by omega) hts
        haveI : CharP E 2 := charP_two_of_algebra (K := K)
        haveI := D.finite_E
        let e1 : R.IsometryEquiv (evenNormTailForm D.N 2) :=
          { toLinearEquiv := ψ
            map_app' := fun w => hψ w }
        let e2 : R.IsometryEquiv D.sixForm := e1.trans D.sixIsometry
        obtain ⟨-, -, -, -, -, -, -, -, hinj, -, -, -, -, -, -, -, hcomm, -⟩ :=
          CFSG.RankThree.PartOne.even_minus_six_unitary_derived_model D
        have hrange : orthDerived D.sixForm = D.sixRho.range := hcomm
        let e3 : D.sixSU ≃* ↥(orthDerived D.sixForm) :=
          (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange.symm)
        obtain ⟨f', hU, hcard, hbar⟩ := D.exists_unitaryFieldData
        obtain ⟨e4⟩ := D.nonempty_sixSU_mulEquiv hU hbar
        let e5 : ↥(StatedSU 4 (2 ^ f') E) ≃* ↥(orthDerived R) :=
          e4.symm.trans (e3.trans (CFSG.RankThree.PartOne.orthDerivedEquiv e2).symm)
        have hE' : Nat.card E = (2 ^ f') ^ 2 := by rw [D.card_E, hcard]
        have hf1' : 1 ≤ f' := by
          by_contra hlt
          have h1 := Finite.one_lt_card (α := K)
          rw [hcard, show f' = 0 by omega, pow_zero] at h1
          exact lt_irrefl 1 h1
        refine finish ⟨.twD, 3, f'⟩ (by show 1 ≤ f' ∧ 2 ≤ 3; exact ⟨hf1', by norm_num⟩)
          (show LargeEvenLieTag.twD ≠ .triD4 by decide)
          (fun h => absurd h.1 (show LargeEvenLieTag.twD ≠ .D by decide)) (orthRealized_of_inn ?_)
        unfold CFSG.Assembly.LargeEvenRawDatum
        dsimp only
        simp only [show (3 : ℕ) ≠ 2 by decide, ↓reduceIte]
        exact orth_unitary4_inn_data hFq hf1' hE' ((supportedFixedDerivedEquiv hx).trans e5.symm)
  ·
    rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus R hR (by omega) hs with
      hψ | ⟨b, c, hirr, hψ⟩
    · obtain ⟨ψ⟩ := hψ
      have hraw := orthRealized_fixed_plus hx hs4 hK ψ hFq
      have hlab : LargeEvenInLambda2 ⟨.D, s, f⟩ := by
        show 1 ≤ f ∧ 3 ≤ s
        exact ⟨hf1, by omega⟩
      by_cases h43 : s = 4 ∧ p = 3
      · obtain ⟨rfl, h3⟩ := h43
        exact ⟨⟨⟨⟨.D, 4, f⟩, hlab, show LargeEvenLieTag.D ≠ .triD4 by decide, hraw⟩, hobs⟩,
          Or.inr ⟨h3, rfl, ⟨ψ⟩⟩⟩
      · exact finish ⟨.D, s, f⟩ hlab (show LargeEvenLieTag.D ≠ .triD4 by decide)
          (fun h => h43 ⟨h.2.1, h.2.2⟩) hraw
    · obtain ⟨ψ⟩ := hψ
      exact finish ⟨.twD, s, f⟩ (by show 1 ≤ f ∧ 2 ≤ s; exact ⟨hf1, by omega⟩)
        (show LargeEvenLieTag.twD ≠ .triD4 by decide)
        (fun h => absurd h.1 (show LargeEvenLieTag.twD ≠ .D by decide))
        (orthRealized_fixed_minus hx hs4 hK hirr ψ hFq)

end FixedMain



end CFSG.LocalAnalysis.GLTheoremA.K155XOr

namespace CFSG.LocalAnalysis.GLTheoremA.K155XOr

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.K155X
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
open Polynomial

theorem orthBlockClass_holds (p : ℕ) : OrthBlockClass p := by
  intro hp hp2 K _ _ _ d Q hQ x hx
  refine ⟨fun h hh hne1 hq => ?_, fun hlist F hFq hFle hFn => orthBlockData_fixed hx hQ hlist hFq hFle hFn⟩
  by_cases hself : h = reciprocalPolynomial h
  · exact orthBlockData_selfDual hx hp hp2 hh hne1 hself hq
  · exact orthBlockData_paired hx hp hp2 hh hne1 hself hq

section FieldForm


theorem l154OmegaFld_orth_of_d4 (hD4 : OrthD4Fact) : L154OmegaFld l154Orth :=
  l154OmegaFld_orth_of Y10GFldOrth.orthLabelDict_holds orthBlockClass_holds hD4

theorem l154OmegaFld_twOrth_of_d4 (hD4 : OrthD4Fact) : L154OmegaFld l154TwOrth :=
  l154OmegaFld_twOrth_of Y10GFldOrth.orthLabelDict_holds orthBlockClass_holds hD4

end FieldForm

section Clauses


theorem l154NIDOn_orth : L154NIDOn l154Orth :=
  (l154NIDOn_and_TD4On_of_omegaNT (l154OmegaNT_orth_of Y10GFldOrth.orthLabelDict_holds
    orthBlockClass_holds)).1

theorem l154TD4On_orth : L154TD4On l154Orth :=
  (l154NIDOn_and_TD4On_of_omegaNT (l154OmegaNT_orth_of Y10GFldOrth.orthLabelDict_holds
    orthBlockClass_holds)).2

theorem l154NIDOn_twOrth : L154NIDOn l154TwOrth :=
  (l154NIDOn_and_TD4On_of_omegaNT (l154OmegaNT_twOrth_of Y10GFldOrth.orthLabelDict_holds
    orthBlockClass_holds)).1

theorem l154TD4On_twOrth : L154TD4On l154TwOrth :=
  (l154NIDOn_and_TD4On_of_omegaNT (l154OmegaNT_twOrth_of Y10GFldOrth.orthLabelDict_holds
    orthBlockClass_holds)).2

end Clauses

end CFSG.LocalAnalysis.GLTheoremA.K155XOr
