module

public import CFSG.ClassicalInvolution.Phan.Defs
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.GH74.QTGen4.Leaves.F112.PSU32Model
public import CFSG.RankThree.PartOne.KC.UnitaryOrthonormalEigenbasis
public import CFSG.ClassicalInvolution.Phan.CenterScalars

public section

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.GH74.QTGen4.Leaves.F112
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
  CFSG.GH74.QTGen4.Leaves.F112.OmegaData

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.Open
open scoped BigOperators

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
private theorem card_eigenbasis_eq {V : Type*} [AddCommGroup V] [Module K V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq K] (b : Module.Basis ι K V)
    (f : Module.End K V) (μ : ι → K) (hf : ∀ i, f (b i) = μ i • b i) (lam : K) :
    (Finset.univ.filter (fun i => μ i = lam)).card
      = Module.finrank K (Module.End.eigenspace f lam) := by
  classical
  have hcoord : ∀ (v : V) (j : ι), b.repr (f v) j = μ j * b.repr v j := by
    intro v j
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    simp only [map_smul, hf, smul_smul]
    rw [map_sum]
    rw [Finsupp.finset_sum_apply]
    simp [Module.Basis.repr_self, Finsupp.single_apply, mul_comm]
  have hker : LinearMap.ker (f - lam • 1) = Submodule.span K (b '' {i | μ i = lam}) := by
    ext v
    rw [LinearMap.mem_ker, Module.Basis.mem_span_image]
    constructor
    · intro hv j hj
      have hj' : j ∈ (b.repr v).support := by simpa using hj
      rw [Finsupp.mem_support_iff] at hj'
      have h1 : f v = lam • v := by
        rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hv
        exact hv
      have h2 := congrArg (fun w => b.repr w j) h1
      rw [hcoord, map_smul, Finsupp.smul_apply, smul_eq_mul] at h2
      exact mul_right_cancel₀ hj' h2
    · intro hsub
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
      apply b.repr.injective
      ext j
      rw [hcoord, map_smul, Finsupp.smul_apply, smul_eq_mul]
      by_cases hj : b.repr v j = 0
      · rw [hj, mul_zero, mul_zero]
      · have hmem : j ∈ (b.repr v).support := by rwa [Finsupp.mem_support_iff]
        have := hsub hmem
        rw [this]
  rw [Module.End.eigenspace_def, hker]
  have hli : LinearIndependent K (fun i : {i : ι // μ i = lam} => b i.1) :=
    b.linearIndependent.comp _ Subtype.val_injective
  rw [show b '' {i | μ i = lam} = Set.range (fun i : {i : ι // μ i = lam} => b i.1) by
    ext v
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, i.2, rfl⟩]
  rw [finrank_span_eq_card hli, Fintype.card_subtype]

omit [Finite K] [CharP K 2] in
private theorem finrank_eigenspace_conj {V : Type*} [AddCommGroup V] [Module K V]
    (e : V ≃ₗ[K] V) (A B : Module.End K V)
    (hB : B = (e : V →ₗ[K] V) * A * (e.symm : V →ₗ[K] V)) (lam : K) :
    Module.finrank K (Module.End.eigenspace B lam)
      = Module.finrank K (Module.End.eigenspace A lam) := by
  have hBw : ∀ w : V, B ((e : V →ₗ[K] V) w) = (e : V →ₗ[K] V) (A w) := by
    intro w
    have hsymm : (e.symm : V →ₗ[K] V) ((e : V →ₗ[K] V) w) = w := e.symm_apply_apply w
    calc B ((e : V →ₗ[K] V) w) = ((e : V →ₗ[K] V) * A * (e.symm : V →ₗ[K] V))
          ((e : V →ₗ[K] V) w) := by rw [hB]
      _ = (e : V →ₗ[K] V) (A ((e.symm : V →ₗ[K] V) ((e : V →ₗ[K] V) w))) := rfl
      _ = (e : V →ₗ[K] V) (A w) := by rw [hsymm]
  have hmap : Module.End.eigenspace B lam
      = (Module.End.eigenspace A lam).map (e : V →ₗ[K] V) := by
    ext v
    rw [Module.End.mem_eigenspace_iff, Submodule.mem_map]
    constructor
    · intro hv
      refine ⟨(e.symm : V →ₗ[K] V) v, ?_, ?_⟩
      · rw [Module.End.mem_eigenspace_iff]
        have hsymm : (e : V →ₗ[K] V) ((e.symm : V →ₗ[K] V) v) = v := e.apply_symm_apply v
        have h' : B ((e : V →ₗ[K] V) ((e.symm : V →ₗ[K] V) v))
            = lam • (e : V →ₗ[K] V) ((e.symm : V →ₗ[K] V) v) := by
          rw [hsymm]
          exact hv
        rw [hBw] at h'
        have h2 := congrArg (fun x => (e.symm : V →ₗ[K] V) x) h'
        simpa using h2
      · exact e.apply_symm_apply v
    · rintro ⟨w, hw, rfl⟩
      rw [Module.End.mem_eigenspace_iff] at hw
      rw [hBw, hw, map_smul]
  rw [hmap, LinearEquiv.finrank_map_eq]

omit [Finite K] [CharP K 2] in
private theorem eigenspace_mul_inv {V : Type*} [AddCommGroup V] [Module K V]
    (A B : Module.End K V) (hAB : A * B = 1) (hBA : B * A = 1) {lam : K} (hlam : lam ≠ 0) :
    Module.End.eigenspace B lam = Module.End.eigenspace A lam⁻¹ := by
  ext v
  rw [Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff]
  constructor
  · intro h
    have h2 := congrArg (fun w => A w) h
    rw [map_smul] at h2
    have hAB' : A (B v) = v := by
      rw [← Module.End.mul_apply, hAB, Module.End.one_apply]
    rw [hAB'] at h2
    calc A v = lam⁻¹ • (lam • A v) := (inv_smul_smul₀ hlam (A v)).symm
      _ = lam⁻¹ • v := by rw [← h2]
  · intro h
    have h2 := congrArg (fun w => B w) h
    rw [map_smul] at h2
    have hBA' : B (A v) = v := by
      rw [← Module.End.mul_apply, hBA, Module.End.one_apply]
    rw [hBA'] at h2
    calc B v = lam • (lam⁻¹ • B v) := (smul_inv_smul₀ hlam (B v)).symm
      _ = lam • v := by rw [← h2]


theorem injective_of_ker_le_center (hK : Nat.card K = 4)
    (ρ : Su K 2 1 3 →* Su K 2 1 4)
    (hρ : ρ.ker ≤ Subgroup.center (Su K 2 1 3)) : Function.Injective ρ := by
  classical
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hσ : IsUnitaryInvolution (unitaryInvolution K 2 1) :=
    isUnitaryInvolution_unitaryInvolution hK'
  have hSU3 : SUid (unitaryInvolution K 2 1) 3 = StatedSU 3 2 K := by
    simpa using SUid_eq_statedSU (F := K) (p := 2) (f := 1) hK' 3
  let Z3 : Subgroup (Su K 2 1 3) :=
    (StatedScalars (Fin 3) K).subgroupOf (SUid (unitaryInvolution K 2 1) 3)
  have hZ3center : Z3 = Subgroup.center (Su K 2 1 3) := by
    dsimp only [Z3]
    exact (center_SUid_eq hσ (m := 3) (by norm_num)).symm
  have hZ3card : Nat.card Z3 = 3 := by
    have hscal := (unitary_scalar_kernel (K := K) (p := 2) (f := 1) (by norm_num) hK'
      (n := 3) (by norm_num)).2.2
    have hmap : Subgroup.map (MulEquiv.subgroupCongr hSU3) Z3
        = (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 2 K) := by
      ext x
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨y, hy, rfl⟩
        dsimp only [Z3] at hy
        rw [Subgroup.mem_subgroupOf] at hy
        simpa [MulEquiv.subgroupCongr_apply] using hy
      · intro hx
        refine ⟨(MulEquiv.subgroupCongr hSU3).symm x, ?_, ?_⟩
        · dsimp only [Z3]
          rw [Subgroup.mem_subgroupOf, MulEquiv.subgroupCongr_symm_apply]
          exact hx
        · exact MulEquiv.apply_symm_apply (MulEquiv.subgroupCongr hSU3) x
    have hcard := Subgroup.card_mapSubgroup (MulEquiv.subgroupCongr hSU3) (H := Z3)
    rw [MulEquiv.mapSubgroup_apply, hmap] at hcard
    rw [← hcard]
    simpa using hscal
  by_contra hnot
  rw [injective_iff_map_eq_one] at hnot
  push Not at hnot
  obtain ⟨z, hzker, hzne⟩ := hnot
  have hzZ : z ∈ Z3 := by
    rw [hZ3center]
    exact hρ hzker
  have hZle : Z3 ≤ ρ.ker := by
    have hZp : Nat.Prime (Nat.card Z3) := by rw [hZ3card]; norm_num
    have hprime : Fact (Nat.Prime (Nat.card Z3)) := ⟨hZp⟩
    have hzZ' : (⟨z, hzZ⟩ : Z3) ≠ 1 := by
      intro h
      exact hzne (Subtype.ext_iff.mp h)
    have htop : Subgroup.zpowers (⟨z, hzZ⟩ : Z3) = ⊤ :=
      zpowers_eq_top_of_prime_card hZ3card hzZ'
    intro w hw
    have hmem : (⟨w, hw⟩ : Z3) ∈ Subgroup.zpowers (⟨z, hzZ⟩ : Z3) := by
      rw [htop]
      trivial
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hwk : w = z ^ k := by
      have := congrArg Subtype.val hk
      simpa using this.symm
    rw [hwk]
    exact Subgroup.zpow_mem ρ.ker (show z ∈ ρ.ker from hzker) k
  let hN : Z3.Normal := Subgroup.normal_of_le_center hZ3center.le
  have hZker : ρ.ker ≤ Z3 := by
    intro g hg
    rw [hZ3center]
    exact hρ hg
  let φ : (Su K 2 1 3 ⧸ Z3) →* Su K 2 1 4 := QuotientGroup.lift Z3 ρ hZle
  have hφ_inj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z3 y
    rw [QuotientGroup.mk'_apply] at hy
    rw [QuotientGroup.lift_mk'] at hy
    have hg : g ∈ Z3 := hZker hy
    exact (QuotientGroup.eq_one_iff g).mpr hg
  let e₂ : (Su K 2 1 3 ⧸ Z3) ≃* Ug K :=
    QuotientGroup.congr Z3 ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 2 K))
      (MulEquiv.subgroupCongr hSU3) (by
        ext x
        simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          exact ⟨(MulEquiv.subgroupCongr hSU3).symm x, by
            dsimp only [Z3]
            rw [Subgroup.mem_subgroupOf, MulEquiv.subgroupCongr_symm_apply]
            exact hx, by simp⟩)
  obtain ⟨ω, hω, h2⟩ := exists_omega (F := K) hK
  let o : OmegaData K := ⟨ω, hω, h2⟩
  let N := Multiplicative (ZMod 3 × ZMod 3)
  let ψ : Ug K →* Su K 2 1 4 := φ.comp e₂.symm.toMonoidHom
  let F : N →* Su K 2 1 4 := ψ.comp (theta o)
  have hF_inj : Function.Injective F := by
    intro x y hxy
    have h1 : e₂.symm (theta o x) = e₂.symm (theta o y) :=
      hφ_inj (by simpa [F, ψ] using hxy)
    exact theta_injective o (e₂.symm.injective h1)
  have hF_conj : ∀ x y : N, x ≠ 1 → y ≠ 1 →
      ∃ h : Su K 2 1 4, h * F x * h⁻¹ = F y := by
    intro x y hx hy
    obtain ⟨h, hh⟩ := theta_conj o x y hx hy
    refine ⟨ψ h, ?_⟩
    have := congrArg ψ hh
    simpa [F, ψ, map_mul] using this


  have hU : UnitaryFieldData 2 1 K :=
    ⟨by norm_num, by norm_num, by rw [hK]; norm_num⟩
  let V := Fin 4 → K
  let B : V →ₛₗ[hU.bar] V →ₗ[K] K := gramForm hU (1 : Matrix (Fin 4) (Fin 4) K)
  let act : Su K 2 1 4 →* Module.End K V := DistribMulAction.toModuleEnd K V
  let g : N →* Module.End K V := act.comp F
  have hbar : ∀ c : K, hU.bar c = unitaryInvolution K 2 1 c := by
    intro c
    rw [UnitaryFieldData.bar_apply, unitaryInvolution_apply]
  have hB : B.IsSymm := by
    dsimp only [B]
    exact gramForm_isSymm hU (by ext i j; simp [Matrix.one_apply, eq_comm])
  have hBl : B.SeparatingLeft := by
    dsimp only [B]
    exact gramForm_separatingLeft hU (by simp)
  have hcomm : ∀ x y : N, Commute (g x) (g y) := by
    intro x y
    show g x * g y = g y * g x
    rw [← map_mul, ← map_mul, mul_comm]
  have hx3 : ∀ x : N, x ^ 3 = 1 := by
    intro x
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    ext
    · simpa using (card_nsmul_eq_zero (G := ZMod 3) (x := (Multiplicative.toAdd x).1))
    · simpa using (card_nsmul_eq_zero (G := ZMod 3) (x := (Multiplicative.toAdd x).2))
  have hpow : ∀ x : N, g x ^ 3 = 1 := by
    intro x
    rw [← map_pow, hx3 x, map_one]
  have hBherm : ∀ x y : V, B x y = herm (unitaryInvolution K 2 1) x y := by
    intro x y
    dsimp only [B]
    rw [gramForm_apply, Matrix.one_mulVec, dotProduct]
    simp only [hbar, herm]
  have hgact : ∀ (x : N) (v : V),
      g x v = ((F x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v := by
    intro x v
    show act (F x) v = _
    rw [DistribMulAction.toModuleEnd_apply]
    exact smul_def (unitaryInvolution K 2 1) (F x) v
  have hiso : ∀ x v w, B (g x v) (g x w) = B v w := by
    intro x v w
    rw [hBherm, hBherm, hgact, hgact]
    exact ((mem_SUid_iff (unitaryInvolution K 2 1)).mp (F x).2).2 v w
  have hp3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hω1 : o.ω ≠ 1 := by
    intro h
    have h1 : (1 : K) = 0 := by
      have hthis : (1 : K) = (1 : K) + 1 := by
        have := o.hω
        rw [h] at this
        simpa using this.symm
      calc (1 : K) = (1 : K) + 1 := hthis
        _ = (2 : K) := by ring
        _ = 0 := o.h2
    exact one_ne_zero h1
  have hord : orderOf o.ω = 3 := orderOf_eq_prime o.cube hω1
  have hζ : IsPrimitiveRoot o.ω 3 := by
    rw [IsPrimitiveRoot.iff_def]
    refine ⟨o.cube, fun l hl => ?_⟩
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hl
  obtain ⟨b, μ, hbμ, _⟩ :=
    exists_orthonormal_common_eigenbasis (h := hU) (p := 3) (ζ := o.ω) hζ (by norm_num)
      hB hBl g hcomm hpow hiso
  have hd : Module.finrank K V = 4 := Module.finrank_fin_fun K


  let d := Module.finrank K V
  have hd' : d = 4 := hd
  have hEigen : ∀ (x : N) (lam : K),
      (Finset.univ.filter (fun j : Fin d => μ x j = lam)).card
        = Module.finrank K (Module.End.eigenspace (g x) lam) := by
    intro x lam
    exact card_eigenbasis_eq b (g x) (μ x) (hbμ x) lam
  have hconjEig : ∀ (x y : N), x ≠ 1 → y ≠ 1 → ∀ lam : K,
      Module.finrank K (Module.End.eigenspace (g x) lam)
        = Module.finrank K (Module.End.eigenspace (g y) lam) := by
    intro x y hx hy lam
    obtain ⟨h, hh⟩ := hF_conj x y hx hy
    let e : V ≃ₗ[K] V := DistribMulAction.toLinearEquiv (R := K) (M := V) h
    have hB : g y = (e : V →ₗ[K] V) * g x * (e.symm : V →ₗ[K] V) := by
      have hh' : act (h * F x * h⁻¹) = act (F y) := congrArg act hh
      rw [map_mul, map_mul] at hh'
      apply LinearMap.ext
      intro v
      have hv := congrArg (fun f : Module.End K V => f v) hh'
      simpa [g, act, e, Module.End.mul_apply, DistribMulAction.toLinearEquiv_apply,
        DistribMulAction.toLinearEquiv_symm_apply, DistribMulAction.toModuleEnd_apply]
        using hv.symm
    exact (finrank_eigenspace_conj e (g x) (g y) hB lam).symm
  let x₀ : N := Multiplicative.ofAdd ((1, 0) : ZMod 3 × ZMod 3)
  have hx₀ : x₀ ≠ 1 := by
    intro h
    have := congrArg Multiplicative.toAdd h
    simp [x₀] at this
  let a := (Finset.univ.filter (fun j : Fin d => μ x₀ j = 1)).card
  have ha : ∀ x : N, x ≠ 1 →
      (Finset.univ.filter (fun j : Fin d => μ x j = 1)).card = a := by
    intro x hx
    dsimp only [a]
    rw [hEigen x 1, hEigen x₀ 1, hconjEig x x₀ hx hx₀ 1]
  have hNcard : Nat.card N = 9 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_prod, ZMod.card]
  have hNcard' : Fintype.card N = 9 := by
    rw [← Nat.card_eq_fintype_card, hNcard]
  have hleft : (Finset.univ.erase (1 : N)).sum
      (fun x => (Finset.univ.filter (fun j : Fin d => μ x j = 1)).card) = 8 * a := by
    have hsum : (Finset.univ.erase (1 : N)).sum
        (fun x => (Finset.univ.filter (fun j : Fin d => μ x j = 1)).card)
        = (Finset.univ.erase (1 : N)).sum (fun _ => a) :=
      Finset.sum_congr rfl fun x hx => ha x (Finset.ne_of_mem_erase hx)
    rw [hsum, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, hNcard']
    simp
  have hμne : ∀ (x : N) (j : Fin d), μ x j ≠ 0 := by
    intro x j h0
    have hinv : g (x⁻¹) * g x = 1 := by
      have hx1 : x⁻¹ * x = 1 := inv_mul_cancel x
      calc g (x⁻¹) * g x = g (x⁻¹ * x) := (map_mul g x⁻¹ x).symm
        _ = g 1 := congrArg g hx1
        _ = 1 := map_one g
    have h1 : g x (b j) = 0 := by rw [hbμ x j, h0, zero_smul]
    have h2 : b j = 0 := by
      have h := congrArg (fun w => g (x⁻¹) w) h1
      rw [← Module.End.mul_apply, hinv, Module.End.one_apply, map_zero] at h
      exact h
    exact b.ne_zero j h2
  let χ : Fin d → N →* Kˣ := fun j =>
    { toFun := fun x => Units.mk0 (μ x j) (hμne x j)
      map_one' := by
        apply Units.ext
        simp only [Units.val_mk0]
        have h2 : b j = μ 1 j • b j := by simpa using hbμ 1 j
        have h3 := congrArg (fun w => b.repr w j) h2
        simpa [Module.Basis.repr_self] using h3.symm
      map_mul' := fun x y => by
        apply Units.ext
        simp only [Units.val_mk0, Units.val_mul]
        have h1 : g (x * y) (b j) = μ (x * y) j • b j := hbμ (x * y) j
        rw [map_mul] at h1
        have h2 : (g x * g y) (b j) = (μ x j * μ y j) • b j := by
          rw [Module.End.mul_apply, hbμ y j, map_smul, hbμ x j, smul_smul, mul_comm]
        have h3 : μ (x * y) j • b j = (μ x j * μ y j) • b j := by rw [← h1, h2]
        have h4 := congrArg (fun w => b.repr w j) h3
        simpa [Module.Basis.repr_self] using h4 }
  have hkerCard : ∀ j : Fin d,
      (Finset.univ.filter (fun x : N => χ j x = 1)).card = Nat.card (χ j).ker := by
    intro j
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
  have hcase : ∀ j : Fin d, Nat.card (χ j).ker - 1 = if χ j = 1 then 8 else 2 := by
    intro j
    by_cases hχ : χ j = 1
    · rw [if_pos hχ]
      have htop : (χ j).ker = ⊤ := (MonoidHom.ker_eq_top_iff).mpr hχ
      rw [htop, Subgroup.card_top, hNcard]
    · rw [if_neg hχ]
      have hKunits : Nat.card Kˣ = 3 := by
        rw [Nat.card_units, hK]
      have hKprime : Fact (Nat.card Kˣ).Prime := ⟨by rw [hKunits]; norm_num⟩
      have hrange_top : (χ j).range = ⊤ := by
        rcases Subgroup.eq_bot_or_eq_top_of_prime_card (χ j).range with h | h
        · exact absurd ((MonoidHom.range_eq_bot_iff).mp h) hχ
        · exact h
      have hrange_card : Nat.card (χ j).range = 3 := by
        rw [hrange_top, Subgroup.card_top, hKunits]
      have hmul := Subgroup.card_ker_mul_card_range (χ j)
      rw [hrange_card, hNcard] at hmul
      omega


  have hωne0 : o.ω ≠ 0 := by
    intro h
    have hc := o.cube
    rw [h] at hc
    norm_num at hc
  have hωinv : (o.ω)⁻¹ = o.ω ^ 2 := by
    rw [inv_eq_of_mul_eq_one_right]
    rw [← pow_succ', o.cube]
  have hμ3 : ∀ (x : N) (j : Fin d), μ x j ^ 3 = 1 := by
    intro x j
    have hpow_apply : ∀ n : ℕ, (g x ^ n) (b j) = (μ x j) ^ n • b j := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          simp only [pow_succ', Module.End.mul_apply, ih, map_smul, hbμ,
            smul_smul, pow_succ']
          rw [mul_comm]
    have h1 := hpow_apply 3
    rw [hpow x, Module.End.one_apply] at h1
    have h2 := congrArg (fun w => b.repr w j) h1
    simpa [Module.Basis.repr_self] using h2.symm
  have h1ω : (1 : K) ≠ o.ω := hω1.symm
  have hω2_ne_one : o.ω ^ 2 ≠ 1 := by
    intro h
    apply hω1
    have h3 : o.ω ^ 3 = o.ω := by rw [pow_succ, h, one_mul]
    rw [o.cube] at h3
    exact h3.symm
  have hω_ne_ω2 : o.ω ≠ o.ω ^ 2 := by
    intro h
    have hh := o.hω
    rw [h.symm] at hh
    have h0 : (0 : K) = 1 := by
      have := congrArg (fun x => x - o.ω) hh
      simp at this
    exact zero_ne_one h0
  have hsum : o.ω + o.ω ^ 2 = 1 := by
    rw [o.hω]
    linear_combination o.ω * o.h2
  have hfac : ∀ a : K, (a - 1) * (a - o.ω) * (a - o.ω ^ 2) = a ^ 3 - 1 := by
    intro a
    have hprod : (a - o.ω) * (a - o.ω ^ 2) = a ^ 2 + a + 1 := by
      linear_combination -a * hsum + o.cube - a * o.h2
    calc (a - 1) * (a - o.ω) * (a - o.ω ^ 2)
        = (a - 1) * ((a - o.ω) * (a - o.ω ^ 2)) := by ring
      _ = (a - 1) * (a ^ 2 + a + 1) := by rw [hprod]
      _ = a ^ 3 - 1 := by ring
  have hμvals : ∀ (x : N) (j : Fin d),
      μ x j = 1 ∨ μ x j = o.ω ∨ μ x j = o.ω ^ 2 := by
    intro x j
    have h3 := hμ3 x j
    have h0 : (μ x j - 1) * (μ x j - o.ω) * (μ x j - o.ω ^ 2) = 0 := by
      rw [hfac, h3, sub_self]
    rcases mul_eq_zero.mp h0 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · left; linear_combination h'
      · right; left; linear_combination h'
    · right; right; linear_combination h
  have hpartition : ∀ x : N,
      (Finset.univ.filter (fun j : Fin d => μ x j = 1)).card
        + (Finset.univ.filter (fun j : Fin d => μ x j = o.ω)).card
        + (Finset.univ.filter (fun j : Fin d => μ x j = o.ω ^ 2)).card = d := by
    intro x
    let A := Finset.univ.filter (fun j : Fin d => μ x j = 1)
    let B := Finset.univ.filter (fun j : Fin d => μ x j = o.ω)
    let C := Finset.univ.filter (fun j : Fin d => μ x j = o.ω ^ 2)
    have hdisjAB : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro j hjA hjB
      simp only [A, B, Finset.mem_filter] at hjA hjB
      exact h1ω (hjA.2.symm.trans hjB.2)
    have hdisjABC : Disjoint (A ∪ B) C := by
      rw [Finset.disjoint_left]
      intro j hj hjC
      simp only [Finset.mem_union, A, B, C, Finset.mem_filter] at hj hjC
      rcases hj with ⟨_, h1⟩ | ⟨_, h2⟩
      · exact hω2_ne_one (hjC.2.symm.trans h1)
      · exact hω_ne_ω2 (h2.symm.trans hjC.2)
    have hunion : A ∪ B ∪ C = Finset.univ := by
      ext j
      simp only [Finset.mem_union, Finset.mem_univ, iff_true, true_and, A, B, C,
        Finset.mem_filter, or_assoc]
      exact hμvals x j
    have hcard := Finset.card_union_of_disjoint hdisjABC
    rw [hunion, Finset.card_univ] at hcard
    have hcard2 := Finset.card_union_of_disjoint hdisjAB
    rw [hcard2] at hcard
    dsimp only [A, B, C] at hcard ⊢
    simpa using hcard.symm
  have hωcount : ∀ x : N, x ≠ 1 →
      (Finset.univ.filter (fun j : Fin d => μ x j = o.ω)).card
        = (Finset.univ.filter (fun j : Fin d => μ x j = o.ω ^ 2)).card := by
    intro x hx
    rw [hEigen x o.ω, hEigen x (o.ω ^ 2)]
    have hAB : g x * g (x⁻¹) = 1 := by
      have hx1 : x * x⁻¹ = 1 := mul_inv_cancel x
      calc g x * g (x⁻¹) = g (x * x⁻¹) := (map_mul g x x⁻¹).symm
        _ = g 1 := congrArg g hx1
        _ = 1 := map_one g
    have hBA : g (x⁻¹) * g x = 1 := by
      have hx1 : x⁻¹ * x = 1 := inv_mul_cancel x
      calc g (x⁻¹) * g x = g (x⁻¹ * x) := (map_mul g x⁻¹ x).symm
        _ = g 1 := congrArg g hx1
        _ = 1 := map_one g
    have heig : Module.End.eigenspace (g (x⁻¹)) o.ω
        = Module.End.eigenspace (g x) (o.ω)⁻¹ :=
      eigenspace_mul_inv (g x) (g (x⁻¹)) hAB hBA hωne0
    calc Module.finrank K (Module.End.eigenspace (g x) o.ω)
        = Module.finrank K (Module.End.eigenspace (g (x⁻¹)) o.ω) :=
          hconjEig x (x⁻¹) hx (inv_ne_one.mpr hx) o.ω
      _ = Module.finrank K (Module.End.eigenspace (g x) (o.ω)⁻¹) := by rw [heig]
      _ = Module.finrank K (Module.End.eigenspace (g x) (o.ω ^ 2)) := by rw [hωinv]


  have hfixsum : ∀ x : N,
      (Finset.univ.filter (fun j : Fin d => μ x j = 1)).card
        = ∑ j : Fin d, (if μ x j = 1 then 1 else 0) := by
    intro x
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hdouble : (Finset.univ.erase (1 : N)).sum
      (fun x => (Finset.univ.filter (fun j : Fin d => μ x j = 1)).card)
      = ∑ j : Fin d, (Nat.card (χ j).ker - 1) := by
    calc (Finset.univ.erase (1 : N)).sum
          (fun x => (Finset.univ.filter (fun j : Fin d => μ x j = 1)).card)
        = (Finset.univ.erase (1 : N)).sum
            (fun x => ∑ j : Fin d, (if μ x j = 1 then 1 else 0)) := by
          exact Finset.sum_congr rfl fun x _ => hfixsum x
      _ = ∑ j : Fin d, (Finset.univ.erase (1 : N)).sum
            (fun x => (if μ x j = 1 then 1 else 0)) := Finset.sum_comm
      _ = ∑ j : Fin d, (Nat.card (χ j).ker - 1) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          have hχif : (Finset.univ.erase (1 : N)).sum
              (fun x => (if μ x j = 1 then 1 else 0))
              = (Finset.univ.erase (1 : N)).sum
                (fun x => (if χ j x = 1 then 1 else 0)) := by
            exact Finset.sum_congr rfl fun x _ => by
              by_cases h : μ x j = 1
              · simp [χ, h]
              · have h' : ¬ (χ j x = 1) := by
                  intro hc
                  exact h (by simpa [χ] using congrArg (fun u : Kˣ => (u : K)) hc)
                simp [h, h']
          rw [hχif]
          have h1 : (Finset.univ.erase (1 : N)).sum
              (fun x => (if χ j x = 1 then 1 else 0))
              = ((Finset.univ.erase (1 : N)).filter (fun x => χ j x = 1)).card := by
            rw [Finset.card_eq_sum_ones, Finset.sum_filter]
          rw [h1]
          have h2 : (Finset.univ.erase (1 : N)).filter (fun x => χ j x = 1)
              = (Finset.univ.filter (fun x => χ j x = 1)).erase 1 := by
            ext x
            simp [Finset.mem_filter, Finset.mem_erase, and_comm]
          rw [h2, Finset.card_erase_of_mem (by simp), hkerCard j]
  let S := Finset.univ.filter (fun j : Fin d => χ j = 1)
  let t := S.card
  have hsum3 : (∑ j : Fin d, (Nat.card (χ j).ker - 1)) = 2 * d + 6 * t := by
    rw [show (∑ j : Fin d, (Nat.card (χ j).ker - 1))
        = ∑ j : Fin d, (2 + 6 * (if χ j = 1 then 1 else 0)) from by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hcase j]
      by_cases h : χ j = 1 <;> simp [h]]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hind : (∑ j : Fin d, (if χ j = 1 then 1 else 0)) = t := by
      dsimp only [t, S]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [hind, Finset.sum_const, Finset.card_univ, Fintype.card_fin, hd']
    ring
  have hcount : 8 * a = 6 * t + 8 := by
    rw [← hleft, hdouble, hsum3, hd']
    ring
  have ha_le : a ≤ 4 := by
    dsimp only [a]
    calc (Finset.univ.filter (fun j : Fin d => μ x₀ j = 1)).card
        ≤ Finset.univ.card := Finset.card_filter_le _ _
      _ = d := by simp
      _ = 4 := hd'
  have ht_le : t ≤ 4 := by
    dsimp only [t, S]
    calc (Finset.univ.filter (fun j : Fin d => χ j = 1)).card
        ≤ Finset.univ.card := Finset.card_filter_le _ _
      _ = d := by simp
      _ = 4 := hd'
  have ha_even : Even a := by
    have hpart := hpartition x₀
    have hωeq := hωcount x₀ hx₀
    dsimp only [a]
    have hpart4 : (Finset.univ.filter (fun j : Fin d => μ x₀ j = 1)).card
        + (Finset.univ.filter (fun j : Fin d => μ x₀ j = o.ω)).card
        + (Finset.univ.filter (fun j : Fin d => μ x₀ j = o.ω ^ 2)).card = 4 :=
      hpart.trans hd'
    rw [← hωeq] at hpart4
    refine ⟨2 - (Finset.univ.filter (fun j : Fin d => μ x₀ j = o.ω)).card, ?_⟩
    omega
  obtain ⟨u, hua⟩ := ha_even
  have ht4 : t = 4 := by omega
  have hS : S = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [show S.card = t from rfl, ht4, Fintype.card_fin, hd']
  have hχ1 : ∀ j : Fin d, χ j = 1 := by
    intro j
    have hj : j ∈ S := by
      rw [hS]
      simp
    have hj' : j ∈ Finset.univ.filter (fun j : Fin d => χ j = 1) := by
      simpa [S] using hj
    exact (Finset.mem_filter.mp hj').2
  have hμ1 : ∀ (x : N) (j : Fin d), μ x j = 1 := by
    intro x j
    have hj1 : χ j x = 1 := by rw [hχ1 j]; rfl
    have hco := congrArg (fun u : Kˣ => (u : K)) hj1
    simpa [χ] using hco
  have hg1 : g x₀ = 1 := by
    apply b.ext
    intro j
    rw [hbμ x₀ j, hμ1 x₀ j, one_smul, Module.End.one_apply]
  have hF1 : F x₀ = 1 := by
    apply ext_smul
    intro v
    have h := congrArg (fun f : Module.End K V => f v) hg1
    simpa [g, act, DistribMulAction.toModuleEnd_apply] using h
  exact hx₀ (hF_inj (by rw [hF1, map_one]))

end CFSG.ClassicalInvolution.PhanDn.QTwo

end
