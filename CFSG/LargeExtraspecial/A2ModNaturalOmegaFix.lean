module

public import CFSG.LargeExtraspecial.A2ModBasic
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticTransvection
public import CFSG.Open.StatedDefs

import CFSG.ClassicalGroups.Alternating.BinaryPointFix
import CFSG.ClassicalGroups.Alternating.Transvections
import CFSG.LinearAlgebra.F2PlaneMaps
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LargeExtraspecial.OrthoF2Eichler
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Utils
public import CFSG.Timmesfeld.Outcome

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod.OmegaFix

open Module Submodule QuadraticMap CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticTransvection
open CFSG.ClassicalGroups.Alternating

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem polarBilin_isAlt (q : QuadraticForm (ZMod 2) W) :
    LinearMap.BilinForm.IsAlt (polarBilin q) := fun v => by
  rw [polarBilin_apply_apply, polar_self, two_nsmul, CharTwo.add_self_eq_zero]

theorem map_add_eq (q : QuadraticForm (ZMod 2) W) (x y : W) :
    q (x + y) = q x + q y + polar q x y := by
  unfold QuadraticMap.polar
  ring

theorem map_transvection {q : QuadraticForm (ZMod 2) W} {x : W} (hx : q x = 1) (v : W) :
    q ((binarySymplecticTransvection (polarBilin q) (polarBilin_isAlt q) x :
      W →ₗ[ZMod 2] W) v) = q v := by
  rw [binarySymplecticTransvection_apply, map_add_eq, QuadraticMap.map_smul, hx,
    polar_smul_right, polarBilin_apply_apply, smul_eq_mul, smul_eq_mul, mul_one, add_assoc,
    ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul, add_zero]

theorem exists_anisotropic_pair [FiniteDimensional (ZMod 2) W] {q : QuadraticForm (ZMod 2) W}
    (hq : (polarBilin q).Nondegenerate) (hdim : 7 ≤ finrank (ZMod 2) W) {v₀ ℓ : W}
    (hv₀ : v₀ ≠ 0) (hℓ0 : ℓ ≠ 0) (hℓv : ℓ ≠ v₀) (hqℓ : q ℓ = 0) (hvℓ : polar q v₀ ℓ = 0) :
    ∃ x y, q x = 1 ∧ q y = 1 ∧ polar q x y = 1 ∧ polar q v₀ x = 0 ∧ polar q v₀ y = 0 ∧
      polar q ℓ x = 1 := by
  classical
  set B : LinearMap.BilinForm (ZMod 2) W := polarBilin q with hB_def
  have hpB : ∀ u w, B u w = polar q u w := fun u w => polarBilin_apply_apply q u w
  obtain ⟨f, hf⟩ := alternating_pairing_surjectivity hq
    (BinaryPointFix.linearIndependent_pair_of_ne hv₀ hℓ0 (Ne.symm hℓv)) ![0, 1]
  have hf0 : polar q v₀ f = 0 := by
    have := congrFun hf 0
    simpa only [LinearMap.pi_apply, Matrix.cons_val_zero, hpB] using this
  have hf1 : polar q ℓ f = 1 := by
    have := congrFun hf 1
    simpa only [LinearMap.pi_apply, Matrix.cons_val_one, Matrix.cons_val_zero, hpB] using this
  obtain ⟨x, hqx, hvx, hℓx⟩ : ∃ x, q x = 1 ∧ polar q v₀ x = 0 ∧ polar q ℓ x = 1 := by
    rcases zmod_two_cases (q f) with h0 | h1
    · refine ⟨f + ℓ, ?_, ?_, ?_⟩
      · rw [map_add_eq, h0, hqℓ, polar_comm, hf1, zero_add, zero_add]
      · rw [polar_add_right, hf0, hvℓ, add_zero]
      · rw [polar_add_right, hf1, polar_self, hqℓ, smul_zero, add_zero]
    · exact ⟨f, h1, hf0, hf1⟩
  set N : Submodule (ZMod 2) W := span (ZMod 2) (({v₀, ℓ, x} : Finset W) : Set W) with hN_def
  set M := LinearMap.BilinForm.orthogonal B N with hM_def
  have hNr : finrank (ZMod 2) N ≤ 3 :=
    (finrank_span_finset_le_card _).trans Finset.card_le_three
  have hMr : finrank (ZMod 2) M = finrank (ZMod 2) W - finrank (ZMod 2) N :=
    LinearMap.BilinForm.finrank_orthogonal hq N
  obtain ⟨t, htM, hqt⟩ : ∃ t ∈ M, q t = 1 := by
    by_contra hno
    push Not at hno
    have hzero : ∀ t ∈ M, q t = 0 := fun t ht => (zmod_two_cases (q t)).resolve_right (hno t ht)
    have hle : M ≤ LinearMap.BilinForm.orthogonal B M := by
      intro s hs
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro u hu
      rw [hpB]
      have h := map_add_eq q u s
      rw [hzero _ (M.add_mem hu hs), hzero u hu, hzero s hs, zero_add, zero_add] at h
      exact h.symm
    have h1 := Submodule.finrank_mono hle
    rw [LinearMap.BilinForm.finrank_orthogonal hq M] at h1
    omega
  have hmemN : ∀ u ∈ (({v₀, ℓ, x} : Finset W) : Set W), polar q u t = 0 := fun u hu => by
    rw [← hpB]
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp htM) u (subset_span hu)
  have htv : polar q v₀ t = 0 := hmemN v₀ (by simp)
  have htℓ : polar q ℓ t = 0 := hmemN ℓ (by simp)
  have htx : polar q x t = 0 := hmemN x (by simp)
  refine ⟨x, ℓ + t, hqx, ?_, ?_, hvx, ?_, hℓx⟩
  · rw [map_add_eq, hqℓ, hqt, htℓ, zero_add, add_zero]
  · rw [polar_add_right, polar_comm, hℓx, htx, add_zero]
  · rw [polar_add_right, hvℓ, htv, add_zero]

end CFSG.LargeExtraspecial.A2Mod.OmegaFix

namespace CFSG.LargeExtraspecial.A2Mod

open Module Submodule QuadraticMap CFSG.LocalAnalysis.ComponentInitial CFSG.Open Matrix
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticTransvection
open CFSG.ClassicalGroups.Alternating CFSG.RankThree.OrthogonalInvolutions
open scoped commutatorElement

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}

theorem false_of_commute_of_natural_omega {ι : Type} [Fintype ι] [DecidableEq ι]
    (hA : A2Action D Q ρ) {qW : QuadraticForm (ZMod 2) (ι → ZMod 2)}
    (hqW : (polarBilin qW).Nondegenerate) (hdim : 7 ≤ Fintype.card ι)
    {Qf : (ι → ZMod 2) → ZMod 2} (hQf : ⇑qW = Qf) (φ : X ≃* ↥(StatedOmega Qf))
    (π : V →ₗ[ZMod 2] (ι → ZMod 2)) (hinj : commSpaceOf ρ ⊤ ⊓ LinearMap.ker π = ⊥)
    (hπ : ∀ x, ∀ v ∈ commSpaceOf ρ ⊤, π (ρ x v) =
      ((φ x : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ π v)
    (hQ : ∀ v ∈ commSpaceOf ρ ⊤, Qf (π v) = Q v) {α : X} (hα : α ∈ D) {a : V}
    (ha : a ∈ commSpace (ρ α)) (ha0 : a ≠ 0)
    (hcomm : ∀ y : X, y ^ 3 = 1 → ρ y a = a → y * α = α * y) : False := by
  classical
  set U := commSpaceOf ρ ⊤ with hU_def
  have hTA := hA.isTypeA hα
  have hL2 : finrank (ZMod 2) (commSpace (ρ α)) = 2 := hTA.2.2.2.1
  have hLsing : ∀ v ∈ commSpace (ρ α), Q v = 0 := hTA.2.2.2.2
  have hLU : commSpace (ρ α) ≤ U := commSpace_le_commSpaceOf ρ (Subgroup.mem_top α)
  have hinj' : ∀ u ∈ U, ∀ w ∈ U, π u = π w → u = w := fun u hu w hw h => by
    have hmem : u - w ∈ U ⊓ LinearMap.ker π :=
      Submodule.mem_inf.mpr ⟨U.sub_mem hu hw, by rw [LinearMap.mem_ker, map_sub, h, sub_self]⟩
    rw [hinj, Submodule.mem_bot] at hmem
    exact sub_eq_zero.mp hmem
  have hQW : ∀ v ∈ U, qW (π v) = Q v := fun v hv => by rw [hQf]; exact hQ v hv
  obtain ⟨ℓ, hℓL, hℓ0, hℓa⟩ : ∃ ℓ ∈ commSpace (ρ α), ℓ ≠ 0 ∧ ℓ ≠ a := by
    by_contra hno
    push Not at hno
    have hle : commSpace (ρ α) ≤ span (ZMod 2) {a} := fun ℓ hℓ => by
      by_cases h0 : ℓ = 0
      · rw [h0]
        exact zero_mem _
      · rw [hno ℓ hℓ h0]
        exact mem_span_singleton_self a
    have := (Submodule.finrank_mono hle).trans (finrank_span_singleton ha0).le
    omega
  have haU := hLU ha
  have hℓU := hLU hℓL
  have hv₀ : π a ≠ 0 := fun h0 => ha0 (hinj' a haU 0 U.zero_mem (by rw [h0, map_zero]))
  have hℓ₀ : π ℓ ≠ 0 := fun h0 => hℓ0 (hinj' ℓ hℓU 0 U.zero_mem (by rw [h0, map_zero]))
  have hℓv : π ℓ ≠ π a := fun h => hℓa (hinj' ℓ hℓU a haU h)
  have hqℓ : qW (π ℓ) = 0 := by rw [hQW ℓ hℓU, hLsing ℓ hℓL]
  have hvℓ : polar qW (π a) (π ℓ) = 0 := by
    have h := OmegaFix.map_add_eq qW (π a) (π ℓ)
    rw [← map_add, hQW _ (U.add_mem haU hℓU), hQW a haU, hQW ℓ hℓU,
      hLsing _ ((commSpace (ρ α)).add_mem ha hℓL), hLsing a ha, hLsing ℓ hℓL, zero_add,
      zero_add] at h
    exact h.symm
  obtain ⟨x, y, hqx, hqy, hxy, hvx, hvy, hℓx⟩ := OmegaFix.exists_anisotropic_pair hqW
    (by rw [Module.finrank_fintype_fun_eq_card]; exact hdim) hv₀ hℓ₀ hℓv hqℓ hvℓ
  set B : LinearMap.BilinForm (ZMod 2) (ι → ZMod 2) := polarBilin qW with hB_def
  have hBa : B.IsAlt := OmegaFix.polarBilin_isAlt qW
  have hpB : ∀ u w, B u w = polar qW u w := fun u w => polarBilin_apply_apply qW u w
  have hBn : B.Nondegenerate := hqW
  set τx := binarySymplecticTransvection B hBa x with hτx
  set τy := binarySymplecticTransvection B hBa y with hτy
  set g := τx * τy with hg_def
  have hxy' : B x y = 1 := by rw [hpB]; exact hxy
  have hg3 : g ^ 3 = 1 := BinaryPointFix.mul_pow_three hBa hBn hxy'
  have hgv : ((g : LinearMap.GeneralLinearGroup (ZMod 2) (ι → ZMod 2)) :
      (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) (π a) = π a :=
    BinaryPointFix.mul_apply_of_apply_eq_zero hBa (by rw [hpB]; exact hvx)
      (by rw [hpB]; exact hvy)
  have hgc : g = ⁅τx, τy⁆ ^ 2 := by
    have hc : ⁅τx, τy⁆ = g ^ 2 := by
      have h1 : τx⁻¹ = τx := inv_eq hBa x
      have h2 : τy⁻¹ = τy := inv_eq hBa y
      rw [commutatorElement_def, h1, h2, hg_def, _root_.sq]
      simp only [mul_assoc]
    rw [hc, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hg3, one_mul]
  let toM := (Matrix.GeneralLinearGroup.toLin :
    GL ι (ZMod 2) ≃* LinearMap.GeneralLinearGroup (ZMod 2) (ι → ZMod 2)).symm
  have happ : ∀ (h : LinearMap.GeneralLinearGroup (ZMod 2) (ι → ZMod 2)) (v : ι → ZMod 2),
      ((toM h : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ v =
        (h : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) v := fun h v => by
    have := Matrix.GeneralLinearGroup.toLin_apply (toM h) v
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  have hiso : ∀ {c : ι → ZMod 2}, qW c = 1 →
      toM (binarySymplecticTransvection B hBa c) ∈ CFSG.MatrixModel.isometryCore Qf :=
    fun {c} hc => Subgroup.subset_closure fun v => by
      rw [happ, ← hQf]
      exact OmegaFix.map_transvection hc v
  have hGmem : toM g ∈ StatedOmega Qf := by
    rw [hgc, map_pow, map_commutatorElement]
    exact Subgroup.pow_mem _
      (Subgroup.commutator_mem_commutator (hiso hqx) (hiso hqy)) 2
  set y' := φ.symm ⟨toM g, hGmem⟩ with hy'_def
  have hφy' : φ y' = ⟨toM g, hGmem⟩ := φ.apply_symm_apply _
  have hy'3 : y' ^ 3 = 1 := φ.injective (by
    rw [map_pow, hφy', map_one]
    exact Subtype.ext (by rw [SubmonoidClass.coe_pow, ← map_pow, hg3, map_one]; rfl))
  have hy'app : ∀ v ∈ U, π (ρ y' v) =
      ((g : LinearMap.GeneralLinearGroup (ZMod 2) (ι → ZMod 2)) :
        (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) (π v) := fun v hv => by
    rw [hπ y' v hv, hφy']
    exact happ g (π v)
  have hfix : ρ y' a = a :=
    hinj' _ (apply_mem_commSpaceOf ρ (Subgroup.mem_top y') haU) a haU
      (by rw [hy'app a haU, hgv])
  have hc := hcomm y' hy'3 hfix
  have hpres : ∀ v ∈ commSpace (ρ α), ρ y' v ∈ commSpace (ρ α) := by
    intro v hv
    obtain ⟨u, rfl⟩ := mem_commSpace.mp hv
    refine mem_commSpace.mpr ⟨ρ y' u, ?_⟩
    have h1 : ρ α (ρ y' u) = ρ y' (ρ α u) := by
      rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul, ← map_mul, hc]
    rw [map_sub, h1]
  have hodd : Odd (orderOf (ρ y')) := by
    have hdvd : orderOf (ρ y') ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hy'3, map_one])
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1 <;> rw [h1] <;> decide
  have hfixℓ := CFSG.LinearAlgebra.apply_eq_self_of_odd_of_apply_eq hL2 hpres hodd ha ha0 hfix
    ℓ hℓL
  have hgℓ := hy'app ℓ hℓU
  rw [hfixℓ] at hgℓ
  have h0 := (BinaryPointFix.apply_eq_zero_of_mul_apply_eq hBa hxy' hgℓ.symm).1
  rw [hpB, hℓx] at h0
  exact one_ne_zero h0

end CFSG.LargeExtraspecial.A2Mod
