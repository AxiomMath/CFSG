module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCompFamQS
import CFSG.LinearAlgebra.RootGroupSL.SchurSL
import CFSG.RankThree.PartOne.KC.SymplecticIsotypicFixed
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
import CFSG.RankThree.Classical.SteinbergBJOrthogonalDerivedCentralizer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open Matrix Module CFSG.ComponentClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {σ : K →+* K}

section Ext

variable {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K} {U W : Submodule K (ι → K)}

theorem extU_mem_blkI (hUW : IsCompl U W) (horth : ∀ u ∈ U, ∀ w ∈ W, β u w = 0 ∧ β w u = 0)
    {s : U ≃ₗ[K] U} (hs : s ∈ ⁅isomU β U, isomU β U⁆) :
    glEquiv.symm (extU hUW s) ∈ blkI β U W := by
  have hmap : (isomU β U).map (glEquiv.symm.toMonoidHom.comp (extHom hUW)) ≤ blkSub β U W := by
    rintro _ ⟨t, ht, rfl⟩
    exact extU_mem_blkSub hUW horth ht
  have h := Subgroup.mem_map_of_mem (glEquiv.symm.toMonoidHom.comp (extHom hUW)) hs
  rw [Subgroup.map_commutator] at h
  exact Subgroup.commutator_mono hmap hmap h

theorem commute_on_U (hUW : IsCompl U W) (horth : ∀ u ∈ U, ∀ w ∈ W, β u w = 0 ∧ β w u = 0)
    {y : GL ι K} (hyU : ∀ u ∈ U, glEquiv y u ∈ U) (hy : ∀ g ∈ blkI β U W, y * g = g * y)
    {s : U ≃ₗ[K] U} (hs : s ∈ ⁅isomU β U, isomU β U⁆) (v : U) :
    glEquiv y (s v : ι → K) = (s ⟨glEquiv y v, hyU v v.2⟩ : ι → K) := by
  have h := congrArg (fun g : GL ι K => glEquiv g (v : ι → K))
    (hy _ (extU_mem_blkI hUW horth hs))
  simp only [map_mul, LinearEquiv.mul_apply, MulEquiv.apply_symm_apply] at h
  rw [extU_apply_mem hUW s v] at h
  rw [h]
  exact extU_apply_mem hUW s ⟨glEquiv y v, hyU v v.2⟩

end Ext

section Schur

theorem exists_smul_of_commute_blkI_zero [Finite K] {U W : Submodule K (ι → K)}
    (hUW : IsCompl U W) (hdim : 3 ≤ finrank K U ∨ (finrank K U = 2 ∧ 4 ≤ Nat.card K))
    {y : GL ι K} (hyU : ∀ u ∈ U, glEquiv y u ∈ U)
    (hy : ∀ g ∈ blkI (0 : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K) U W, y * g = g * y) :
    ∃ c : K, ∀ u ∈ U, glEquiv y u = c • u := by
  have horth : ∀ u ∈ U, ∀ w ∈ W, (0 : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K) u w = 0 ∧
      (0 : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K) w u = 0 := fun _ _ _ _ => ⟨rfl, rfl⟩
  have heq := commutator_isomU_zero (σ := σ) U hdim
  obtain ⟨c, hc⟩ := CFSG.LinearAlgebra.RootGroupSL.exists_smul_of_commute_specialLinear
    (show 2 ≤ finrank K U by omega)
    ((glEquiv y).toLinearMap.restrict fun u hu => hyU u hu).toAddMonoidHom
    fun g v => Subtype.ext (commute_on_U hUW horth hyU hy (heq ▸ MonoidHom.mem_ker.2 g.2) v)
  exact ⟨c, fun u hu => congrArg Subtype.val (hc ⟨u, hu⟩)⟩

theorem exists_smul_of_commute_blkI_unitForm {r f : ℕ}
    (hK : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData r f K) (hr : r ≠ 2)
    {U W : Submodule K (ι → K)} (hUW : IsCompl U W)
    (horth : ∀ u ∈ U, ∀ w ∈ W, unitForm hK.bar u w = 0 ∧ unitForm hK.bar w u = 0)
    (hnd : ∀ u ∈ U, (∀ u' ∈ U, unitForm hK.bar u u' = 0) → u = 0)
    (hdim : 3 ≤ finrank K U ∨ (finrank K U = 2 ∧ r ^ f ≠ 3)) {y : GL ι K}
    (hyU : ∀ u ∈ U, glEquiv y u ∈ U) (hy : ∀ g ∈ blkI (unitForm hK.bar) U W, y * g = g * y) :
    ∃ c : K, ∀ u ∈ U, glEquiv y u = c • u := by
  have heq := commutator_isomU_unitForm hK hr hnd hdim
  have hq : 2 ≤ r ^ f := le_trans hK.prime.two_le (Nat.le_self_pow (by have := hK.one_le; omega) r)
  obtain ⟨c, hc⟩ := CFSG.RankThree.PartOne.KCUnitary.exists_smul_of_commute_special_unitary hK
    (unitFormU_isSymm hK.bar (fun _ => rfl) hK.bar_bar U)
    (unitFormU_nondegenerate hK.bar (fun _ => rfl) hK.bar_bar hnd).1 (by omega) hq
    ((glEquiv y).toLinearMap.restrict fun u hu => hyU u hu) fun δ hδ => by
      rw [CFSG.LocalAnalysis.ComponentInitial.mem_sesqSpecialUnitaryGroup] at hδ
      have hs : LinearMap.GeneralLinearGroup.generalLinearEquiv K U δ ∈
          ⁅isomU (unitForm hK.bar) U, isomU (unitForm hK.bar) U⁆ := by
        rw [heq]
        refine Subgroup.mem_inf.2 ⟨fun x x' => hδ.1 x' x, MonoidHom.mem_ker.2 (Units.ext ?_)⟩
        rw [LinearEquiv.coe_det, Units.val_one]
        exact hδ.2
      show _ * _ = _ * _
      exact LinearMap.ext fun v => Subtype.ext (commute_on_U hUW horth hyU hy hs v)
  exact ⟨c, fun u hu => congrArg Subtype.val (hc ⟨u, hu⟩)⟩

theorem exists_smul_of_commute_blkI_toBilin' [Finite K] (hodd : Odd (Nat.card K))
    {J : Matrix ι ι K} (hJ : ∀ x, Matrix.toBilin' J x x = 0) {U W : Submodule K (ι → K)}
    (hUW : IsCompl U W)
    (horth : ∀ u ∈ U, ∀ w ∈ W, Matrix.toBilin' J u w = 0 ∧ Matrix.toBilin' J w u = 0)
    (hnd : ∀ u ∈ U, (∀ u' ∈ U, Matrix.toBilin' J u u' = 0) → u = 0)
    (hdim : 2 ≤ finrank K U) (hexc : finrank K U ≠ 2 ∨ Nat.card K ≠ 3) {y : GL ι K}
    (hyU : ∀ u ∈ U, glEquiv y u ∈ U) (hy : ∀ g ∈ blkI (Matrix.toBilin' J) U W, y * g = g * y) :
    ∃ c : K, ∀ u ∈ U, glEquiv y u = c • u := by
  have heq := commutator_eq_of_perfect (Subgroup.commutator_le_self _) le_rfl
    (isQuasisimple_isomU_toBilin' hodd hJ hnd hdim hexc).1
  obtain ⟨c, hc⟩ := CFSG.RankThree.PartOne.KCSpIsotypic.exists_smul_of_commute_sesqUnitaryGroup_alt
    (resBilin_isAlt hJ U) (resBilin_nondegenerate hJ hnd)
    ((glEquiv y).toLinearMap.restrict fun u hu => hyU u hu) fun g hg => by
      have hs : LinearMap.GeneralLinearGroup.generalLinearEquiv K U g ∈
          ⁅isomU (Matrix.toBilin' J) U, isomU (Matrix.toBilin' J) U⁆ := by
        rw [heq]
        exact fun x x' => hg x x'
      show _ * _ = _ * _
      exact LinearMap.ext fun v => Subtype.ext (commute_on_U hUW horth hyU hy hs v)
  exact ⟨c, fun u hu => congrArg Subtype.val (hc ⟨u, hu⟩)⟩

theorem exists_smul_of_commute_blkI_polarBilin [Finite K] (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K (ι → K)) {U W : Submodule K (ι → K)} (hUW : IsCompl U W)
    (horth : ∀ u ∈ U, ∀ w ∈ W,
      QuadraticMap.polarBilin Q u w = 0 ∧ QuadraticMap.polarBilin Q w u = 0)
    (hnd : ∀ u ∈ U, (∀ u' ∈ U, QuadraticMap.polarBilin Q u u' = 0) → u = 0)
    (hdim : 3 ≤ finrank K U) {y : GL ι K} (hyU : ∀ u ∈ U, glEquiv y u ∈ U)
    (hy : ∀ g ∈ blkI (QuadraticMap.polarBilin Q) U W, y * g = g * y) :
    ∃ c : K, ∀ u ∈ U, glEquiv y u = c • u := by
  have hO := isomU_polarBilin_eq (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd) Q U
  have hK2 : 2 < Nat.card K := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨hiff, -, -⟩ :=
    CFSG.RankThree.Classical.finite_orthogonal_derived_natural_linear_centralizer_scalar hK2
      (Q.comp U.subtype) (polarBilin_comp_nondegenerate Q hnd) hdim
  obtain ⟨c, hc⟩ := (hiff ((glEquiv y).toLinearMap.restrict fun u hu => hyU u hu)).1
    fun g hg => by
      have hs : g ∈ ⁅isomU (QuadraticMap.polarBilin Q) U,
          isomU (QuadraticMap.polarBilin Q) U⁆ := by
        rw [hO]
        exact hg
      exact LinearMap.ext fun v => Subtype.ext (commute_on_U hUW horth hyU hy hs v)
  refine ⟨c, fun u hu => ?_⟩
  have h := congrArg (fun M : U →ₗ[K] U => (M ⟨u, hu⟩ : ι → K)) hc
  simpa using h

end Schur

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls

end
