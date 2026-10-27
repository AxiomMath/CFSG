module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightOnTwistMat
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAnisoEight

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix Module QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.RankThree.OrthogonalInvolutions (commSpace omegaGroup mem_omegaGroup)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (minusIndexEquiv
  coordinateQuadMinus reindexQuadraticForm reindexVectorEquiv reindexQuadraticForm_map)
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus quadMinus coe_quadMinus)

section Six

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem on_exists_ne_zero_quadMinus_three {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (U : Submodule K (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K)) (hU : finrank K U = 3) :
    ∃ u ∈ U, quadMinus 3 K b c u ≠ 0 := by
  obtain ⟨-, hW⟩ := OmegaPilot.regular_wittIndex_coordinateQuadMinus (K := K) (m := 3)
    (by norm_num) hirr
  by_contra hcon
  push Not at hcon
  have h1 := hW (U.map (reindexVectorEquiv (K := K) (minusIndexEquiv 3 (by norm_num))).toLinearMap)
    (by
      rintro _ ⟨u, hu, rfl⟩
      rw [coordinateQuadMinus]
      change reindexQuadraticForm _ _ (reindexVectorEquiv _ u) = 0
      rw [reindexQuadraticForm_map]
      exact hcon u hu)
  rw [LinearEquiv.finrank_map_eq, hU] at h1
  omega

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem on_mem_statedOmega_of_even_six (Q : QuadraticForm K (ι → K))
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Fintype.card ι = 6)
    (hts : ∀ U : Submodule K (ι → K), finrank K U = 3 → ∃ u ∈ U, Q u ≠ 0) {A : GL ι K}
    (hA : ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v) (hev : Even (((A : Matrix ι ι K) - 1).rank)) :
    A ∈ StatedOmega ⇑Q := by
  have hO : pdLinEquiv A ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by rw [pdLinEquiv_apply]; exact hA v
  have hΩ : pdLinEquiv A ∈ omegaGroup Q hQ := mem_omegaGroup.mpr ⟨hO, by
    rw [pd_commSpace_eq]
    exact hev⟩
  have hD := OmegaPilot.omegaGroup_le_orthDerived_of_six hQ
    (by rw [Module.finrank_fintype_fun_eq_card, hdim]) hts hΩ
  have hD' : pdLinEquiv A ∈ (StatedOmega ⇑Q).map pdLinEquiv.toMonoidHom := by
    rw [on_map_statedOmega_eq]
    exact hD
  obtain ⟨A', hA', hAA'⟩ := hD'
  rw [MulEquiv.coe_toMonoidHom] at hAA'
  rwa [← pdLinEquiv.injective hAA']

theorem on_commutator_statedOmega_quadMinus_three (hK : Nat.card K = 2) :
    ⁅(⊤ : Subgroup (StatedOmega (StatedQuadMinus (2 + 1) K 1 1))),
      (⊤ : Subgroup (StatedOmega (StatedQuadMinus (2 + 1) K 1 1)))⁆ = ⊤ := by
  have hirr := q2Omega_irreducible_one_one hK
  have hQ := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 3 K hirr
  obtain ⟨hq, -⟩ := OmegaPilot.isQuasisimple_orthDerived_of_six hQ
    (by rw [Module.finrank_fintype_fun_eq_card]; simp) (on_exists_ne_zero_quadMinus_three hirr)
  have h := hq.1.commutator_eq_top
  rw [commutator_def] at h
  rw [← coe_quadMinus]
  set e : StatedOmega ⇑(quadMinus 3 K 1 1) ≃* orthDerived (quadMinus 3 K 1 1) :=
    (MulEquiv.subgroupMap pdLinEquiv (StatedOmega ⇑(quadMinus 3 K 1 1))).trans
      (MulEquiv.subgroupCongr (by exact on_map_statedOmega_eq (quadMinus 3 K 1 1)))
  have h2 := congrArg (Subgroup.map e.symm.toMonoidHom) h
  rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.2 e.symm.surjective] at h2

end Six

section Ext

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {K : Type}
  [Field K] [Finite K] [CharP K 2] {M : Matrix κ ι K} {R : Matrix ι κ K}

omit [Finite K] in
theorem onExists_pcExtMat_eq_of_fix (hRM : R * M = 1)
    {Qg : QuadraticForm K (κ → K)} {Qm : QuadraticForm K (ι → K)}
    (hQ : ∀ x y, Qg (x + M *ᵥ y) - Qg x = Qm (R *ᵥ x + y) - Qm (R *ᵥ x))
    (hker : ∀ z, R *ᵥ z = 0 → (∀ x, R *ᵥ x = 0 → polar Qg z x = 0) → z = 0)
    (hndg : Qg.polarBilin.Nondegenerate)
    (hΩm : ∀ h : GL ι K, (∀ y, Qm ((h : Matrix ι ι K) *ᵥ y) = Qm y) →
      Even (((h : Matrix ι ι K) - 1).rank) → h ∈ StatedOmega ⇑Qm)
    {A : GL κ K} (hA : A ∈ StatedOmega ⇑Qg)
    (hfix : ∀ x, R *ᵥ x = 0 → (A : Matrix κ κ K) *ᵥ x = x) :
    ∃ h : GL ι K, h ∈ StatedOmega ⇑Qm ∧ pcExtMat M R (h : Matrix ι ι K) = A := by
  have hAiso := pd_isometry_of_mem_statedOmega hA
  have hAinv : A⁻¹ ∈ StatedOmega ⇑Qg := inv_mem hA
  have hfixinv : ∀ x, R *ᵥ x = 0 → ((A⁻¹ : GL κ K) : Matrix κ κ K) *ᵥ x = x := by
    intro x hx
    conv_lhs => rw [← hfix x hx]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  obtain ⟨hAM, hA1⟩ := pcExtMat_eq_of_fix hRM hQ hker hAiso hfix
  obtain ⟨-, hA2⟩ := pcExtMat_eq_of_fix hRM hQ hker (pd_isometry_of_mem_statedOmega hAinv)
    hfixinv
  set H := R * (A : Matrix κ κ K) * M with hH
  set H' := R * ((A⁻¹ : GL κ K) : Matrix κ κ K) * M with hH'
  have hHH' : H * H' = 1 := by
    apply pcExtMat_injective hRM
    rw [pcExtMat_mul hRM, ← hA1, ← hA2, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      pcExtMat_one]
  have hH'H : H' * H = 1 := by
    apply pcExtMat_injective hRM
    rw [pcExtMat_mul hRM, ← hA1, ← hA2, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      pcExtMat_one]
  set h0 : GL ι K := ⟨H, H', hHH', hH'H⟩ with hh0
  have hQM : ∀ y, Qg (M *ᵥ y) = Qm y := fun y => by
    have h1 := hQ 0 y
    simpa using h1
  have hiso : ∀ y, Qm ((h0 : Matrix ι ι K) *ᵥ y) = Qm y := fun y => by
    change Qm (H *ᵥ y) = Qm y
    rw [← hQM, ← hAM, hAiso, hQM]
  have hev : Even (((h0 : Matrix ι ι K) - 1).rank) := by
    have h1 := pdEven_rank_of_mem_statedOmega Qg hndg hA
    have h2 : (A : Matrix κ κ K) - 1 = M * (H - 1) * R := by
      conv_lhs => rw [hA1]
      rw [pcExtMat, add_sub_cancel_left]
    rw [h2, pd_rank_conj hRM] at h1
    exact h1
  exact ⟨h0, hΩm h0 hiso hev, hA1.symm⟩

omit [Finite K] in
theorem onExists_eq_of_fix_frame {Qg : QuadraticForm K (κ → K)} {Qm : QuadraticForm K (ι → K)}
    {a b : κ → K} (hF : IsPDFramePlane M R Qg Qm a b) (hndg : Qg.polarBilin.Nondegenerate)
    (hΩm : ∀ h : GL ι K, (∀ y, Qm ((h : Matrix ι ι K) *ᵥ y) = Qm y) →
      Even (((h : Matrix ι ι K) - 1).rank) → h ∈ StatedOmega ⇑Qm) {g : GL κ K}
    (hg : g ∈ StatedOmega ⇑Qg) (hga : (g : Matrix κ κ K) *ᵥ a = a)
    (hgb : (g : Matrix κ κ K) *ᵥ b = b) :
    ∃ h : GL ι K, h ∈ StatedOmega ⇑Qm ∧ pcExtMat M R (h : Matrix ι ι K) = g := by
  refine onExists_pcExtMat_eq_of_fix hF.1 hF.2.1 hF.hker hndg hΩm hg fun x hx => ?_
  obtain ⟨p, q, rfl⟩ := hF.2.2.2.2.1 x hx
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hga, hgb]

end Ext

section Levi

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem onMem_pcOMExt_range_iff_two (hK : Nat.card K = 2) (k : Fin (2 + 1))
    (g : StatedOmega (StatedQuadPlus (2 + 2) K)) :
    g ∈ (pcOMExt (K := K) k).range ↔
      ((g : GL (Fin (2 + 2) ⊕ Fin (2 + 2)) K) : Matrix (Fin (2 + 2) ⊕ Fin (2 + 2))
        (Fin (2 + 2) ⊕ Fin (2 + 2)) K) *ᵥ pdMA K k = pdMA K k ∧
      ((g : GL (Fin (2 + 2) ⊕ Fin (2 + 2)) K) : Matrix (Fin (2 + 2) ⊕ Fin (2 + 2))
        (Fin (2 + 2) ⊕ Fin (2 + 2)) K) *ᵥ pdMB K k = pdMB K k := by
  have hirr := q2Omega_irreducible_one_one hK
  constructor
  · rintro ⟨h, rfl⟩
    rw [coe_pcOMExt]
    exact (isPDFramePlane_pcOM k).ext_fix _
  · rintro ⟨ha, hb⟩
    have hg : (g : GL (Fin (2 + 2) ⊕ Fin (2 + 2)) K) ∈ StatedOmega ⇑(quadPlus (2 + 2) K) := by
      rw [coe_quadPlus]
      exact g.2
    obtain ⟨h, hh, he⟩ := onExists_eq_of_fix_frame (isPDFramePlane_pcOM k)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus (2 + 2) K)
      (fun h hiso hev => on_mem_statedOmega_of_even_six (quadMinus (2 + 1) K 1 1)
        (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (2 + 1) K hirr)
        (by simp) (on_exists_ne_zero_quadMinus_three hirr) hiso hev) hg ha hb
    rw [coe_quadMinus] at hh
    exact ⟨⟨h, hh⟩, Subtype.ext (Units.ext he)⟩

end Levi

end CFSG.SeitzReduction.SymplecticPilot
