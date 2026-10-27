module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FHD4OddDef

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open scoped MatrixGroups Pointwise

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)

section Asm


theorem fh_d4OddCent_of (h11 : FHSimFamO 1 1) (h1m : FHSimFamO 1 (-1))
    (hm1 : FHSimFamO (-1) 1) (hmm : FHSimFamO (-1) (-1)) :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → LieModel S .POmegaPlus 4 3 1 →
      ∀ f : MulAut S, f * f = 1 → ∀ β : MulAut S, Odd (orderOf β) →
        (∀ x : S, f x = x → Odd (orderOf x) → β x = x) → β ∈ Q3NM.innSubgroup S := by
  intro S _ _ _ hmodel f hf2 β hβodd hfix
  have hFT : IsFundTag StatedLieTag.POmegaPlus := trivial
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  obtain ⟨ψ, hψ, hker⟩ :=
    Upgrade.lieModelCentralCover _ 4 3 1 Nat.prime_three (by norm_num) hFT hadm S hmodel
  obtain ⟨hSq, -, -, -, -⟩ := Q3NM.centralQuotientData Nat.prime_three hFT hadm S ψ hψ hker
  have hZ := center_eq_bot_of_isQuasisimple hSq
  have hker' : ψ.ker = Subgroup.center (spinGroup Q₄) :=
    le_antisymm hker (ModelFacts.ChevAut.center_le_ker_of_surjective hψ hZ)
  obtain ⟨e, -⟩ := Q3T.exists_mulEquiv_apply_eq ψ hψ (Q3T.d4Proj 𝔽₃)
    (spinToStatedProj_quadPlus (by norm_num : 3 ≤ 4)).1
    (hker'.trans (spinToStatedProj_quadPlus (by norm_num : 3 ≤ 4)).2.2.symm)
  have hf'2 : MulAut.congr e f * MulAut.congr e f = 1 := by rw [← map_mul, hf2, map_one]
  have hβ'fix : ∀ y, MulAut.congr e f y = y → Odd (orderOf y) → MulAut.congr e β y = y := by
    intro y hy hyodd
    have h1 : f (e.symm y) = e.symm y := by
      have h2 : e (f (e.symm y)) = y := hy
      apply e.injective
      rw [MulEquiv.apply_symm_apply]
      exact h2
    have hodd' : Odd (orderOf (e.symm y)) := by rwa [MulEquiv.orderOf_eq]
    show e (β (e.symm y)) = y
    rw [hfix _ h1 hodd', MulEquiv.apply_symm_apply]
  obtain ⟨α, hα2, hdesc⟩ := exists_lift_desc (MulAut.congr e f) hf'2
  obtain ⟨σ, -, hpres⟩ := Q3MFOD.exists_pres_conj α hα2
  have hα''2 : σ * α * σ⁻¹ * (σ * α * σ⁻¹) = 1 := by
    calc σ * α * σ⁻¹ * (σ * α * σ⁻¹) = σ * (α * α) * σ⁻¹ := by group
      _ = 1 := by rw [hα2]; group
  obtain ⟨a, m, s, hm, hs, hsim, ha2, hαa⟩ := exists_sim_of_pres _ hα''2 hpres
  set τ := Q3MFOD.descAut σ with hτ
  have hdesc'' : Q3MFOD.descAut (σ * α * σ⁻¹) = τ * MulAut.congr e f * τ⁻¹ := by
    rw [Q3MFOD.descAut_mul, Q3MFOD.descAut_mul, Q3MFOD.descAut_inv, hdesc]
  set β'' := MulAut.conj τ (MulAut.congr e β) with hβ''
  have hβ''odd : Odd (orderOf β'') := by
    rw [hβ'', MulEquiv.orderOf_eq, MulEquiv.orderOf_eq]
    exact hβodd
  have hβ''fix : ∀ x : spinGroup Q₄, spinAction Q₄ x * a = a * spinAction Q₄ x →
      Odd (orderOf (Q3T.d4Proj 𝔽₃ x)) → β'' (Q3T.d4Proj 𝔽₃ x) = Q3T.d4Proj 𝔽₃ x := by
    intro x hx hxodd
    have hfx : Q3MFOD.descAut (σ * α * σ⁻¹) (Q3T.d4Proj 𝔽₃ x) = Q3T.d4Proj 𝔽₃ x := by
      rw [Q3MFOD.descAut_apply]
      refine d4Proj_eq_of_spinAction_eq ?_
      rw [hαa]
      calc a * spinAction Q₄ x * a⁻¹ = spinAction Q₄ x * a * a⁻¹ := by rw [hx]
        _ = spinAction Q₄ x := by group
    rw [hdesc''] at hfx
    have hy : MulAut.congr e f (τ⁻¹ (Q3T.d4Proj 𝔽₃ x)) = τ⁻¹ (Q3T.d4Proj 𝔽₃ x) := by
      have h1 := congrArg (⇑(τ⁻¹ : MulAut (D4P 𝔽₃))) hfx
      simpa only [MulAut.mul_apply, MulAut.inv_apply_self] using h1
    have hyodd : Odd (orderOf (τ⁻¹ (Q3T.d4Proj 𝔽₃ x))) := by
      rwa [MulEquiv.orderOf_eq]
    rw [hβ'', MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply, hβ'fix _ hy hyodd,
      MulAut.apply_inv_self]
  have hfam : β'' • statedPointFamily (coe_quadPlus 4 𝔽₃) =
      statedPointFamily (coe_quadPlus 4 𝔽₃) := by
    rcases hm with rfl | rfl <;> rcases hs with rfl | rfl
    · exact h11 a hsim ha2 β'' hβ''odd hβ''fix
    · exact h1m a hsim ha2 β'' hβ''odd hβ''fix
    · exact hm1 a hsim ha2 β'' hβ''odd hβ''fix
    · exact hmm a hsim ha2 β'' hβ''odd hβ''fix
  obtain ⟨y, hy⟩ := Q3T.exists_eq_conj_of_smul_statedPointFamily β'' hfam hβ''odd
  have hβ'conj : MulAut.congr e β = MulAut.conj (τ⁻¹ y) := by
    rw [← inv_mul_conj_mul, ← hy, hβ'', MulAut.conj_apply]
    group
  rw [Q3NM.mem_innSubgroup_iff]
  refine ⟨e.symm (τ⁻¹ y), (MulAut.congr e).injective ?_⟩
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
  exact hβ'conj.symm

end Asm

end CFSG.OddStandard.SmallF3.Omega
