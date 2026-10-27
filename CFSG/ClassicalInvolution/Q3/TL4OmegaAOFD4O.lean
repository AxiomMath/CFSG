module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFD4C
public import CFSG.ClassicalInvolution.Q3.TL4D4NC
public import CFSG.ClassicalInvolution.Q3.Q3MFODOrb
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFSim

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open scoped MatrixGroups Pointwise

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)

local notation "V₈" => Fin 4 ⊕ Fin 4 → GaloisField 3 1

@[expose] def SimFam (m s : 𝔽₃) : Prop :=
  ∀ a : V₈ ≃ₗ[𝔽₃] V₈, (∀ v, Q₄ (a v) = m * Q₄ v) → (∀ v, a (a v) = s • v) →
    ∀ β : MulAut (D4P 𝔽₃), Odd (orderOf β) →
      (∀ x : spinGroup Q₄, spinAction Q₄ x * a = a * spinAction Q₄ x →
        β (Q3T.d4Proj 𝔽₃ x) = Q3T.d4Proj 𝔽₃ x) →
        β • statedPointFamily (coe_quadPlus 4 𝔽₃) = statedPointFamily (coe_quadPlus 4 𝔽₃)

theorem d4Proj_eq_of_spinAction_eq {x y : spinGroup Q₄} (h : spinAction Q₄ x = spinAction Q₄ y) :
    Q3T.d4Proj 𝔽₃ x = Q3T.d4Proj 𝔽₃ y := by
  have hm : spinMatrix Q₄ x = spinMatrix Q₄ y := by
    apply (toLinEquiv _ 𝔽₃).injective
    rw [toLinEquiv_spinMatrix, toLinEquiv_spinMatrix, h]
  rw [spinToStatedProj_apply, spinToStatedProj_apply]
  congr 1
  exact Subtype.ext hm

theorem inv_mul_conj_mul {X : Type} [Group X] (τ : MulAut X) (y : X) :
    τ⁻¹ * MulAut.conj y * τ = MulAut.conj (τ⁻¹ y) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.inv_apply_self]

theorem exists_sim_of_pres (α : MulAut (spinGroup Q₄)) (hα2 : α * α = 1)
    (hpres : Q3MFOD.Pres α) :
    ∃ (a : V₈ ≃ₗ[𝔽₃] V₈) (m s : 𝔽₃), (m = 1 ∨ m = -1) ∧ (s = 1 ∨ s = -1) ∧
      (∀ v, Q₄ (a v) = m * Q₄ v) ∧ (∀ v, a (a v) = s • v) ∧
      ∀ x, spinAction Q₄ (α x) = a * spinAction Q₄ x * a⁻¹ := by
  have hn3 : 3 ≤ 4 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsPerfect (spinGroup Q₄) := isPerfect_spinGroup_quadPlus hn3
  have hF3 : Nat.card 𝔽₃ = 3 := ModelFacts.TG3.natCard_galoisField_three
  obtain ⟨a, μ, hμ, hsim, hαa⟩ := Q3MFOD.exists_sim_of_mat3 hF3 α
    (Q3MFOD.spin_plus4_sim_of_family α (Q3MFOD.descAut α) (Q3MFOD.descAut_apply α) hpres)
  have hcomm : ∀ h ∈ elementaryGroup Q₄, a * a * h = h * (a * a) := by
    intro h hh
    rw [← range_spinAction_quadPlus (K := 𝔽₃) hn3] at hh
    obtain ⟨x, rfl⟩ := hh
    have h1 : spinAction Q₄ (α (α x)) = spinAction Q₄ x := by
      rw [← MulAut.mul_apply, hα2, MulAut.one_apply]
    rw [hαa, hαa] at h1
    calc a * a * spinAction Q₄ x
        = (a * (a * spinAction Q₄ x * a⁻¹) * a⁻¹) * (a * a) := by group
      _ = spinAction Q₄ x * (a * a) := by rw [h1]
  have hdim8 : Module.finrank 𝔽₃ V₈ = 8 := finrank_d4
  obtain ⟨hμ1, ha2⟩ := sim_cases4 hF3 (nondegenerate_polarBilin_quadPlus 4 𝔽₃) (by omega) hμ
    hsim hcomm
  rcases ha2 with ha2 | ha2
  · refine ⟨a, μ, 1, hμ1, Or.inl rfl, hsim, fun v => ?_, hαa⟩
    rw [← LinearEquiv.mul_apply, ha2, one_smul]
    rfl
  · exact ⟨a, μ, -1, hμ1, Or.inr rfl, hsim, fun v => by rw [ha2, neg_one_smul], hαa⟩

section Out


theorem exists_lift_desc (f' : MulAut (D4P 𝔽₃)) (hf'2 : f' * f' = 1) :
    ∃ α : MulAut (spinGroup Q₄), α * α = 1 ∧ Q3MFOD.descAut α = f' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : NeZero 4 := ⟨by norm_num⟩
  have : Group.IsPerfect (spinGroup Q₄) := isPerfect_spinGroup_quadPlus (by norm_num)
  have : Finite (spinGroup Q₄) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  obtain ⟨E₁, hE₁⟩ := Q3T.exists_mulEquiv_apply_eq
    (QuotientGroup.mk' (Subgroup.center (spinGroup Q₄))) (QuotientGroup.mk'_surjective _)
    (Q3T.d4Proj 𝔽₃) Q3MFOD.d4Proj_surjective (by rw [QuotientGroup.ker_mk', Q3MFOD.ker_d4Proj])
  obtain ⟨α, hα⟩ := Q3PP.exists_lift_plus4 (MulAut.congr E₁.symm f')
  have hρ2 : MulAut.congr E₁.symm f' * MulAut.congr E₁.symm f' = 1 := by
    rw [← map_mul, hf'2, map_one]
  refine ⟨α, Q3PP.mul_self_eq_one_of_lift α _ hρ2 hα, MulEquiv.ext fun y => ?_⟩
  obtain ⟨x, rfl⟩ := Q3MFOD.d4Proj_surjective y
  have h1 := hE₁ (α x)
  have h2 := hE₁ x
  rw [QuotientGroup.mk'_apply] at h1 h2
  rw [Q3MFOD.descAut_apply, ← h1, ← h2, hα, MulAut.congr_apply, MulEquiv.symm_symm,
    MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]

theorem d4OutCentR_of (h11 : SimFam 1 1) (h1m : SimFam 1 (-1)) (hm1 : SimFam (-1) 1)
    (hmm : SimFam (-1) (-1)) : D4OutCentR := by
  intro S _ _ _ hmodel f hf2 _ β hβodd hβf hfix
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
  have hβ'fix : ∀ y, MulAut.congr e f y = y → MulAut.congr e β y = y := by
    intro y hy
    have h1 : f (e.symm y) = e.symm y := by
      have h2 : e (f (e.symm y)) = y := hy
      apply e.injective
      rw [MulEquiv.apply_symm_apply]
      exact h2
    show e (β (e.symm y)) = y
    rw [hfix _ h1, MulEquiv.apply_symm_apply]
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
      β'' (Q3T.d4Proj 𝔽₃ x) = Q3T.d4Proj 𝔽₃ x := by
    intro x hx
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
    rw [hβ'', MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply, hβ'fix _ hy,
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

end Out

end CFSG.ClassicalInvolution.Q3.TL4
