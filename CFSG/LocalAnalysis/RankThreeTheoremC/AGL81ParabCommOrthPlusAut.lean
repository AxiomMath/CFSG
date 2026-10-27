module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthPlusDefs
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1C2B
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusCover
public import CFSG.RankThree.PartOne.KFR4.Row4

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthPlus

open Matrix QuadraticMap CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
  CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonalAut
  CFSG.RankThree.Classical.SteinbergBY CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.Assembly.LowTwoRank
open scoped Pointwise

variable {r : ℕ} {K : Type} [Field K]

theorem orthDerived_eq_orthElementary [CharP K 2] (hr : 3 ≤ r) :
    orthDerived (quadPlus r K) = orthElementaryGroup (quadPlus r K) :=
  commutator_orthogonalGroup_quadPlus hr

@[expose] noncomputable def projEquiv [Finite K] [CharP K 2] (hr : 3 ≤ r) :
    ↥(orthElementaryGroup (quadPlus r K)) ≃* ProjOrthDerived (quadPlus r K) :=
  haveI : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
  (MulEquiv.subgroupCongr (orthDerived_eq_orthElementary hr).symm).trans
    (CFSG.RankThree.PartOne.KFR4.orthDerivedEquivProj (nondegenerate_polarBilin_quadPlus r K))

@[expose] def toDerived [CharP K 2] (hr : 3 ≤ r) (x : ↥(orthElementaryGroup (quadPlus r K))) :
    ↥(orthDerived (quadPlus r K)) :=
  ⟨x, by rw [orthDerived_eq_orthElementary hr]; exact x.2⟩

theorem projEquiv_apply [Finite K] [CharP K 2] (hr : 3 ≤ r)
    (x : ↥(orthElementaryGroup (quadPlus r K))) :
    projEquiv hr x = QuotientGroup.mk (toDerived hr x) := rfl

@[expose] noncomputable def untwist (σ : K ≃+* K) (F : (Fin r ⊕ Fin r → K) ≃+ (Fin r ⊕ Fin r → K))
    (hF : ∀ (c : K) (v : Fin r ⊕ Fin r → K), F (c • v) = σ c • F v) : GLV r K :=
  ((AddEquiv.piCongrRight fun _ : Fin r ⊕ Fin r => σ.symm.toAddEquiv).trans F).toLinearEquiv
    (fun c v => by
      have h1 : (AddEquiv.piCongrRight fun _ : Fin r ⊕ Fin r => σ.symm.toAddEquiv) (c • v) =
          σ.symm c • (AddEquiv.piCongrRight fun _ : Fin r ⊕ Fin r => σ.symm.toAddEquiv) v := by
        funext i
        simp
      rw [AddEquiv.trans_apply, AddEquiv.trans_apply, h1, hF, RingEquiv.apply_symm_apply])

theorem untwist_apply (σ : K ≃+* K) (F : (Fin r ⊕ Fin r → K) ≃+ (Fin r ⊕ Fin r → K))
    (hF : ∀ (c : K) (v : Fin r ⊕ Fin r → K), F (c • v) = σ c • F v) (v : Fin r ⊕ Fin r → K) :
    untwist σ F hF v = F (sCoord σ.symm v) := rfl

theorem untwist_quad (σ : K ≃+* K) (F : (Fin r ⊕ Fin r → K) ≃+ (Fin r ⊕ Fin r → K))
    (hF : ∀ (c : K) (v : Fin r ⊕ Fin r → K), F (c • v) = σ c • F v) (μ : K)
    (hQ : ∀ v, quadPlus r K (F v) = μ * σ (quadPlus r K v)) (v : Fin r ⊕ Fin r → K) :
    quadPlus r K (untwist σ F hF v) = μ * quadPlus r K v := by
  rw [untwist_apply, hQ, quadPlus_sCoord, RingEquiv.apply_symm_apply]

theorem eq_untwist_sCoord (σ : K ≃+* K) (F : (Fin r ⊕ Fin r → K) ≃+ (Fin r ⊕ Fin r → K))
    (hF : ∀ (c : K) (v : Fin r ⊕ Fin r → K), F (c • v) = σ c • F v)
    (v : Fin r ⊕ Fin r → K) : F v = untwist σ F hF (sCoord σ v) := by
  rw [untwist_apply, sCoord_symm_sCoord]

theorem isSemilinear_of_induced [Finite K] [CharP K 2] (hr : 3 ≤ r)
    (α : MulAut ↥(orthElementaryGroup (quadPlus r K)))
    (h : InducedBySemilinear (quadPlus r K) (MulAut.congr (projEquiv hr) α)) :
    IsSemilinear α := by
  obtain ⟨σ, F, hF, μ, hμ, hQF, hind⟩ := h
  set hl : GLV r K := untwist σ F hF with hhl
  have hQl : ∀ v, quadPlus r K (hl v) = μ * quadPlus r K v := untwist_quad σ F hF μ hQF
  obtain ⟨ν, hν⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) μ
  have hν0 : ν ≠ 0 := by
    rintro rfl
    exact hμ (by simpa using hν)
  let h₀ : GLV r K := hl.trans (LinearEquiv.smulOfUnit (Units.mk0 ν hν0)⁻¹)
  have h₀_apply : ∀ v, h₀ v = ν⁻¹ • hl v := fun v => rfl
  have hO : h₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [h₀_apply, QuadraticMap.map_smul, smul_eq_mul, hQl, hν]
    field_simp
  have h₀symm : ∀ v, h₀.symm v = ν • hl.symm v := by
    intro v
    rw [LinearEquiv.symm_apply_eq, h₀_apply, map_smul, LinearEquiv.apply_symm_apply, smul_smul,
      inv_mul_cancel₀ hν0, one_smul]
  refine ⟨h₀, σ, hO, fun x => ?_⟩
  have hcandE : h₀ * fieldConj r K σ x * h₀⁻¹ ∈ orthElementaryGroup (quadPlus r K) :=
    conj_mem_orthElementaryGroup hO (fieldConj_mem_orthElementaryGroup hr σ x.2)
  have hFsymm : ∀ v, F.symm v = sCoord σ.symm (hl.symm v) := by
    intro v
    rw [AddEquiv.symm_apply_eq, eq_untwist_sCoord σ F hF, sCoord_sCoord_symm,
      LinearEquiv.apply_symm_apply]
  have key := hind (toDerived hr x) ⟨h₀ * fieldConj r K σ x * h₀⁻¹, by
      rw [orthDerived_eq_orthElementary hr]; exact hcandE⟩ (fun v => by
    change (h₀ * fieldConj r K σ x * h₀⁻¹) v = F (x.1 (F.symm v))
    rw [hFsymm, eq_untwist_sCoord σ F hF, ← fieldConj_apply]
    show h₀ (fieldConj r K σ x (h₀.symm v)) = hl (fieldConj r K σ x (hl.symm v))
    rw [h₀symm, map_smul, h₀_apply, map_smul, smul_smul, inv_mul_cancel₀ hν0, one_smul])
  have h2 : projEquiv hr (α x) =
      projEquiv hr ⟨h₀ * fieldConj r K σ x * h₀⁻¹, hcandE⟩ := by
    have h3 : (MulAut.congr (projEquiv hr)) α (QuotientGroup.mk (toDerived hr x)) =
        projEquiv hr (α x) := by
      rw [← projEquiv_apply]
      change projEquiv hr (α ((projEquiv hr).symm (projEquiv hr x))) = _
      rw [MulEquiv.symm_apply_apply]
    rw [← h3]
    exact key
  exact congrArg Subtype.val ((projEquiv hr).injective h2)


theorem isSemilinear_of_five_le [Finite K] [CharP K 2] (hr : 5 ≤ r)
    (α : MulAut ↥(orthElementaryGroup (quadPlus r K))) : IsSemilinear α := by
  have hdim : Module.finrank K (Fin r ⊕ Fin r → K) = 2 * r := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp [two_mul]
  refine isSemilinear_of_induced (by omega) α ?_
  exact orthogonal_aut_semilinear_of_seven_le (quadPlus r K)
    (nondegenerate_polarBilin_quadPlus r K) (by omega) (fun h => absurd h (by omega)) _

theorem isPGroup_zpowers_of_pow_eq_one {G : Type*} [Group G] {p k : ℕ} {β : G}
    (h : β ^ p ^ k = 1) : IsPGroup p (Subgroup.zpowers β) := by
  intro g
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
  refine ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, ← hm, ← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm,
    _root_.zpow_mul, _root_.zpow_natCast, h, _root_.one_zpow]
  rfl

theorem exists_orthogonalGates_four (K : Type) [Field K] [Finite K] [CharP K 2] :
    ∃ f : ℕ, OrthogonalGates (coordinateQuadPlus 4 K) f := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hmodel : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus 4 K)))
      .POmegaPlus 4 2 n :=
    ⟨⟨hℓ, n.pos, le_rfl⟩, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  exact ⟨n, orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaPlus
    (Or.inr (Or.inl rfl)) 4 2 n hmodel K hK (MulEquiv.refl _)⟩

theorem inducedBySemilinear_of_pow_eq_one_four (K : Type) [Field K] [Finite K] [CharP K 2]
    {p k : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (β : MulAut (ProjOrthDerived (coordinateQuadPlus 4 K))) (hβ : β ^ p ^ k = 1) :
    InducedBySemilinear (coordinateQuadPlus 4 K) β := by
  obtain ⟨f, hg⟩ := exists_orthogonalGates_four K
  have hd : 0 < 2 * 4 := by norm_num
  set β' : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) :=
    MulAut.congr (coordBridge (coordinateQuadPlus 4 K) hd).symm β with hβ'def
  have hβ' : β' ^ p ^ k = 1 := by rw [hβ'def, ← map_pow, hβ, map_one]
  have hK0 := hg.2.2.2.2.2.2.1 p hp hp3 _ (isPGroup_zpowers_of_pow_eq_one hβ')
  have h1 : β' ∈ projectivePointFamilyAut (coordinateQuadPlus 4 K) :=
    hg.2.2.2.2.1 (hK0 (Subgroup.mem_zpowers β'))
  have h2 : β' ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) := by
    rw [← hg.2.2.2.2.2.1]
    exact h1
  obtain ⟨σ, F, hF, μ, hμ, hQ, hind⟩ :=
    exists_semilin_of_mem_matrixProjectiveImage (coordinateQuadPlus 4 K) hd β h2
  exact ⟨σ, F, hF, μ, hμ, hQ, hind⟩

theorem isSemilinear_of_pow_eq_one_four [Finite K] [CharP K 2] {p k : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (α : MulAut ↥(orthElementaryGroup (quadPlus 4 K))) (hα : α ^ p ^ k = 1) :
    IsSemilinear α := by
  refine isSemilinear_of_induced (by norm_num) α ?_
  let S : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin (2 * 4) → K) :=
    (coordinatePlusIsometry 4 K).toLinearEquiv
  have hS : ∀ v, coordinateQuadPlus 4 K (S v) = ((1 : Kˣ) : K) * quadPlus 4 K v := fun v => by
    change coordinateQuadPlus 4 K ((coordinatePlusIsometry 4 K) v) = _
    rw [(coordinatePlusIsometry 4 K).map_app, Units.val_one, one_mul]
  refine CFSG.ClassicalInvolution.Q3.TL4.E3S3O.inducedBySemilinear_of_similarity_of S 1 hS ?_
  exact inducedBySemilinear_of_pow_eq_one_four K hp hp3 _
    (by rw [← map_pow, ← map_pow, hα, map_one, map_one])

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthPlus
