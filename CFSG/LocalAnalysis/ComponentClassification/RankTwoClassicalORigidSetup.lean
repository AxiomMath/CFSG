module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviGen
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOSiegel
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOTheta

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

section Theta

variable {K : Type} [Field K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]
  {G' : Type} [Group G'] {A : Subgroup G'}

theorem exists_oTheta_spec {Q : QuadraticForm K (ι → K)} (hQ : Q.polarBilin.Nondegenerate)
    {Q₀ : (ι → K) → K} (hQ₀ : ⇑Q = Q₀) (e : rankTwoQuot A ≃* StatedProj (StatedOmega Q₀))
    {p : G'} (hp : IsSingularRankTwo e Q₀ p) {u₀ w₀ : ι → K} (hu₀ : Q u₀ = 0) (hw₀ : Q w₀ = 0)
    (huw : Q.polarBilin u₀ w₀ = 0) (hli : LinearIndependent K ![u₀, w₀])
    {S : Subgroup (StatedProj (StatedOmega Q₀))}
    (hS : ∀ (a : K) (Z : StatedOmega Q₀),
      ((Z : GL ι K) : Matrix ι ι K) = 1 + a • cTwoX Q u₀ w₀ → QuotientGroup.mk Z ∈ S) :
    ∃ θ : ↥A →* StatedProj (StatedOmega Q₀), θ.ker = center ↥A ∧ Function.Surjective θ ∧
      (∀ y ∈ {y : G' | (∃ j : ℕ, y ^ 2 ^ j = 1) ∧ ∃ M N : GL ι K, Represents e p M ∧
        orderOf M = 2 ∧ Represents e y N ∧ ∃ a : K,
          (N : Matrix ι ι K) - 1 = a • ((M : Matrix ι ι K) - 1)},
        y ∈ liftSub θ S ∧ ∃ j : ℕ, y ^ 2 ^ j = 1) ∧
      ∃ (hpA : p ∈ A) (Z₀ : StatedOmega Q₀),
        ((Z₀ : GL ι K) : Matrix ι ι K) = 1 + cTwoX Q u₀ w₀ ∧ θ ⟨p, hpA⟩ = QuotientGroup.mk Z₀ := by
  subst hQ₀
  obtain ⟨-, M, hpM, hM2, hr, hsing⟩ := hp
  have hMΩ : M ∈ StatedOmega ⇑Q := hpM.2.1
  obtain ⟨a₁, a₂, hN, hQa₁, hQa₂, h12, hli'⟩ :=
    exists_cTwoX_of_singular hQ (quad_mulVec_of_mem_statedOmega hMΩ) hM2 hr hsing
  obtain ⟨G, hG, hGa₂, hGa₁⟩ := exists_isometryGL_pair hQ hli' hli hQa₂ hQa₁ hu₀ hw₀
    (by rw [polarBilin_comm]; exact h12) huw
  have hconj : (G : Matrix ι ι K) * ((M : Matrix ι ι K) - 1) * ((G⁻¹ : GL ι K) : Matrix ι ι K) =
      cTwoX Q u₀ w₀ := by
    have h1 := conj_cTwoX (D := G⁻¹) (isometry_inv hG) a₂ a₁
    rw [inv_inv, hGa₂, hGa₁] at h1
    rw [hN, h1]
  have hconj' : ∀ a : K, (G : Matrix ι ι K) * (1 + a • ((M : Matrix ι ι K) - 1)) *
      ((G⁻¹ : GL ι K) : Matrix ι ι K) = 1 + a • cTwoX Q u₀ w₀ := fun a => by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
      hconj, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine ⟨(projConj hG).toMonoidHom.comp (quotModelHom e), ?_, ?_, ?_, ?_⟩
  · rw [← ker_quotModelHom (e := e)]
    ext z
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  · exact (projConj hG).surjective.comp quotModelHom_surjective
  · rintro z ⟨hzj, M₁, N, hpM₁, hM₁2, hzN, a, ha⟩
    refine ⟨?_, hzj⟩
    obtain rfl := hpM.eq_of_orderOf_eq_two hpM₁ hM2 hM₁2
    have hNH : N ∈ StatedOmega ⇑Q := hzN.2.1
    obtain ⟨hzA, hzθ⟩ := (represents_iff_quotModelHom hNH).mp hzN
    refine mem_liftSub.mpr ⟨hzA, ?_⟩
    rw [MonoidHom.comp_apply, hzθ, MulEquiv.coe_toMonoidHom, projConj_mk]
    refine hS a _ ?_
    have hNe : (N : Matrix ι ι K) = 1 + a • ((M : Matrix ι ι K) - 1) := by
      rw [← ha, add_sub_cancel]
    rw [coe_isoConj, Units.val_mul, Units.val_mul]
    change (G : Matrix ι ι K) * (N : Matrix ι ι K) * ((G⁻¹ : GL ι K) : Matrix ι ι K) = _
    rw [hNe, hconj']
  · obtain ⟨hpA, hpθ⟩ := (represents_iff_quotModelHom hMΩ).mp hpM
    refine ⟨hpA, isoConj hG ⟨M, hMΩ⟩, ?_, ?_⟩
    · have hMe : (M : Matrix ι ι K) = 1 + (1 : K) • ((M : Matrix ι ι K) - 1) := by
        rw [one_smul, add_sub_cancel]
      rw [coe_isoConj, Units.val_mul, Units.val_mul]
      change (G : Matrix ι ι K) * (M : Matrix ι ι K) * ((G⁻¹ : GL ι K) : Matrix ι ι K) = _
      rw [hMe, hconj', one_smul]
    · rw [MonoidHom.comp_apply, hpθ, MulEquiv.coe_toMonoidHom, projConj_mk]

end Theta

section Levi

variable {K : Type} [Field K] [CharP K 2] {G : Type} [Group G] {A : Subgroup G}

theorem exists_oLeviTheta_top_spec {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂] [Fintype ι]
    [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q₀ : (ι → K) → K} {Q₂₀ : (ι₂ → K) → K}
    {Qf : QuadraticForm K (ι → K)} {Q₂f : QuadraticForm K (ι₂ → K)} (hQf : ⇑Qf = Q₀)
    (hQ₂f : ⇑Q₂f = Q₂₀) (hnd : Qf.polarBilin.Nondegenerate)
    (hQ : ∀ v, Q₀ v = Q₂₀ (fun a => v (oe (.inl a))) +
      StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
    (hSL : commutator SL(2, K) = ⊤) (e : rankTwoQuot A ≃* StatedProj (StatedOmega Q₀)) {p : G}
    (hp : IsSingularRankTwo e Q₀ p) :
    ∃ θ : ↥A →* StatedProj (StatedOmega Q₀), θ.ker = center ↥A ∧ Function.Surjective θ ∧
      (∀ y ∈ {y : G | (∃ j : ℕ, y ^ 2 ^ j = 1) ∧ ∃ M N : GL ι K, Represents e p M ∧
        orderOf M = 2 ∧ Represents e y N ∧ ∃ a : K,
          (N : Matrix ι ι K) - 1 = a • ((M : Matrix ι ι K) - 1)},
        y ∈ liftSub θ (oBarOne oe hQ hSL) ∧ ∃ j : ℕ, y ^ 2 ^ j = 1) ∧
      ∃ hpA : p ∈ A, θ ⟨p, hpA⟩ = oProj Q₀ (oRhoOne oe hQ hSL (slTr 1)) := by
  subst hQf hQ₂f
  have hQu : ∀ s : Fin 2, Qf (oVec oe 0 (uE (.inl s))) = 0 := fun s => by
    rw [quad_oVec_inr hQ, quadPlus_two_uE_inl]
  have hB : ∀ c c' : Fin 2 ⊕ Fin 2, Qf.polarBilin (oVec oe 0 (uE c)) (oVec oe 0 (uE c')) =
      (quadPlus 2 K).polarBilin (uE c) (uE c') := fun c c' => by
    rw [polarBilin_oVec_inr_inr hQ]
  have hS : ∀ (a : K) (Z : StatedOmega ⇑Qf), ((Z : GL ι K) : Matrix ι ι K) =
      1 + a • cTwoX Qf (oVec oe 0 (uE (.inl 0))) (oVec oe 0 (uE (.inl 1))) →
        QuotientGroup.mk Z ∈ oBarOne oe hQ hSL := fun a Z hZ => by
    refine ⟨slTr a, ?_⟩
    change oProj _ (oRhoOne oe hQ hSL (slTr a)) = oProj _ Z
    congr 1
    apply Subtype.ext
    apply Units.ext
    rw [hZ]
    exact oRhoOneGL_slTr hQ a
  obtain ⟨θ, hker, hθ, hα, hpA, Z₀, hZ₀, hθp⟩ := exists_oTheta_spec hnd rfl e hp
    (u₀ := oVec oe 0 (uE (.inl 0))) (w₀ := oVec oe 0 (uE (.inl 1))) (hQu 0) (hQu 1)
    (by rw [hB, polarBilin_uE_inl_inl])
    (linearIndependent_pair_of_polar (y := oVec oe 0 (uE (.inr 0)))
      (x := oVec oe 0 (uE (.inr 1))) (by rw [hB, polarBilin_uE_inl_inr]; simp)
      (by rw [hB, polarBilin_uE_inl_inr]; simp) (by rw [hB, polarBilin_uE_inl_inr]; simp)) hS
  refine ⟨θ, hker, hθ, hα, hpA, ?_⟩
  rw [hθp]
  change oProj _ Z₀ = _
  congr 1
  apply Subtype.ext
  apply Units.ext
  change _ = ((oRhoOneGL oe (slTr 1) : GL ι K) : Matrix ι ι K)
  rw [hZ₀, oRhoOneGL_slTr hQ 1, one_smul]

theorem exists_oLeviTheta_nested_spec {ι₃ ι₂ ι : Type} [Fintype ι₃] [DecidableEq ι₃]
    [Fintype ι₂] [DecidableEq ι₂] [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι}
    {oe' : ι₃ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι₂} {Q₀ : (ι → K) → K} {Q₂₀ : (ι₂ → K) → K}
    {Q₃₀ : (ι₃ → K) → K} {Qf : QuadraticForm K (ι → K)} {Q₂f : QuadraticForm K (ι₂ → K)}
    {Q₃f : QuadraticForm K (ι₃ → K)} (hQf : ⇑Qf = Q₀) (hQ₂f : ⇑Q₂f = Q₂₀) (hQ₃f : ⇑Q₃f = Q₃₀)
    (hnd : Qf.polarBilin.Nondegenerate)
    (hQ : ∀ v, Q₀ v = Q₂₀ (fun a => v (oe (.inl a))) +
      StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
    (hQ₂ : ∀ w, Q₂₀ w = Q₃₀ (fun a => w (oe' (.inl a))) +
      StatedQuadPlus 2 K (fun b => w (oe' (.inr b))))
    (hSL : commutator SL(2, K) = ⊤) (e : rankTwoQuot A ≃* StatedProj (StatedOmega Q₀)) {p : G}
    (hp : IsSingularRankTwo e Q₀ p) :
    ∃ θ : ↥A →* StatedProj (StatedOmega Q₀), θ.ker = center ↥A ∧ Function.Surjective θ ∧
      (∀ y ∈ {y : G | (∃ j : ℕ, y ^ 2 ^ j = 1) ∧ ∃ M N : GL ι K, Represents e p M ∧
        orderOf M = 2 ∧ Represents e y N ∧ ∃ a : K,
          (N : Matrix ι ι K) - 1 = a • ((M : Matrix ι ι K) - 1)},
        y ∈ liftSub θ (oBarL oe hQ) ∧ ∃ j : ℕ, y ^ 2 ^ j = 1) ∧
      ∃ hpA : p ∈ A, θ ⟨p, hpA⟩ = oProj Q₀ (oKappa oe hQ (oRhoOne oe' hQ₂ hSL (slTr 1))) := by
  subst hQf hQ₂f hQ₃f
  set u₀ := oVec oe (oVec oe' 0 (uE (.inl 0))) (0 : Fin 2 ⊕ Fin 2 → K)
  set w₀ := oVec oe (oVec oe' 0 (uE (.inl 1))) (0 : Fin 2 ⊕ Fin 2 → K)
  have hQu : ∀ s : Fin 2, Qf (oVec oe (oVec oe' 0 (uE (.inl s))) 0) = 0 := fun s => by
    rw [quad_oVec_inl hQ, quad_oVec_inr hQ₂, quadPlus_two_uE_inl]
  have hB : ∀ c c' : Fin 2 ⊕ Fin 2, Qf.polarBilin (oVec oe (oVec oe' 0 (uE c)) 0)
      (oVec oe (oVec oe' 0 (uE c')) 0) = (quadPlus 2 K).polarBilin (uE c) (uE c') := fun c c' => by
    rw [polarBilin_oVec_inl_inl hQ, polarBilin_oVec_inr_inr hQ₂]
  have hS : ∀ (a : K) (Z : StatedOmega ⇑Qf), ((Z : GL ι K) : Matrix ι ι K) =
      1 + a • cTwoX Qf u₀ w₀ → QuotientGroup.mk Z ∈ oBarL oe hQ := fun a Z hZ => by
    refine ⟨oRhoOne oe' hQ₂ hSL (slTr a), ?_⟩
    change oProj _ (oKappa oe hQ (oRhoOne oe' hQ₂ hSL (slTr a))) = oProj _ Z
    congr 1
    apply Subtype.ext
    apply Units.ext
    rw [hZ]
    exact oKappaGL_oRhoOneGL_slTr hQ hQ₂ a
  obtain ⟨θ, hker, hθ, hα, hpA, Z₀, hZ₀, hθp⟩ := exists_oTheta_spec hnd rfl e hp (u₀ := u₀)
    (w₀ := w₀) (hQu 0) (hQu 1) (by rw [hB, polarBilin_uE_inl_inl]) (linearIndependent_pair_of_polar
      (y := oVec oe (oVec oe' 0 (uE (.inr 0))) 0) (x := oVec oe (oVec oe' 0 (uE (.inr 1))) 0)
      (by rw [hB, polarBilin_uE_inl_inr]; simp) (by rw [hB, polarBilin_uE_inl_inr]; simp)
      (by rw [hB, polarBilin_uE_inl_inr]; simp)) hS
  refine ⟨θ, hker, hθ, hα, hpA, ?_⟩
  rw [hθp]
  change oProj _ Z₀ = _
  congr 1
  apply Subtype.ext
  apply Units.ext
  change _ = ((oKappaGL oe (oRhoOneGL oe' (slTr 1)) : GL ι K) : Matrix ι ι K)
  rw [hZ₀, oKappaGL_oRhoOneGL_slTr hQ hQ₂ 1, one_smul]

end Levi

end CFSG.ComponentClassification.RankTwoClassical.ORigid
