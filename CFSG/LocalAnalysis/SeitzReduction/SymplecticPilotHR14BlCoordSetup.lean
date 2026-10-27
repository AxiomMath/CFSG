module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaCanonical
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaDickson
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Partner
public import CFSG.RankThree.PartOne.AUTSL.OmegaOut

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup QuadraticMap Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.OrthogonalInvolutions (commSpace finrank_commSpace_conj)
open CFSG.RankThree.PartOne.AUTSL (reflMat reflMat_mem_isometries reflMat_mul_self comm_reflMat_iff
  mul_reflMat_mem_iff mem_matrixDerived_iff_even finrank_commSpace_reflMat)

section Kappa

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem bCoord_kappa_proj (s : matrixIsometries Q) (A : matrixDerived Q) :
    ∃ B : matrixDerived Q, B.val = s.val * A.val * s.val⁻¹ ∧
      matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)
          (matrixProjectiveProjection Q A) = matrixProjectiveProjection Q B :=
  ⟨CFSG.RankThree.PartOne.AUTSL.conjAct Q (matrixIsometryInclusion Q s) A,
    CFSG.RankThree.PartOne.AUTSL.conjAct_inclusion_val s A,
    matrixProjectiveConjugation_mk Q _ A⟩

theorem bCoord_kappa_of_mem (s : matrixIsometries Q) (hs : s.val ∈ matrixDerived Q) :
    matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) =
      MulAut.conj (matrixProjectiveProjection Q ⟨s.val, hs⟩) :=
  CFSG.ComponentClassification.UnbalancedCatalog.kappa_derived_eq_conj ⟨s.val, hs⟩

theorem bCoord_kappa_fix_of_commute (s : matrixIsometries Q) (A : matrixDerived Q)
    (h : s.val * A.val = A.val * s.val) :
    matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)
        (matrixProjectiveProjection Q A) = matrixProjectiveProjection Q A := by
  obtain ⟨B, hB, hκ⟩ := bCoord_kappa_proj s A
  rw [hκ]
  congr 1
  apply Subtype.ext
  rw [hB, h, mul_inv_cancel_right]

theorem bCoord_mem_range_conj_of_congr {X : Type*} [Group X]
    (ε : X ≃* matrixProjectiveDerived Q) {θ : MulAut X} {p : matrixProjectiveDerived Q}
    (h : MulAut.congr ε θ = MulAut.conj p) :
    θ ∈ (MulAut.conj : X →* MulAut X).range := by
  refine ⟨ε.symm p, (MulAut.congr ε).injective ?_⟩
  rw [h]
  refine MulEquiv.ext fun x => ?_
  simp [MulAut.congr_apply]

theorem bCoord_apply_symm {X : Type*} [Group X] (ε : X ≃* matrixProjectiveDerived Q)
    (θ : MulAut X) (y : matrixProjectiveDerived Q) :
    θ (ε.symm y) = ε.symm (MulAut.congr ε θ y) := by
  simp [MulAut.congr_apply]

variable [CharP K 2]

theorem bCoord_proj_injective (hQ : ∃ v, Q v ≠ 0) :
    Function.Injective (matrixProjectiveProjection Q) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have h1 : A ∈ matrixDerivedScalars Q := (QuotientGroup.eq_one_iff A).1 hA
  rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.matrixDerivedScalars_eq_bot_of_charTwo Q
    hQ] at h1
  exact (Subgroup.mem_bot).1 h1

theorem bCoord_commute_of_kappa_fix (hQ : ∃ v, Q v ≠ 0) (s : matrixIsometries Q)
    (A : matrixDerived Q)
    (h : matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)
        (matrixProjectiveProjection Q A) = matrixProjectiveProjection Q A) :
    s.val * A.val = A.val * s.val := by
  obtain ⟨B, hB, hκ⟩ := bCoord_kappa_proj s A
  rw [hκ] at h
  have hBA := bCoord_proj_injective hQ h
  have h2 : s.val * A.val * s.val⁻¹ = A.val := by rw [← hB, hBA]
  calc s.val * A.val = s.val * A.val * s.val⁻¹ * s.val := by group
    _ = A.val * s.val := by rw [h2]

end Kappa

section Absorb

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem bCoord_exists_kappa_of_conj (hImg : matrixProjectiveImage Q = ⊤)
    {α β : MulAut (matrixProjectiveDerived Q)} {s : matrixIsometries Q} (hs : s * s = 1)
    (hβ : β⁻¹ * α * β = matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) :
    ∃ s' : matrixIsometries Q, s' * s' = 1 ∧
      finrank K (commSpace (matrixLinearIso s'.val)) =
        finrank K (commSpace (matrixLinearIso s.val)) ∧
      α = matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s') := by
  have hβmem : β ∈ matrixProjectiveImage Q := hImg ▸ Subgroup.mem_top β
  obtain ⟨p, rfl⟩ := hβmem
  refine ⟨CFSG.ComponentClassification.UnbalancedCatalog.conjIsometry p s, ?_, ?_, ?_⟩
  · apply Subtype.ext
    change matrixConjugation p.val s.val * matrixConjugation p.val s.val = 1
    rw [← map_mul, ← Subgroup.coe_mul, hs, Subgroup.coe_one, map_one]
  · change finrank K (commSpace (matrixLinearIso (matrixConjugation p.val s.val))) = _
    rw [matrixConjugation_apply, map_mul, map_mul, map_inv, finrank_commSpace_conj,
      finrank_commSpace_glFieldAut]
  · rw [← CFSG.ComponentClassification.UnbalancedCatalog.conj_kappa_inclusion, ← hβ]
    group

end Absorb

section Canonical

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

omit [Finite K] [CharP K 2] in
theorem bCoord_mul_self_linear {s : matrixIsometries Q} (hs : s * s = 1) :
    matrixLinearIso s.val * matrixLinearIso s.val = 1 := by
  rw [← map_mul, ← Subgroup.coe_mul, hs, Subgroup.coe_one, map_one]

theorem bCoord_canonical (hQ : (polarBilin Q).Nondegenerate) {s : matrixIsometries Q}
    (hs : s * s = 1) (hodd : Odd (finrank K (commSpace (matrixLinearIso s.val)))) :
    ∃ w : Fin d → K, Q w = 1 ∧ (s.val : Matrix (Fin d) (Fin d) K) *ᵥ w = w ∧
      ∀ g : GL (Fin d) K, g ∈ matrixIsometries Q → g * s.val = s.val * g →
        (g : Matrix (Fin d) (Fin d) K) *ᵥ w = w := by
  have hS : matrixLinearIso s.val ∈ TauCeti.QuadraticMap.orthogonalGroup Q := s.2
  have hSS := bCoord_mul_self_linear hs
  have hB : OmegaInvTypeB Q (matrixLinearIso s.val)
      (finrank K (omegaInvSpace (matrixLinearIso s.val))) := ⟨hS, hSS, rfl, hodd⟩
  obtain ⟨-, hQw, hfix⟩ := omegaInvVec_typeB hQ hB
  refine ⟨omegaInvVec hQ hB.1 hB.2.1, hQw, ?_, fun g hg hgs => ?_⟩
  · exact (hfix _ hS rfl).1
  · have hG : matrixLinearIso g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hg
    have hGS : matrixLinearIso g * matrixLinearIso s.val =
        matrixLinearIso s.val * matrixLinearIso g := by
      rw [← map_mul, ← map_mul, hgs]
    exact (hfix _ hG hGS).1

end Canonical

section Outer

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem bCoord_finrank_eq_one_of_outer (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {X : Type*} [Group X] (ε : X ≃* matrixProjectiveDerived Q) {θ : MulAut X}
    (hout : θ ∉ (MulAut.conj : X →* MulAut X).range)
    (hZ : ∀ y : X, θ y = y → (∀ z : X, θ z = z → z * y = y * z) → y = 1)
    {s : matrixIsometries Q} (hs : s * s = 1)
    (hθ : MulAut.congr ε θ = matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) :
    finrank K (commSpace (matrixLinearIso s.val)) = 1 := by
  have hnot : s.val ∉ matrixDerived Q := fun hΩ =>
    hout (bCoord_mem_range_conj_of_congr ε (hθ.trans (bCoord_kappa_of_mem s hΩ)))
  have hodd : Odd (finrank K (commSpace (matrixLinearIso s.val))) := by
    rw [← Nat.not_even_iff_odd]
    exact fun hev => hnot ((mem_matrixDerived_iff_even hQ hT s.2).2 hev)
  by_contra hr1
  obtain ⟨w, hw, hsw, hfixw⟩ := bCoord_canonical hQ hs hodd
  have hw0 : Q w ≠ 0 := by rw [hw]; exact one_ne_zero
  have hQ0 : ∃ v, Q v ≠ 0 := ⟨w, hw0⟩
  have hsρ : s.val * reflMat Q w hw0 = reflMat Q w hw0 * s.val :=
    (comm_reflMat_iff hQ s.2 hw hw0).2 hsw
  have hx₀ : s.val * reflMat Q w hw0 ∈ matrixDerived Q :=
    (mul_reflMat_mem_iff hQ hT s.2 w hw0).2 hnot
  have hθy : θ (ε.symm (matrixProjectiveProjection Q ⟨_, hx₀⟩)) =
      ε.symm (matrixProjectiveProjection Q ⟨_, hx₀⟩) := by
    rw [bCoord_apply_symm, hθ, bCoord_kappa_fix_of_commute s ⟨_, hx₀⟩ (by
      change s.val * (s.val * reflMat Q w hw0) = s.val * reflMat Q w hw0 * s.val
      rw [mul_assoc, ← hsρ])]
  have hcomm : ∀ z : X, θ z = z → z * ε.symm (matrixProjectiveProjection Q ⟨_, hx₀⟩) =
      ε.symm (matrixProjectiveProjection Q ⟨_, hx₀⟩) * z := by
    intro z hz
    obtain ⟨A, hA⟩ := matrixProjectiveProjection_surjective Q (ε z)
    have hfixA : MulAut.congr ε θ (matrixProjectiveProjection Q A) =
        matrixProjectiveProjection Q A := by
      rw [hA]
      change ε (θ (ε.symm (ε z))) = ε z
      rw [MulEquiv.symm_apply_apply, hz]
    rw [hθ] at hfixA
    have hsA := bCoord_commute_of_kappa_fix hQ0 s A hfixA
    have hAO : A.val ∈ matrixIsometries Q := matrixDerived_le_isometries Q A.2
    have hAw := hfixw A.val hAO hsA.symm
    have hAρ : A.val * reflMat Q w hw0 = reflMat Q w hw0 * A.val :=
      (comm_reflMat_iff hQ hAO hw hw0).2 hAw
    have hAx : A * ⟨_, hx₀⟩ = (⟨_, hx₀⟩ : matrixDerived Q) * A := by
      apply Subtype.ext
      change A.val * (s.val * reflMat Q w hw0) = s.val * reflMat Q w hw0 * A.val
      rw [← mul_assoc, ← hsA, mul_assoc, hAρ, ← mul_assoc]
    apply ε.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, ← hA, ← map_mul, ← map_mul, hAx]
  have hy1 := hZ _ hθy hcomm
  have hx1 : (⟨_, hx₀⟩ : matrixDerived Q) = 1 := by
    apply bCoord_proj_injective hQ0
    rw [map_one]
    have h1 := congrArg ε hy1
    rwa [MulEquiv.apply_symm_apply, map_one] at h1
  have hsρ1 : s.val = reflMat Q w hw0 := by
    have h1 : s.val * reflMat Q w hw0 = 1 := congrArg Subtype.val hx1
    calc s.val = s.val * reflMat Q w hw0 * reflMat Q w hw0 := by
          rw [mul_assoc, reflMat_mul_self, mul_one]
      _ = reflMat Q w hw0 := by rw [h1, one_mul]
  exact hr1 (by rw [hsρ1]; exact finrank_commSpace_reflMat hQ w hw0)

end Outer

section Setting

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem bCoord_fixed_centreless {n : ℕ} (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hLS : L ≤ spGlobal e) (htN : t ∈ normalizer (spGlobal e : Set G))
    (hout : (spGlobal e).normalizerMonoidHom ⟨t, htN⟩ ∉
      (MulAut.conj : spGlobal e →* MulAut (spGlobal e)).range) :
    ∀ y : spGlobal e, (spGlobal e).normalizerMonoidHom ⟨t, htN⟩ y = y →
      (∀ z : spGlobal e, (spGlobal e).normalizerMonoidHom ⟨t, htN⟩ z = z → z * y = y * z) →
        y = 1 := by
  intro y hy hz
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hyt : t * (y : G) = (y : G) * t := by
    have h1 := congrArg Subtype.val hy
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
    calc t * (y : G) = t * y * t⁻¹ * t := by group
      _ = (y : G) * t := by rw [h1]
  have hyL : (y : G) ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    have hθl : (spGlobal e).normalizerMonoidHom ⟨t, htN⟩ ⟨l, hLS hl⟩ = ⟨l, hLS hl⟩ := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      change t * l * t⁻¹ = l
      rw [← mem_centralizer_iff.1 htC l hl, mul_inv_cancel_right]
    exact congrArg Subtype.val (hz _ hθl)
  have hmem : (y : G) ∈ zpowers t := by
    rw [← hKt]
    exact ⟨hyL, mem_centralizer_singleton_iff.2 hyt.symm⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hk2 : t ^ (k % 2) = (y : G) := by
    rw [← hk]
    have h1 := zpow_mod_orderOf t k
    rw [ht] at h1
    exact_mod_cast h1
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [h0, zpow_zero] at hk2
    exact Subtype.ext hk2.symm
  · rw [h1, zpow_one] at hk2
    exfalso
    have htS : t ∈ spGlobal e := hk2 ▸ y.2
    apply hout
    rw [normalizerMonoidHom_eq_conj_of_mem htS htN]
    exact ⟨_, rfl⟩

theorem bCoord_exists_refl {κ : Sp2mKind} {n f : ℕ} (hn : 1 ≤ n) (hK4 : 4 ≤ Nat.card K)
    (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : SpOmegaRowGlobal e t f κ) (htN : t ∈ normalizer (spGlobal e : Set G))
    {K' : Type} [Field K'] [Finite K'] [CharP K' 2] {d : ℕ} {Q : QuadraticForm K' (Fin d → K')}
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K' (Fin d → K'), finrank K' T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hImg : matrixProjectiveImage Q = ⊤) (ε : spGlobal e ≃* matrixProjectiveDerived Q)
    (hθt : ∃ (β₀ : MulAut (matrixProjectiveDerived Q)) (s₁ : matrixIsometries Q), s₁ * s₁ = 1 ∧
      β₀⁻¹ * MulAut.congr ε ((spGlobal e).normalizerMonoidHom ⟨t, htN⟩) * β₀ =
        matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s₁)) :
    ∃ s₀ : matrixIsometries Q, s₀ * s₀ = 1 ∧
      finrank K' (commSpace (matrixLinearIso s₀.val)) = 1 ∧
      MulAut.congr ε ((spGlobal e).normalizerMonoidHom ⟨t, htN⟩) =
        matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s₀) := by
  obtain ⟨β₀, s₁, hs₁, hβ₀⟩ := hθt
  obtain ⟨s₀, hs₀, -, hθ⟩ := bCoord_exists_kappa_of_conj hImg hs₁ hβ₀
  exact ⟨s₀, hs₀, bCoord_finrank_eq_one_of_outer hQ hT ε (hglob.2 htN).1
    (bCoord_fixed_centreless e ht hKt (le_spGlobal hK4 hn e) htN (hglob.2 htN).1) hs₀ hθ, hθ⟩

end Setting

end CFSG.SeitzReduction.SymplecticPilot
