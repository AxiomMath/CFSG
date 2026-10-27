module

public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalRows
public import CFSG.HardMathSupport.Dickson.Bal207.OrthEightLocal
public import CFSG.HardMathSupport.Dickson.Bal207.OrthEightSemilin
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.Residuals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2D4

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open Module CFSG.RankThree.Classical2 CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonalAut
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
  CFSG.GroupTheory.WeirSylow CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open scoped Pointwise

section Conj

variable {K : Type} [Field K] [Finite K]

theorem exists_conj_mem_matrixProjectiveImage_four [CharP K 2]
    {g : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))}
    (hg : Nat.Coprime 3 (orderOf g)) :
    ∃ β : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
      β⁻¹ * g * β ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) := by
  classical
  set P := projectivePointFamily (coordinateQuadPlus 4 K) with hP
  set O := MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) P
    with hO
  have hmemE : ∀ δ, δ ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) ↔ δ • P = P :=
    CFSG.SeitzReduction.OmegaPilot.mem_image_iff_smul_pointFamily le_rfl
  have hgO : ∀ Y ∈ O, g • Y ∈ O := fun Y hY => by
    obtain ⟨β, rfl⟩ := hY
    exact ⟨g * β, mul_smul _ _ _⟩
  have hO13 : O.ncard = 1 ∨ O.ncard = 3 :=
    CFSG.SeitzReduction.OmegaPilot.orbit_pointFamily_ncard_four (K := K)
  obtain ⟨Y, hYO, hgY⟩ : ∃ Y ∈ O, g • Y = Y := by
    rcases hO13 with h1 | h3
    · obtain ⟨Z, hZ⟩ := Set.ncard_eq_one.1 h1
      have hPO : P ∈ O := MulAction.mem_orbit_self P
      have hgP := hgO P hPO
      rw [hZ, Set.mem_singleton_iff] at hPO hgP
      exact ⟨P, MulAction.mem_orbit_self P, hgP.trans hPO.symm⟩
    · obtain ⟨a, b, c, hab, hac, hbc, habc⟩ := Set.ncard_eq_three.1 h3
      have hmem : ∀ Y ∈ O, Y = a ∨ Y = b ∨ Y = c := fun Y hY => by
        rw [habc] at hY
        simpa using hY
      have haO : a ∈ O := by rw [habc]; simp
      have hbO : b ∈ O := by rw [habc]; simp
      have hcO : c ∈ O := by rw [habc]; simp
      rcases exists_fixed_of_three hg hab hac hbc (hmem _ (hgO a haO)) (hmem _ (hgO b hbO))
          (hmem _ (hgO c hcO)) with h | h | h
      · exact ⟨a, haO, h⟩
      · exact ⟨b, hbO, h⟩
      · exact ⟨c, hcO, h⟩
  obtain ⟨β, rfl⟩ := hYO
  exact ⟨β, (hmemE _).2 (by rw [mul_smul, mul_smul, hgY, inv_smul_smul])⟩

end Conj

namespace OrthEight

section Inner

variable {K : Type} [Field K] [Finite K]

theorem coreFreeAt_conj_projOrthDerived (hK : Nat.card K = 8) {d : ℕ} (hd : 0 < d)
    {Q : QuadraticForm K (Fin d → K)} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K (Fin d → K), finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hpar : IsPlusType Q ↔ Even (finrank K (Fin d → K) / 2))
    (hE : ∀ g : MulAut (ProjOrthDerived Q), Nat.Coprime 3 (orderOf g) →
      ∃ β : MulAut (ProjOrthDerived Q),
        MulAut.congr (coordBridge Q hd).symm (β⁻¹ * g * β) ∈ matrixProjectiveImage Q)
    {a : ProjOrthDerived Q} (ha : orderOf a = 3) : CoreFreeAt 3 (MulAut.conj a) := by
  refine coreFreeAt_conj_of_inner (KCOrthogonalD4.conj_injective_projOrthDerived Q hQ hT)
    (noNormalPPrime_centralizer_projOrthDerived hK hQ hT hpar ha) fun g hg _ hfix => ?_
  obtain ⟨β, hβ⟩ := hE g hg
  have hco : Nat.Coprime 3 (orderOf (β⁻¹ * g * β)) := by
    have h := MulEquiv.orderOf_eq (MulAut.conj β⁻¹) g
    rw [MulAut.conj_apply, inv_inv] at h
    rwa [h]
  obtain ⟨G, hG, hGα⟩ := exists_isometry_of_mem_matrixProjectiveImage hK hd _ hβ hco
  have hα : β⁻¹ * g * β = 1 := by
    refine eq_one_of_fixes_centralizer_projOrthDerived hK hQ hT hpar
      ((MulEquiv.orderOf_eq β⁻¹ a).trans ha) hG hGα hco fun t ht => ?_
    have ht' : β t ∈ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at ht ⊢
      have h1 := congrArg β ht
      rwa [map_mul, map_mul, MulAut.apply_inv_self] at h1
    rw [MulAut.mul_apply, MulAut.mul_apply, hfix _ ht', MulAut.inv_apply_self]
  calc g = β * (β⁻¹ * g * β) * β⁻¹ := by group
    _ = 1 := by rw [hα, mul_one, mul_inv_cancel]

end Inner

end OrthEight

section Row


theorem isLocallyBalancedAbs_three_one_d4Eight {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 8) :
    IsLocallyBalancedAbs 3 1 (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := by
  classical
  have := OrthEight.charP_two hK
  have hd : 0 < 2 * 4 := by norm_num
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus (n := 4) (K := K) (by norm_num)
  have hpar : IsPlusType (coordinateQuadPlus 4 K) ↔ Even (finrank K (Fin (2 * 4) → K) / 2) :=
    iff_of_true ((isPlusType_congr (coordinatePlusIsometry 4 K)).1 (isPlusType_quadPlus K 4))
      (by rw [Module.finrank_fin_fun]; decide)
  have hinj := KCOrthogonalD4.conj_injective_matrixProjectiveDerived _ hd hQ hT
  set φ := coordBridge (coordinateQuadPlus 4 K) hd with hφ
  refine isLocallyBalancedAbs_one_of_good Nat.prime_three hinj fun x hx3 hx1 => Or.inr ?_
  by_cases hxi : x ∈ innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))
  · obtain ⟨y, rfl⟩ := hxi
    have hy : orderOf (φ y) = 3 := by
      rw [MulEquiv.orderOf_eq, ← orderOf_injective _ hinj y]
      exact orderOf_eq_prime hx3 hx1
    have hE : ∀ g : MulAut (ProjOrthDerived (coordinateQuadPlus 4 K)),
        Nat.Coprime 3 (orderOf g) → ∃ β : MulAut (ProjOrthDerived (coordinateQuadPlus 4 K)),
          MulAut.congr φ.symm (β⁻¹ * g * β) ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) := by
      intro g hg
      obtain ⟨β₀, hβ₀⟩ := exists_conj_mem_matrixProjectiveImage_four
        (g := MulAut.congr φ.symm g) (by rwa [MulEquiv.orderOf_eq])
      refine ⟨MulAut.congr φ β₀, ?_⟩
      rwa [map_mul, map_mul, map_inv, congr_symm_congr]
    have h := coreFreeAt_congr φ.symm
      (OrthEight.coreFreeAt_conj_projOrthDerived hK hd hQ hT hpar hE hy)
    have hc : MulAut.congr φ.symm (MulAut.conj (φ y)) = MulAut.conj y :=
      MulEquiv.ext fun t => by simp [MulAut.congr_apply, MulAut.conj_apply]
    rwa [hc] at h
  · obtain ⟨e⟩ := nonempty_matrixProjective_equiv_adjointGroup K
    have hx' : (MulAut.congr e x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
    have hout : MulAut.congr e x ∉ innerAut _ := by
      rintro ⟨c, hc⟩
      apply hxi
      refine ⟨e.symm c, ?_⟩
      have h1 : MulAut.congr e.symm (MulAut.conj c) = MulAut.conj (e.symm c) :=
        MulEquiv.ext fun t => by simp [MulAut.congr_apply, MulAut.conj_apply]
      rw [← h1, hc, congr_symm_congr]
    have h := coreFreeAt_congr e.symm
      (d4OuterCoreFree_of_classes d4GraphCoreFree_holds d4GraphFieldStdCoreFree_holds
        d4FieldStdCoreFree_holds K (by rw [hK]; norm_num) _ hx' hout)
    rwa [congr_symm_congr] at h

theorem bal207LocalBalRow_d4Eight : Bal207LocalBalRow fun p d => p = 3 ∧ IsD4EightIdx d := by
  rintro p ⟨d, hv⟩ ⟨rfl, hd⟩
  cases d with
  | D r q =>
    obtain ⟨rfl, hp, he⟩ := hd
    obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even 4 q hv hp (MulEquiv.refl _)
    have hF : Nat.card F = 8 := by rw [hcard, hp, he]; norm_num
    exact IsLocallyBalancedAbs.of_mulEquiv (coordinatePlusWitnessEquiv F e)
      (isLocallyBalancedAbs_three_one_d4Eight hF)
  | _ => exact False.elim hd

end Row

end CFSG.HardMathSupport.Dickson.Bal207

end
