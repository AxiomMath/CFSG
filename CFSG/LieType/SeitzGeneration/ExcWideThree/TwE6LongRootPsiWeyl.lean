module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootAdj
public import CFSG.LieType.Chevalley.E6PinnedAdjoint

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphHighestRoot

open Psi

variable {K : Type} [Field K]

theorem Psi.reflect_mem_degOne_aux : ∀ γ ∈ degOneRoots, ∀ j : Fin TwistTag.E6.tag.rank,
    j ≠ e6Idx 1 → reflect TwistTag.E6.tag j γ ∈ degOneRoots := by
  decide +kernel

theorem Psi.reflect_highest_aux : ∀ j : Fin TwistTag.E6.tag.rank, j ≠ e6Idx 1 →
    reflect TwistTag.E6.tag j e6HighestRoot = e6HighestRoot := by
  decide +kernel

theorem Psi.comm_reflect_zero_five_aux : ∀ γ ∈ degOneRoots,
    reflect TwistTag.E6.tag 0 (reflect TwistTag.E6.tag 5 γ) =
      reflect TwistTag.E6.tag 5 (reflect TwistTag.E6.tag 0 γ) := by
  decide +kernel

theorem Psi.comm_reflect_two_four_aux : ∀ γ ∈ degOneRoots,
    reflect TwistTag.E6.tag 2 (reflect TwistTag.E6.tag 4 γ) =
      reflect TwistTag.E6.tag 4 (reflect TwistTag.E6.tag 2 γ) := by
  decide +kernel

theorem Psi.orbitWord_zero : TwistTag.E6.orbitWord 0 = [0, 5] := by decide +kernel

theorem Psi.orbitWord_one : TwistTag.E6.orbitWord 1 = [2, 4] := by decide +kernel

theorem Psi.orbitWord_two : TwistTag.E6.orbitWord 2 = [3] := by decide +kernel

theorem Psi.reflect_sub_highest {j : Fin TwistTag.E6.tag.rank}
    (hj : j ≠ e6Idx 1) (v : Fin TwistTag.E6.tag.rank → ℤ) :
    reflect TwistTag.E6.tag j (v - e6HighestRoot) =
      reflect TwistTag.E6.tag j v - e6HighestRoot := by
  have h := map_sub (reflectHom TwistTag.E6.tag j) v e6HighestRoot
  simp only [reflectHom_apply] at h
  rw [h, reflect_highest_aux j hj]

@[expose] def Psi.sD {j : Fin TwistTag.E6.tag.rank} (hj : j ≠ e6Idx 1) (γ : Dr) : Dr :=
  ⟨reflect TwistTag.E6.tag j γ.1, reflect_mem_degOne_aux γ.1 γ.2 j hj⟩

@[expose] def Psi.signedPerm (K : Type) [Field K] (ε : Dr → K) (σ : Dr → Dr) : Rv K →ₗ[K] Rv K where
  toFun v γ := ε γ * v (σ γ)
  map_add' v w := by
    funext γ
    simp [mul_add]
  map_smul' c v := by
    funext γ
    simp [mul_left_comm]

theorem Psi.piD_weylElt
    {j : Fin TwistTag.E6.tag.rank} (hj : j ≠ e6Idx 1) (y : RootModule TwistTag.E6.tag K)
    (γ : Dr) :
    piD K ((weylElt TwistTag.E6.tag K j 1 : Module.End K (RootModule TwistTag.E6.tag K)) y) γ =
      (-1 : K) ^ stringDown TwistTag.E6.tag j (reflect TwistTag.E6.tag j γ.1 - e6HighestRoot) *
        piD K y (sD hj γ) := by
  have key : (piD K).comp (weylElt TwistTag.E6.tag K j 1 :
      Module.End K (RootModule TwistTag.E6.tag K)) = (signedPerm K (fun γ => (-1 : K) ^
        stringDown TwistTag.E6.tag j (reflect TwistTag.E6.tag j γ.1 - e6HighestRoot))
        (sD hj)).comp (piD K) := by
    refine Finsupp.basisSingleOne.ext fun b => ?_
    rcases b with l | ⟨μ, hμ⟩
    · show piD K ((weylElt TwistTag.E6.tag K j 1 : Module.End K (RootModule TwistTag.E6.tag K))
        (hVec TwistTag.E6.tag K l)) = signedPerm K _ (sD hj) (piD K (hVec TwistTag.E6.tag K l))
      rw [weylElt_hVec, map_sub, map_smul, piD_hVec, piD_hVec]
      ext γ
      simp [signedPerm]
    · have hb : (Finsupp.single (Sum.inr ⟨μ, hμ⟩) 1 : RootModule TwistTag.E6.tag K) =
          rootVec TwistTag.E6.tag K μ := (rootVec_eq_single_of_isRoot hμ).symm
      show piD K ((weylElt TwistTag.E6.tag K j 1 : Module.End K (RootModule TwistTag.E6.tag K))
        (Finsupp.single (Sum.inr ⟨μ, hμ⟩) 1)) =
        signedPerm K _ (sD hj) (piD K (Finsupp.single (Sum.inr ⟨μ, hμ⟩) 1))
      rw [hb, E6PinnedAdjoint.weylElt_one_rootVec j hμ, map_smul]
      ext γ
      show ((-1 : K) ^ stringDown TwistTag.E6.tag j μ) *
          piD K (rootVec TwistTag.E6.tag K (reflect TwistTag.E6.tag j μ)) γ =
        (-1 : K) ^ stringDown TwistTag.E6.tag j (reflect TwistTag.E6.tag j γ.1 -
          e6HighestRoot) * piD K (rootVec TwistTag.E6.tag K μ) (sD hj γ)
      simp only [piD_rootVec]
      show _ = (-1 : K) ^ stringDown TwistTag.E6.tag j (reflect TwistTag.E6.tag j γ.1 -
        e6HighestRoot) * (if μ = reflect TwistTag.E6.tag j γ.1 - e6HighestRoot then 1 else 0)
      by_cases h : μ = reflect TwistTag.E6.tag j γ.1 - e6HighestRoot
      · have h' : reflect TwistTag.E6.tag j μ = γ.1 - e6HighestRoot := by
          rw [h, reflect_sub_highest hj, reflect_reflect]
        rw [if_pos h, if_pos h', ← h]
      · have h' : ¬ reflect TwistTag.E6.tag j μ = γ.1 - e6HighestRoot := by
          intro e
          apply h
          have := congrArg (reflect TwistTag.E6.tag j) e
          rw [reflect_reflect, reflect_sub_highest hj] at this
          exact this
        rw [if_neg h, if_neg h']
        simp
  exact congrFun (LinearMap.congr_fun key y) γ

variable (K) in
@[expose] def Psi.IsStep
    (g : Module.End K (RootModule TwistTag.E6.tag K)) (σ : Dr → Dr) : Prop :=
  ∃ (s : K) (ε : Dr → K), (s = 1 ∨ s = -1) ∧ (∀ γ, ε γ = 1 ∨ ε γ = -1) ∧
    g (v0 K) = s • v0 K ∧ ∀ y γ, piD K (g y) γ = ε γ * piD K y (σ γ)

theorem Psi.IsStep.mul
    {g₁ g₂ : Module.End K (RootModule TwistTag.E6.tag K)} {σ₁ σ₂ : Dr → Dr}
    (h₁ : IsStep K g₁ σ₁) (h₂ : IsStep K g₂ σ₂) : IsStep K (g₁ * g₂) (σ₂ ∘ σ₁) := by
  obtain ⟨s₁, ε₁, hs₁, hε₁, hv₁, hp₁⟩ := h₁
  obtain ⟨s₂, ε₂, hs₂, hε₂, hv₂, hp₂⟩ := h₂
  refine ⟨s₂ * s₁, fun γ => ε₁ γ * ε₂ (σ₁ γ), ?_, fun γ => ?_, ?_, fun y γ => ?_⟩
  · rcases hs₁ with rfl | rfl <;> rcases hs₂ with rfl | rfl <;> simp
  · rcases hε₁ γ with h | h <;> rcases hε₂ (σ₁ γ) with h' | h' <;> simp [h, h']
  · rw [Module.End.mul_apply, hv₂, map_smul, hv₁, smul_smul]
  · rw [Module.End.mul_apply, hp₁, hp₂, Function.comp_apply, mul_assoc]

theorem Psi.weylElt_isStep
    {j : Fin TwistTag.E6.tag.rank} (hj : j ≠ e6Idx 1) :
    IsStep K (weylElt TwistTag.E6.tag K j 1 : Module.End K (RootModule TwistTag.E6.tag K))
      (sD hj) := by
  have hr : reflect TwistTag.E6.tag j (-e6HighestRoot) = -e6HighestRoot := by
    have h := map_neg (reflectHom TwistTag.E6.tag j) e6HighestRoot
    simp only [reflectHom_apply] at h
    rw [h, reflect_highest_aux j hj]
  refine ⟨(-1) ^ stringDown TwistTag.E6.tag j (-e6HighestRoot),
    fun γ => (-1 : K) ^ stringDown TwistTag.E6.tag j
      (reflect TwistTag.E6.tag j γ.1 - e6HighestRoot), neg_one_pow_eq_or K _,
    fun γ => neg_one_pow_eq_or K _, ?_, fun y γ => piD_weylElt hj y γ⟩
  unfold v0
  rw [E6PinnedAdjoint.weylElt_one_rootVec j isRoot_neg_highest, hr]

theorem Psi.psi_conj_of_isStep (n : ModGL TwistTag.E6.tag K)
    {σ : Dr → Dr}
    (h : IsStep K (n : Module.End K (RootModule TwistTag.E6.tag K)) σ) :
    ∃ ε : Dr → K, (∀ γ, ε γ = 1 ∨ ε γ = -1) ∧ ∀ (z : ModGL TwistTag.E6.tag K) (γ : Dr),
      psi K (n * z * n⁻¹) γ = ε γ * psi K z (σ γ) := by
  obtain ⟨s, ε, hs, hε, hv, hp⟩ := h
  refine ⟨fun γ => s * ε γ, fun γ => ?_, fun z γ => ?_⟩
  · rcases hs with rfl | rfl <;> rcases hε γ with h | h <;> simp [h]
  · have h0 := E6PinnedAdjoint.units_inv_apply_of_apply_eq n s hs hv
    have := psi_conj n z s (signedPerm K ε σ) h0 fun y => by
      ext γ
      exact hp y γ
    rw [this]
    simp [signedPerm, mul_assoc, psi_apply]

theorem Psi.reflD_eq_of {a : Fin TwistTag.E6.foldedTag.rank} {γ γ' : Dr}
    (h : reflOrb a γ.1 = γ'.1) : reflD a γ = γ' := by
  unfold reflD
  rw [dif_pos (h ▸ γ'.2)]
  exact Subtype.ext h

theorem Psi.sD_comm_zero_five (γ : Dr) :
    reflD 0 γ = sD (j := 5) (by decide) (sD (j := 0) (by decide) γ) := by
  refine reflD_eq_of ?_
  simp only [reflOrb, orbitWord_zero, sD, List.foldr_cons, List.foldr_nil]
  exact comm_reflect_zero_five_aux γ.1 γ.2

theorem Psi.sD_comm_two_four (γ : Dr) :
    reflD 1 γ = sD (j := 4) (by decide) (sD (j := 2) (by decide) γ) := by
  refine reflD_eq_of ?_
  simp only [reflOrb, orbitWord_one, sD, List.foldr_cons, List.foldr_nil]
  exact comm_reflect_two_four_aux γ.1 γ.2

theorem Psi.sD_three (γ : Dr) :
    reflD 2 γ = sD (j := 3) (by decide) γ := by
  refine reflD_eq_of ?_
  simp only [reflOrb, orbitWord_two, sD, List.foldr_cons, List.foldr_nil]

theorem Psi.isStep_orbitReflection
    {a : Fin TwistTag.E6.foldedTag.rank} (ha : a ≠ 3) :
    IsStep K (canonicalRep (coxeterSystem TwistTag.E6.tag) K (TwistTag.E6.orbitReflection a) :
      Module.End K (RootModule TwistTag.E6.tag K)) (reflD a) := by
  have hcases : ∀ a : Fin TwistTag.E6.foldedTag.rank, a ≠ 3 → a = 0 ∨ a = 1 ∨ a = 2 := by
    decide
  rw [canonicalRep_orbitReflection]
  rcases hcases a ha with rfl | rfl | rfl
  · rw [orbitWord_zero]
    have h := (weylElt_isStep (K := K) (j := 0) (by decide)).mul
      (weylElt_isStep (K := K) (j := 5) (by decide))
    have e : (sD (j := 5) (by decide) ∘ sD (j := 0) (by decide)) = reflD 0 :=
      funext fun γ => (sD_comm_zero_five γ).symm
    rw [e] at h
    simpa using h
  · rw [orbitWord_one]
    have h := (weylElt_isStep (K := K) (j := 2) (by decide)).mul
      (weylElt_isStep (K := K) (j := 4) (by decide))
    have e : (sD (j := 4) (by decide) ∘ sD (j := 2) (by decide)) = reflD 1 :=
      funext fun γ => (sD_comm_two_four γ).symm
    rw [e] at h
    simpa using h
  · rw [orbitWord_two]
    have h := weylElt_isStep (K := K) (j := 3) (by decide)
    have e : sD (j := 3) (by decide) = reflD 2 := funext fun γ => (sD_three γ).symm
    rw [e] at h
    simpa using h

variable (K) in
theorem psi_conj_orbitReflection
    {a : Fin TwistTag.E6.foldedTag.rank} (ha : a ≠ 3) :
    ∃ ε : Dr → K, (∀ γ, ε γ = 1 ∨ ε γ = -1) ∧ ∀ (z : ModGL TwistTag.E6.tag K) (γ : Dr),
      psi K (canonicalRep (coxeterSystem TwistTag.E6.tag) K (TwistTag.E6.orbitReflection a) * z *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K (TwistTag.E6.orbitReflection a))⁻¹) γ =
        ε γ * psi K z (reflD a γ) :=
  psi_conj_of_isStep _ (isStep_orbitReflection ha)

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot
