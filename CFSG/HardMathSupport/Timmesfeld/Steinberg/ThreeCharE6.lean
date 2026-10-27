module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharDataE6
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharStabilizer

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Steinberg

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem e6ThreeCheck_true : e6ThreeCheck () = true := by
  decide +kernel

theorem e6ThreeCheck_spec :
    orbitCheck3 .E6 e6ThreeReps e6ThreeOrbit = true ∧
      ∀ S ∈ [e6ThreeStab0, e6ThreeStab1, e6ThreeStab2, e6ThreeStab3, e6ThreeStab4, e6ThreeStab5],
        S.check e6Certificate = true ∧ (S.passing e6Certificate).length ≤ 1 := by
  have h := e6ThreeCheck_true
  simpa only [e6ThreeCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] using h

theorem e6ThreeOrbit_check : orbitCheck3 .E6 e6ThreeReps e6ThreeOrbit = true :=
  (e6ThreeCheck_spec).1

theorem card_kernelPosStabilizer_le_E6_three :
    ∀ ρ < 6,
    Nat.card (kernelPosStabilizer (triChar (τ := .E6) (vec3 (e6ThreeReps.getD ρ [])))) ≤ 1 := by
  intro ρ hρ
  interval_cases ρ
  · obtain ⟨hc, hp⟩ := (e6ThreeCheck_spec).2 e6ThreeStab0 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le e6Certificate_check hc).trans hp
  · obtain ⟨hc, hp⟩ := (e6ThreeCheck_spec).2 e6ThreeStab1 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le e6Certificate_check hc).trans hp
  · obtain ⟨hc, hp⟩ := (e6ThreeCheck_spec).2 e6ThreeStab2 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le e6Certificate_check hc).trans hp
  · obtain ⟨hc, hp⟩ := (e6ThreeCheck_spec).2 e6ThreeStab3 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le e6Certificate_check hc).trans hp
  · obtain ⟨hc, hp⟩ := (e6ThreeCheck_spec).2 e6ThreeStab4 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le e6Certificate_check hc).trans hp
  · obtain ⟨hc, hp⟩ := (e6ThreeCheck_spec).2 e6ThreeStab5 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le e6Certificate_check hc).trans hp

theorem charStabilizer_eq_kernelWeylGroup_E6_three
    (χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* Z3)
    (hD4 : ∀ t : WeylGroup .E6,
      ¬ IsCharConj (triChar (τ := .E6) (vec3 (e6ThreeReps.getD 6 []))) χ t)
    (hA2 : ∀ t : WeylGroup .E6,
      ¬ IsCharConj (triChar (τ := .E6) (vec3 (e6ThreeReps.getD 7 []))) χ t) :
    charStabilizer χ = kernelWeylGroup χ := by
  obtain ⟨ρ, hρ, t, ht⟩ := exists_isCharConj_of_orbitCheck3 e6ThreeOrbit_check χ
  have hlen : e6ThreeReps.length = 8 := rfl
  rw [hlen] at hρ
  have hρ6 : ρ < 6 := by
    by_contra hcon
    have h67 : ρ = 6 ∨ ρ = 7 := by omega
    rcases h67 with rfl | rfl
    · exact hD4 t ht
    · exact hA2 t ht
  have hq : Nat.card (CharQuotient χ) ≤ 1 := by
    rw [← Nat.card_congr (quotientMulEquivOfIsCharConj ht).toEquiv]
    exact card_quotient_le_card_kernelPosStabilizer.trans
      (card_kernelPosStabilizer_le_E6_three ρ hρ6)
  exact charStabilizer_eq_of_card_le_one hq

section Kernel

variable {τ : Tag}

theorem kernelRoots_eq_image_of_isCharConj
    {M : Type*} [CommGroup M]
    {χ χ' : Multiplicative (Fin τ.rank → ℤ) →* M} {t : WeylGroup τ} (h : IsCharConj χ χ' t) :
    kernelRoots χ' = (fun α => t • α) '' kernelRoots χ := by
  ext α
  rw [kernelRoots_iff_of_isCharConj h]
  constructor
  · intro hα
    exact ⟨t⁻¹ • α, hα, smul_inv_smul t α⟩
  · rintro ⟨β, hβ, rfl⟩
    rwa [inv_smul_smul]

theorem rootCharStabilizerSubgroup_eq_kernelReflectionGroup_of_triChar_ker
    {K : Type} [Field K]
    (a : Fin τ.rank → Kˣ) (h3 : ∀ i, a i ^ 3 = 1)
    (hZ3 : ∀ χ : Multiplicative (Fin τ.rank → ℤ) →* Z3,
      (∀ x, rootCharHom3 a x = 1 ↔ χ x = 1) → charStabilizer χ ≤ kernelWeylGroup χ) :
    rootCharStabilizerSubgroup a = kernelReflectionGroup a := by
  obtain ⟨χ', hker⟩ := exists_triChar_ker_eq (rootCharHom3 a) (rootCharHom3_pow_three a h3)
  have hS : rootCharStabilizerSubgroup a = charStabilizer (rootCharHom3 a) :=
    Subgroup.ext fun w => Iff.rfl
  have hW : kernelReflectionGroup a = kernelWeylGroup (rootCharHom3 a) := rfl
  rw [hS, hW]
  refine le_antisymm ?_ kernelWeylGroup_le
  rw [charStabilizer_congr_ker hker, kernelWeylGroup_congr_ker hker]
  exact hZ3 χ' hker

end Kernel

theorem rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E6_three
    {K : Type} [Field K]
    (a : Fin Tag.E6.rank → Kˣ) (h3 : ∀ i, a i ^ 3 = 1)
    (h6 : ∀ t : WeylGroup .E6, kernelRoots (rootCharHom3 a) ≠
      (fun α => t • α) '' kernelRoots (triChar (τ := .E6) (vec3 (e6ThreeReps.getD 6 []))))
    (h7 : ∀ t : WeylGroup .E6, kernelRoots (rootCharHom3 a) ≠
      (fun α => t • α) '' kernelRoots (triChar (τ := .E6) (vec3 (e6ThreeReps.getD 7 [])))) :
    rootCharStabilizerSubgroup a = kernelReflectionGroup a := by
  refine rootCharStabilizerSubgroup_eq_kernelReflectionGroup_of_triChar_ker a h3 fun χ hker => ?_
  refine (charStabilizer_eq_kernelWeylGroup_E6_three χ ?_ ?_).le
  · intro t ht
    exact h6 t ((kernelRoots_congr_ker hker).trans (kernelRoots_eq_image_of_isCharConj ht))
  · intro t ht
    exact h7 t ((kernelRoots_congr_ker hker).trans (kernelRoots_eq_image_of_isCharConj ht))

end CFSG.HardMathSupport.Timmesfeld.Steinberg

end
