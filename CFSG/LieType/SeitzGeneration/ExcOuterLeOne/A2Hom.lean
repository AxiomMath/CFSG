module

public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.A2Facts
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.A2Lemma
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.IrrationalRoot
public import CFSG.LinearAlgebra.DesarguesianPlanes.SteinbergRecognition

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement MatrixGroups

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne



section Gen

variable {τ : Tag}

theorem exists_adjData_valid_all (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ∃ D : AdjData τ, D.Valid ∧ NoG2 τ := by
  rcases hτ with rfl | rfl | rfl | rfl
  · exact ⟨_, f4Data_valid, noG2_F4⟩
  · exact exists_adjData_valid_E (Or.inl rfl)
  · exact exists_adjData_valid_E (Or.inr (Or.inl rfl))
  · exact exists_adjData_valid_E (Or.inr (Or.inr rfl))

theorem commutator_xPar_pair {D : AdjData τ} (hD : D.Valid) (hτ : NoG2 τ) {K : Type} [Field K]
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β)
    (hs : IsRoot τ (α + β)) (hd : ¬IsRoot τ (β - α))
    (h12 : ¬IsRoot τ (α + (2 : ℕ) • β)) (h21 : ¬IsRoot τ ((2 : ℕ) • α + β)) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ a b : K,
      ⁅xPar (rootOperatorFamily τ) α a, xPar (rootOperatorFamily τ) β b⁆ =
        xPar (rootOperatorFamily τ) (α + β) ((ε : K) * a * b) := by
  have hne'' : β ≠ -α := fun h => hne' (by rw [h, neg_neg])
  have hN : (RootOperatorFamily'.coeff11 (rootOperatorFamily τ) hD ⟨_, hα⟩ ⟨_, hβ⟩).natAbs = 1 := by
    rw [RootOperatorFamily'.coeff11,
      RootOperatorFamily'.bracketCoeff_natAbs (rootOperatorFamily τ) hD hne'' hs]
    exact stringNorm_of_not_isRoot hd
  refine ⟨RootOperatorFamily'.coeff11 (rootOperatorFamily τ) hD ⟨_, hα⟩ ⟨_, hβ⟩, ?_, fun a b => ?_⟩
  · rcases Int.natAbs_eq_iff.1 hN with h | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr (by simpa using h)
  · rw [commutator_xPar (F := rootOperatorFamily τ) hD hτ hα hβ hne hne' a b,
      xPar_of_not_isRoot h12, xPar_of_not_isRoot h21, mul_one, mul_one]

theorem intCast_eq_one_of_pm_one {K : Type} [Field K] [CharP K 2] {ε : ℤ} (h : ε = 1 ∨ ε = -1) :
    (ε : K) = 1 := by
  rcases h with rfl | rfl
  · simp
  · simp [CharTwo.neg_eq]

@[expose] noncomputable def a2X (τ : Tag) (K : Type) [Field K] (i j : Fin 3) (c : K) :
    ↥(adjointGroup τ K) :=
  xPar (rootOperatorFamily τ) (a2Root τ i j) c

theorem a2_steinbergFamily (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K]
    [CharP K 2] : CFSG.DesarguesianPlanes.IsSteinbergFamily (a2X τ K) := by
  obtain ⟨D, hD, hG2⟩ := exists_adjData_valid_all hτ
  have hroot : ∀ i j : Fin 3, i ≠ j → IsRoot τ (a2Root τ i j) := fun i j hij =>
    mem_rootFinset.1 (a2Root_mem hτ i j hij)
  refine ⟨fun i j _ c d => (xPar_add _ c d).symm, fun i j k l hij hkl hex c d => ?_⟩
  unfold a2X
  by_cases hjk : j = k
  · subst hjk
    have hil : i ≠ l := fun h => hex ⟨rfl, h.symm⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := a2_adj hτ i j j l ⟨hij, hkl, hex, Or.inl rfl⟩
    have hsum : IsRoot τ (a2Root τ i j + a2Root τ j l) := by
      rw [a2Root_add]; exact hroot i l hil
    have hd' : ¬IsRoot τ (a2Root τ j l - a2Root τ i j) := fun h => h1 (mem_rootFinset.2 (by
      have := IsRoot.neg h
      rwa [neg_sub] at this))
    obtain ⟨ε, hε, hcomm⟩ := commutator_xPar_pair hD hG2 (K := K) (hroot i j hij) (hroot j l hkl) h4 h5
      hsum hd' (fun h => h2 (mem_rootFinset.2 h)) (fun h => h3 (mem_rootFinset.2 h))
    rw [hcomm c d, a2Root_add, intCast_eq_one_of_pm_one hε, one_mul, if_pos rfl]
  · by_cases hil : i = l
    · subst hil
      obtain ⟨h1, h2, h3, h4, h5⟩ := a2_adj hτ i j k i ⟨hij, hkl, hex, Or.inr rfl⟩
      have hkj : k ≠ j := fun h => hjk h.symm
      have hsum : IsRoot τ (a2Root τ i j + a2Root τ k i) := by
        rw [add_comm, a2Root_add]; exact hroot k j hkj
      have hd' : ¬IsRoot τ (a2Root τ k i - a2Root τ i j) := fun h => h1 (mem_rootFinset.2 (by
        have := IsRoot.neg h
        rwa [neg_sub] at this))
      obtain ⟨ε, hε, hcomm⟩ := commutator_xPar_pair hD hG2 (K := K) (hroot i j hij) (hroot k i hkl) h4 h5
        hsum hd' (fun h => h2 (mem_rootFinset.2 h)) (fun h => h3 (mem_rootFinset.2 h))
      rw [hcomm c d, add_comm (a2Root τ i j) (a2Root τ k i), a2Root_add, intCast_eq_one_of_pm_one hε,
        one_mul, if_neg hjk, if_pos rfl, CharTwo.neg_eq]
    · obtain ⟨h1, h2⟩ := a2_far hτ i j k l ⟨hij, hkl, hjk, hil⟩
      rw [if_neg hjk, if_neg hil]
      exact commutatorElement_eq_one_iff_commute.2
        (commute_xPar hD hG2 (hroot i j hij) (hroot k l hkl) h2 (fun h => h1 (mem_rootFinset.2 h)) c d)


theorem exists_a2Hom (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    [CharP K 2] :
    ∃ φ : SL(3, K) →* ↥(adjointGroup τ K),
      (∀ c, φ (t12 c) = xPar (rootOperatorFamily τ) (delta1 τ) c) ∧
      (∀ c, φ (t23 c) = xPar (rootOperatorFamily τ) (delta2 τ) c) ∧
      (∀ c, φ (t13 c) = xPar (rootOperatorFamily τ) (hiRoot τ) c) ∧
      (∀ c, φ (t31 c) = xPar (rootOperatorFamily τ) (-hiRoot τ) c) := by
  obtain ⟨φ, hφ⟩ := CFSG.DesarguesianPlanes.exists_hom_of_steinbergFamily (a2_steinbergFamily hτ (K := K))
  refine ⟨φ, fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_⟩
  · have h := hφ 0 1 c (t12 c) (by decide) rfl
    rw [h]; unfold a2X; rw [a2Root_01]
  · have h := hφ 1 2 c (t23 c) (by decide) rfl
    rw [h]; unfold a2X; rw [a2Root_12]
  · have h := hφ 0 2 c (t13 c) (by decide) rfl
    rw [h]; unfold a2X; rw [a2Root_02]
  · have h := hφ 2 0 c (t31 c) (by decide) rfl
    rw [h]; unfold a2X; rw [a2Root_20]

end Gen

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
