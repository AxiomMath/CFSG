module

public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootPerfectness
public import CFSG.LieType.Chevalley.CLSOddToralOrdinaryComponentRootFactor
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorBasic

public noncomputable section

namespace CFSG.ComponentClassification.ExcSelector

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag} {K : Type} [Field K]

theorem HSL_neg_one_eq : HSL (-1 : Kˣ) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [HSL]

theorem rootSL2_neg_one (β : Fin τ.rank → ℤ) : rootSL2 τ K β (-1) = rootTorusSL2 τ K β (-1) := by
  rw [rootTorusSL2, HSL_neg_one_eq]

theorem rootSL2_injective_of_ne_two (hK : ringChar K ≠ 2) (β : Fin τ.rank → ℤ) :
    Function.Injective (rootSL2 τ K β) :=
  ((exceptional_Lang_root_rank_one_data τ K β).2.2.2.2.2.2.2.1 hK).1

theorem range_rootSL2_eq {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    (rootSL2 τ K β).range = rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) :=
  (exceptional_Lang_root_rank_one_torus_transport τ K hβ).1

theorem not_smallType_of_rootSL2_odd [Finite K] (hK : ringChar K ≠ 2) {X : Subgroup (ModGL τ K)}
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hodd : ¬ Even (2 * iform β α / iform β β))
    (hQ : rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) ≤ X) (hX : pinnedX τ K α 1 ∈ X) :
    ¬ SmallType X := by
  have hmem : ∀ A, rootSL2 τ K β A ∈ X := fun A => hQ (by
    rw [← range_rootSL2_eq hβ]
    exact ⟨A, rfl⟩)
  set φ : SL2 K →* X := (rootSL2 τ K β).codRestrict X hmem
  refine not_smallType_of_sl2 hK φ
    (fun A B h => rootSL2_injective_of_ne_two hK β (congrArg Subtype.val h)) fun hz => ?_
  have h1 := congrArg Subtype.val ((mem_center_iff.1 hz) ⟨_, hX⟩)
  change pinnedX τ K α 1 * rootSL2 τ K β (-1) = rootSL2 τ K β (-1) * pinnedX τ K α 1 at h1
  rw [rootSL2_neg_one] at h1
  have h2 := rootTorusSL2_conj_pinnedX_of_isRoot hβ hα (-1 : Kˣ) 1
  have hm : (-1 : Kˣ) ^ (2 * iform β α / iform β β) = -1 :=
    (Int.not_even_iff_odd.1 hodd).neg_one_zpow
  rw [hm, ← h1, mul_inv_cancel_right] at h2
  have h3 := pinnedX_injective τ K α h2
  simp only [Units.val_neg, Units.val_one, mul_one] at h3
  exact Ring.two_ne_zero hK (by linear_combination h3)

variable {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem neg_mem_componentRoots {i : KernelComponent χ} {α : Fin τ.rank → ℤ}
    (hα : α ∈ componentRoots χ i) : -α ∈ componentRoots χ i := by
  obtain ⟨hα', rfl⟩ := hα
  have hneg : -α ∈ kernelRoots χ := ⟨IsRoot.neg hα'.1, chi_neg hα'.2⟩
  refine ⟨hneg, (mk_eq_of_iform_ne_zero (α := ⟨α, hα'⟩) (β := ⟨-α, hneg⟩) ?_).symm⟩
  change iform α (-α) ≠ 0
  rw [iform_neg_right]
  exact neg_ne_zero.2 (iform_self_pos_of_isRoot hα'.1).ne'

theorem isRoot_of_mem_componentRoots {i : KernelComponent χ} {α : Fin τ.rank → ℤ}
    (hα : α ∈ componentRoots χ i) : IsRoot τ α :=
  hα.1.1

theorem f4_pairing : 2 * iform (τ := .F4) (f4Rho + f4Sigma) f4Rho /
    iform (τ := .F4) (f4Rho + f4Sigma) (f4Rho + f4Sigma) = 1 := by
  decide

theorem exists_odd_pairing (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) (i : KernelComponent χ)
    (hi : 2 < (componentRoots χ i).ncard) :
    ∃ α ∈ componentRoots χ i, ∃ β ∈ componentRoots χ i, ¬ Even (2 * iform β α / iform β β) := by
  obtain ⟨α, hα⟩ : (componentRoots χ i).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by omega)
  rcases sign_kernel_nonrankone_root_commutator_witnesses τ χ i hi hα with
    ⟨β, hβ, n, hn, hnβ⟩ | ⟨rfl, w, hρ, -, rfl⟩
  · refine ⟨α, hα, β, hβ, ?_⟩
    rw [dotProduct_mulVec_eq_iform, dotProduct_mulVec_eq_iform] at hnβ
    have hpos := iform_self_pos_of_isRoot (isRoot_of_mem_componentRoots hβ)
    rw [← hnβ, Int.mul_ediv_cancel _ hpos.ne']
    exact Int.not_even_iff_odd.2 hn
  · refine ⟨_, hρ, _, hα, ?_⟩
    rw [iform_smul, iform_smul, f4_pairing]
    decide

theorem toral_component_not_smallType [Finite K] (hK : ringChar K ≠ 2) (a : Fin τ.rank → Kˣ)
    (ha : ∀ i, a i = 1 ∨ a i = -1) {M' : Subgroup (ModGL τ K)}
    (hM : Assembly.IsComponentOf M' (toralCentralizer τ K a)) : ¬ SmallType M' := by
  classical
  have hr : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  have : CharP K (ringChar K) := ringChar.charP K
  set χ := maskChar (signTupleBits a) with hχ
  obtain ⟨Ψ, hMeq, hroots, -⟩ := odd_toral_ordinary_component_root_factor_and_prime_divisor
    (ringChar K) hr hK K τ a ha χ (rootCharKernel_eq_kernelRoots hK ha).symm M' hM
  obtain ⟨⟨α₀, hα₀⟩, hΨ⟩ := Quotient.exists_rep Ψ
  have hα₀Ψ : α₀ ∈ componentRoots χ Ψ := ⟨hα₀, hΨ⟩
  have hnegΨ := neg_mem_componentRoots hα₀Ψ
  by_cases hi : 2 < (componentRoots χ Ψ).ncard
  · obtain ⟨α, hα, β, hβ, hodd⟩ := exists_odd_pairing χ Ψ hi
    exact not_smallType_of_rootSL2_odd hK (isRoot_of_mem_componentRoots hα)
      (isRoot_of_mem_componentRoots hβ) hodd
      (sup_le (hroots _ hβ) (hroots _ (neg_mem_componentRoots hβ)))
      (hroots _ hα (Subgroup.subset_closure ⟨1, rfl⟩))
  ·
    have hfin : (componentRoots χ Ψ).Finite :=
      (root_character_kernel_orthogonal_central_product τ K χ).1.subset fun _ h => h.1
    have hne : α₀ ≠ -α₀ := fun h => (isRoot_of_mem_componentRoots hα₀Ψ).ne_zero
      (funext fun j => by
        have := congrFun h j
        simp only [Pi.neg_apply, Pi.zero_apply] at this ⊢
        omega)
    have hsub : componentRoots χ Ψ ⊆ {α₀, -α₀} := by
      intro γ hγ
      by_contra hγ'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hγ'
      have h3 : ({α₀, -α₀, γ} : Set (Fin τ.rank → ℤ)).ncard = 3 := by
        rw [Set.ncard_insert_of_notMem (by simp [hne, Ne.symm hγ'.1]),
          Set.ncard_pair (Ne.symm hγ'.2)]
      have h3' := Set.ncard_le_ncard (s := {α₀, -α₀, γ}) (by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        exacts [hα₀Ψ, hnegΨ, hγ]) hfin
      omega
    have hle : M' ≤ rootSubgroup τ K α₀ ⊔ rootSubgroup τ K (-α₀) := by
      rw [hMeq]
      refine iSup₂_le fun γ hγ => ?_
      rcases hsub hγ with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    have heq : rootSubgroup τ K α₀ ⊔ rootSubgroup τ K (-α₀) = M' :=
      le_antisymm (sup_le (hroots _ hα₀Ψ) (hroots _ hnegΨ)) hle
    have e : SL2 K ≃* M' := (MonoidHom.ofInjective (rootSL2_injective_of_ne_two hK α₀)).trans
      (MulEquiv.subgroupCongr
        ((range_rootSL2_eq (isRoot_of_mem_componentRoots hα₀Ψ)).trans heq))
    exact not_smallType_of_equiv_sl2 hK e.symm

end CFSG.ComponentClassification.ExcSelector
