module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassListE8
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionClass
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
public import CFSG.LieType.Chevalley.ExceptionalESchreier
public import CFSG.LieType.Chevalley.DiagramFixedModelSchreier

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def perpNegClosedB {n : ℕ} (SP : List (Fin n → ℤ)) : Bool :=
  SP.all fun b => oddDerivMemB (-b) SP

theorem neg_mem_of_perpNegClosedB {n : ℕ} {SP : List (Fin n → ℤ)}
    (h : perpNegClosedB SP = true) : ∀ b ∈ SP, -b ∈ SP := fun b hb =>
  mem_of_oddDerivMemB (List.all_eq_true.1 h b hb)

@[expose] def frameSubB {n : ℕ} (F SA : List (Fin n → ℤ)) : Bool :=
  F.all fun σ => oddDerivMemB σ SA

theorem mem_of_frameSubB {n : ℕ} {F SA : List (Fin n → ℤ)} (h : frameSubB F SA = true) :
    ∀ σ ∈ F, σ ∈ SA := fun σ hσ => mem_of_oddDerivMemB (List.all_eq_true.1 h σ hσ)

section Generic

variable {τ : Tag} {K : Type} [Field K]

theorem commutator_rootSubgroup_sup_neg [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    {b : Fin τ.rank → ℤ} (hb : IsRoot τ b) :
    ⁅rootSubgroup τ K b ⊔ rootSubgroup τ K (-b), rootSubgroup τ K b ⊔ rootSubgroup τ K (-b)⁆ =
      rootSubgroup τ K b ⊔ rootSubgroup τ K (-b) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h⟩ :=
    CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps τ K hb
  exact Subgroup.isPerfect_iff.1 (h ‹Finite K› hq).2.1

theorem commutator_rootSpan_eq_self_of_oddDerivOK [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    {SA SP : List (Fin τ.rank → ℤ)}
    {D : List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ) × (Fin τ.rank → ℤ))}
    (hD : oddDerivOK τ SA SP D = true) (hcov : ∀ δ ∈ SA, ∃ e ∈ D, e.1 = δ)
    (hneg : ∀ b ∈ SP, -b ∈ SP) :
    ⁅rootSpan τ K {γ | γ ∈ SA ∨ γ ∈ SP}, rootSpan τ K {γ | γ ∈ SA ∨ γ ∈ SP}⁆ =
      rootSpan τ K {γ | γ ∈ SA ∨ γ ∈ SP} := by
  set P := rootSpan τ K {γ | γ ∈ SA ∨ γ ∈ SP} with hPdef
  have hroots : ∀ γ ∈ SA ++ SP, IsRoot τ γ := by
    simp only [oddDerivOK, Bool.and_eq_true, List.all_eq_true] at hD
    exact fun γ hγ => isRoot_of_oddDerivIsRootB (hD.1.1 γ hγ)
  have hgen : ∀ γ, γ ∈ SA ∨ γ ∈ SP → rootSubgroup τ K γ ≤ P := fun γ hγ =>
    le_iSup₂_of_le (f := fun δ (_ : δ ∈ {γ | γ ∈ SA ∨ γ ∈ SP}) => rootSubgroup τ K δ) γ hγ
      le_rfl
  have hmono : rootSpan τ K {γ | γ ∈ SA} ≤ P := iSup₂_le fun γ hγ => hgen γ (Or.inl hγ)
  have hSA : rootSpan τ K {γ | γ ∈ SA} ≤ ⁅P, P⁆ :=
    (rootSpan_le_commutator_of_oddDerivOK CharTwo.two_eq_zero hD hcov).trans
      (Subgroup.commutator_mono hmono le_rfl)
  have hself : ⁅P, P⁆ ≤ P := Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  refine le_antisymm hself (iSup₂_le fun γ hγ => ?_)
  rcases hγ with hγ | hγ
  · exact (le_iSup₂_of_le (f := fun δ (_ : δ ∈ {γ | γ ∈ SA}) => rootSubgroup τ K δ) γ hγ
      le_rfl).trans hSA
  · have hJ : rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ) ≤ P :=
      sup_le (hgen γ (Or.inr hγ)) (hgen (-γ) (Or.inr (hneg γ hγ)))
    calc rootSubgroup τ K γ ≤ rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ) := le_sup_left
      _ = ⁅rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ),
            rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ)⁆ :=
          (commutator_rootSubgroup_sup_neg hq (hroots γ (List.mem_append_right _ hγ))).symm
      _ ≤ ⁅P, P⁆ := Subgroup.commutator_mono hJ hJ

theorem exists_perfect_le_centralizer_of_oddDerivFrame [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) {t : adjointGroup τ K} (F : List (Fin τ.rank → ℤ))
    (htF : (t : ModGL τ K) = (F.map fun σ => pinnedX τ K σ 1).prod)
    {SA SP : List (Fin τ.rank → ℤ)}
    {D : List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ) × (Fin τ.rank → ℤ))}
    (hD : oddDerivOK τ SA SP D = true) (hcov : ∀ δ ∈ SA, ∃ e ∈ D, e.1 = δ)
    (hF : oddDerivFrameB τ F (SA ++ SP) = true) (hneg : ∀ b ∈ SP, -b ∈ SP)
    (hFA : ∀ σ ∈ F, σ ∈ SA) :
    ∃ P : Subgroup (adjointGroup τ K), ⁅P, P⁆ = P ∧ t ∈ P ∧
      P ≤ centralizer ({t} : Set (adjointGroup τ K)) := by
  have hsub : rootSpan τ K {γ | γ ∈ SA ∨ γ ∈ SP} ≤ adjointGroup τ K :=
    iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α
  have hroots : ∀ γ ∈ SA ++ SP, IsRoot τ γ := by
    simp only [oddDerivOK, Bool.and_eq_true, List.all_eq_true] at hD
    exact fun γ hγ => isRoot_of_oddDerivIsRootB (hD.1.1 γ hγ)
  simp only [oddDerivFrameB, Bool.and_eq_true, List.all_eq_true] at hF
  obtain ⟨hFr, hFc⟩ := hF
  have hcen : rootSpan τ K {γ | γ ∈ SA ∨ γ ∈ SP} ≤
      Subgroup.centralizer {(t : ModGL τ K)} := by
    refine iSup₂_le fun γ hγ => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, htF]
    exact (commute_pinnedX_list_prod_of_oddDerivCommB (hroots γ (List.mem_append.2 hγ))
      (fun σ hσ => isRoot_of_oddDerivIsRootB (hFr σ hσ))
      (List.all_eq_true.2 (hFc γ (List.mem_append.2 hγ))) c fun _ => 1).eq
  refine ⟨(rootSpan τ K {γ | γ ∈ SA ∨ γ ∈ SP}).subgroupOf (adjointGroup τ K),
    CFSG.SeitzReduction.commutator_subgroupOf_eq_self hsub
      (commutator_rootSpan_eq_self_of_oddDerivOK hq hD hcov hneg), ?_, ?_⟩
  · rw [mem_subgroupOf, htF]
    refine list_prod_mem fun x hx => ?_
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hx
    exact pinnedX_mem_rootSpan_oddDeriv (S := {γ | γ ∈ SA ∨ γ ∈ SP}) (Or.inl (hFA σ hσ)) 1
  · intro x hx
    rw [mem_subgroupOf] at hx
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hcen hx))

end Generic

@[expose] def e8PosXDeriv :
    List ((Fin Tag.E8.rank → ℤ) × (Fin Tag.E8.rank → ℤ) × (Fin Tag.E8.rank → ℤ)) := [
  (![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 0, -1, 0]),
  (![0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1, 0]),
  (![0, 0, 0, 0, 0, 1, 1, 1], ![0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 0]),
  (![0, 0, 0, 0, 1, 1, 1, 1], ![0, 0, 0, 0, 0, 1, 1, 1], ![0, 0, 0, 0, 1, 0, 0, 0]),
  (![0, 0, 0, 1, 1, 1, 1, 1], ![0, 0, 0, 0, 1, 1, 1, 1], ![0, 0, 0, 1, 0, 0, 0, 0]),
  (![0, 0, 1, 1, 1, 1, 1, 1], ![0, 0, 0, 1, 1, 1, 1, 1], ![0, 0, 1, 0, 0, 0, 0, 0]),
  (![0, 1, 0, 1, 1, 1, 1, 1], ![0, 0, 0, 1, 1, 1, 1, 1], ![0, 1, 0, 0, 0, 0, 0, 0]),
  (![0, 1, 1, 1, 1, 1, 1, 1], ![0, 1, 0, 1, 1, 1, 1, 1], ![0, 0, 1, 0, 0, 0, 0, 0]),
  (![1, 0, 1, 1, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 1, 1, 1], ![1, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 1, 1, 2, 1, 1, 1, 1], ![0, 1, 1, 1, 1, 1, 1, 1], ![0, 0, 0, 1, 0, 0, 0, 0]),
  (![1, 1, 1, 1, 1, 1, 1, 1], ![1, 0, 1, 1, 1, 1, 1, 1], ![0, 1, 0, 0, 0, 0, 0, 0]),
  (![0, 1, 1, 2, 2, 1, 1, 1], ![0, 1, 1, 2, 1, 1, 1, 1], ![0, 0, 0, 0, 1, 0, 0, 0]),
  (![1, 1, 1, 2, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1], ![0, 0, 0, 1, 0, 0, 0, 0]),
  (![0, 1, 1, 2, 2, 2, 1, 1], ![0, 1, 1, 2, 2, 1, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 0]),
  (![1, 1, 1, 2, 2, 1, 1, 1], ![1, 1, 1, 2, 1, 1, 1, 1], ![0, 0, 0, 0, 1, 0, 0, 0]),
  (![1, 1, 2, 2, 1, 1, 1, 1], ![1, 1, 1, 2, 1, 1, 1, 1], ![0, 0, 1, 0, 0, 0, 0, 0]),
  (![0, 1, 1, 2, 2, 2, 2, 1], ![0, 1, 1, 2, 2, 2, 1, 1], ![0, 0, 0, 0, 0, 0, 1, 0]),
  (![1, 1, 1, 2, 2, 2, 1, 1], ![1, 1, 1, 2, 2, 1, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 0]),
  (![1, 1, 2, 2, 2, 1, 1, 1], ![1, 1, 2, 2, 1, 1, 1, 1], ![0, 0, 0, 0, 1, 0, 0, 0]),
  (![1, 1, 1, 2, 2, 2, 2, 1], ![1, 1, 1, 2, 2, 2, 1, 1], ![0, 0, 0, 0, 0, 0, 1, 0]),
  (![1, 1, 2, 2, 2, 2, 1, 1], ![1, 1, 2, 2, 2, 1, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 0]),
  (![1, 1, 2, 3, 2, 1, 1, 1], ![1, 1, 2, 2, 2, 1, 1, 1], ![0, 0, 0, 1, 0, 0, 0, 0]),
  (![1, 1, 2, 2, 2, 2, 2, 1], ![1, 1, 2, 2, 2, 2, 1, 1], ![0, 0, 0, 0, 0, 0, 1, 0]),
  (![1, 1, 2, 3, 2, 2, 1, 1], ![1, 1, 2, 3, 2, 1, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 0]),
  (![1, 2, 2, 3, 2, 1, 1, 1], ![1, 1, 2, 3, 2, 1, 1, 1], ![0, 1, 0, 0, 0, 0, 0, 0]),
  (![1, 1, 2, 3, 2, 2, 2, 1], ![1, 1, 2, 3, 2, 2, 1, 1], ![0, 0, 0, 0, 0, 0, 1, 0]),
  (![1, 1, 2, 3, 3, 2, 1, 1], ![1, 1, 2, 3, 2, 2, 1, 1], ![0, 0, 0, 0, 1, 0, 0, 0]),
  (![1, 2, 2, 3, 2, 2, 1, 1], ![1, 2, 2, 3, 2, 1, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 0]),
  (![1, 1, 2, 3, 3, 2, 2, 1], ![1, 1, 2, 3, 3, 2, 1, 1], ![0, 0, 0, 0, 0, 0, 1, 0]),
  (![1, 2, 2, 3, 2, 2, 2, 1], ![1, 2, 2, 3, 2, 2, 1, 1], ![0, 0, 0, 0, 0, 0, 1, 0]),
  (![1, 2, 2, 3, 3, 2, 1, 1], ![1, 2, 2, 3, 2, 2, 1, 1], ![0, 0, 0, 0, 1, 0, 0, 0]),
  (![1, 1, 2, 3, 3, 3, 2, 1], ![1, 1, 2, 3, 3, 2, 2, 1], ![0, 0, 0, 0, 0, 1, 0, 0]),
  (![1, 2, 2, 3, 3, 2, 2, 1], ![1, 2, 2, 3, 3, 2, 1, 1], ![0, 0, 0, 0, 0, 0, 1, 0]),
  (![1, 2, 2, 4, 3, 2, 1, 1], ![1, 2, 2, 3, 3, 2, 1, 1], ![0, 0, 0, 1, 0, 0, 0, 0]),
  (![1, 2, 2, 3, 3, 3, 2, 1], ![1, 2, 2, 3, 3, 2, 2, 1], ![0, 0, 0, 0, 0, 1, 0, 0]),
  (![1, 2, 2, 4, 3, 2, 2, 1], ![1, 2, 2, 4, 3, 2, 1, 1], ![0, 0, 0, 0, 0, 0, 1, 0]),
  (![1, 2, 3, 4, 3, 2, 1, 1], ![1, 2, 2, 4, 3, 2, 1, 1], ![0, 0, 1, 0, 0, 0, 0, 0]),
  (![1, 2, 2, 4, 3, 3, 2, 1], ![1, 2, 2, 4, 3, 2, 2, 1], ![0, 0, 0, 0, 0, 1, 0, 0]),
  (![1, 2, 3, 4, 3, 2, 2, 1], ![1, 2, 3, 4, 3, 2, 1, 1], ![0, 0, 0, 0, 0, 0, 1, 0]),
  (![2, 2, 3, 4, 3, 2, 1, 1], ![1, 2, 3, 4, 3, 2, 1, 1], ![1, 0, 0, 0, 0, 0, 0, 0]),
  (![1, 2, 2, 4, 4, 3, 2, 1], ![1, 2, 2, 4, 3, 3, 2, 1], ![0, 0, 0, 0, 1, 0, 0, 0]),
  (![1, 2, 3, 4, 3, 3, 2, 1], ![1, 2, 3, 4, 3, 2, 2, 1], ![0, 0, 0, 0, 0, 1, 0, 0]),
  (![2, 2, 3, 4, 3, 2, 2, 1], ![2, 2, 3, 4, 3, 2, 1, 1], ![0, 0, 0, 0, 0, 0, 1, 0]),
  (![1, 2, 3, 4, 4, 3, 2, 1], ![1, 2, 3, 4, 3, 3, 2, 1], ![0, 0, 0, 0, 1, 0, 0, 0]),
  (![2, 2, 3, 4, 3, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 2, 1], ![0, 0, 0, 0, 0, 1, 0, 0]),
  (![1, 2, 3, 5, 4, 3, 2, 1], ![1, 2, 3, 4, 4, 3, 2, 1], ![0, 0, 0, 1, 0, 0, 0, 0]),
  (![2, 2, 3, 4, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 3, 2, 1], ![0, 0, 0, 0, 1, 0, 0, 0]),
  (![1, 3, 3, 5, 4, 3, 2, 1], ![1, 2, 3, 5, 4, 3, 2, 1], ![0, 1, 0, 0, 0, 0, 0, 0]),
  (![2, 2, 3, 5, 4, 3, 2, 1], ![2, 2, 3, 4, 4, 3, 2, 1], ![0, 0, 0, 1, 0, 0, 0, 0]),
  (![2, 2, 4, 5, 4, 3, 2, 1], ![2, 2, 3, 5, 4, 3, 2, 1], ![0, 0, 1, 0, 0, 0, 0, 0]),
  (![2, 3, 3, 5, 4, 3, 2, 1], ![2, 2, 3, 5, 4, 3, 2, 1], ![0, 1, 0, 0, 0, 0, 0, 0]),
  (![2, 3, 4, 5, 4, 3, 2, 1], ![2, 3, 3, 5, 4, 3, 2, 1], ![0, 0, 1, 0, 0, 0, 0, 0]),
  (![2, 3, 4, 6, 4, 3, 2, 1], ![2, 3, 4, 5, 4, 3, 2, 1], ![0, 0, 0, 1, 0, 0, 0, 0]),
  (![2, 3, 4, 6, 5, 3, 2, 1], ![2, 3, 4, 6, 4, 3, 2, 1], ![0, 0, 0, 0, 1, 0, 0, 0]),
  (![2, 3, 4, 6, 5, 4, 2, 1], ![2, 3, 4, 6, 5, 3, 2, 1], ![0, 0, 0, 0, 0, 1, 0, 0]),
  (![2, 3, 4, 6, 5, 4, 3, 1], ![2, 3, 4, 6, 5, 4, 2, 1], ![0, 0, 0, 0, 0, 0, 1, 0]),
  (![2, 3, 4, 6, 5, 4, 3, 2], ![2, 3, 4, 6, 5, 4, 3, 1], ![0, 0, 0, 0, 0, 0, 0, 1])]

@[expose] def e8PosXPerpPos : List (Fin Tag.E8.rank → ℤ) := [
  ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 1, 0],
  ![0, 0, 0, 0, 1, 1, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0], ![0, 0, 1, 1, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0, 0, 0],
  ![1, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 1, 1, 0], ![0, 0, 0, 1, 1, 1, 0, 0], ![0, 0, 1, 1, 1, 0, 0, 0],
  ![0, 1, 0, 1, 1, 0, 0, 0], ![0, 1, 1, 1, 0, 0, 0, 0], ![1, 0, 1, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 1, 1, 0],
  ![0, 0, 1, 1, 1, 1, 0, 0], ![0, 1, 0, 1, 1, 1, 0, 0], ![0, 1, 1, 1, 1, 0, 0, 0], ![1, 0, 1, 1, 1, 0, 0, 0],
  ![1, 1, 1, 1, 0, 0, 0, 0], ![0, 0, 1, 1, 1, 1, 1, 0], ![0, 1, 0, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 1, 1, 0, 0],
  ![0, 1, 1, 2, 1, 0, 0, 0], ![1, 0, 1, 1, 1, 1, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0], ![0, 1, 1, 1, 1, 1, 1, 0],
  ![0, 1, 1, 2, 1, 1, 0, 0], ![1, 0, 1, 1, 1, 1, 1, 0], ![1, 1, 1, 1, 1, 1, 0, 0], ![1, 1, 1, 2, 1, 0, 0, 0],
  ![0, 1, 1, 2, 1, 1, 1, 0], ![0, 1, 1, 2, 2, 1, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 0], ![1, 1, 1, 2, 1, 1, 0, 0],
  ![1, 1, 2, 2, 1, 0, 0, 0], ![0, 1, 1, 2, 2, 1, 1, 0], ![1, 1, 1, 2, 1, 1, 1, 0], ![1, 1, 1, 2, 2, 1, 0, 0],
  ![1, 1, 2, 2, 1, 1, 0, 0], ![0, 1, 1, 2, 2, 2, 1, 0], ![1, 1, 1, 2, 2, 1, 1, 0], ![1, 1, 2, 2, 1, 1, 1, 0],
  ![1, 1, 2, 2, 2, 1, 0, 0], ![1, 1, 1, 2, 2, 2, 1, 0], ![1, 1, 2, 2, 2, 1, 1, 0], ![1, 1, 2, 3, 2, 1, 0, 0],
  ![1, 1, 2, 2, 2, 2, 1, 0], ![1, 1, 2, 3, 2, 1, 1, 0], ![1, 2, 2, 3, 2, 1, 0, 0], ![1, 1, 2, 3, 2, 2, 1, 0],
  ![1, 2, 2, 3, 2, 1, 1, 0], ![1, 1, 2, 3, 3, 2, 1, 0], ![1, 2, 2, 3, 2, 2, 1, 0], ![1, 2, 2, 3, 3, 2, 1, 0],
  ![1, 2, 2, 4, 3, 2, 1, 0], ![1, 2, 3, 4, 3, 2, 1, 0], ![2, 2, 3, 4, 3, 2, 1, 0]]

@[expose] def e8PosXPerp : List (Fin Tag.E8.rank → ℤ) :=
  e8PosXPerpPos ++ e8PosXPerpPos.map fun v => -v

@[expose] def e8PosXFrame : List (Fin Tag.E8.rank → ℤ) := [![2, 3, 4, 6, 5, 4, 3, 2]]

theorem e8PosXFrame_eq : e8PosXFrame = [highRoot .E8] := rfl

theorem e8PosX_check :
    (oddDerivOK .E8 (e8PosXDeriv.map Prod.fst) e8PosXPerp e8PosXDeriv &&
      oddDerivFrameB .E8 e8PosXFrame (e8PosXDeriv.map Prod.fst ++ e8PosXPerp) &&
      perpNegClosedB e8PosXPerp && frameSubB e8PosXFrame (e8PosXDeriv.map Prod.fst) &&
      oddDerivTailB .E8 1 (e8PosXDeriv.map Prod.fst ++ e8PosXPerp)) = true := by
  decide +kernel

theorem e8PosYZU_check :
    (perpNegClosedB oddDerivE8YPerp && frameSubB oddDerivE8YFrame (oddDerivE8YDeriv.map Prod.fst) &&
      perpNegClosedB oddDerivE8ZPerp &&
        frameSubB oddDerivE8ZFrame (oddDerivE8ZDeriv.map Prod.fst) &&
      perpNegClosedB oddDerivE8UPerp &&
        frameSubB oddDerivE8UFrame (oddDerivE8UDeriv.map Prod.fst)) = true := by
  decide +kernel

section Classes

variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def e8PosXSpan : Subgroup (ModGL .E8 K) :=
  rootSpan .E8 K {γ | γ ∈ e8PosXDeriv.map Prod.fst ∨ γ ∈ e8PosXPerp}

theorem commutator_e8PosXSpan [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    ⁅e8PosXSpan K, e8PosXSpan K⁆ = e8PosXSpan K := by
  have h := e8PosX_check
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hD, -⟩, hneg⟩, -⟩, -⟩ := h
  exact commutator_rootSpan_eq_self_of_oddDerivOK hq hD (oddDeriv_cov_map_fst _)
    (neg_mem_of_perpNegClosedB hneg)

theorem e8PosXSpan_le_centralizer :
    e8PosXSpan K ≤ Subgroup.centralizer {pinnedX .E8 K (highRoot .E8) 1} := by
  have h := e8PosX_check
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hD, hF⟩, -⟩, -⟩, -⟩ := h
  have hroots : ∀ γ ∈ e8PosXDeriv.map Prod.fst ++ e8PosXPerp, IsRoot .E8 γ := by
    simp only [oddDerivOK, Bool.and_eq_true, List.all_eq_true] at hD
    exact fun γ hγ => isRoot_of_oddDerivIsRootB (hD.1.1 γ hγ)
  simp only [oddDerivFrameB, Bool.and_eq_true, List.all_eq_true] at hF
  obtain ⟨hFr, hFc⟩ := hF
  refine iSup₂_le fun γ hγ => (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  have h1 : pinnedX .E8 K γ c * (e8PosXFrame.map fun σ => pinnedX .E8 K σ 1).prod =
      (e8PosXFrame.map fun σ => pinnedX .E8 K σ 1).prod * pinnedX .E8 K γ c :=
    (commute_pinnedX_list_prod_of_oddDerivCommB (hroots γ (List.mem_append.2 hγ))
      (fun σ hσ => isRoot_of_oddDerivIsRootB (hFr σ hσ))
      (List.all_eq_true.2 (hFc γ (List.mem_append.2 hγ))) c fun _ => (1 : K)).eq
  have h3 : (e8PosXFrame.map fun σ => pinnedX .E8 K σ 1).prod =
      pinnedX .E8 K (highRoot .E8) 1 := by
    rw [e8PosXFrame_eq, List.map_singleton, List.prod_singleton]
  rw [h3] at h1
  exact h1

theorem exists_perfect_le_centralizer_E8_x [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    ∃ P : Subgroup (adjointGroup .E8 K), ⁅P, P⁆ = P ∧
      (⟨pinnedX .E8 K (highRoot .E8) 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .E8 K) ∈ P ∧
      P ≤ centralizer ({⟨pinnedX .E8 K (highRoot .E8) 1, pinnedX_mem_adjointGroup _ _⟩} :
        Set (adjointGroup .E8 K)) := by
  have h := e8PosX_check
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hD, hF⟩, hneg⟩, hFA⟩, -⟩ := h
  exact exists_perfect_le_centralizer_of_oddDerivFrame hq e8PosXFrame
    (by rw [e8PosXFrame_eq, List.map_singleton, List.prod_singleton]) hD
    (oddDeriv_cov_map_fst _) hF
    (neg_mem_of_perpNegClosedB hneg) (mem_of_frameSubB hFA)

theorem exists_perfect_le_centralizer_E8_y [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    {t : adjointGroup .E8 K}
    (ht : (t : ModGL .E8 K) = (oddDerivE8YFrame.map fun σ => pinnedX .E8 K σ 1).prod) :
    ∃ P : Subgroup (adjointGroup .E8 K), ⁅P, P⁆ = P ∧ t ∈ P ∧
      P ≤ centralizer ({t} : Set (adjointGroup .E8 K)) := by
  have h := oddDerivE8Y_check
  simp only [oddDerivCheck, Bool.and_eq_true] at h
  have h' := e8PosYZU_check
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨hyn, hyf⟩, -⟩, -⟩, -⟩, -⟩ := h'
  exact exists_perfect_le_centralizer_of_oddDerivFrame hq _ ht h.1.1.1 (oddDeriv_cov_map_fst _)
    h.1.2 (neg_mem_of_perpNegClosedB hyn) (mem_of_frameSubB hyf)

theorem exists_perfect_le_centralizer_E8_z [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    {t : adjointGroup .E8 K}
    (ht : (t : ModGL .E8 K) = (oddDerivE8ZFrame.map fun σ => pinnedX .E8 K σ 1).prod) :
    ∃ P : Subgroup (adjointGroup .E8 K), ⁅P, P⁆ = P ∧ t ∈ P ∧
      P ≤ centralizer ({t} : Set (adjointGroup .E8 K)) := by
  have h := oddDerivE8Z_check
  simp only [oddDerivCheck, Bool.and_eq_true] at h
  have h' := e8PosYZU_check
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨-, -⟩, hzn⟩, hzf⟩, -⟩, -⟩ := h'
  exact exists_perfect_le_centralizer_of_oddDerivFrame hq _ ht h.1.1.1 (oddDeriv_cov_map_fst _)
    h.1.2 (neg_mem_of_perpNegClosedB hzn) (mem_of_frameSubB hzf)

theorem exists_perfect_le_centralizer_E8_u [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    {t : adjointGroup .E8 K}
    (ht : (t : ModGL .E8 K) = (oddDerivE8UFrame.map fun σ => pinnedX .E8 K σ 1).prod) :
    ∃ P : Subgroup (adjointGroup .E8 K), ⁅P, P⁆ = P ∧ t ∈ P ∧
      P ≤ centralizer ({t} : Set (adjointGroup .E8 K)) := by
  have h := oddDerivE8U_check
  simp only [oddDerivCheck, Bool.and_eq_true] at h
  have h' := e8PosYZU_check
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hun⟩, huf⟩ := h'
  exact exists_perfect_le_centralizer_of_oddDerivFrame hq _ ht h.1.1.1 (oddDeriv_cov_map_fst _)
    h.1.2 (neg_mem_of_perpNegClosedB hun) (mem_of_frameSubB huf)

theorem exists_perfect_le_centralizer_of_mem_innerRepsE8 [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) {s : adjointGroup .E8 K} (hs : s ∈ innerRepsE8 K) :
    ∃ P : Subgroup (adjointGroup .E8 K), ⁅P, P⁆ = P ∧ s ∈ P ∧
      P ≤ centralizer ({s} : Set (adjointGroup .E8 K)) := by
  simp only [innerRepsE8, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact exists_perfect_le_centralizer_E8_x hq
  · exact exists_perfect_le_centralizer_E8_y hq rfl
  · exact exists_perfect_le_centralizer_E8_z hq rfl
  · exact exists_perfect_le_centralizer_E8_u hq rfl

theorem exists_perfect_le_centralizer_of_orderOf_eq_two_E8 [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) {w : adjointGroup .E8 K} (hw : orderOf w = 2) :
    ∃ P : Subgroup (adjointGroup .E8 K), ⁅P, P⁆ = P ∧ w ∈ P ∧
      P ≤ centralizer ({w} : Set (adjointGroup .E8 K)) := by
  have hw2 : w ^ 2 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hw
    exact absurd hw (by norm_num)
  obtain ⟨g, hg⟩ := classListE8_exists_conj_mem_innerRepsE8 hw2 hw1
  obtain ⟨P, hP, hsP, hPc⟩ := exists_perfect_le_centralizer_of_mem_innerRepsE8 hq hg
  exact F4Pilot.exists_perfect_of_conj hP hsP hPc

end Classes

theorem exists_perfect_le_of_mulEquiv_of_forall {G : Type*} [Group G] {L : Subgroup G}
    {C : Type*} [Group C] (e : L ≃* C)
    (hC : ∀ w : C, orderOf w = 2 → ∃ P : Subgroup C, ⁅P, P⁆ = P ∧ w ∈ P ∧
      P ≤ centralizer ({w} : Set C)) :
    ∀ w ∈ L, orderOf w = 2 → ∃ P : Subgroup G, ⁅P, P⁆ = P ∧ w ∈ P ∧ P ≤ L ∧
      P ≤ centralizer ({w} : Set G) := by
  intro w hwL hw
  set φ : C →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hwC : orderOf (e ⟨w, hwL⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, orderOf_mk, hw]
  obtain ⟨P, hP, hwP, hPc⟩ := hC _ hwC
  have hφw : φ (e ⟨w, hwL⟩) = w := by simp [hφdef]
  refine ⟨P.map φ, by rw [← map_commutator, hP], ⟨_, hwP, hφw⟩, ?_, ?_⟩
  · rintro _ ⟨p, -, rfl⟩
    exact (e.symm p).2
  · rintro _ ⟨p, hp, rfl⟩
    have h := mem_centralizer_singleton_iff.1 (hPc hp)
    rw [mem_centralizer_singleton_iff, ← hφw, ← map_mul, ← map_mul, h]

theorem exists_perfect_le_of_mulEquiv_E8 {G : Type*} [Group G] {L : Subgroup G} {K : Type}
    [Field K] [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) (e : L ≃* adjointGroup .E8 K) :
    ∀ w ∈ L, orderOf w = 2 → ∃ P : Subgroup G, ⁅P, P⁆ = P ∧ w ∈ P ∧ P ≤ L ∧
      P ≤ centralizer ({w} : Set G) :=
  exists_perfect_le_of_mulEquiv_of_forall e fun _ hw =>
    exists_perfect_le_centralizer_of_orderOf_eq_two_E8 hq hw

theorem isSolvable_outer_of_mulEquiv_E8 {G : Type*} [Group G] {L : Subgroup G} {K : Type}
    [Field K] [Finite K] (e : L ≃* adjointGroup .E8 K) : Group.IsSolvable (Outer L) :=
  ⟨⟨2, derivedSeries_outer_eq_bot_of_mulEquiv e (exceptional_E_pinned_model_Schreier K).2.2⟩⟩

theorem conj_not_mem_of_mulEquiv_E8 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) (e : L ≃* adjointGroup .E8 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (g : G) : g⁻¹ * t * g ∉ L :=
  F4Pilot.conj_not_mem_of_forall_perfect hset (isSolvable_outer_of_mulEquiv_E8 e)
    (by rw [← map_center_eq e.symm, center_adjointGroup_eq_bot, Subgroup.map_bot])
    (exists_perfect_le_of_mulEquiv_E8 hq e) htC ht g

end CFSG.SeitzReduction.E8Pilot
