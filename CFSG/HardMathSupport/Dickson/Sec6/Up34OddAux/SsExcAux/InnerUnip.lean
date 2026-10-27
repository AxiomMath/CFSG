module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighPin
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LangTorus

section Unip


variable {τ : Tag} {K : Type} [Field K] {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem ssexc_exists_pos_root (i : KernelComponent χ) :
    ∃ γ ∈ componentRoots χ i, 0 < height γ := by
  obtain ⟨⟨α, hαk⟩, rfl⟩ := Quotient.exists_rep i
  have hα : α ∈ componentRoots χ ⟦⟨α, hαk⟩⟧ := ⟨hαk, rfl⟩
  have hΨ := isRootComponent_componentRoots (χ := χ) ⟦⟨α, hαk⟩⟧
  rcases IsRoot.height_pos_or_neg hαk.1 with h | h
  · exact ⟨α, hα, h⟩
  · exact ⟨-α, hΨ.neg_mem α hα, by rw [height_neg]; omega⟩

@[expose] noncomputable def ssexcPosPart (K : Type) [Field K] (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    (i : KernelComponent χ) : Subgroup ↥(componentRootSpan K χ i) :=
  (posUnipotent τ K).subgroupOf (componentRootSpan K χ i)

theorem ssexc_isPGroup_posPart [Finite K] {r : ℕ} [Fact r.Prime] [CharP K r]
    (i : KernelComponent χ) : IsPGroup r ↥(ssexcPosPart K χ i) :=
  (isPGroup_posUnipotent r τ).comap_subtype

@[expose] noncomputable def ssexcX {i : KernelComponent χ} {γ : Fin τ.rank → ℤ} (hγ : γ ∈ componentRoots χ i)
    (c : K) : ↥(componentRootSpan K χ i) :=
  ⟨pinnedX τ K γ c, pinnedX_mem_rootSpan hγ c⟩

theorem ssexcX_mem_posPart {i : KernelComponent χ} {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ componentRoots χ i) (hγp : 0 < height γ) (c : K) :
    ssexcX hγ c ∈ ssexcPosPart K χ i :=
  Subgroup.mem_subgroupOf.2 (pinnedX_mem_rootSpan (S := {α | IsRoot τ α ∧ 0 < height α})
    ⟨isRoot_of_mem_componentRoots hγ, hγp⟩ c)

theorem ssexc_card_posPart_one [Finite K] {i : KernelComponent χ} {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ componentRoots χ i) (hγp : 0 < height γ) :
    Nat.card K ≤ Nat.card ↥(ssexcPosPart K χ i) := by
  let φ : K → ↥(ssexcPosPart K χ i) := fun c => ⟨ssexcX hγ c, ssexcX_mem_posPart hγ hγp c⟩
  refine Nat.card_le_card_of_injective φ fun a b hab => ?_
  have h1 := congrArg (fun x : ↥(ssexcPosPart K χ i) => ((x.1 : ↥(componentRootSpan K χ i)) : ModGL τ K))
    hab
  exact pinnedX_injective τ K γ h1

theorem ssexc_card_posPart_two [Finite K] {i : KernelComponent χ} {γ δ : Fin τ.rank → ℤ}
    (hγ : γ ∈ componentRoots χ i) (hδ : δ ∈ componentRoots χ i) (hγp : 0 < height γ)
    (hδp : 0 < height δ) (hne : γ ≠ δ) :
    Nat.card K * Nat.card K ≤ Nat.card ↥(ssexcPosPart K χ i) := by
  have hmem : ∀ a b : K, ssexcX hγ a * ssexcX hδ b ∈ ssexcPosPart K χ i := fun a b =>
    mul_mem (ssexcX_mem_posPart hγ hγp a) (ssexcX_mem_posPart hδ hδp b)
  let φ : K × K → ↥(ssexcPosPart K χ i) := fun ab => ⟨ssexcX hγ ab.1 * ssexcX hδ ab.2,
    hmem ab.1 ab.2⟩
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective φ fun ab ab' hab => ?_
  have h1 := congrArg (fun x : ↥(ssexcPosPart K χ i) =>
    ((x.1 : ↥(componentRootSpan K χ i)) : ModGL τ K)) hab
  simp only [φ] at h1
  have h2 : (([γ, δ].map fun α => pinnedX τ K α (if α = γ then ab.1 else ab.2)).prod) =
      (([γ, δ].map fun α => pinnedX τ K α (if α = γ then ab'.1 else ab'.2)).prod) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, if_pos,
      if_neg (Ne.symm hne)]
    exact h1
  have hnd : [γ, δ].Nodup := by simp [hne]
  have hL : ∀ α ∈ [γ, δ], IsRoot τ α ∧ 0 < height α := by
    intro α hα
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
    rcases hα with rfl | rfl
    · exact ⟨isRoot_of_mem_componentRoots hγ, hγp⟩
    · exact ⟨isRoot_of_mem_componentRoots hδ, hδp⟩
  have e1 := pinnedX_list_prod_injective (R := K) [γ, δ] hnd hL _ _ h2 γ (by simp)
  have e2 := pinnedX_list_prod_injective (R := K) [γ, δ] hnd hL _ _ h2 δ (by simp)
  simp only [if_pos, if_neg (Ne.symm hne)] at e1 e2
  exact Prod.ext e1 e2

theorem ssexc_exists_two_pos (i : KernelComponent χ) {γ δ : Fin τ.rank → ℤ}
    (hγ : γ ∈ componentRoots χ i) (hδ : δ ∈ componentRoots χ i) (h1 : δ ≠ γ) (h2 : δ ≠ -γ) :
    ∃ γ' ∈ componentRoots χ i, ∃ δ' ∈ componentRoots χ i, 0 < height γ' ∧ 0 < height δ' ∧
      γ' ≠ δ' := by
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  have hγn : -γ ∈ componentRoots χ i := hΨ.neg_mem γ hγ
  have hδn : -δ ∈ componentRoots χ i := hΨ.neg_mem δ hδ
  rcases IsRoot.height_pos_or_neg (isRoot_of_mem_componentRoots hγ) with hγp | hγp <;>
    rcases IsRoot.height_pos_or_neg (isRoot_of_mem_componentRoots hδ) with hδp | hδp
  · exact ⟨γ, hγ, δ, hδ, hγp, hδp, fun h => h1 h.symm⟩
  · refine ⟨γ, hγ, -δ, hδn, hγp, by rw [height_neg]; omega, fun h => h2 ?_⟩
    rw [h, neg_neg]
  · refine ⟨-γ, hγn, δ, hδ, by rw [height_neg]; omega, hδp, fun h => h2 h.symm⟩
  · refine ⟨-γ, hγn, -δ, hδn, by rw [height_neg]; omega, by rw [height_neg]; omega, fun h => h1 ?_⟩
    exact (neg_injective h).symm

theorem ssexc_card_le_of_rank_one [Finite K] {i : KernelComponent χ} {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ componentRoots χ i) (h : ∀ δ ∈ componentRoots χ i, δ = γ ∨ δ = -γ) :
    Nat.card ↥(componentRootSpan K χ i) ≤ Nat.card K ^ 4 := by
  have hγr : IsRoot τ γ := isRoot_of_mem_componentRoots hγ
  have hle : componentRootSpan K χ i ≤ (rootSL2 τ K γ).range := by
    refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    obtain ⟨hαk, hαi⟩ := hα
    have hαΨ : α ∈ componentRoots χ i := ⟨hαk, hαi⟩
    rcases h α hαΨ with rfl | rfl
    · refine ⟨uSL ((((pinnedData τ α).2.2 : ℤ) : K) * c), ?_⟩
      exact (pinnedX_eq_rootSL2_uSL α c).symm
    · obtain ⟨ε, hε, hv⟩ := exists_rootSL2_vSL_eq (K := K) hγr
      refine ⟨vSL (ε * c), ?_⟩
      rw [hv, ← mul_assoc, hε, one_mul]
  haveI : Finite (SL2 K) := by
    haveI : Finite (Matrix (Fin 2) (Fin 2) K) := inferInstance
    exact Finite.of_injective (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K)) Subtype.coe_injective
  haveI : Finite ↥(rootSL2 τ K γ).range := inferInstance
  have h1 : Nat.card ↥(componentRootSpan K χ i) ≤ Nat.card ↥(rootSL2 τ K γ).range :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have h2 : Nat.card ↥(rootSL2 τ K γ).range ≤ Nat.card (SL2 K) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_range_dvd _)
  have h3 : Nat.card (SL2 K) ≤ Nat.card (Matrix (Fin 2) (Fin 2) K) :=
    Nat.card_le_card_of_injective (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K))
      Subtype.coe_injective
  have h4 : Nat.card (Matrix (Fin 2) (Fin 2) K) = Nat.card K ^ 4 := by
    haveI : Fintype K := Fintype.ofFinite K
    simp only [Matrix, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
    ring
  omega

end Unip

end CFSG.HardMathSupport.Dickson.Sec6
