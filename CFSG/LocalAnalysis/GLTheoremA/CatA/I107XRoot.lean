module

public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107XChk

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I107X

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement IsMulCommutative

@[expose] noncomputable def rootEl (τ : Tag) (K : Type) [Field K] (ε : Fin τ.rank → ℤ) (c : K) :
    adjointGroup τ K :=
  ⟨pinnedX τ K ε c, pinnedX_mem_adjointGroup ε c⟩

@[expose] def rootSet (τ : Tag) (K : Type) [Field K] (Ψ : List (Fin τ.rank → ℤ)) :
    Set (adjointGroup τ K) :=
  {g | ∃ ε ∈ Ψ, ∃ c : K, g = rootEl τ K ε c}

theorem rootEl_val (τ : Tag) (K : Type) [Field K] (ε : Fin τ.rank → ℤ) (c : K) :
    (rootEl τ K ε c).1 = pinnedX τ K ε c :=
  rfl

theorem rootEl_mul (τ : Tag) (K : Type) [Field K] (ε : Fin τ.rank → ℤ) (c d : K) :
    rootEl τ K ε c * rootEl τ K ε d = rootEl τ K ε (c + d) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, rootEl_val, rootEl_val, rootEl_val, pinnedX_add]

theorem rootEl_inv (τ : Tag) (K : Type) [Field K] (ε : Fin τ.rank → ℤ) (c : K) :
    (rootEl τ K ε c)⁻¹ = rootEl τ K ε (-c) := by
  apply Subtype.ext
  rw [Subgroup.coe_inv, rootEl_val, rootEl_val, pinnedX_neg]

theorem rootEl_commute {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K]
    {Ψ : List (Fin τ.rank → ℤ)} (hroot : ∀ ε ∈ Ψ, IsRoot τ ε)
    (hpos : ∀ ε ∈ Ψ, ∀ ε' ∈ Ψ, ε ≠ ε' → 0 ≤ rf τ ε ε')
    {ε ε' : Fin τ.rank → ℤ} (hε : ε ∈ Ψ) (hε' : ε' ∈ Ψ) (c c' : K) :
    Commute (rootEl τ K ε c) (rootEl τ K ε' c') := by
  show rootEl τ K ε c * rootEl τ K ε' c' = rootEl τ K ε' c' * rootEl τ K ε c
  by_cases h : ε = ε'
  · subst h
    rw [rootEl_mul, rootEl_mul, add_comm]
  · apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, rootEl_val, rootEl_val]
    exact (pinnedX_commute_of_rootForm_nonneg hτ (hroot ε hε) (hroot ε' hε') h
      (hpos ε hε ε' hε' h) c c').eq

theorem rootSet_pairwise_comm {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] {Ψ : List (Fin τ.rank → ℤ)} (hroot : ∀ ε ∈ Ψ, IsRoot τ ε)
    (hpos : ∀ ε ∈ Ψ, ∀ ε' ∈ Ψ, ε ≠ ε' → 0 ≤ rf τ ε ε') :
    (rootSet τ K Ψ).Pairwise Commute := by
  rintro _ ⟨ε, hε, c, rfl⟩ _ ⟨ε', hε', c', rfl⟩ _
  exact rootEl_commute hτ hroot hpos hε hε' c c'

theorem rootSet_isMulCommutative {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] {Ψ : List (Fin τ.rank → ℤ)} (hroot : ∀ ε ∈ Ψ, IsRoot τ ε)
    (hpos : ∀ ε ∈ Ψ, ∀ ε' ∈ Ψ, ε ≠ ε' → 0 ≤ rf τ ε ε') :
    IsMulCommutative (Subgroup.closure (rootSet τ K Ψ)) :=
  Subgroup.isMulCommutative_closure (rootSet_pairwise_comm hτ hroot hpos)

theorem commutator_root_caseA {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] {ε β : Fin τ.rank → ℤ} (hε : IsRoot τ ε) (hβ : IsRoot τ β) (hne : ε ≠ β)
    (h0 : 0 ≤ rf τ ε β) (c : K) :
    ⁅rootEl τ K β 1, rootEl τ K ε c⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_commute]
  show rootEl τ K β 1 * rootEl τ K ε c = rootEl τ K ε c * rootEl τ K β 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, rootEl_val, rootEl_val]
  exact (Commute.symm (pinnedX_commute_of_rootForm_nonneg hτ hε hβ hne h0 c 1)).eq

theorem commutator_root_caseB {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] {ε β : Fin τ.rank → ℤ} (hε : IsRoot τ ε) (hβ : IsRoot τ β) (hne : ε ≠ β)
    (hne' : ε ≠ -β) (hsum : IsRoot τ (ε + β)) :
    ∃ s : K, (s = 1 ∨ s = -1) ∧ ∀ c : K,
      ⁅rootEl τ K β 1, rootEl τ K ε c⁆ = rootEl τ K (ε + β) (s * c) := by
  obtain ⟨hC, hF⟩ := (simply_laced_root_commutator_unit τ hτ hε hβ hne hne').1 hsum
  refine ⟨-((commConst τ ε β (1, 1) : ℤ) : K), ?_, fun c => ?_⟩
  · rcases hC with h | h <;> rw [h] <;> simp
  · have h1 : ⁅rootEl τ K ε c, rootEl τ K β 1⁆ =
        rootEl τ K (ε + β) (((commConst τ ε β (1, 1) : ℤ) : K) * c * 1) := by
      apply Subtype.ext
      have h2 := hF K c 1
      rw [commutatorElement_def] at h2
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, rootEl_val]
      exact h2
    calc ⁅rootEl τ K β 1, rootEl τ K ε c⁆
        = (⁅rootEl τ K ε c, rootEl τ K β 1⁆)⁻¹ := by rw [commutatorElement_inv]
      _ = rootEl τ K (ε + β) (-(((commConst τ ε β (1, 1) : ℤ) : K) * c * 1)) := by
          rw [h1, rootEl_inv]
      _ = rootEl τ K (ε + β) (-((commConst τ ε β (1, 1) : ℤ) : K) * c) := by
          congr 1
          ring

theorem prod_eq_one_of_fix {A : Type*} [CommGroup A] {ι : Type*} [Fintype ι] (φ : A →* A)
    (f w : ι → A) (hφ : ∀ i, φ (f i) = w i * f i) (hfix : φ (∏ i, f i) = ∏ i, f i) :
    ∏ i, w i = 1 := by
  rw [map_prod] at hfix
  simp only [hφ, Finset.prod_mul_distrib] at hfix
  have h := congrArg (fun a => a * (∏ i, f i)⁻¹) hfix
  simpa using h

theorem prod_erase_inv {A : Type*} [CommGroup A] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → A) (h : ∏ i, w i = 1) (i₀ : ι) :
    w i₀ = (∏ i ∈ Finset.univ.erase i₀, w i)⁻¹ := by
  rw [← Finset.mul_prod_erase Finset.univ w (Finset.mem_univ i₀)] at h
  exact eq_inv_of_mul_eq_one_left h

end CFSG.LocalAnalysis.GLTheoremA.I107X

end
