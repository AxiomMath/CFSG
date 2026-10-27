module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningRoots
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCoverRoots
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.KE.CTRational

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement Matrix

set_option linter.unusedSectionVars false


section QuotChar

variable {τ : Tag}

@[expose] noncomputable def quotChar (Δ : AddSubgroup (Fin τ.rank → ℤ)) :
    Multiplicative (Fin τ.rank → ℤ) →* Multiplicative ((Fin τ.rank → ℤ) ⧸ Δ) :=
  AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' Δ)

theorem quotChar_eq_one_iff (Δ : AddSubgroup (Fin τ.rank → ℤ)) (α : Fin τ.rank → ℤ) :
    quotChar Δ (Multiplicative.ofAdd α) = 1 ↔ α ∈ Δ := by
  unfold quotChar
  constructor
  · intro h
    have h' : QuotientAddGroup.mk' Δ α = 0 := by
      have := congrArg Multiplicative.toAdd h
      simpa using this
    exact (QuotientAddGroup.eq_zero_iff _).1 h'
  · intro h
    have h' : QuotientAddGroup.mk' Δ α = 0 := (QuotientAddGroup.eq_zero_iff _).2 h
    apply Multiplicative.toAdd.injective
    simpa using h'

end QuotChar

section A2

variable {τ : Tag}

@[expose] def A2roots (β β' : Fin τ.rank → ℤ) : Set (Fin τ.rank → ℤ) :=
  {β, -β, β', -β', β + β', -(β + β')}

@[expose] def A2lattice (β β' : Fin τ.rank → ℤ) : AddSubgroup (Fin τ.rank → ℤ) :=
  AddSubgroup.closure {β, β'}

variable (hsl : ∀ i, τ.symmetrizer i i = 1)
include hsl

theorem iform_self_A2 {β β' : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hβ' : IsRoot τ β')
    (hab : iform β β' = -1) (m n : ℤ) :
    iform (m • β + n • β') (m • β + n • β') = 2 * (m * m - m * n + n * n) := by
  have h1 := SimplyLacedCover.iform_self_eq_two hsl hβ
  have h2 := SimplyLacedCover.iform_self_eq_two hsl hβ'
  have h3 : iform β' β = -1 := by rw [iform_comm, hab]
  simp only [iform_add_left, iform_add_right, iform_smul_left, iform_smul_right, h1, h2, hab, h3]
  ring

theorem mem_A2roots_of_mem_closure {β β' : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hβ' : IsRoot τ β')
    (hab : iform β β' = -1) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hmem : α ∈ A2lattice β β') : α ∈ A2roots β β' := by
  obtain ⟨m, n, rfl⟩ := AddSubgroup.mem_closure_pair.1 hmem
  have h := iform_self_A2 hsl hβ hβ' hab m n
  rw [SimplyLacedCover.iform_self_eq_two hsl hα] at h
  have h1 : m * m - m * n + n * n = 1 := by linarith
  have hn : n * n ≤ 1 := by nlinarith [sq_nonneg (2 * m - n)]
  have hn' : -1 ≤ n ∧ n ≤ 1 := by constructor <;> nlinarith
  have hm : m * m ≤ 1 := by nlinarith [sq_nonneg (2 * n - m)]
  have hm' : -1 ≤ m ∧ m ≤ 1 := by constructor <;> nlinarith
  obtain ⟨hn1, hn2⟩ := hn'
  obtain ⟨hm1, hm2⟩ := hm'
  interval_cases n <;> interval_cases m <;> simp at h1 <;>
    simp [A2roots]
  all_goals (iterate 5 right); abel

theorem isRoot_A2roots {β β' : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hβ' : IsRoot τ β')
    (hab : iform β β' = -1) {α : Fin τ.rank → ℤ} (hα : α ∈ A2roots β β') : IsRoot τ α := by
  have hs : IsRoot τ (β + β') := SimplyLacedCover.isRoot_add hsl hβ hβ' hab
  simp only [A2roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hα
  rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [hβ, IsRoot.neg hβ, hβ', IsRoot.neg hβ', hs, IsRoot.neg hs]

theorem A2roots_subset_lattice (β β' : Fin τ.rank → ℤ) : A2roots β β' ⊆ (A2lattice β β' : Set _) := by
  intro α hα
  have h1 : β ∈ A2lattice β β' := AddSubgroup.subset_closure (by simp)
  have h2 : β' ∈ A2lattice β β' := AddSubgroup.subset_closure (by simp)
  simp only [A2roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hα
  rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h1, neg_mem h1, h2, neg_mem h2, add_mem h1 h2, neg_mem (add_mem h1 h2)]

theorem kernelRoots_quotChar_A2 {β β' : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hβ' : IsRoot τ β')
    (hab : iform β β' = -1) :
    kernelRoots (quotChar (A2lattice β β')) = A2roots β β' := by
  ext α
  constructor
  · rintro ⟨hα, hk⟩
    exact mem_A2roots_of_mem_closure hsl hβ hβ' hab hα ((quotChar_eq_one_iff _ _).1 hk)
  · intro hα
    exact ⟨isRoot_A2roots hsl hβ hβ' hab hα,
      (quotChar_eq_one_iff _ _).2 (A2roots_subset_lattice hsl β β' hα)⟩

theorem componentRoots_quotChar_A2 {β β' : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hβ' : IsRoot τ β')
    (hab : iform β β' = -1) (hβk : β ∈ kernelRoots (quotChar (A2lattice β β'))) :
    componentRoots (quotChar (A2lattice β β')) (⟦⟨β, hβk⟩⟧ : KernelComponent _) =
      A2roots β β' := by
  have hker := kernelRoots_quotChar_A2 hsl hβ hβ' hab
  ext α
  constructor
  · rintro ⟨hα, -⟩
    rw [hker] at hα
    exact hα
  · intro hα
    have hαk : α ∈ kernelRoots (quotChar (A2lattice β β')) := by rw [hker]; exact hα
    refine ⟨hαk, mk_eq_of_iform_ne_zero (α := ⟨α, hαk⟩) (β := ⟨β, hβk⟩) ?_⟩
    change iform α β ≠ 0
    have h11 := SimplyLacedCover.iform_self_eq_two hsl hβ
    have h22 := SimplyLacedCover.iform_self_eq_two hsl hβ'
    have h21 : iform β' β = -1 := by rw [iform_comm, hab]
    simp only [A2roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hα
    rcases hα with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [iform_add_left, SimplyLacedCover.iform_neg_left, h11, h21]

theorem rootReflection_smul_two {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (v : Fin τ.rank → ℤ) :
    rootReflection γ • v = v - iform γ v • γ := by
  rw [rootReflection_smul hγ, corootPair, SimplyLacedCover.iform_self_eq_two hsl hγ,
    Int.mul_ediv_cancel_left _ (by norm_num)]

theorem A2_rotation {β β' : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hβ' : IsRoot τ β')
    (hab : iform β β' = -1) :
    ∃ w ∈ Subgroup.closure {t : WeylGroup τ | ∃ γ ∈ A2roots β β', t = rootReflection γ},
      w • β = β' ∧ w • β' = -(β + β') ∧ w • (-(β + β')) = β ∧ w • (-β) = -β' ∧
        w • (-β') = β + β' ∧ w • (β + β') = -β := by
  have hs : IsRoot τ (β + β') := SimplyLacedCover.isRoot_add hsl hβ hβ' hab
  have h11 := SimplyLacedCover.iform_self_eq_two hsl hβ
  have h22 := SimplyLacedCover.iform_self_eq_two hsl hβ'
  have h21 : iform β' β = -1 := by rw [iform_comm, hab]
  refine ⟨rootReflection (β + β') * rootReflection β,
    mul_mem (Subgroup.subset_closure ⟨β + β', by simp [A2roots], rfl⟩)
      (Subgroup.subset_closure ⟨β, by simp [A2roots], rfl⟩), ?_⟩
  simp only [mul_smul, rootReflection_smul_two hsl hβ, rootReflection_smul_two hsl hs, sub_eq_add_neg,
    iform_add_left, iform_add_right, SimplyLacedCover.iform_neg_left,
    SimplyLacedCover.iform_neg_right, iform_smul_right, h11, h22, hab, h21]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> module

end A2

end CFSG.HardMathSupport.Timmesfeld.LangTorus
