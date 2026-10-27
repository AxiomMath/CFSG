module

public import CFSG.LieType.Chevalley.ConnectedDiagram
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidRank
public import CFSG.LieType.Chevalley.BruhatCellFactorization
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint

set_option linter.unusedSectionVars false

section RootGraph

variable {τ : Tag}

@[expose] def RootAdj (τ : Tag) (a b : Fin τ.rank → ℤ) : Prop :=
  IsRoot τ a ∧ IsRoot τ b ∧ iform a b ≠ 0

theorem RootAdj.symm
    {a b : Fin τ.rank → ℤ} (h : RootAdj τ a b) : RootAdj τ b a :=
  ⟨h.2.1, h.1, fun e => h.2.2 ((iform_comm a b).trans e)⟩

theorem symmetrizer_eq_one_of_simplyLaced (hτ : SimplyLacedTag τ) (i : Fin τ.rank) :
    τ.symmetrizer i i = 1 := by
  rcases hτ with rfl | rfl | rfl | rfl <;> fin_cases i <;> decide

theorem iform_self_eq_two
    (hτ : SimplyLacedTag τ) {v : Fin τ.rank → ℤ} (hv : IsRoot τ v) : iform v v = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hv
  rw [hj, symmetrizer_eq_one_of_simplyLaced hτ]
  norm_num

theorem rootAdj_reflect
    (hτ : SimplyLacedTag τ) {v : Fin τ.rank → ℤ} (hv : IsRoot τ v) (i : Fin τ.rank) :
    RootAdj τ (reflect τ i v) v := by
  refine ⟨IsRoot.reflect i hv, hv, ?_⟩
  have hx : reflect τ i v = v - (∑ j, τ.cartan i j * v j) • Pi.single i 1 := rfl
  rw [hx, iform_sub_left, iform_smul_left, iform_single_left, symmetrizer_eq_one_of_simplyLaced hτ,
    iform_self_eq_two hτ hv]
  intro h
  set c := ∑ j, τ.cartan i j * v j
  have h2 : c * c = 2 := by linarith
  have : c ≤ 1 := by nlinarith
  have : -1 ≤ c := by nlinarith
  interval_cases c <;> omega

theorem rootAdj_single
    {i j : Fin τ.rank} (h : (dynkinGraph τ).Adj i j) :
    RootAdj τ (Pi.single i 1) (Pi.single j 1) := by
  refine ⟨isRoot_single τ i, isRoot_single τ j, ?_⟩
  have hsum : ∑ k, τ.cartan i k * (Pi.single j 1 : Fin τ.rank → ℤ) k = τ.cartan i j := by
    simp [Pi.single_apply]
  rw [iform_single_left, hsum]
  have hs : 0 < τ.symmetrizer i i := symmetrizer_pos τ i
  have : τ.cartan i j ≠ 0 := by
    intro h0
    have := h.2
    rw [h0, zero_mul] at this
    exact lt_irrefl _ this
  exact mul_ne_zero hs.ne' this

theorem reach_single
    (hτ : SimplyLacedTag τ) {v : Fin τ.rank → ℤ} (hv : IsRoot τ v) :
    ∃ j, Relation.ReflTransGen (RootAdj τ) v (Pi.single j 1) := by
  induction hv with
  | basis j => exact ⟨j, Relation.ReflTransGen.refl⟩
  | @reflect i v hv ih =>
    obtain ⟨j, hj⟩ := ih
    exact ⟨j, Relation.ReflTransGen.head (rootAdj_reflect hτ hv i) hj⟩

theorem reach_simple (τ : Tag)
    (i j : Fin τ.rank) :
    Relation.ReflTransGen (RootAdj τ) (Pi.single i 1) (Pi.single j 1) := by
  have h := (SimpleGraph.reachable_iff_reflTransGen i j).1
    ((dynkinGraph_connected τ).preconnected i j)
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (rootAdj_single hstep)

theorem reach_all
    (hτ : SimplyLacedTag τ) {a b : Fin τ.rank → ℤ} (ha : IsRoot τ a) (hb : IsRoot τ b) :
    Relation.ReflTransGen (RootAdj τ) a b := by
  obtain ⟨i, hi⟩ := reach_single hτ ha
  obtain ⟨j, hj⟩ := reach_single hτ hb
  have key : ∀ x y : Fin τ.rank → ℤ, Relation.ReflTransGen (RootAdj τ) x y →
      Relation.ReflTransGen (RootAdj τ) y x := by
    intro x y h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ h ih => exact Relation.ReflTransGen.head h.symm ih
  have hj' := key _ _ hj
  exact hi.trans ((reach_simple τ i j).trans hj')

end RootGraph

section Closed

variable {τ : Tag}

structure IsClosedRoots (Ψ' : Set (Fin τ.rank → ℤ)) : Prop where
  isRoot : ∀ α ∈ Ψ', IsRoot τ α
  neg_mem : ∀ α ∈ Ψ', -α ∈ Ψ'
  add_mem : ∀ α ∈ Ψ', ∀ β ∈ Ψ', IsRoot τ (α + β) → α + β ∈ Ψ'

variable {Ψ' : Set (Fin τ.rank → ℤ)}

theorem exists_neg_pair (h : IsClosedRoots Ψ') {β γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hγ' : γ ∉ Ψ') (hf : iform β γ ≠ 0) :
    ∃ γ'', IsRoot τ γ'' ∧ γ'' ∉ Ψ' ∧ iform β γ'' < 0 := by
  by_cases hlt : iform β γ < 0
  · exact ⟨γ, hγ, hγ', hlt⟩
  · refine ⟨-γ, IsRoot.neg hγ, fun hm => hγ' ?_, ?_⟩
    · simpa using h.neg_mem _ hm
    · rw [← neg_one_smul ℤ γ, iform_smul_right]
      omega

theorem exists_add_of_neighbor (h : IsClosedRoots Ψ') {β γ : Fin τ.rank → ℤ} (hβ : β ∈ Ψ')
    (hγ : IsRoot τ γ) (hγ' : γ ∉ Ψ') (hf : iform β γ ≠ 0) :
    ∃ γ₁ γ₂, IsRoot τ γ₁ ∧ γ₁ ∉ Ψ' ∧ IsRoot τ γ₂ ∧ γ₂ ∉ Ψ' ∧ β = γ₁ + γ₂ := by
  obtain ⟨g, hg, hg', hlt⟩ := exists_neg_pair h hγ hγ' hf
  have hβr := h.isRoot β hβ
  have hne : β ≠ -g := fun e => hg' (by simpa [e] using h.neg_mem _ hβ)
  have hsum := isRoot_add_of_iform_neg hβr hg hne hlt
  refine ⟨β + g, -g, hsum, fun hm => hg' ?_, IsRoot.neg hg, fun hm => hg' ?_, by abel⟩
  · have := h.add_mem _ hm _ (h.neg_mem _ hβ) (by simpa using hg)
    simpa using this
  · simpa using h.neg_mem _ hm

@[expose] def AllNeighborsIn (Ψ' : Set (Fin τ.rank → ℤ)) (β : Fin τ.rank → ℤ) : Prop :=
  β ∈ Ψ' ∧ ∀ γ, IsRoot τ γ → γ ∉ Ψ' → iform β γ = 0

theorem allNeighborsIn_propagate (h : IsClosedRoots Ψ') {β ε : Fin τ.rank → ℤ}
    (hβ : AllNeighborsIn Ψ' β) (hε : IsRoot τ ε) (hf : iform β ε ≠ 0) :
    AllNeighborsIn Ψ' ε := by
  have hεΨ : ε ∈ Ψ' := by
    by_contra hε'
    exact hf (hβ.2 ε hε hε')
  refine ⟨hεΨ, fun ζ hζ hζ' => ?_⟩
  by_contra hne
  obtain ⟨g, hg, hg', hlt⟩ := exists_neg_pair h hζ hζ' hne
  have hne' : ε ≠ -g := fun e => hg' (by simpa [e] using h.neg_mem _ hεΨ)
  have hsum := isRoot_add_of_iform_neg hε hg hne' hlt
  have hout : ε + g ∉ Ψ' := fun hm => by
    apply hg'
    have := h.add_mem _ hm _ (h.neg_mem _ hεΨ) (by simpa using hg)
    simpa using this
  have h0 : iform β g = 0 := hβ.2 g hg hg'
  have h1 := hβ.2 (ε + g) hsum hout
  rw [iform_add_right, h0, add_zero] at h1
  exact hf h1

theorem exists_neighbor_outside (hτ : SimplyLacedTag τ) (h : IsClosedRoots Ψ')
    (hproper : ∃ γ, IsRoot τ γ ∧ γ ∉ Ψ') {β : Fin τ.rank → ℤ} (hβ : β ∈ Ψ') :
    ∃ γ, IsRoot τ γ ∧ γ ∉ Ψ' ∧ iform β γ ≠ 0 := by
  by_contra hno
  push Not at hno
  have hP : AllNeighborsIn Ψ' β := ⟨hβ, hno⟩
  obtain ⟨γ₀, hγ₀, hγ₀'⟩ := hproper
  have key : ∀ x, Relation.ReflTransGen (RootAdj τ) β x → AllNeighborsIn Ψ' x := by
    intro x hx
    induction hx with
    | refl => exact hP
    | tail _ hs ih => exact allNeighborsIn_propagate h ih hs.2.1 hs.2.2
  exact hγ₀' (key γ₀ (reach_all hτ (h.isRoot β hβ) hγ₀)).1

theorem exists_add_outside (hτ : SimplyLacedTag τ) (h : IsClosedRoots Ψ')
    (hproper : ∃ γ, IsRoot τ γ ∧ γ ∉ Ψ') {β : Fin τ.rank → ℤ} (hβ : β ∈ Ψ') :
    ∃ γ₁ γ₂, IsRoot τ γ₁ ∧ γ₁ ∉ Ψ' ∧ IsRoot τ γ₂ ∧ γ₂ ∉ Ψ' ∧ β = γ₁ + γ₂ := by
  obtain ⟨γ, hγ, hγ', hf⟩ := exists_neighbor_outside hτ h hproper hβ
  exact exists_add_of_neighbor h hβ hγ hγ' hf

end Closed

section Generation


open scoped commutatorElement

variable {τ : Tag} {L : Type} [Field L] {Ψ' : Set (Fin τ.rank → ℤ)}

theorem pinnedX_mem_rootSpan_of_add (hτ : SimplyLacedTag τ) (h : IsClosedRoots Ψ')
    (hproper : ∃ γ, IsRoot τ γ ∧ γ ∉ Ψ') {β : Fin τ.rank → ℤ} (hβ : β ∈ Ψ') (t : L) :
    pinnedX τ L β t ∈ rootSpan τ L {γ | IsRoot τ γ ∧ γ ∉ Ψ'} := by
  obtain ⟨γ₁, γ₂, h1, h1', h2, h2', rfl⟩ := exists_add_outside hτ h hproper hβ
  have hsum : IsRoot τ (γ₁ + γ₂) := h.isRoot _ hβ
  have hne1 : γ₁ ≠ γ₂ := by
    intro e
    rw [← e] at hsum
    have h2 := iform_self_eq_two hτ hsum
    have h3 := iform_self_eq_two hτ h1
    rw [← two_smul ℤ γ₁, iform_smul_left, iform_smul_right, h3] at h2
    omega
  have hne2 : γ₁ ≠ -γ₂ := by
    intro e
    rw [e, neg_add_cancel] at hsum
    exact (IsRoot.ne_zero hsum) rfl
  obtain ⟨hε, hform⟩ := (simply_laced_root_commutator_unit τ hτ h1 h2 hne1 hne2).1 hsum
  have hε' : ((commConst τ γ₁ γ₂ (1, 1) : ℤ) : L) * ((commConst τ γ₁ γ₂ (1, 1) : ℤ) : L) = 1 := by
    rcases hε with e | e <;> rw [e] <;> simp
  have key := hform L (((commConst τ γ₁ γ₂ (1, 1) : ℤ) : L) * t) 1
  have e2 : ((commConst τ γ₁ γ₂ (1, 1) : ℤ) : L) *
      (((commConst τ γ₁ γ₂ (1, 1) : ℤ) : L) * t) * 1 = t := by
    rw [← mul_assoc, hε', one_mul, mul_one]
  rw [e2] at key
  rw [← key, commutatorElement_def]
  have m1 : γ₁ ∈ {γ | IsRoot τ γ ∧ γ ∉ Ψ'} := ⟨h1, h1'⟩
  have m2 : γ₂ ∈ {γ | IsRoot τ γ ∧ γ ∉ Ψ'} := ⟨h2, h2'⟩
  exact mul_mem (mul_mem (mul_mem (pinnedX_mem_rootSpan m1 _) (pinnedX_mem_rootSpan m2 _))
    (inv_mem (pinnedX_mem_rootSpan m1 _))) (inv_mem (pinnedX_mem_rootSpan m2 _))

theorem adjointGroup_le_rootSpan_compl (hτ : SimplyLacedTag τ) (h : IsClosedRoots Ψ')
    (hproper : ∃ γ, IsRoot τ γ ∧ γ ∉ Ψ') :
    adjointGroup τ L ≤ rootSpan τ L {γ | IsRoot τ γ ∧ γ ∉ Ψ'} := by
  rw [adjointGroup_eq_rootSpan]
  refine iSup₂_le fun γ hγ => ?_
  by_cases hγ' : γ ∈ Ψ'
  · rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    exact pinnedX_mem_rootSpan_of_add hτ h hproper hγ' c
  · exact le_iSup₂_of_le γ ⟨hγ, hγ'⟩ le_rfl

end Generation

end CFSG.HardMathSupport.Timmesfeld.LangTorus
