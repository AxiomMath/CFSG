module

public import Mathlib.RepresentationTheory.Character

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

section ValueKernel

variable {M R : Type*} [One M]

def charValueKernel (θ : M → R) : Set M := {x | θ x = θ 1}

@[simp]
theorem mem_charValueKernel {θ : M → R} {x : M} : x ∈ charValueKernel θ ↔ θ x = θ 1 := Iff.rfl

theorem charValueKernel_eq_preimage (θ : M → R) : charValueKernel θ = θ ⁻¹' {θ 1} := (rfl)

theorem one_mem_charValueKernel (θ : M → R) : (1 : M) ∈ charValueKernel θ :=
  mem_charValueKernel.2 rfl

theorem charValueKernel_nonempty (θ : M → R) : (charValueKernel θ).Nonempty :=
  ⟨1, one_mem_charValueKernel θ⟩

end ValueKernel

variable {k : Type*} [Field k] {K : Type*} [Group K]

def irrChar (k : Type*) [Field k] (K : Type*) [Group K] : Set (K → k) :=
  {θ | ∃ V : FDRep k K, Representation.IsIrreducible V.ρ ∧ V.character = θ}

theorem mem_irrChar {θ : K → k} :
    θ ∈ irrChar k K ↔ ∃ V : FDRep k K, Representation.IsIrreducible V.ρ ∧ V.character = θ :=
  Iff.rfl

theorem FDRep.character_mem_irrChar (V : FDRep k K) (hV : Representation.IsIrreducible V.ρ) :
    V.character ∈ irrChar k K := ⟨V, hV, rfl⟩

theorem irrChar_conj {θ : K → k} (hθ : θ ∈ irrChar k K) (g h : K) : θ (h * g * h⁻¹) = θ g := by
  obtain ⟨V, -, rfl⟩ := hθ
  exact V.char_conj g h

theorem charValueKernel_conj_mem {θ : K → k} (hθ : θ ∈ irrChar k K) {g : K}
    (hg : g ∈ charValueKernel θ) (h : K) : h * g * h⁻¹ ∈ charValueKernel θ :=
  mem_charValueKernel.2 <| (irrChar_conj hθ g h).trans hg

def irrKer (k : Type*) [Field k] {K : Type*} [Group K] (H M : Subgroup K) : Set (K → k) :=
  {θ ∈ irrChar k K | (M : Set K) ⊆ charValueKernel θ ∧ ¬ (H : Set K) ⊆ charValueKernel θ}

def irrDetect (k : Type*) [Field k] {K : Type*} [Group K] (H : Subgroup K) : Set (K → k) :=
  {θ ∈ irrChar k K | ¬ (H : Set K) ⊆ charValueKernel θ}

theorem mem_irrKer {H M : Subgroup K} {θ : K → k} :
    θ ∈ irrKer k H M ↔
      θ ∈ irrChar k K ∧ (M : Set K) ⊆ charValueKernel θ ∧ ¬ (H : Set K) ⊆ charValueKernel θ :=
  Iff.rfl

theorem mem_irrDetect {H : Subgroup K} {θ : K → k} :
    θ ∈ irrDetect k H ↔ θ ∈ irrChar k K ∧ ¬ (H : Set K) ⊆ charValueKernel θ := Iff.rfl

theorem mem_irrKer_iff_values {H M : Subgroup K} {θ : K → k} :
    θ ∈ irrKer k H M ↔ θ ∈ irrChar k K ∧ (∀ x ∈ M, θ x = θ 1) ∧ ∃ x ∈ H, θ x ≠ θ 1 := by
  simp [mem_irrKer, Set.subset_def]

theorem mem_irrDetect_iff_values {H : Subgroup K} {θ : K → k} :
    θ ∈ irrDetect k H ↔ θ ∈ irrChar k K ∧ ∃ x ∈ H, θ x ≠ θ 1 := by
  simp [mem_irrDetect, Set.subset_def]

theorem irrKer_subset_irrChar (H M : Subgroup K) : irrKer k H M ⊆ irrChar k K := fun _ hθ => hθ.1

theorem irrDetect_subset_irrChar (H : Subgroup K) : irrDetect k H ⊆ irrChar k K :=
  fun _ hθ => hθ.1

theorem irrKer_subset_irrDetect (H M : Subgroup K) : irrKer k H M ⊆ irrDetect k H :=
  fun _ hθ => ⟨hθ.1, hθ.2.2⟩

theorem irrKer_eq_irrDetect_inter (H M : Subgroup K) :
    irrKer k H M = irrDetect k H ∩ {θ | (M : Set K) ⊆ charValueKernel θ} := by
  ext θ
  simp only [mem_irrKer, mem_irrDetect, Set.mem_inter_iff, Set.mem_ofPred_eq]
  tauto

theorem irrKer_bot (H : Subgroup K) : irrKer k H ⊥ = irrDetect k H := by
  rw [irrKer_eq_irrDetect_inter]
  refine Set.inter_eq_left.2 fun θ _ x hx => ?_
  rw [SetLike.mem_coe, Subgroup.mem_bot] at hx
  exact mem_charValueKernel.2 (by rw [hx])

theorem irrDetect_bot : irrDetect k (⊥ : Subgroup K) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun θ hθ => hθ.2 fun x hx => ?_
  rw [SetLike.mem_coe, Subgroup.mem_bot] at hx
  exact mem_charValueKernel.2 (by rw [hx])

theorem irrDetect_mono {H H' : Subgroup K} (h : H ≤ H') : irrDetect k H ⊆ irrDetect k H' :=
  fun _ hθ => ⟨hθ.1, fun hsub => hθ.2 fun _ hx => hsub (h hx)⟩

theorem irrKer_mono_left {H H' M : Subgroup K} (h : H ≤ H') : irrKer k H M ⊆ irrKer k H' M :=
  fun _ hθ => ⟨hθ.1, hθ.2.1, fun hsub => hθ.2.2 fun _ hx => hsub (h hx)⟩

theorem irrKer_anti_right {H M M' : Subgroup K} (h : M ≤ M') : irrKer k H M' ⊆ irrKer k H M :=
  fun _ hθ => ⟨hθ.1, fun _ hx => hθ.2.1 (h hx), hθ.2.2⟩

theorem irrKer_eq_empty_of_le {H M : Subgroup K} (h : H ≤ M) : irrKer k H M = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hθ => hθ.2.2 fun _ hx => hθ.2.1 (h hx)

end CFSG.FeitThompson
