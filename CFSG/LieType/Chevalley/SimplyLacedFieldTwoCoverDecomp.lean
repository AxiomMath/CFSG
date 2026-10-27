module

public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCoverRoots
public import CFSG.LieType.Chevalley.ExceptionalFieldFourCoverEdge

public section

namespace CFSG.LieType.Chevalley.SimplyLacedCover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Chevalley.RootOps

variable {τ : Tag}

@[expose] def DecompCond (γ δ α β : Fin τ.rank → ℤ) : Prop :=
  γ + δ = α ∧ iform γ δ = -1 ∧ γ ≠ -β ∧ 0 ≤ iform γ β ∧ δ ≠ -β ∧ 0 ≤ iform δ β

instance (γ δ α β : Fin τ.rank → ℤ) : Decidable (DecompCond γ δ α β) := by
  unfold DecompCond
  infer_instance

variable (τ) in
@[expose] def RepCheck (r : ℕ × ℕ × List Factor) : Prop :=
  0 ≤ iform (τ.rootCertificate.root r.1) (τ.rootCertificate.root r.2.1) →
    ∃ m < τ.rootCertificate.roots.length, ∃ m' < τ.rootCertificate.roots.length,
      DecompCond (τ.rootCertificate.root m) (τ.rootCertificate.root m')
        (τ.rootCertificate.root r.1) (τ.rootCertificate.root r.2.1)

instance (r : ℕ × ℕ × List Factor) : Decidable (RepCheck τ r) := by
  unfold RepCheck
  infer_instance

theorem repCheck_E6 : ∀ r ∈ repsOf .E6, RepCheck .E6 r := by
  decide +kernel

theorem repCheck_E7 : ∀ r ∈ repsOf .E7, RepCheck .E7 r := by
  decide +kernel

theorem repCheck_E8 : ∀ r ∈ repsOf .E8, RepCheck .E8 r := by
  decide +kernel

theorem simplyLaced_of_tag (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ∀ i, τ.symmetrizer i i = 1 := by
  rcases hτ with rfl | rfl | rfl <;> intro i <;> simp [Tag.symmetrizer]

theorem DecompAt.smul
    {α β : Fin τ.rank → ℤ} (h : DecompAt τ α β) (w : WeylGroup τ) :
    DecompAt τ (w • α) (w • β) := by
  obtain ⟨γ, δ, hγ, hδ, hsum, hγδ, hγβ, hγβ', hδβ, hδβ'⟩ := h
  refine ⟨w • γ, w • δ, IsRoot.smul hγ w, IsRoot.smul hδ w, by rw [← smul_add, hsum],
    by rw [iform_smul, hγδ], fun h => hγβ ?_, by rw [iform_smul]; exact hγβ', fun h => hδβ ?_,
    by rw [iform_smul]; exact hδβ'⟩
  · rw [← smul_neg] at h
    exact smul_left_cancel w h
  · rw [← smul_neg] at h
    exact smul_left_cancel w h

theorem decompAt_self_of
    (hτ : ∀ i, τ.symmetrizer i i = 1) {α γ δ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hδ : IsRoot τ δ) (hsum : γ + δ = α) (hγδ : iform γ δ = -1) :
    DecompAt τ α α := by
  have hγα : iform γ α = 1 := by
    rw [← hsum, iform_add_right, iform_self_eq_two hτ hγ, hγδ]
    norm_num
  have hδα : iform δ α = 1 := by
    rw [← hsum, iform_add_right, iform_self_eq_two hτ hδ, iform_comm, hγδ]
    norm_num
  have hα : IsRoot τ α := hsum ▸ isRoot_add hτ hγ hδ hγδ
  refine ⟨γ, δ, hγ, hδ, hsum, hγδ, ne_neg_of_iform hτ hα (by omega), by omega,
    ne_neg_of_iform hτ hα (by omega), by omega⟩

theorem decompAt_self
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) : DecompAt τ α α := by
  have hsl := simplyLaced_of_tag hτ
  obtain ⟨w, j, rfl⟩ := isRoot_iff_exists_smul_single.1 hα
  have hτ' : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := Or.inr hτ
  obtain ⟨k, hkj, hjk⟩ := ExceptionalCover.exists_single_edge hτ' j
  have hjk' : iform (Pi.single j 1 : Fin τ.rank → ℤ) (Pi.single k 1) = -1 := by
    rw [iform_single_left, hsl j, one_mul, Finset.sum_eq_single k
      (fun l _ hl => by rw [Pi.single_eq_of_ne hl, mul_zero])
      (fun h => absurd (Finset.mem_univ k) h), Pi.single_eq_same, mul_one, hjk]
  have hγ : IsRoot τ (Pi.single j 1 + Pi.single k 1) :=
    isRoot_add hsl (isRoot_single τ j) (isRoot_single τ k) hjk'
  have hδ : IsRoot τ (-Pi.single k 1) := IsRoot.neg (isRoot_single τ k)
  have hγδ : iform (Pi.single j 1 + Pi.single k 1 : Fin τ.rank → ℤ) (-Pi.single k 1) = -1 := by
    rw [iform_neg_right, iform_add_left, hjk', iform_self_eq_two hsl (isRoot_single τ k)]
    norm_num
  have h := decompAt_self_of hsl hγ hδ (by abel) hγδ
  exact h.smul w

theorem hasDecomp
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) : HasDecomp τ := by
  have hsl := simplyLaced_of_tag hτ
  intro α β hα hβ hne h0
  by_cases hab : α = β
  · subst hab
    exact decompAt_self hτ hα
  obtain ⟨r, hr, w, h1, h2⟩ := exists_smul_rep hα hβ hab hne
  have h0' : 0 ≤ iform (τ.rootCertificate.root r.1) (τ.rootCertificate.root r.2.1) := by
    rw [← iform_smul w, h1, h2]
    exact h0
  have hcheck : RepCheck τ r := by
    rcases hτ with rfl | rfl | rfl
    · exact repCheck_E6 r hr
    · exact repCheck_E7 r hr
    · exact repCheck_E8 r hr
  obtain ⟨m, hm, m', hm', hsum, hγδ, hγβ, hγβ', hδβ, hδβ'⟩ := hcheck h0'
  have hdec : DecompAt τ (τ.rootCertificate.root r.1) (τ.rootCertificate.root r.2.1) :=
    ⟨_, _, RootCertificate.isRoot_root (Tag.rootCertificate_check τ) m hm,
      RootCertificate.isRoot_root (Tag.rootCertificate_check τ) m' hm', hsum, hγδ, hγβ, hγβ',
      hδβ, hδβ'⟩
  have h := hdec.smul w
  rwa [h1, h2] at h

end CFSG.LieType.Chevalley.SimplyLacedCover
