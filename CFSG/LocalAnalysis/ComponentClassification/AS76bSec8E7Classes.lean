module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Defs
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalModel

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction

variable {K : Type} [Field K]

noncomputable abbrev e7RootElt
    (γ : Fin Tag.E7.rank → ℤ) : adjointGroup .E7 K :=
  ⟨pinnedX .E7 K γ 1, pinnedX_mem_adjointGroup _ _⟩

theorem e7Frames_facts : ∀ F ∈ [e7FrameX, e7FrameY, e7FrameZ, e7FrameU, e7FrameV],
    F ≠ [] ∧ F.Nodup ∧ F.Pairwise fun σ σ' => iform σ σ' = 0 := by
  decide +kernel

theorem e7FramePt_mul_self
    [CharP K 2] {F : List (Fin Tag.E7.rank → ℤ)} (hF : ∀ σ ∈ F, IsRoot .E7 σ)
    (horth : F.Pairwise fun σ σ' => iform σ σ' = 0) :
    e7FramePt K F * e7FramePt K F = 1 := by
  have hτ : Tag.E7 = .D4 ∨ Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8 :=
    Or.inr (Or.inr (Or.inl rfl))
  apply Subtype.ext
  show (F.map fun σ => pinnedX .E7 K σ 1).prod * (F.map fun σ => pinnedX .E7 K σ 1).prod = 1
  induction F with
  | nil => simp
  | cons a F ih =>
    rw [List.pairwise_cons] at horth
    have ha := hF a List.mem_cons_self
    have hcomm : Commute (pinnedX .E7 K a 1) (F.map fun σ => pinnedX .E7 K σ 1).prod :=
      Commute.list_prod_right _ _ fun y hy => by
        obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hy
        exact classD4_commute_pinnedX hτ ha (hF σ (List.mem_cons_of_mem _ hσ))
          (horth.1 σ hσ).ge 1 1
    simp only [List.map_cons, List.prod_cons]
    calc pinnedX .E7 K a 1 * (F.map fun σ => pinnedX .E7 K σ 1).prod *
          (pinnedX .E7 K a 1 * (F.map fun σ => pinnedX .E7 K σ 1).prod)
        = pinnedX .E7 K a 1 * pinnedX .E7 K a 1 *
            ((F.map fun σ => pinnedX .E7 K σ 1).prod *
              (F.map fun σ => pinnedX .E7 K σ 1).prod) := by
          rw [mul_assoc, ← mul_assoc _ (pinnedX .E7 K a 1), ← hcomm.eq]
          group
      _ = 1 := by
          rw [← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero, one_mul,
            ih (fun σ hσ => hF σ (List.mem_cons_of_mem _ hσ)) horth.2]

theorem e7FramePt_ne_one
    {F : List (Fin Tag.E7.rank → ℤ)}
    (hne : F ≠ []) (hnd : F.Nodup) (hF : ∀ σ ∈ F, IsRoot .E7 σ ∧ 0 < height σ) :
    e7FramePt K F ≠ 1 := by
  intro h1
  have h := congrArg Subtype.val h1
  have h0 : (F.map fun σ => pinnedX .E7 K σ ((fun _ => (1 : K)) σ)).prod =
      (F.map fun σ => pinnedX .E7 K σ ((fun _ => (0 : K)) σ)).prod := by
    simp only [pinnedX_zero, List.map_const', List.prod_replicate, one_pow]
    exact h
  obtain ⟨σ, hσ⟩ := List.exists_mem_of_ne_nil F hne
  exact one_ne_zero (pinnedX_list_prod_injective F hnd hF _ _ h0 σ hσ)

theorem involution_e7Reps
    [CharP K 2] : ∀ x ∈ e7Reps K, x * x = 1 ∧ x ≠ 1 := by
  have hroots : ∀ F : List (Fin Tag.E7.rank → ℤ),
      (∀ σ ∈ F, σ ∈ e7FrameX ++ e7FrameY ++ e7FrameZ ++ e7FrameU ++ e7FrameV) →
      ∀ σ ∈ F, IsRoot .E7 σ ∧ 0 < height σ := fun F hF σ hσ =>
    ⟨(isRoot_of_mem_e7Frames σ (hF σ hσ)).1, (isRoot_of_mem_e7Frames σ (hF σ hσ)).2.2⟩
  have key : ∀ F ∈ [e7FrameX, e7FrameY, e7FrameZ, e7FrameU, e7FrameV],
      (∀ σ ∈ F, σ ∈ e7FrameX ++ e7FrameY ++ e7FrameZ ++ e7FrameU ++ e7FrameV) →
        e7FramePt K F * e7FramePt K F = 1 ∧ e7FramePt K F ≠ 1 := by
    intro F hF hsub
    obtain ⟨h1, h2, h3⟩ := e7Frames_facts F hF
    have hr := hroots F hsub
    exact ⟨e7FramePt_mul_self (fun σ hσ => (hr σ hσ).1) h3, e7FramePt_ne_one h1 h2 hr⟩
  intro x hx
  simp only [e7Reps, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact key _ (by simp) fun σ hσ => by simp_all
  · exact key _ (by simp) fun σ hσ => by simp_all
  · exact key _ (by simp) fun σ hσ => by simp_all
  · exact key _ (by simp) fun σ hσ => by simp_all
  · exact key _ (by simp) fun σ hσ => by simp_all

theorem charTwo_e7Reps
    [Finite K] [CharP K 2] : ∀ x ∈ e7Reps K, Exc.CharTwo x := by
  intro x hx
  obtain ⟨hx2, hx1⟩ := involution_e7Reps x hx
  exact EvenOddRadical.charTwo_of_involution (.ordinary .E7) (x := x) hx2 hx1

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
