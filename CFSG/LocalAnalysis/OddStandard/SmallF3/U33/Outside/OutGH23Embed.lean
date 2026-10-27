module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGHII23
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGH23Vocab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGH23GL4
public import CFSG.GH74.Exceptional.LinearFourTwo

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open CFSG.GH74.GLS.Bg.TwoGroups

theorem gh23_exists_embedding : ∃ ρ : MulAut (E2 4) →* Equiv.Perm (Fin 8),
    Function.Injective ρ ∧ ∀ φ, ρ φ ∈ alternatingGroup (Fin 8) := by
  obtain ⟨e⟩ := gh23_mulAut_equiv_GL4
  let g : MulAut (E2 4) ≃* alternatingGroup (Fin 8) :=
    e.trans CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.symm
  refine ⟨(alternatingGroup (Fin 8)).subtype.comp g.toMonoidHom, ?_, ?_⟩
  · intro x y hxy
    exact g.injective (Subtype.val_injective hxy)
  · intro φ
    exact (g φ).2

theorem gh23_noNormalTwo_range {P G : Type*} [Group P] [Group G] (ι : P →* G)
    (hι : Function.Injective ι) (hO : O2 (⊤ : Subgroup P) = ⊥) : NoNormalTwo ι.range := by
  unfold NoNormalTwo
  intro N hN hHnorm h2
  let N' : Subgroup P := N.comap ι
  have hnorm' : (⊤ : Subgroup P) ≤ Subgroup.normalizer (N' : Set P) := by
    rw [Subgroup.le_normalizer_iff]
    intro x _ k hk
    rw [Subgroup.mem_comap] at hk ⊢
    have hx : ι x ∈ Subgroup.normalizer (N : Set G) := hHnorm ⟨x, rfl⟩
    rw [Subgroup.mem_normalizer_iff] at hx
    simpa using (hx (ι k)).mp hk
  have h2' : IsPGroup 2 N' := h2.comap_of_injective ι hι
  have hN'O : N' ≤ O2 (⊤ : Subgroup P) := by
    rw [O2]
    exact le_iSup
      (fun M : {M : Subgroup P // M ≤ ⊤ ∧ ⊤ ≤ Subgroup.normalizer (M : Set P) ∧ IsPGroup 2 M}
        => M.1) ⟨N', le_top, hnorm', h2'⟩
  rw [hO] at hN'O
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp (hN hy)
  have hxN' : x ∈ N' := by
    rw [Subgroup.mem_comap]
    exact hy
  have hxbot : x ∈ (⊥ : Subgroup P) := hN'O hxN'
  rw [Subgroup.mem_bot] at hxbot
  simp [hxbot]

theorem ghii23List_of_alt8 (h : Alt8Classification) : GHII23List := by
  unfold GHII23List
  intro P _ ι hι hns hO
  obtain ⟨ρ, hρ, hρA⟩ := gh23_exists_embedding
  let ι₁ : P →* Equiv.Perm (Fin 8) := ρ.comp ι
  have hι₁ : Function.Injective ι₁ := hρ.comp hι
  let H : Subgroup (Equiv.Perm (Fin 8)) := ι₁.range
  have hH : H ≤ alternatingGroup (Fin 8) := by
    rintro _ ⟨p, rfl⟩
    exact hρA (ι p)
  have hnsH : ¬ IsSolvable ↥H := by
    intro hs
    exact hns (@Group.isSolvable_of_isSolvable_injective P ↥ι₁.range _ _
      (MonoidHom.ofInjective hι₁).toMonoidHom (MonoidHom.ofInjective hι₁).injective hs)
  have hNN : NoNormalTwo H := gh23_noNormalTwo_range ι₁ hι₁ hO
  unfold Alt8Classification at h
  exact GH23Concl.of_mulEquiv (MonoidHom.ofInjective hι₁) (h H hH hnsH hNN)

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
