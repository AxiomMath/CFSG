module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHigh
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7FrameLine

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction

variable {K : Type} [Field K]

theorem commute_e7FrameLine_root
    [CharP K 2] {γ : Fin Tag.E7.rank → ℤ} (hγ : IsRoot .E7 γ) {c : K} (hc : c ≠ 0)
    {g : adjointGroup .E7 K} (hg : g ∈ Exc.cent (e7FrameElt K [γ] c))
    {z : adjointGroup .E7 K} (hz : z ∈ e7FrameLine K [γ]) : z * g = g * z := by
  have hτ : Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8 := Or.inr (Or.inl rfl)
  have hτ' : Tag.E7 = .D4 ∨ Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8 :=
    Or.inr (Or.inr (Or.inl rfl))
  have hr : ∀ σ ∈ [γ], IsRoot .E7 σ := by simpa using hγ
  have ho : [γ].Pairwise fun σ σ' => iform σ σ' = 0 := List.pairwise_singleton _ _
  obtain ⟨d, rfl⟩ := (mem_e7FrameLine hr ho).1 hz
  have hg' : (g : ModGL .E7 K) ∈
      centralizer ({pinnedX .E7 K γ c} : Set (ModGL .E7 K)) ⊓ adjointGroup .E7 K := by
    refine ⟨mem_centralizer_singleton_iff.2 ?_, g.2⟩
    have h := congrArg Subtype.val (mem_centralizer_singleton_iff.1 hg)
    simpa [coe_e7FrameElt] using h
  rw [EPilot.centralizer_pinnedX_inf_eq hτ hγ hc] at hg'
  have hle : rootSpan .E7 K (EPilot.radicalRoots .E7 γ) ⊔ rootSpan .E7 K (EPilot.rootPerp .E7 γ) ≤
      centralizer ({pinnedX .E7 K γ d} : Set (ModGL .E7 K)) := by
    refine sup_le (iSup₂_le fun δ hδ => (closure_le _).2 ?_) (iSup₂_le fun δ hδ =>
      (closure_le _).2 ?_)
    · rintro _ ⟨e, rfl⟩
      exact mem_centralizer_singleton_iff.2 (classD4_commute_pinnedX hτ' hδ.1 hγ hδ.2.le e d).eq
    · rintro _ ⟨e, rfl⟩
      exact mem_centralizer_singleton_iff.2 (classD4_commute_pinnedX hτ' hδ.1 hγ hδ.2.ge e d).eq
  have h2 := mem_centralizer_singleton_iff.1 (hle hg')
  apply Subtype.ext
  simpa [coe_e7FrameElt] using h2.symm

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
