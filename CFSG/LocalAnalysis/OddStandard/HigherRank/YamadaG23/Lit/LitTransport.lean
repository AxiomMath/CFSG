module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitInputs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

theorem lit_isQuotIso_subgroupOf {Γ : Type} [Group Γ] {K N C : Subgroup Γ} (hNK : N ≤ K)
    {Q : Type} [Group Q] (h : IsQuotIso N C Q) :
    IsQuotIso (N.subgroupOf K) (C.subgroupOf K) Q := by
  obtain ⟨hCN, φ, hφ, hker⟩ := h
  let ψ : ↥(N.subgroupOf K) →* ↥N := (Subgroup.subgroupOfEquivOfLe hNK).toMonoidHom
  refine ⟨Subgroup.subgroupOf_mono K hCN, φ.comp ψ,
    hφ.comp (Subgroup.subgroupOfEquivOfLe hNK).surjective, ?_⟩
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker]
  simp only [Subgroup.mem_subgroupOf]
  rfl

theorem lit_isQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.IsQuasisimple A) : CFSG.IsQuasisimple B :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv e h

theorem lit_psl4_of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : LitPSLU4All S) : LitPSLU4All S' := by
  rcases h with ⟨p, f, hp, hf, hmod, hmodel⟩ | ⟨p, f, hp, hf, hmod, hmodel⟩
  · exact Or.inl ⟨p, f, hp, hf, hmod, CFSG.Blueprint.LieModel.of_mulEquiv e hmodel⟩
  · exact Or.inr ⟨p, f, hp, hf, hmod, CFSG.Blueprint.LieModel.of_mulEquiv e hmodel⟩

theorem lit_isSporadic_of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    {s : TauCeti.SporadicName} (h : CFSG.Blueprint.NativeSporadic.IsSporadic S' s) :
    CFSG.Blueprint.NativeSporadic.IsSporadic S s := by
  obtain ⟨f⟩ := h
  exact ⟨e.trans f⟩

end CFSG.OddStandard.HigherRank.YamadaG23
