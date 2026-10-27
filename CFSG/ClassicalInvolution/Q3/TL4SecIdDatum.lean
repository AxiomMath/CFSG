module

public import CFSG.ClassicalInvolution.Q3.TL4E3Norm

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.Blueprint

theorem inClass3_conjClass_of_lift {Y : Type} [Group Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    (hc : TightCls Y R S t) {L : Subgroup Y} (hKL : tightCore R ≤ L)
    (hL : IsClassicalMember3 L t) : InClass3 (CoreAssembly.conjClass L) := by
  refine Q3B.inClass3_conjClass hL ?_
  have hgen : (⨆ g : Y, conjSub g (tightCore R)) = ⊤ := hc.2.1
  rw [eq_top_iff, ← hgen]
  refine iSup_le fun g y hy => ?_
  rw [mem_conjSub_iff] at hy
  have h1 : g⁻¹ * y * g ∈ Subgroup.normalClosure (L : Set Y) :=
    Subgroup.subset_normalClosure (hKL hy)
  have h2 := (Subgroup.normalClosure_normal (s := (L : Set Y))).conj_mem _ h1 g
  rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at h2

section Cit3


@[expose] def SecIdLie3 {Y : Type} [Group Y] (R : Subgroup Y) (t : Y) : Prop :=
  ∃ L : Subgroup Y, tightCore R ≤ L ∧ IsClassicalMember3 L t ∧
    InClass3 (CoreAssembly.conjClass L) ∧ LieSystemMod3 (CoreAssembly.conjClass L)

@[expose] def SecIdentOut3 (Y : Type) [Group Y] (R : Subgroup Y) (t : Y) : Prop :=
  TightInO2 t ∨
    (TightEdgeless R ∧ ¬ TightActs3 R t ∧ (Thm6Exit Y ∨ TightTwisted Y t)) ∨
    (TightEdgeless R ∧ Nonempty (Y ⧸ Subgroup.center Y ≃* NativeSporadic.Carrier .M12)) ∨
    (Subgroup.center Y ≠ ⊥ ∧ (LieModel (Y ⧸ Subgroup.center Y) .PSp 3 2 1 ∨
      LieModel (Y ⧸ Subgroup.center Y) .POmegaPlus 4 2 1)) ∨
    SecIdLie3 R t

@[expose] def SecIdentDatum3 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n → ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightDatum R S t → TightCls Y R S t → SecIdentOut3 Y R t

theorem secIdentDatum3_of {n : ℕ} (hP : TightBelowRPlus 3 n) (hA : CIT3Below n) :
    SecIdentDatum3 n := by
  intro Y _ _ hY R S t hd hc
  have hcR : TightClsR 3 Y R S t := tightClsR_three_iff.mpr hc
  rcases hP.tbelow Y hY R S t hd hcR with hex | hg
  · by_cases hE2 : TightInO2 t
    · exact Or.inl hE2
    rcases TightEx.reduce hd hc hex hE2 with ⟨he, h3⟩ | ⟨he, hM⟩ | h4
    · refine Or.inr (Or.inl ⟨he, h3, ?_⟩)
      rcases (tightDichotomy_of hd hc).resolve_left hE2 with hq | htw
      · rcases hP.thm6 Y hY R S t hd hcR hE2 hq he with hg | hx
        · exact absurd (acts3_of_good hg) h3
        · exact Or.inl hx
      · exact Or.inr htw
    · exact Or.inr (Or.inr (Or.inl ⟨he, hM⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  · obtain ⟨L, hKL, hL⟩ := tightHasLift_of_good hd hg
    have hΛ := inClass3_conjClass_of_lift hc hKL hL
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨L, hKL, hL, hΛ, hA Y hY _ hΛ⟩)))

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
