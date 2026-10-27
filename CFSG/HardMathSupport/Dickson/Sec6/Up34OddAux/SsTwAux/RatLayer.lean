module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.LayerGen

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem SsBig.exists_subgroupOf {ℓ : ℕ} {G : Type*} [Group G] {R : Subgroup G} (h : SsBig ℓ R) :
    ∃ V : Subgroup ↥R, IsPGroup ℓ V ∧ 8 ≤ Nat.card V := by
  obtain ⟨V, hV, hp, h8⟩ := h
  refine ⟨V.subgroupOf R, ?_, ?_⟩
  · exact hp.of_surjective (Subgroup.subgroupOfEquivOfLe hV).symm.toMonoidHom
      (MulEquiv.surjective _)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV).toEquiv]
    exact h8

section Layer

variable {τ : Tag} {L : Type}
  [Field L] [IsAlgClosed L] {p : ℕ}

theorem ssTw_rationalComponent_eq_layer (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hqs : CFSG.IsQuasisimple ↥(rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model)) :
    rationalComponent S.ρ S.Γ (rootCharHom a) i =
      rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model := by
  have horbit : rationalRoots S.ρ (rootCharHom a) i = componentRoots (rootCharHom a) i := by
    ext γ
    constructor
    · rintro ⟨k, δ, hδ, rfl⟩
      induction k generalizing δ with
      | zero => exact hδ
      | succ k ih =>
        rw [Function.iterate_succ_apply]
        exact ih _ (hρ δ hδ)
    · intro hγ
      exact ⟨0, γ, hγ, rfl⟩
  set P := rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model with hP
  have hPP : ⁅P, P⁆ = P := by
    have h1 := (Group.isPerfect_def.1 hqs.1)
    rw [_root_.commutator_def] at h1
    have h2 := congrArg (Subgroup.map P.subtype) h1
    rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
  have hPΓ : P ≤ S.Γ := by
    rw [← hPP]
    exact Subgroup.commutator_mono inf_le_right inf_le_right
  have hspan : rationalSpan S.ρ S.Γ (rootCharHom a) i = P := by
    rw [rationalSpan, horbit]
    refine le_antisymm ?_ ?_
    · exact inf_le_inf_left _ (Subgroup.commutator_le.2 fun x hx y hy => by
        rw [commutatorElement_def]
        exact S.D.model.mul_mem (S.D.model.mul_mem (S.D.model.mul_mem hx hy)
          (S.D.model.inv_mem hx)) (S.D.model.inv_mem hy))
    · exact le_inf inf_le_left hPΓ
  rw [rationalComponent, hspan, hPP]

theorem ssTw_exists_f (S : LangSetup τ L p) {ℓ : ℕ} [hch : CharP L ℓ] :
    ∃ f : ℕ, 1 ≤ f ∧ S.D.q = ℓ ^ f := by
  obtain ⟨ℓ', f, hℓ', hchar, hf, hq⟩ := S.exists_char_pow
  have : ℓ' = ℓ := CharP.eq L hchar hch
  subst this
  exact ⟨f, hf, hq⟩

theorem ssTw_exists_pgroup_of_layer (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    {ℓ : ℕ}
    (hP : SsQB ℓ (rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model)) :
    ∃ V : Subgroup ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i), IsPGroup ℓ V ∧
      8 ≤ Nat.card V := by
  have heq := ssTw_rationalComponent_eq_layer S i hρ hP.1
  rw [heq]
  exact hP.2.exists_subgroupOf

theorem ssTw_finite_rationalComponent (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) :
    Finite ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  haveI := S.finite
  have hcomm : ∀ H : Subgroup (ModGL τ L), ⁅H, H⁆ ≤ H := fun H =>
    Subgroup.commutator_le.2 fun x hx y hy => by
      rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)
  have hΓ : S.Γ ≤ S.D.model := hcomm S.D.model
  have hR : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ S.D.model :=
    (hcomm _).trans (inf_le_right.trans hΓ)
  exact Finite.of_injective (Subgroup.inclusion hR) (Subgroup.inclusion_injective hR)

end Layer

end CFSG.HardMathSupport.Dickson.Sec6
