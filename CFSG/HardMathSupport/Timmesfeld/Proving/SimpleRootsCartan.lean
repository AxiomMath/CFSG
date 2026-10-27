module

public import CFSG.LieType.Chevalley.KernelComponentRoots

public section

namespace CFSG.HardMathSupport.Timmesfeld.Proving

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

section Helpers

variable {τ : Tag}
  {Ψ : Set (Fin τ.rank → ℤ)}

theorem corootPair_self_simpleRoot {β : Fin τ.rank → ℤ} (hβ : β ∈ simpleRoots Ψ) :
    corootPair β β = 2 := by
  have hβr := simpleRoots_isRoot hβ
  have h := corootPair_mul hβr β
  have hp := iform_self_pos_of_isRoot hβr
  exact mul_right_cancel₀ hp.ne' (by rw [h])

theorem corootPair_ne_zero_iff {β γ : Fin τ.rank → ℤ} (hβ : β ∈ simpleRoots Ψ) :
    corootPair β γ ≠ 0 ↔ iform β γ ≠ 0 := by
  have hβr := simpleRoots_isRoot hβ
  have h := corootPair_mul hβr γ
  have hp := iform_self_pos_of_isRoot hβr
  constructor
  · intro h0 h1
    rw [h1, mul_zero] at h
    exact h0 ((mul_eq_zero.1 h).resolve_right hp.ne')
  · intro h0 h1
    rw [h1, zero_mul] at h
    omega

theorem posDef_iform_simpleRoots (hΨ : IsRootComponent Ψ) :
    (Matrix.of fun β γ : simpleRoots Ψ => iform (β : Fin τ.rank → ℤ) γ).PosDef := by
  classical
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · ext β γ
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    exact iform_comm _ _
  · set v : Fin τ.rank → ℤ := ∑ β : simpleRoots Ψ, x β • (β : Fin τ.rank → ℤ) with hv
    have hv0 : v ≠ 0 := by
      intro h0
      apply hx
      set c : (Fin τ.rank → ℤ) → ℤ := fun γ => if h : γ ∈ simpleRoots Ψ then x ⟨γ, h⟩ else 0
        with hc
      have hsum : ∑ γ ∈ simpleRoots Ψ, c γ • γ =
          ∑ γ ∈ simpleRoots Ψ, (0 : (Fin τ.rank → ℤ) → ℤ) γ • γ := by
        rw [← Finset.sum_coe_sort (simpleRoots Ψ)]
        simp only [hc, Finset.coe_mem, ↓reduceDIte, Pi.zero_apply, zero_smul,
          Finset.sum_const_zero]
        exact h0
      funext β
      have := coords_unique hΨ hsum β β.2
      simpa [hc] using this
    have hpos := iform_self_pos hv0
    have e : dotProduct (star x) (Matrix.mulVec
        (Matrix.of fun β γ : simpleRoots Ψ => iform (β : Fin τ.rank → ℤ) γ) x) = iform v v := by
      rw [hv, iform_finset_sum_left]
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, star_trivial, iform_smul_left,
        iform_finset_sum_right, iform_smul_right, Finset.mul_sum]
      refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun γ _ => ?_
      ring
    rw [e]
    exact hpos

end Helpers

theorem isFiniteType_simpleRoots_corootPair
    {τ : CFSG.Blueprint.Chevalley.Tag}
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : CFSG.LieType.Chevalley.IsRootComponent Ψ) :
    TauCeti.IsFiniteType (Matrix.of fun β γ : CFSG.LieType.Chevalley.simpleRoots Ψ =>
      CFSG.LieType.Chevalley.corootPair (β : Fin τ.rank → ℤ) (γ : Fin τ.rank → ℤ)) := by
  classical
  refine TauCeti.isFiniteType_of (fun β => ?_) (fun β γ hne => ?_)
    (d := fun β : simpleRoots Ψ => (iform (β : Fin τ.rank → ℤ) β : ℚ) / 2) (fun β => ?_) ?_
  · simp only [Matrix.of_apply]
    exact corootPair_self_simpleRoot β.2
  · simp only [Matrix.of_apply]
    have hβr := simpleRoots_isRoot β.2
    have h := corootPair_mul hβr (γ : Fin τ.rank → ℤ)
    have hp := iform_self_pos_of_isRoot hβr
    have hle := iform_simpleRoots_nonpos hΨ β.2 γ.2 (fun h => hne (Subtype.ext h))
    by_contra hc
    push Not at hc
    have : 0 < corootPair (β : Fin τ.rank → ℤ) γ * iform (β : Fin τ.rank → ℤ) β := mul_pos hc hp
    omega
  · have hp := iform_self_pos_of_isRoot (simpleRoots_isRoot β.2)
    have : (0 : ℚ) < iform (β : Fin τ.rank → ℤ) β := by exact_mod_cast hp
    positivity
  · have e : (Matrix.of fun β γ : simpleRoots Ψ =>
        (iform (β : Fin τ.rank → ℤ) β : ℚ) / 2 *
          ((Matrix.of fun β γ : simpleRoots Ψ =>
            corootPair (β : Fin τ.rank → ℤ) (γ : Fin τ.rank → ℤ)) β γ : ℚ)) =
        (Matrix.of fun β γ : simpleRoots Ψ => iform (β : Fin τ.rank → ℤ) γ).map
          (Int.cast : ℤ → ℚ) := by
      ext β γ
      simp only [Matrix.of_apply, Matrix.map_apply]
      have h := corootPair_mul (simpleRoots_isRoot β.2) (γ : Fin τ.rank → ℤ)
      have h' : ((corootPair (β : Fin τ.rank → ℤ) γ : ℤ) : ℚ) * (iform (β : Fin τ.rank → ℤ) β) =
          2 * (iform (β : Fin τ.rank → ℤ) γ : ℚ) := by exact_mod_cast h
      linear_combination h' / 2
    rw [e]
    exact TauCeti.Matrix.posDef_map_intCast (posDef_iform_simpleRoots hΨ)

theorem diagramGraph_simpleRoots_connected
    {τ : CFSG.Blueprint.Chevalley.Tag}
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : CFSG.LieType.Chevalley.IsRootComponent Ψ)
    (hne : Ψ.Nonempty) :
    (TauCeti.diagramGraph (Matrix.of fun β γ : CFSG.LieType.Chevalley.simpleRoots Ψ =>
      CFSG.LieType.Chevalley.corootPair (β : Fin τ.rank → ℤ) (γ : Fin τ.rank → ℤ))).Connected := by
  classical
  obtain ⟨α, hα⟩ := hne
  obtain ⟨-, -, β₀, hβ₀, -⟩ := exists_smul_simpleRoot hΨ hα
  have : Nonempty (simpleRoots Ψ) := ⟨⟨β₀, hβ₀⟩⟩
  refine ⟨fun β γ => ?_⟩
  suffices h : ∀ δ : Fin τ.rank → ℤ, Relation.ReflTransGen (SimpleAdj Ψ) (β : Fin τ.rank → ℤ) δ →
      ∀ hδ : δ ∈ simpleRoots Ψ, (TauCeti.diagramGraph (Matrix.of fun β γ : simpleRoots Ψ =>
        corootPair (β : Fin τ.rank → ℤ) (γ : Fin τ.rank → ℤ))).Reachable β ⟨δ, hδ⟩ from
    h γ (simpleRoots_connected hΨ β.2 γ.2) γ.2
  intro δ hrel
  induction hrel with
  | refl => exact fun _ => SimpleGraph.Reachable.refl _
  | @tail c d _ hstep ih =>
    intro hd
    obtain ⟨hc, -, hcd⟩ := hstep
    refine (ih hc).trans ?_
    by_cases hcd' : c = d
    · subst hcd'
      exact SimpleGraph.Reachable.refl _
    · refine SimpleGraph.Adj.reachable ?_
      rw [TauCeti.diagramGraph_adj]
      refine ⟨fun h => hcd' (congrArg Subtype.val h), ?_, ?_⟩
      · simp only [Matrix.of_apply]
        exact (corootPair_ne_zero_iff hc).2 hcd
      · simp only [Matrix.of_apply]
        exact (corootPair_ne_zero_iff hd).2 (by rwa [iform_comm])

end CFSG.HardMathSupport.Timmesfeld.Proving
