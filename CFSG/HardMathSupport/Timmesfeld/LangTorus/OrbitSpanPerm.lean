module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentPerm
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.Basic

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem rationalRoots_eq_iUnion {τ : Tag} {L : Type} [Field L]
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ)
    (i : KernelComponent χ) :
    rationalRoots ρ χ i = ⋃ k : ℕ, (ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots χ i := by
  ext γ
  simp only [rationalRoots, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨k, δ, hδ, rfl⟩
    exact ⟨k, δ, hδ, rfl⟩
  · rintro ⟨k, δ, hδ, rfl⟩
    exact ⟨k, δ, hδ, rfl⟩

theorem exists_map_conj_rootSpan_rationalRoots
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
    {a : Fin τ.rank → Lˣ} {y : ModGL τ L} (hy : y ∈ S.D.model)
    (hya : y * rootDiagUnit τ a * y⁻¹ = rootDiagUnit τ a)
    (i : KernelComponent (rootCharHom a)) :
    ∃ i' : KernelComponent (rootCharHom a),
      (rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i)).map (MulAut.conj y).toMonoidHom =
        rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i') := by
  have hyC : y ∈ toralCentralizer τ L a := by
    rw [toralCentralizer, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    refine ⟨(S.D.mem_model.1 hy).1, ?_⟩
    calc y * rootDiagUnit τ a = y * rootDiagUnit τ a * y⁻¹ * y := by group
      _ = rootDiagUnit τ a * y := by rw [hya]
  have hstep : S.D.step y = y := (S.D.mem_model.1 hy).2
  have hcomm : S.D.step.comp (MulAut.conj y).toMonoidHom =
      (MulAut.conj y).toMonoidHom.comp S.D.step := by
    ext x
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, map_mul, map_inv, hstep]
  obtain ⟨w, hw, m, hm, hym⟩ := exists_mul_canonicalRep_of_mem_toralCentralizer a hyC
  obtain ⟨i', hi'⟩ := exists_weyl_image_component a hw i
  refine ⟨i', ?_⟩
  have hroots : ∀ (j : KernelComponent (rootCharHom a)) (k : ℕ),
      ∀ γ ∈ (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) j, IsRoot τ γ := by
    intro j k
    induction k with
    | zero =>
      rintro γ ⟨δ, hδ, rfl⟩
      exact isRoot_of_mem_componentRoots hδ
    | succ k ih =>
      rintro γ ⟨δ, hδ, rfl⟩
      rw [Function.iterate_succ_apply']
      exact (S.frob.isRoot_iff _).2 (ih _ ⟨δ, hδ, rfl⟩)
  have hk : ∀ k : ℕ,
      (rootSpan τ L ((S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i)).map
          (MulAut.conj y).toMonoidHom =
        rootSpan τ L ((S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i') := by
    intro k
    induction k with
    | zero =>
      simp only [Function.iterate_zero, Set.image_id]
      rw [hym]
      exact map_conj_componentRootSpan a hw hm hi'
    | succ k ih =>
      have himg : ∀ j : KernelComponent (rootCharHom a),
          (S.ρ : (Fin τ.rank → ℤ) → _)^[k + 1] '' componentRoots (rootCharHom a) j =
            (S.ρ : (Fin τ.rank → ℤ) → _) ''
              ((S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) j) := by
        intro j
        rw [Function.iterate_succ', Set.image_comp]
      rw [himg, himg, ← map_rootSpan_step S _ (hroots i k), ← map_rootSpan_step S _ (hroots i' k),
        Subgroup.map_map, ← hcomm, ← Subgroup.map_map, ih]
  rw [rationalRoots_eq_iUnion, rationalRoots_eq_iUnion]
  simp only [rootSpan] at hk ⊢
  rw [iSup_iUnion, iSup_iUnion, Subgroup.map_iSup]
  exact iSup_congr hk

theorem not_disjoint_rationalRoots_of_rootSpan_eq
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    {i i' : KernelComponent (rootCharHom a)}
    (h : rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) =
      rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i')) :
    ¬ Disjoint (rationalRoots S.ρ (rootCharHom a) i) (rationalRoots S.ρ (rootCharHom a) i') := by
  intro hdis
  obtain ⟨b, hb⟩ := Quotient.exists_rep i
  have hγ : (b : Fin τ.rank → ℤ) ∈ componentRoots (rootCharHom a) i := ⟨b.2, hb⟩
  have hneg : -(b : Fin τ.rank → ℤ) ∈ componentRoots (rootCharHom a) i :=
    (isRootComponent_componentRoots i).neg_mem _ hγ
  have hmem : ∀ {γ}, γ ∈ componentRoots (rootCharHom a) i →
      γ ∈ rationalRoots S.ρ (rootCharHom a) i := fun {γ} hγ => ⟨0, γ, hγ, rfl⟩
  obtain ⟨c, d, hcd⟩ :=
    CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.TwBasicAux.exists_not_commute_pinnedX_neg
      (K := L)
      (isRoot_of_mem_componentRoots hγ)
  have hcent : rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i') ≤
      Subgroup.centralizer (rootSpan τ L (componentRoots (rootCharHom a) i) : Set (ModGL τ L)) := by
    refine iSup₂_le fun γ hγ' => ?_
    obtain ⟨k, δ, hδ, rfl⟩ := hγ'
    obtain ⟨j, hj⟩ := outer_iterate_image_component S hT i' k
    have hδj : (S.ρ : (Fin τ.rank → ℤ) → _)^[k] δ ∈ componentRoots (rootCharHom a) j := by
      rw [hj]
      exact ⟨δ, hδ, rfl⟩
    have hji : j ≠ i := by
      rintro rfl
      have hbk : (b : Fin τ.rank → ℤ) ∈
          (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i' := by
        rw [← hj]
        exact hγ
      obtain ⟨δ', hδ', he⟩ := hbk
      exact Set.disjoint_left.1 hdis (hmem hγ) ⟨k, δ', hδ', he.symm⟩
    exact (le_iSup₂ (f := fun α (_ : α ∈ componentRoots (rootCharHom a) j) => rootSubgroup τ L α)
      _ hδj).trans (componentRootSpan_le_centralizer L hji)
  have hx : pinnedX τ L (b : Fin τ.rank → ℤ) c ∈ rootSpan τ L (componentRoots (rootCharHom a) i) :=
    CFSG.LieType.Chevalley.pinnedX_mem_rootSpan hγ c
  have hy : pinnedX τ L (-(b : Fin τ.rank → ℤ)) d ∈
      rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i') := by
    rw [← h]
    exact CFSG.LieType.Chevalley.pinnedX_mem_rootSpan (hmem hneg) d
  exact hcd (Subgroup.mem_centralizer_iff.1 (hcent hy) _ hx)

end CFSG.HardMathSupport.Timmesfeld.LangTorus
