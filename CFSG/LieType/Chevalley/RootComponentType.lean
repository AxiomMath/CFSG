module

public import CFSG.LieType.Chevalley.CorootCoordinates
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcInnerD4Center

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint TauCeti

variable {τ : Tag}

theorem det_cartanMatrix_of_isSimplyLaced {t : DynkinType} (ht : t.Valid)
    (hs : t.IsSimplyLaced) :
    (t = .A t.rank ∧ t.cartanMatrix.det = t.rank + 1) ∨
      (t = .D t.rank ∧ 4 ≤ t.rank ∧ t.cartanMatrix.det = 4) ∨
      (t = .E6 ∧ t.cartanMatrix.det = 3) ∨ (t = .E7 ∧ t.cartanMatrix.det = 2) ∨
      (t = .E8 ∧ t.cartanMatrix.det = 1) := by
  cases t with
  | A n =>
    have h : (DynkinType.A n).cartanMatrix.det = (CartanMatrix.A n).det :=
      congrArg Matrix.det (DynkinType.cartanMatrix_A n)
    exact Or.inl ⟨rfl, by rw [h, CartanMatrix.A_det]; rfl⟩
  | B n => exact absurd hs (DynkinType.not_isSimplyLaced_B n)
  | C n => exact absurd hs (DynkinType.not_isSimplyLaced_C n)
  | D n =>
    have hn : 4 ≤ n := DynkinType.valid_D.1 ht
    have h : (DynkinType.D n).cartanMatrix.det = (CartanMatrix.D n).det :=
      congrArg Matrix.det (DynkinType.cartanMatrix_D n)
    exact Or.inr (Or.inl ⟨rfl, hn, by rw [h, CartanMatrix.D_det (by omega)]⟩)
  | E6 =>
    have h : DynkinType.E6.cartanMatrix.det = (CartanMatrix.E 6).det :=
      congrArg Matrix.det DynkinType.cartanMatrix_E6
    exact Or.inr (Or.inr (Or.inl ⟨rfl, by rw [h, CartanMatrix.E_det (by norm_num)]; norm_num⟩))
  | E7 =>
    have h : DynkinType.E7.cartanMatrix.det = (CartanMatrix.E 7).det :=
      congrArg Matrix.det DynkinType.cartanMatrix_E7
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by
      rw [h, CartanMatrix.E_det (by norm_num)]; norm_num⟩)))
  | E8 =>
    have h : DynkinType.E8.cartanMatrix.det = (CartanMatrix.E 8).det :=
      congrArg Matrix.det DynkinType.cartanMatrix_E8
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, by
      rw [h, CartanMatrix.E_det (by norm_num)]; norm_num⟩)))
  | F4 => exact absurd hs DynkinType.not_isSimplyLaced_F4
  | G2 => exact absurd hs DynkinType.not_isSimplyLaced_G2


theorem iform_simpleRoots_eq_zero_or_eq_neg_one (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) {β γ : Fin τ.rank → ℤ}
    (hβ : β ∈ simpleRoots Ψ) (hγ : γ ∈ simpleRoots Ψ) (hne : β ≠ γ) :
    iform β γ = 0 ∨ iform β γ = -1 := by
  have hle := iform_simpleRoots_nonpos hΨ hβ hγ hne
  have hnorm : ∀ {x : Fin τ.rank → ℤ}, IsRoot τ x → iform x x = 2 := fun hx => by
    rw [← dotProduct_mulVec_eq_iform]
    exact rootForm_self hτ hx
  have hsum : β + γ ≠ 0 := by
    intro h0
    have h1 := simpleRoots_height_pos hβ
    have h2 := simpleRoots_height_pos hγ
    have h3 := height_add β γ
    have h00 : height (0 : Fin τ.rank → ℤ) = 0 := by simp [height]
    rw [h0, h00] at h3
    omega
  have hpos := iform_self_pos hsum
  rw [iform_add_left, iform_add_right, iform_add_right, hnorm (simpleRoots_isRoot hβ),
    hnorm (simpleRoots_isRoot hγ), iform_comm γ β] at hpos
  omega

theorem exists_dynkinType (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) (hne : Ψ.Nonempty) :
    ∃ (t : DynkinType) (e : simpleRoots Ψ ≃ Fin t.rank), t.Valid ∧ t.IsSimplyLaced ∧
      (∀ β γ : simpleRoots Ψ, iform (β : Fin τ.rank → ℤ) γ = t.cartanMatrix (e β) (e γ)) ∧
      (simpleRoots Ψ).card = t.rank ∧ Ψ.ncard = t.numRoots := by
  classical
  obtain ⟨t, ⟨ht, e, he⟩, -⟩ := (CFSG.HardMathSupport.Timmesfeld.Proving.isFiniteType_simpleRoots_corootPair hΨ).existsUnique_dynkinType
      (CFSG.HardMathSupport.Timmesfeld.Proving.diagramGraph_simpleRoots_connected hΨ hne)
  have he' : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ =
      t.cartanMatrix (e β) (e γ) := fun β γ => by
    simpa only [Matrix.of_apply] using he β γ
  have hiform : ∀ β γ : simpleRoots Ψ, iform (β : Fin τ.rank → ℤ) γ =
      t.cartanMatrix (e β) (e γ) := fun β γ => by
    rw [← he' β γ, corootPair_eq_iform_of_simplyLaced hτ (simpleRoots_isRoot β.2)]
  have hsl : t.cartanMatrix.IsSimplyLaced := by
    intro i j hij
    have hne' : ((e.symm i : simpleRoots Ψ) : Fin τ.rank → ℤ) ≠ (e.symm j : simpleRoots Ψ) :=
      fun h => hij (e.symm.injective (Subtype.ext h))
    have h := iform_simpleRoots_eq_zero_or_eq_neg_one hτ hΨ (e.symm i).2 (e.symm j).2 hne'
    rw [hiform, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    exact h
  have hcard : (simpleRoots Ψ).card = t.rank := by
    rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_fin]
  refine ⟨t, e, ht, (DynkinType.isSimplyLaced_cartanMatrix_iff_of_valid ht).1 hsl, hiform, hcard,
    ?_⟩
  rw [CFSG.HardMathSupport.Timmesfeld.RootAut.ncard_eq_ncard_orbit hΨ e he',
    CFSG.LocalAnalysis.GLTheoremA.T171Sh.ncard_setOf_isOrbitRoot_cartanMatrix t ht]

end CFSG.LieType.Chevalley
