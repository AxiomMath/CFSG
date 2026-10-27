module

public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent

public section

namespace CFSG.ClassicalGroups.Orthogonal

open CFSG.RankThree.Classical2 (orthDerived)
open QuadraticMap

variable {F F' : Type} [Field F] [Field F']
  {W W' : Type} [AddCommGroup W] [Module F W]
  [AddCommGroup W'] [Module F' W']

private theorem eq_zero_or_eq_one_of_natCard_eq_two (hF : Nat.card F = 2) (c : F) :
    c = 0 ∨ c = 1 := by
  classical
  have hFin : Finite F := Nat.finite_of_card_ne_zero (by omega)
  letI : Fintype F := Fintype.ofFinite F
  have hc : ({0, 1} : Finset F).card = Fintype.card F := by
    rw [Finset.card_pair zero_ne_one, ← Nat.card_eq_fintype_card, hF]
  have h := Finset.eq_univ_of_card _ hc
  have hr : c ∈ ({0, 1} : Finset F) := h ▸ Finset.mem_univ c
  simpa using hr

private theorem eq_iff_eq_zero_iff_of_natCard_eq_two (hF : Nat.card F = 2)
    {a b : F} : a = b ↔ (a = 0 ↔ b = 0) := by
  constructor
  · intro h
    rw [h]
  · intro h
    rcases eq_zero_or_eq_one_of_natCard_eq_two hF a with ha | ha <;>
      rcases eq_zero_or_eq_one_of_natCard_eq_two hF b with hb | hb <;>
      simp_all

private noncomputable def addConj {A B : Type} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (g : A ≃+ A) : B ≃+ B :=
  e.symm.trans (g.trans e)

private noncomputable def conjMulEquiv (hF : Nat.card F = 2) (hF' : Nat.card F' = 2)
    (κ : W ≃+ W') : (W ≃ₗ[F] W) ≃* (W' ≃ₗ[F'] W') where
  toFun g := (addConj κ g.toAddEquiv).toLinearEquiv (fun c x => by
    rcases eq_zero_or_eq_one_of_natCard_eq_two hF' c with rfl | rfl <;> simp)
  invFun g' := (addConj κ.symm g'.toAddEquiv).toLinearEquiv (fun c x => by
    rcases eq_zero_or_eq_one_of_natCard_eq_two hF c with rfl | rfl <;> simp)
  left_inv g := by
    ext x
    simp [addConj, AddEquiv.trans_apply]
  right_inv g' := by
    ext x
    simp [addConj, AddEquiv.trans_apply]
  map_mul' g h := by
    ext x
    simp [addConj, AddEquiv.trans_apply]

private theorem conjMulEquiv_apply (hF : Nat.card F = 2) (hF' : Nat.card F' = 2)
    (κ : W ≃+ W') (g : W ≃ₗ[F] W) (w : W) :
    (conjMulEquiv hF hF' κ g) (κ w) = κ (g w) := by
  simp [conjMulEquiv, addConj, AddEquiv.trans_apply]

private theorem map_orthogonalGroup_addConj (hF : Nat.card F = 2) (hF' : Nat.card F' = 2)
    (Q : QuadraticForm F W) (Q' : QuadraticForm F' W') (κ : W ≃+ W')
    (hκ : ∀ w, Q' (κ w) = 0 ↔ Q w = 0) :
    (TauCeti.QuadraticMap.orthogonalGroup Q).map
        (conjMulEquiv hF hF' κ).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Q' := by
  ext g'
  rw [Subgroup.mem_map, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩ v
    obtain ⟨w, rfl⟩ := κ.surjective v
    have h_app : ((conjMulEquiv hF hF' κ).toMonoidHom g) (κ w) = κ (g w) := by
      simpa only [MulEquiv.coe_toMonoidHom] using conjMulEquiv_apply hF hF' κ g w
    rw [h_app]
    rw [eq_iff_eq_zero_iff_of_natCard_eq_two hF']
    rw [hκ (g w), hκ w, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg w]
  · intro hg'
    refine ⟨(conjMulEquiv hF hF' κ).symm g', ?_,
      by simpa only [MulEquiv.coe_toMonoidHom] using
        MulEquiv.apply_symm_apply (conjMulEquiv hF hF' κ) g'⟩
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro w
    have h_app : ((conjMulEquiv hF hF' κ).symm g') w = κ.symm (g' (κ w)) := by
      simp [conjMulEquiv, addConj, AddEquiv.trans_apply]
    rw [h_app, eq_iff_eq_zero_iff_of_natCard_eq_two hF]
    rw [← hκ (κ.symm (g' (κ w))), AddEquiv.apply_symm_apply,
      hg' (κ w), hκ w]

private theorem map_orthDerived_addConj (hF : Nat.card F = 2) (hF' : Nat.card F' = 2)
    (Q : QuadraticForm F W) (Q' : QuadraticForm F' W') (κ : W ≃+ W')
    (hκ : ∀ w, Q' (κ w) = 0 ↔ Q w = 0) :
    (orthDerived Q).map (conjMulEquiv hF hF' κ).toMonoidHom = orthDerived Q' := by
  rw [orthDerived, orthDerived, Subgroup.map_commutator,
    map_orthogonalGroup_addConj hF hF' Q Q' κ hκ]

private noncomputable def orthDerivedEquivOfAddEquiv (hF : Nat.card F = 2) (hF' : Nat.card F' = 2)
    (Q : QuadraticForm F W) (Q' : QuadraticForm F' W') (κ : W ≃+ W')
    (hκ : ∀ w, Q' (κ w) = 0 ↔ Q w = 0) :
    ↥(orthDerived Q) ≃* ↥(orthDerived Q') :=
  ((conjMulEquiv hF hF' κ).subgroupMap (orthDerived Q)).trans
    (MulEquiv.subgroupCongr (map_orthDerived_addConj hF hF' Q Q' κ hκ))

theorem exists_mulEquiv_orthDerived_of_addEquiv {F F' : Type} [Field F] [Field F']
    (hF : Nat.card F = 2) (hF' : Nat.card F' = 2) {W W' : Type} [AddCommGroup W] [Module F W]
    [AddCommGroup W'] [Module F' W'] (Q : QuadraticForm F W) (Q' : QuadraticForm F' W')
    (κ : W ≃+ W') (hκ : ∀ w, Q' (κ w) = 0 ↔ Q w = 0) :
    ∃ Θ : ↥(orthDerived Q) ≃* ↥(orthDerived Q'),
      ∀ (y : ↥(orthDerived Q)) (w : W),
        (Θ y : W' ≃ₗ[F'] W') (κ w) = κ ((y : W ≃ₗ[F] W) w) := by
  refine ⟨orthDerivedEquivOfAddEquiv hF hF' Q Q' κ hκ, ?_⟩
  intro y w
  change (conjMulEquiv hF hF' κ (y : W ≃ₗ[F] W)) (κ w) =
    κ ((y : W ≃ₗ[F] W) w)
  exact conjMulEquiv_apply hF hF' κ (y : W ≃ₗ[F] W) w

end CFSG.ClassicalGroups.Orthogonal
