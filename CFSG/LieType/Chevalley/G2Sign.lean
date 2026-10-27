module

public import CFSG.LieType.Chevalley.G2Rank

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {K : Type} [Field K]

theorem torusElement_conj_rootHom
    {τ : Tag} (i : Fin τ.rank) (t : Kˣ) (β : Root τ)
    (c : Multiplicative K) :
    torusElement τ K i t * rootHom β c * (torusElement τ K i t)⁻¹ =
      rootHom β (Multiplicative.ofAdd
        (((t ^ (∑ j, τ.cartan i j * β.1 j) : Kˣ) : K) * Multiplicative.toAdd c)) :=
  (rootOperatorFamily τ).torusElement_mul_eltElement_mul_inv i t β (Multiplicative.toAdd c)

theorem pairing_g2 :
    (∑ j, Tag.G2.cartan (0 : Fin 2) j * g2r12.1 j = 0 ∧
      ∑ j, Tag.G2.cartan (0 : Fin 2) j * g2r13.1 j = -1 ∧
      ∑ j, Tag.G2.cartan (0 : Fin 2) j * g2r23.1 j = 1) ∧
    (∑ j, Tag.G2.cartan (1 : Fin 2) j * g2r12.1 j = 1 ∧
      ∑ j, Tag.G2.cartan (1 : Fin 2) j * g2r13.1 j = 3 ∧
      ∑ j, Tag.G2.cartan (1 : Fin 2) j * g2r23.1 j = 0) := by
  have e12 : g2r12.1 = g2Vec [0, 1] 1 := val_inv_smul_simpleRoot _ _
  have e13 : g2r13.1 = g2Vec [1] 0 := val_inv_smul_simpleRoot _ _
  have e23 : g2r23.1 = g2Vec [1, 0, 1] 0 := val_inv_smul_simpleRoot _ _
  rw [e12, e13, e23]
  decide +kernel

variable {p : ℕ}

@[expose] def g2Coord (ι : ZMod p ≃+ K) :
    Multiplicative (Fin 3 → ZMod p) →*
      Multiplicative K × (Multiplicative K × Multiplicative K) where
  toFun v := (Multiplicative.ofAdd (ι (Multiplicative.toAdd v 1)),
    Multiplicative.ofAdd (ι (Multiplicative.toAdd v 0)),
    Multiplicative.ofAdd (ι (Multiplicative.toAdd v 2)))
  map_one' := by
    simp only [toAdd_one, Pi.zero_apply, map_zero, ofAdd_zero, Prod.mk_eq_one, and_self]
  map_mul' v w := by
    simp only [toAdd_mul, Pi.add_apply, map_add, ofAdd_add, Prod.mk_mul_mk]

theorem g2Coord_injective (ι : ZMod p ≃+ K) : Function.Injective (g2Coord ι) := fun v w h => by
  simp only [g2Coord, MonoidHom.coe_mk, OneHom.coe_mk, Prod.mk.injEq] at h
  obtain ⟨h1, h0, h2⟩ := h
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · exact ι.injective (Multiplicative.ofAdd.injective h0)
  · exact ι.injective (Multiplicative.ofAdd.injective h1)
  · exact ι.injective (Multiplicative.ofAdd.injective h2)

@[expose] noncomputable def g2Param
    (ι : ZMod p ≃+ K) :
    Multiplicative (Fin 3 → ZMod p) →* adjointGroup .G2 K :=
  g2RootProd.comp (g2Coord ι)

theorem g2Param_apply
    (ι : ZMod p ≃+ K) (v : Multiplicative (Fin 3 → ZMod p)) :
    g2Param ι v = rootHom g2r13 (Multiplicative.ofAdd (ι (Multiplicative.toAdd v 1))) *
      (rootHom g2r12 (Multiplicative.ofAdd (ι (Multiplicative.toAdd v 0))) *
        rootHom g2r23 (Multiplicative.ofAdd (ι (Multiplicative.toAdd v 2)))) := rfl

theorem g2Param_injective
    [Finite K] (ι : ZMod p ≃+ K) : Function.Injective (g2Param ι) :=
  g2RootProd_injective.comp (g2Coord_injective ι)

theorem neg_one_zpow_mul_odd (ι : ZMod p ≃+ K) {k : ℤ} (hk : Odd k) (a : ZMod p) :
    (((-1 : Kˣ) ^ k : Kˣ) : K) * ι a = ι (-1 * a) := by
  rw [hk.neg_one_zpow, Units.val_neg, Units.val_one, neg_one_mul, neg_one_mul, map_neg]

theorem neg_one_zpow_mul_even (ι : ZMod p ≃+ K) {k : ℤ} (hk : Even k) (a : ZMod p) :
    (((-1 : Kˣ) ^ k : Kˣ) : K) * ι a = ι (1 * a) := by
  rw [hk.neg_one_zpow, Units.val_one, one_mul, one_mul]

theorem conj_mul_mul {G : Type*} [Group G] (d a b c : G) :
    d * (a * (b * c)) * d⁻¹ = (d * a * d⁻¹) * ((d * b * d⁻¹) * (d * c * d⁻¹)) := by
  group

theorem torusElement_conj_g2Param_zero
    (ι : ZMod p ≃+ K) (v : Multiplicative (Fin 3 → ZMod p)) :
    torusElement .G2 K (0 : Fin 2) (-1) * g2Param ι v * (torusElement .G2 K (0 : Fin 2) (-1))⁻¹ =
      g2Param ι (Multiplicative.ofAdd (![1, -1, -1] * Multiplicative.toAdd v)) := by
  obtain ⟨⟨h12, h13, h23⟩, -⟩ := pairing_g2
  have c13 := torusElement_conj_rootHom (K := K) (τ := .G2) (0 : Fin 2) (-1) g2r13
    (Multiplicative.ofAdd (ι (Multiplicative.toAdd v 1)))
  have c12 := torusElement_conj_rootHom (K := K) (τ := .G2) (0 : Fin 2) (-1) g2r12
    (Multiplicative.ofAdd (ι (Multiplicative.toAdd v 0)))
  have c23 := torusElement_conj_rootHom (K := K) (τ := .G2) (0 : Fin 2) (-1) g2r23
    (Multiplicative.ofAdd (ι (Multiplicative.toAdd v 2)))
  rw [h13] at c13
  rw [h12] at c12
  rw [h23] at c23
  rw [toAdd_ofAdd, neg_one_zpow_mul_odd ι (by decide)] at c13 c23
  rw [toAdd_ofAdd, neg_one_zpow_mul_even ι (by decide)] at c12
  rw [g2Param_apply, g2Param_apply, conj_mul_mul, c13, c12, c23]
  rfl

theorem torusElement_conj_g2Param_one
    (ι : ZMod p ≃+ K) (v : Multiplicative (Fin 3 → ZMod p)) :
    torusElement .G2 K (1 : Fin 2) (-1) * g2Param ι v * (torusElement .G2 K (1 : Fin 2) (-1))⁻¹ =
      g2Param ι (Multiplicative.ofAdd (![-1, -1, 1] * Multiplicative.toAdd v)) := by
  obtain ⟨-, ⟨h12, h13, h23⟩⟩ := pairing_g2
  have c13 := torusElement_conj_rootHom (K := K) (τ := .G2) (1 : Fin 2) (-1) g2r13
    (Multiplicative.ofAdd (ι (Multiplicative.toAdd v 1)))
  have c12 := torusElement_conj_rootHom (K := K) (τ := .G2) (1 : Fin 2) (-1) g2r12
    (Multiplicative.ofAdd (ι (Multiplicative.toAdd v 0)))
  have c23 := torusElement_conj_rootHom (K := K) (τ := .G2) (1 : Fin 2) (-1) g2r23
    (Multiplicative.ofAdd (ι (Multiplicative.toAdd v 2)))
  rw [h13] at c13
  rw [h12] at c12
  rw [h23] at c23
  rw [toAdd_ofAdd, neg_one_zpow_mul_odd ι (by decide)] at c13 c12
  rw [toAdd_ofAdd, neg_one_zpow_mul_even ι (by decide)] at c23
  rw [g2Param_apply, g2Param_apply, conj_mul_mul, c13, c12, c23]
  rfl

end CFSG.LieType.Chevalley
