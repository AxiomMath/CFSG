module

public import CFSG.CharacterTheory.Wreathed.FullSylowCoveringObstruction
public import CFSG.CharacterTheory.Wreathed.SimpleOddIndexQuotient
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare

public noncomputable section

namespace CFSG.Wreathed.SameFieldOddKernel

open FullSylowCoveringObstruction SimpleOddIndexQuotient WreathCentralSquare

universe u
variable {G : Type u} [Group G] [Finite G]

@[expose] def quotientSylow (S : Sylow 2 G) (K : Subgroup G)
    (hSK : (S : Subgroup G) ≤ K) (O : Subgroup K) [O.Normal] : Sylow 2 (K ⧸ O) :=
  (subgroupSylow S K hSK).mapSurjective (QuotientGroup.mk'_surjective O)

theorem quotientSylow_coe (S : Sylow 2 G) (K : Subgroup G)
    (hSK : (S : Subgroup G) ≤ K) (O : Subgroup K) [O.Normal] :
    (quotientSylow S K hSK O : Subgroup (K ⧸ O)) =
      ((S : Subgroup G).subgroupOf K).map (QuotientGroup.mk' O) := rfl

@[expose] def quotientSylowEquiv (S : Sylow 2 G) (K : Subgroup G)
    (hSK : (S : Subgroup G) ≤ K) (O : Subgroup K) [O.Normal]
    (hO : Odd (Nat.card O)) : S ≃* quotientSylow S K hSK O :=
  (Subgroup.subgroupOfEquivOfLe hSK).symm.trans
    (oddQuotientSylowEquiv O hO (subgroupSylow S K hSK))

theorem quotientSylowEquiv_apply (S : Sylow 2 G) (K : Subgroup G)
    (hSK : (S : Subgroup G) ≤ K) (O : Subgroup K) [O.Normal]
    (hO : Odd (Nat.card O)) (s : S) :
    (quotientSylowEquiv S K hSK O hO s : K ⧸ O) =
      QuotientGroup.mk' O (⟨(s : G), hSK s.property⟩ : K) := by
  exact oddQuotientSylowEquiv_apply O hO (subgroupSylow S K hSK)
    ((Subgroup.subgroupOfEquivOfLe hSK).symm s)

@[expose] def quotientCoordinates {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) (O : Subgroup K) [O.Normal]
    (hO : Odd (Nat.card O)) : quotientSylow S K hSK O ≃* Wreath m :=
  (quotientSylowEquiv S K hSK O hO).symm.trans e

theorem quotientModelHom_apply {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) (O : Subgroup K) [O.Normal]
    (hO : Odd (Nat.card O)) (w : Wreath m) :
    wreathModelHom (quotientSylow S K hSK O) (quotientCoordinates S e K hSK O hO) w =
      QuotientGroup.mk' O (wreathModelHom (subgroupSylow S K hSK)
        (subgroupCoordinates S e K hSK) w) := by
  exact quotientSylowEquiv_apply S K hSK O hO (e.symm w)

theorem quotientSylow_le_normal_odd_index (S : Sylow 2 G) (K : Subgroup G)
    (hSK : (S : Subgroup G) ≤ K) (O : Subgroup K) [O.Normal]
    (L : Subgroup (K ⧸ O)) [L.Normal] (hindex : Odd L.index) :
    (quotientSylow S K hSK O : Subgroup (K ⧸ O)) ≤ L :=
  Sylow_le_normal_of_odd_index L hindex (quotientSylow S K hSK O)

@[expose] def layerSylow (S : Sylow 2 G) (K : Subgroup G)
    (hSK : (S : Subgroup G) ≤ K) (O : Subgroup K) [O.Normal]
    (L : Subgroup (K ⧸ O)) [L.Normal] (hindex : Odd L.index) : Sylow 2 L :=
  subgroupSylow (quotientSylow S K hSK O) L
    (quotientSylow_le_normal_odd_index S K hSK O L hindex)

@[expose] def layerCoordinates {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) (O : Subgroup K) [O.Normal]
    (hO : Odd (Nat.card O)) (L : Subgroup (K ⧸ O)) [L.Normal] (hindex : Odd L.index) :
    layerSylow S K hSK O L hindex ≃* Wreath m :=
  subgroupCoordinates (quotientSylow S K hSK O) (quotientCoordinates S e K hSK O hO) L
    (quotientSylow_le_normal_odd_index S K hSK O L hindex)

theorem layerModelHom_apply {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) (O : Subgroup K) [O.Normal]
    (hO : Odd (Nat.card O)) (L : Subgroup (K ⧸ O)) [L.Normal] (hindex : Odd L.index)
    (w : Wreath m) :
    (wreathModelHom (layerSylow S K hSK O L hindex)
      (layerCoordinates S e K hSK O hO L hindex) w : K ⧸ O) =
      QuotientGroup.mk' O (wreathModelHom (subgroupSylow S K hSK)
        (subgroupCoordinates S e K hSK) w) := by
  have h := congrArg (fun f : Wreath m →* K ⧸ O => f w)
    (subgroupModelHom_comp (quotientSylow S K hSK O)
      (quotientCoordinates S e K hSK O hO) L
      (quotientSylow_le_normal_odd_index S K hSK O L hindex))
  exact h.trans (quotientModelHom_apply S e K hSK O hO w)

theorem quotientSylow_restriction_injective (S : Sylow 2 G) (K : Subgroup G)
    (hSK : (S : Subgroup G) ≤ K) (O : Subgroup K) [O.Normal]
    (hO : Odd (Nat.card O)) :
    Function.Injective (fun s : S =>
      QuotientGroup.mk' O (⟨(s : G), hSK s.property⟩ : K)) := by
  intro s t h
  apply (quotientSylowEquiv S K hSK O hO).injective
  apply Subtype.ext
  simpa only [quotientSylowEquiv_apply] using h

theorem quotientModelHom_orderOf {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) (O : Subgroup K) [O.Normal]
    (hO : Odd (Nat.card O)) (w : Wreath m) :
    orderOf (wreathModelHom (quotientSylow S K hSK O)
      (quotientCoordinates S e K hSK O hO) w) = orderOf (wreathModelHom S e w) := by
  rw [orderOf_injective _ (wreathModelHom_injective _ _),
    orderOf_injective _ (wreathModelHom_injective _ _)]

theorem layerModelHom_orderOf {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) (O : Subgroup K) [O.Normal]
    (hO : Odd (Nat.card O)) (L : Subgroup (K ⧸ O)) [L.Normal] (hindex : Odd L.index)
    (w : Wreath m) :
    orderOf (wreathModelHom (layerSylow S K hSK O L hindex)
      (layerCoordinates S e K hSK O hO L hindex) w) = orderOf (wreathModelHom S e w) := by
  rw [orderOf_injective _ (wreathModelHom_injective _ _),
    orderOf_injective _ (wreathModelHom_injective _ _)]

@[expose] def layerSylowEquiv (S : Sylow 2 G) (K : Subgroup G)
    (hSK : (S : Subgroup G) ≤ K) (O : Subgroup K) [O.Normal]
    (hO : Odd (Nat.card O)) (L : Subgroup (K ⧸ O)) [L.Normal] (hindex : Odd L.index) :
    S ≃* layerSylow S K hSK O L hindex :=
  (quotientSylowEquiv S K hSK O hO).trans
    (Subgroup.subgroupOfEquivOfLe
      (quotientSylow_le_normal_odd_index S K hSK O L hindex)).symm

theorem layerSylowEquiv_apply (S : Sylow 2 G) (K : Subgroup G)
    (hSK : (S : Subgroup G) ≤ K) (O : Subgroup K) [O.Normal]
    (hO : Odd (Nat.card O)) (L : Subgroup (K ⧸ O)) [L.Normal] (hindex : Odd L.index)
    (s : S) :
    ((layerSylowEquiv S K hSK O hO L hindex s : L) : K ⧸ O) =
      QuotientGroup.mk' O (⟨(s : G), hSK s.property⟩ : K) :=
  quotientSylowEquiv_apply S K hSK O hO s

omit [Finite G] in
theorem coveringRoot_coe {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) :
    ((actualRoot (subgroupSylow S K hSK) (subgroupCoordinates S e K hSK) : K) : G) =
      actualRoot S e := rfl

theorem layerRoot_coe {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) (O : Subgroup K) [O.Normal]
    (hO : Odd (Nat.card O)) (L : Subgroup (K ⧸ O)) [L.Normal] (hindex : Odd L.index) :
    ((actualRoot (layerSylow S K hSK O L hindex)
      (layerCoordinates S e K hSK O hO L hindex) : L) : K ⧸ O) =
      QuotientGroup.mk' O
        (actualRoot (subgroupSylow S K hSK) (subgroupCoordinates S e K hSK)) :=
  layerModelHom_apply S e K hSK O hO L hindex (originalRoot m)

theorem layerInvolution_coe (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) (O : Subgroup K) [O.Normal]
    (hO : Odd (Nat.card O)) (L : Subgroup (K ⧸ O)) [L.Normal] (hindex : Odd L.index) :
    (wreathModelHom (layerSylow S K hSK O L hindex)
      (layerCoordinates S e K hSK O hO L hindex) (Original.x (2 ^ n)) : K ⧸ O) =
      QuotientGroup.mk' O (coveringInvolution n S e K hSK) :=
  layerModelHom_apply S e K hSK O hO L hindex (Original.x (2 ^ n))

omit [Finite G] in
theorem coveringRoot_order (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) :
    orderOf (actualRoot (subgroupSylow S K hSK) (subgroupCoordinates S e K hSK)) =
      2 ^ (n + 1) := by
  rw [actualRoot_orderOf n hn, pow_succ, Nat.mul_comm]

theorem layerRoot_order (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) (O : Subgroup K) [O.Normal]
    (hO : Odd (Nat.card O)) (L : Subgroup (K ⧸ O)) [L.Normal] (hindex : Odd L.index) :
    orderOf (actualRoot (layerSylow S K hSK O L hindex)
      (layerCoordinates S e K hSK O hO L hindex)) = 2 ^ (n + 1) := by
  rw [actualRoot_orderOf n hn, pow_succ, Nat.mul_comm]

theorem layerInvolution_order (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) (O : Subgroup K) [O.Normal]
    (hO : Odd (Nat.card O)) (L : Subgroup (K ⧸ O)) [L.Normal] (hindex : Odd L.index) :
    orderOf (wreathModelHom (layerSylow S K hSK O L hindex)
      (layerCoordinates S e K hSK O hO L hindex) (Original.x (2 ^ n))) = 2 := by
  rw [orderOf_injective _ (wreathModelHom_injective _ _)]
  exact (wreath_center_involution_and_quaternion_coordinates n hn).involution_orders.1

end CFSG.Wreathed.SameFieldOddKernel
