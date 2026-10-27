module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoFixedCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingSymmetric

public section

namespace CFSG.ComponentClassification.CatalogueBLinearTwoInvolution

noncomputable section

open CFSG.GorensteinWalter CatalogueSchreierLinearTwo

universe u

abbrev fixedGroup (K : Type u) [Field K] (a : Equiv.Perm (Omega K)) :=
  (Subgroup.centralizer ({a} : Set (Equiv.Perm (Omega K)))).subgroupOf (coordinateG K)

@[expose] def intersectionEquivRestriction {G : Type*} [Group G]
    (N H : Subgroup G) : ↥(N ⊓ H) ≃* H.subgroupOf N where
  toFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  invFun x := ⟨x.val.val, x.val.property, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[expose] def normalizerFixedEquiv {G : Type*} [Group G]
    (N : Subgroup G) (h : G) (hnormal : h ∈ Subgroup.normalizer (N : Set G))
    (a : G) :
    (Subgroup.centralizer ({a} : Set G)).subgroupOf N ≃*
      (Subgroup.centralizer ({h * a * h⁻¹} : Set G)).subgroupOf N := by
  let e : MulAut N := N.normalizerMonoidHom ⟨h, hnormal⟩
  have he (x : N) : (e x : G) = h * (x : G) * h⁻¹ :=
    Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
  have heback (x : N) : (e.symm x : G) = h⁻¹ * (x : G) * h := by
    have hx := he (e.symm x)
    rw [e.apply_symm_apply] at hx
    calc
      (e.symm x : G) = h⁻¹ * (h * (e.symm x : G) * h⁻¹) * h := by group
      _ = h⁻¹ * (x : G) * h := by rw [← hx]
  refine
    { toFun := fun x => ⟨e x.val, ?_⟩
      invFun := fun x => ⟨e.symm x.val, ?_⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
      right_inv := fun x => Subtype.ext (e.apply_symm_apply x.val)
      map_mul' := fun x y => Subtype.ext (map_mul e x.val y.val) }
  · apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hx := Subgroup.mem_centralizer_singleton_iff.mp x.property
    change (x.val : G) * a = a * (x.val : G) at hx
    change (e x.val : G) * (h * a * h⁻¹) = (h * a * h⁻¹) * (e x.val : G)
    rw [he]
    have hc := congrArg (MulAut.conj h) hx
    simpa only [map_mul, MulAut.conj_apply] using hc
  · apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hx := Subgroup.mem_centralizer_singleton_iff.mp x.property
    change (x.val : G) * (h * a * h⁻¹) = (h * a * h⁻¹) * (x.val : G) at hx
    change (e.symm x.val : G) * a = a * (e.symm x.val : G)
    rw [heback]
    have hc := congrArg (MulAut.conj h⁻¹) hx
    simp only [map_mul, MulAut.conj_apply] at hc
    convert hc using 1 <;> group

theorem normalizerFixedEquiv_coe {G : Type*} [Group G]
    (N : Subgroup G) (h : G) (hnormal : h ∈ Subgroup.normalizer (N : Set G))
    (a : G) (x : (Subgroup.centralizer ({a} : Set G)).subgroupOf N) :
    ((normalizerFixedEquiv N h hnormal a x).val : G) = h * (x.val : G) * h⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _

@[expose] def subfieldFixedEquiv (K : Type u) [Field K] [Finite K]
    (hodd : ringChar K ≠ 2) (sigma : K ≃+* K) (hsigma : orderOf sigma = 2) :
    coordinateD (CatalogueBLinearTwoFixed.fixedField K sigma) ≃*
      fixedGroup K (fieldExtension K sigma) :=
  (CatalogueBLinearTwoFixed.subfieldCoordinateEquivGCentralizer K hodd sigma hsigma).trans
    (intersectionEquivRestriction (coordinateG K)
      (Subgroup.centralizer {fieldExtension K sigma}))

theorem subfieldFixedEquiv_coe (K : Type u) [Field K] [Finite K]
    (hodd : ringChar K ≠ 2) (sigma : K ≃+* K) (hsigma : orderOf sigma = 2)
    (g : coordinateD (CatalogueBLinearTwoFixed.fixedField K sigma)) :
    ((subfieldFixedEquiv K hodd sigma hsigma g).val : Equiv.Perm (Omega K)) =
      (CatalogueBLinearTwoFixed.subfieldCoordinateMap K
        (CatalogueBLinearTwoFixed.fixedField K sigma) g : Equiv.Perm (Omega K)) := rfl

theorem coordinateD_three_solvable (K : Type u) [Field K] [Finite K]
    (hcard : Nat.card K = 3) : Group.IsSolvable (coordinateD K) := by
  let : Group.IsSolvable (Equiv.Perm (Omega K)) := Equiv.Perm.isSolvable (by
    change Nat.card (Option K) ≤ 4
    let : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Fintype.card_option, ← Nat.card_eq_fintype_card, hcard])
  infer_instance

theorem no_pComponent_of_solvable {G : Type*} [Group G] [Group.IsSolvable G]
    (p : ℕ) (L : Subgroup G) : ¬ CFSG.IsPComponent p L := by
  intro hL
  let : Group.IsPerfect L := CatalogueBAlternating.pComponent_perfect hL
  let : Nontrivial L := CatalogueBAlternating.pComponent_nontrivial hL
  exact Group.IsPerfect.not_isSolvable L inferInstance

end

end CFSG.ComponentClassification.CatalogueBLinearTwoInvolution
