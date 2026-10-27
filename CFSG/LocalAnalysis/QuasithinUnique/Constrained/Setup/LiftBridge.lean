module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open scoped commutatorElement

theorem preimage_center_eq_center {G H : Type*} [Group G] [Group H] (hP : Group.IsPerfect G)
    (φ : G →* H) (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G) :
    (Subgroup.center H).comap φ = Subgroup.center G := by
  apply le_antisymm
  · intro x hx
    have hx' : ∀ h : H, h * φ x = φ x * h := fun h => (Subgroup.mem_center_iff.mp hx h)
    have hc : ∀ l : G, ⁅x, l⁆ ∈ Subgroup.center G := by
      intro l
      apply hker
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr (hx' (φ l)).symm
    let f : G →* Subgroup.center G :=
      { toFun := fun l => ⟨⁅x, l⁆, hc l⟩
        map_one' := by ext; simp
        map_mul' := by
          intro a b
          ext
          simp only [Subgroup.coe_mul]
          rw [commutatorElement_mul_right_eq_mul_conj]
          have h2 : a * ⁅x, b⁆ * a⁻¹ = ⁅x, b⁆ := by
            rw [mul_inv_eq_iff_eq_mul]
            exact (Subgroup.mem_center_iff.mp (hc b) a)
          calc ⁅x, a⁆ * a * ⁅x, b⁆ * a⁻¹ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by group
            _ = ⁅x, a⁆ * ⁅x, b⁆ := by rw [h2] }
    have hf : commutator G ≤ f.ker := Abelianization.commutator_subset_ker f
    rw [Group.isPerfect_def.mp hP] at hf
    rw [Subgroup.mem_center_iff]
    intro l
    have h3 := hf (Subgroup.mem_top l)
    rw [MonoidHom.mem_ker] at h3
    have h4 : ⁅x, l⁆ = 1 := congrArg Subtype.val h3
    exact (commutatorElement_eq_one_iff_commute.mp h4).symm.eq
  · intro x hx
    exact Subgroup.mem_center_iff.mpr fun h => by
      obtain ⟨g, rfl⟩ := hφ h
      simp only [← map_mul]
      rw [(Subgroup.mem_center_iff.mp hx g).symm]

@[expose] noncomputable def quotientCenterEquiv {G H : Type*} [Group G] [Group H] (hP : Group.IsPerfect G)
    (φ : G →* H) (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G) :
    (G ⧸ Subgroup.center G) ≃* (H ⧸ Subgroup.center H) :=
  let ψ : G →* (H ⧸ Subgroup.center H) := (QuotientGroup.mk' (Subgroup.center H)).comp φ
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hφ
  have hψker : ψ.ker = Subgroup.center G := by
    rw [← preimage_center_eq_center hP φ hφ hker]
    ext g
    simp [ψ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  (QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)

theorem quotientCenterEquiv_mk {G H : Type*} [Group G] [Group H] (hP : Group.IsPerfect G)
    (φ : G →* H) (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G) (g : G) :
    quotientCenterEquiv hP φ hφ hker (QuotientGroup.mk g) = QuotientGroup.mk (φ g) := rfl

section Units

variable {k : Type*} [Field k] {W : Type*} [AddCommGroup W] [Module k W]

@[expose] noncomputable def unitsEquiv (k : Type*) [Field k] (W : Type*) [AddCommGroup W] [Module k W] :
    (Module.End k W)ˣ ≃* (W ≃ₗ[k] W) :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv k W

theorem unitsEquiv_apply (g : (Module.End k W)ˣ) (w : W) : unitsEquiv k W g w = g.val w := rfl

@[expose] noncomputable def toUnits (L : Subgroup (W ≃ₗ[k] W)) : Subgroup (Module.End k W)ˣ :=
  L.comap (unitsEquiv k W).toMonoidHom

theorem mem_toUnits {L : Subgroup (W ≃ₗ[k] W)} {g : (Module.End k W)ˣ} :
    g ∈ toUnits L ↔ unitsEquiv k W g ∈ L := Iff.rfl

@[expose] noncomputable def toUnitsEquiv (L : Subgroup (W ≃ₗ[k] W)) : ↥(toUnits L) ≃* ↥L where
  toFun g := ⟨unitsEquiv k W g.1, g.2⟩
  invFun x := ⟨(unitsEquiv k W).symm x.1, by
    show unitsEquiv k W ((unitsEquiv k W).symm x.1) ∈ L
    rw [MulEquiv.apply_symm_apply]
    exact x.2⟩
  left_inv g := by
    apply Subtype.ext
    exact (unitsEquiv k W).symm_apply_apply g.1
  right_inv x := by
    apply Subtype.ext
    exact (unitsEquiv k W).apply_symm_apply x.1
  map_mul' a b := Subtype.ext (map_mul (unitsEquiv k W) a.1 b.1)

theorem toUnitsEquiv_apply (L : Subgroup (W ≃ₗ[k] W)) (g : ↥(toUnits L)) :
    ((toUnitsEquiv L g : ↥L) : W ≃ₗ[k] W) = unitsEquiv k W g.1 := rfl

theorem toUnitsEquiv_symm_val (L : Subgroup (W ≃ₗ[k] W)) (x : ↥L) (w : W) :
    ((toUnitsEquiv L).symm x).1.val w = (x : W ≃ₗ[k] W) w := by
  have := toUnitsEquiv_apply L ((toUnitsEquiv L).symm x)
  rw [MulEquiv.apply_symm_apply] at this
  rw [← unitsEquiv_apply, ← this]

theorem toUnits_normalizer {L A : Subgroup (W ≃ₗ[k] W)}
    (h : A ≤ Subgroup.normalizer (L : Set (W ≃ₗ[k] W))) :
    toUnits A ≤ Subgroup.normalizer (toUnits L : Set (Module.End k W)ˣ) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hg' : unitsEquiv k W g ∈ Subgroup.normalizer (L : Set (W ≃ₗ[k] W)) := h hg
  have key : unitsEquiv k W (g * x * g⁻¹) =
      unitsEquiv k W g * unitsEquiv k W x * (unitsEquiv k W g)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  show unitsEquiv k W x ∈ L ↔ unitsEquiv k W (g * x * g⁻¹) ∈ L
  rw [key]
  exact (Subgroup.mem_normalizer_iff.mp hg' _)

theorem natCard_toUnits (L : Subgroup (W ≃ₗ[k] W)) : Nat.card ↥(toUnits L) = Nat.card ↥L :=
  Nat.card_congr (toUnitsEquiv L).toEquiv

theorem isElementaryAbelian_of_equiv {p : ℕ} {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.IsElementaryAbelian p B) : CFSG.IsElementaryAbelian p A :=
  CFSG.IsElementaryAbelian.of_mulEquiv e.symm h

end Units

end CFSG.QuasithinUnique.Setup.Lift
