module

public import Mathlib.FieldTheory.Finite.GaloisField
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceFixedCodimensions

public section

namespace CFSG.GH74.M12.Thm1

open Subgroup
open scoped Matrix

variable {G : Type*} [Group G]

theorem card_GL3_two : Nat.card (GL (Fin 3) (ZMod 2)) = 168 :=
  CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.FixedCodim.card_GL3

theorem isElementaryAbelian_of {E : Subgroup G}
    (hEe : ∀ a ∈ E, ∀ b ∈ E, a * a = 1 ∧ a * b = b * a) : IsElementaryAbelian 2 ↥E where
  is_comm := ⟨fun a b => Subtype.ext (hEe a a.2 b b.2).2⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
    Subtype.ext (by simp [pow_two, (hEe g g.2 g g.2).1])

theorem exists_coords8 [Finite G] {E : Subgroup G} (hE8 : Nat.card ↥E = 8)
    (hEe : ∀ a ∈ E, ∀ b ∈ E, a * a = 1 ∧ a * b = b * a) :
    Nonempty (Multiplicative (Fin 3 → ZMod 2) ≃* ↥E) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := isElementaryAbelian_of hEe
  open scoped IsMulCommutative in
  have hfin : Module.finrank (ZMod 2) (Additive ↥E) = 3 := by
    have h := FiniteField.pow_finrank_eq_natCard 2 (Additive ↥E)
    have h' : Nat.card (Additive ↥E) = 2 ^ 3 := hE8
    exact Nat.pow_right_injective le_rfl (h.trans h')
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive ↥E) hfin
  exact ⟨MulEquiv.toAdditiveRight.symm b.equivFun.symm.toAddEquiv⟩

section Coords

variable {E : Subgroup G} (f : Multiplicative (Fin 3 → ZMod 2) ≃* ↥E)

@[expose] noncomputable def coordLin8 (σ : MulAut ↥E) :
    (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
  (AddEquiv.toMultiplicative.symm ((f.trans σ).trans f.symm)).toLinearEquiv fun c v => by
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

theorem coordLin8_apply (σ : MulAut ↥E) (v : Fin 3 → ZMod 2) :
    coordLin8 f σ v = Multiplicative.toAdd (f.symm (σ (f (Multiplicative.ofAdd v)))) := rfl

@[expose] noncomputable def coordHom8 :
    MulAut ↥E →* ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) where
  toFun := coordLin8 f
  map_one' := by ext v; simp [coordLin8_apply]
  map_mul' σ τ := by ext v; simp [coordLin8_apply]

@[expose] noncomputable def toGL8 :
    ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) ≃* GL (Fin 3) (ZMod 2) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 3 → ZMod 2)).symm.trans
    Matrix.GeneralLinearGroup.toLin.symm

theorem toGL8_mulVec (g : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) (v : Fin 3 → ZMod 2) :
    (toGL8 g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v = g v := by
  have h1 : Matrix.GeneralLinearGroup.toLin (toGL8 g) =
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 3 → ZMod 2)).symm g :=
    MulEquiv.apply_symm_apply _ _
  have h2 := congrArg (fun u : LinearMap.GeneralLinearGroup (ZMod 2) (Fin 3 → ZMod 2) =>
    (u : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) v) h1
  simp only [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply] at h2
  exact h2

@[expose] noncomputable def actGL : ↥(normalizer (E : Set G)) →* GL (Fin 3) (ZMod 2) :=
  toGL8.toMonoidHom.comp ((coordHom8 f).comp E.normalizerMonoidHom)

theorem actGL_mulVec (g : ↥(normalizer (E : Set G))) (v : Fin 3 → ZMod 2) :
    ((f (Multiplicative.ofAdd ((actGL f g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v)) : ↥E) : G) =
      (g : G) * (f (Multiplicative.ofAdd v) : G) * (g : G)⁻¹ := by
  rw [actGL, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    toGL8_mulVec]
  show ((f (Multiplicative.ofAdd (coordLin8 f _ v)) : ↥E) : G) = _
  rw [coordLin8_apply, ofAdd_toAdd, MulEquiv.apply_symm_apply]
  rfl

theorem actGL_eq_one_iff (g : ↥(normalizer (E : Set G))) :
    actGL f g = 1 ↔ ∀ e ∈ E, (g : G) * e = e * g := by
  constructor
  · intro h e he
    have := actGL_mulVec f g (Multiplicative.toAdd (f.symm ⟨e, he⟩))
    rw [h, Units.val_one, Matrix.one_mulVec, ofAdd_toAdd, MulEquiv.apply_symm_apply] at this
    calc (g : G) * e = ((g : G) * e * (g : G)⁻¹) * g := by group
      _ = e * g := by rw [← this]
  · intro h
    apply Units.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_apply, Units.val_one, Matrix.toLin'_one, LinearMap.id_apply]
    apply (Multiplicative.ofAdd.trans f.toEquiv).injective
    apply Subtype.ext
    show ((f (Multiplicative.ofAdd ((actGL f g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v)) : ↥E) :
      G) = (f (Multiplicative.ofAdd v) : G)
    rw [actGL_mulVec]
    have := h _ (f (Multiplicative.ofAdd v)).2
    calc (g : G) * (f (Multiplicative.ofAdd v) : G) * (g : G)⁻¹ =
        ((f (Multiplicative.ofAdd v) : G) * g) * (g : G)⁻¹ := by rw [this]
      _ = _ := by group

end Coords

theorem card_normalizer_dvd [Finite G] {E : Subgroup G} (hE8 : Nat.card ↥E = 8)
    (hEe : ∀ a ∈ E, ∀ b ∈ E, a * a = 1 ∧ a * b = b * a)
    (hC : ∀ g : G, (∀ e ∈ E, g * e = e * g) → g ∈ E) :
    Nat.card ↥(normalizer (E : Set G)) ∣ 1344 := by
  obtain ⟨f⟩ := exists_coords8 hE8 hEe
  have hker : (actGL f).ker = E.subgroupOf (normalizer (E : Set G)) := by
    ext g
    rw [MonoidHom.mem_ker, actGL_eq_one_iff, Subgroup.mem_subgroupOf]
    constructor
    · exact hC g
    · intro hg e he
      exact (hEe _ hg e he).2
  have h1 := Subgroup.card_mul_index (actGL f).ker
  rw [Subgroup.index_ker, hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (Subgroup.le_normalizer : E ≤ normalizer (E : Set G))).toEquiv, hE8] at h1
  have h2 : Nat.card ↥(actGL f).range ∣ 168 := by
    rw [← card_GL3_two]; exact Subgroup.card_subgroup_dvd_card _
  rw [← h1]
  exact Nat.mul_dvd_mul_left 8 h2

theorem nonempty_quotient_equiv_GL3 [Finite G] {E : Subgroup G} [hn : E.Normal]
    (hE8 : Nat.card ↥E = 8) (hEe : ∀ a ∈ E, ∀ b ∈ E, a * a = 1 ∧ a * b = b * a)
    (hC : ∀ g : G, (∀ e ∈ E, g * e = e * g) → g ∈ E) (hG : Nat.card G = 1344) :
    Nonempty (G ⧸ E ≃* GL (Fin 3) (ZMod 2)) := by
  obtain ⟨f⟩ := exists_coords8 hE8 hEe
  have htop : normalizer (E : Set G) = ⊤ := Subgroup.normalizer_eq_top E
  let ι : G →* ↥(normalizer (E : Set G)) :=
    (MonoidHom.id G).codRestrict _ (fun g => by rw [htop]; exact Subgroup.mem_top g)
  let ρ : G →* GL (Fin 3) (ZMod 2) := (actGL f).comp ι
  have hker : ρ.ker = E := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, actGL_eq_one_iff]
    constructor
    · exact hC g
    · intro hg e he
      exact (hEe _ hg e he).2
  have h1 := Subgroup.card_mul_index ρ.ker
  rw [Subgroup.index_ker, hker, hE8, hG] at h1
  have hsurj : Function.Surjective ρ := by
    rw [← MonoidHom.range_eq_top]
    apply Subgroup.eq_top_of_card_eq
    rw [card_GL3_two]
    omega
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ hsurj)⟩

end CFSG.GH74.M12.Thm1
