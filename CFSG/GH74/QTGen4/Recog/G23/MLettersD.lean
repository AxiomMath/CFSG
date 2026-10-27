module

public import CFSG.GH74.QTGen4.Recog.G23.MLetters
public import CFSG.GH74.QTGen4.Recog.G23.MSylow
public import CFSG.GH74.QTGen4.Recog.G23.MLettersC
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Set.Card
public meta import Mathlib.Algebra.Field.ZMod
public meta import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace CFSG.GH74.QTGen4.Recog.G23

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G23Type
open scoped MatrixGroups IsMulCommutative

variable {G : Type*} [Group G]

theorem card_invertible_fin3 :
    Set.ncard {B : Matrix (Fin 3) (Fin 3) (ZMod 2) | B.det ≠ 0} = 168 := by
  have hS : {B : Matrix (Fin 3) (Fin 3) (ZMod 2) | B.det ≠ 0} =
      ↑(Finset.univ.filter (fun B : Matrix (Fin 3) (Fin 3) (ZMod 2) => B.det ≠ 0)) := by
    ext B
    simp
  rw [hS, Set.ncard_coe_finset]
  decide +kernel

theorem G23Two.exists_conj_eq [Finite G] {M : Subgroup G} (hM : G23Two M) {z z' : G}
    (hz : z ∈ quasithinGenFitting M) (hz1 : z ≠ 1) (hz' : z' ∈ quasithinGenFitting M)
    (hz'1 : z' ≠ 1) : ∃ m ∈ M, m * z * m⁻¹ = z' := by
  have hVM : quasithinGenFitting M ≤ M := CFSG.Quasithin.quasithinGenFitting_le M
  have hcomm : IsMulCommutative ↥(quasithinGenFitting M) := hM.elem.1
  have hexp : ∀ x : ↥(quasithinGenFitting M), x ^ 2 = 1 := fun x =>
    Subtype.ext (by simpa using hM.elem.2 _ x.2)
  let hmod : Module (ZMod 2) (Additive ↥(quasithinGenFitting M)) :=
    AddCommGroup.zmodModule (n := 2) (fun x => by
      show 2 • x = 0
      apply Additive.toMul.injective
      simp only [toMul_nsmul, toMul_zero]
      exact hexp x.toMul)
  have hcard : Nat.card (Additive ↥(quasithinGenFitting M)) = 8 :=
    (Nat.card_congr Additive.toMul).trans hM.card
  have hfin : Finite (Additive ↥(quasithinGenFitting M)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : Module.Finite (ZMod 2) (Additive ↥(quasithinGenFitting M)) := Module.Finite.of_finite
  have hrank : Module.finrank (ZMod 2) (Additive ↥(quasithinGenFitting M)) = 3 := by
    have hfc := Fintype.ofFinite (Additive ↥(quasithinGenFitting M))
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive ↥(quasithinGenFitting M))
    rw [← Nat.card_eq_fintype_card, hcard, ZMod.card] at h
    have h' : 2 ^ Module.finrank (ZMod 2) (Additive ↥(quasithinGenFitting M)) = 2 ^ 3 := by
      rw [← h]
      norm_num
    exact Nat.pow_right_injective (le_refl 2) h'
  let b : Module.Basis (Fin 3) (ZMod 2) (Additive ↥(quasithinGenFitting M)) :=
    Module.finBasisOfFinrankEq (ZMod 2) (Additive ↥(quasithinGenFitting M)) hrank
  let T : M →* Module.End (ZMod 2) (Additive ↥(quasithinGenFitting M)) :=
    { toFun := fun g => AddMonoidHom.toZModLinearMap 2
        (AddMonoidHom.mk'
          (fun x : Additive ↥(quasithinGenFitting M) =>
            Additive.ofMul (⟨(g : G) * x.toMul * (g : G)⁻¹,
              G23Two.conj_mem_fitting hM g.2 x.toMul.2⟩ : ↥(quasithinGenFitting M)))
          (fun x y => by
            apply Additive.toMul.injective
            apply Subtype.ext
            simp [mul_assoc]))
      map_one' := by
        ext x
        simp [AddMonoidHom.toZModLinearMap]
      map_mul' := fun a c => by
        ext x
        simp [AddMonoidHom.toZModLinearMap, mul_assoc] }
  let Φ0 : M →* Matrix (Fin 3) (Fin 3) (ZMod 2) :=
    (LinearMap.toMatrixAlgEquiv b).toAlgHom.toMonoidHom.comp T
  let Φ : M →* (Matrix (Fin 3) (Fin 3) (ZMod 2))ˣ := Φ0.toHomUnits
  have hker : Φ.ker = (quasithinGenFitting M).subgroupOf M := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hg
      have h0 : Φ0 g = 1 := by
        have := congrArg Units.val hg
        exact this
      have hT : T g = 1 := by
        apply (LinearMap.toMatrixAlgEquiv b).injective
        rw [map_one]
        exact h0
      have hconj : ∀ x : Additive ↥(quasithinGenFitting M),
          (g : G) * x.toMul * (g : G)⁻¹ = x.toMul := by
        intro x
        have h2 : T g x = x := LinearMap.congr_fun hT x
        have h3 := congrArg (fun y : Additive ↥(quasithinGenFitting M) => ((Additive.toMul y : ↥(quasithinGenFitting M)) : G)) h2
        exact h3
      have hcen : (g : G) ∈ Subgroup.centralizer (quasithinGenFitting M : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        have h4 : (g : G) * h * (g : G)⁻¹ = h := hconj (Additive.ofMul ⟨h, hh⟩)
        exact (mul_inv_eq_iff_eq_mul.mp h4).symm
      have hmemM : (g : G) ∈ M ⊓ Subgroup.centralizer (quasithinGenFitting M : Set G) :=
        ⟨g.2, hcen⟩
      rwa [G23Two.inf_centralizer_fitting hM] at hmemM
    · intro hg
      have hT : T g = 1 := by
        apply LinearMap.ext
        intro x
        apply Additive.toMul.injective
        apply Subtype.ext
        show (g : G) * x.toMul * (g : G)⁻¹ = x.toMul
        rw [G23Two.fitting_comm hM hg x.toMul.2, mul_inv_cancel_right]
      apply Units.ext
      show (LinearMap.toMatrixAlgEquiv b) (T g) = 1
      rw [hT, map_one]
  have hkerCard : Nat.card Φ.ker = 8 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVM).toEquiv, hM.card]
  have hrange : Nat.card Φ.range = 168 := by
    have h := Subgroup.card_ker_mul_card_range Φ
    rw [hkerCard, G23Two.card_group hM] at h
    omega
  set R : Set (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    (fun u : (Matrix (Fin 3) (Fin 3) (ZMod 2))ˣ => (u : Matrix (Fin 3) (Fin 3) (ZMod 2))) ''
      (Φ.range : Set (Matrix (Fin 3) (Fin 3) (ZMod 2))ˣ) with hR
  have hRcard : R.ncard = 168 := by
    rw [hR, Set.ncard_image_of_injective _ (fun _ _ h => Units.ext h), ← Nat.card_coe_set_eq]
    exact hrange
  have hsub : R ⊆ {B : Matrix (Fin 3) (Fin 3) (ZMod 2) | B.det ≠ 0} := by
    rintro _ ⟨u, _, rfl⟩
    show (u : Matrix (Fin 3) (Fin 3) (ZMod 2)).det ≠ 0
    exact ((Matrix.isUnit_iff_isUnit_det _).mp u.isUnit).ne_zero
  have hRS : R = {B : Matrix (Fin 3) (Fin 3) (ZMod 2) | B.det ≠ 0} :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hRcard, card_invertible_fin3]) (Set.toFinite _)
  let zE : Additive ↥(quasithinGenFitting M) := Additive.ofMul ⟨z, hz⟩
  let zE' : Additive ↥(quasithinGenFitting M) := Additive.ofMul ⟨z', hz'⟩
  have hzE : zE ≠ 0 := by
    intro h
    apply hz1
    have := congrArg (fun y : Additive ↥(quasithinGenFitting M) => ((Additive.toMul y : ↥(quasithinGenFitting M)) : G)) h
    simpa [zE] using this
  have hzE' : zE' ≠ 0 := by
    intro h
    apply hz'1
    have := congrArg (fun y : Additive ↥(quasithinGenFitting M) => ((Additive.toMul y : ↥(quasithinGenFitting M)) : G)) h
    simpa [zE'] using this
  have hx : (⇑(b.repr zE) : Fin 3 → ZMod 2) ≠ 0 := by
    intro h
    exact hzE (b.repr.map_eq_zero_iff.mp (Finsupp.coe_eq_zero.mp h))
  have hx' : (⇑(b.repr zE') : Fin 3 → ZMod 2) ≠ 0 := by
    intro h
    exact hzE' (b.repr.map_eq_zero_iff.mp (Finsupp.coe_eq_zero.mp h))
  obtain ⟨B, hBdet, hB⟩ := GL3_two_transitive _ _ hx hx'
  have hBR : Matrix.of B ∈ R := by
    rw [hRS]
    exact hBdet
  obtain ⟨u, hu, hue⟩ := hBR
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (hu : u ∈ Φ.range)
  have hΦ0 : Φ0 g = Matrix.of B := by
    rw [← hue, ← hg]
    try rfl
  have hrep : ∀ y : Additive ↥(quasithinGenFitting M),
      (⇑(b.repr (T g y)) : Fin 3 → ZMod 2) = Matrix.mulVec (Matrix.of B) ⇑(b.repr y) := by
    intro y
    rw [← hΦ0]
    show _ = Matrix.mulVec (LinearMap.toMatrix b b (T g)) ⇑(b.repr y)
    exact (LinearMap.toMatrix_mulVec_repr b b (T g) y).symm
  have hfun : ⇑(b.repr (T g zE)) = ⇑(b.repr zE') := (hrep zE).trans hB
  have hT2 : T g zE = zE' := b.repr.injective (DFunLike.coe_injective hfun)
  refine ⟨g, g.2, ?_⟩
  have h5 := congrArg (fun y : Additive ↥(quasithinGenFitting M) => ((Additive.toMul y : ↥(quasithinGenFitting M)) : G)) hT2
  exact h5

end CFSG.GH74.QTGen4.Recog.G23
