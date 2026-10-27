module

public import CFSG.Fischer.Classification.Orthogonal3.Model
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.ClassicalInvolution.Orders.OrthogonalIndex

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35R3

open Subgroup CFSG.Fischer.Classification

variable {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

theorem polarBilin_toQuadraticMap_nondegenerate (hf : IsF3Form f) :
    (QuadraticMap.polarBilin (LinearMap.BilinMap.toQuadraticMap f)).Nondegenerate := by
  have hpolar : ∀ x y, QuadraticMap.polar (LinearMap.BilinMap.toQuadraticMap f) x y =
      2 * f x y := fun x y => by
    rw [LinearMap.BilinMap.polar_toQuadraticMap, hf.symm y x, two_mul]
  have hsep : ∀ x, (∀ y, QuadraticMap.polar (LinearMap.BilinMap.toQuadraticMap f) x y = 0) →
      x = 0 := fun x hx =>
    hf.nondeg x fun y => by
      have h := hx y
      rw [hpolar] at h
      exact (mul_eq_zero.mp h).resolve_left (by decide)
  refine ⟨fun x hx => hsep x fun y => ?_, fun y hy => hsep y fun x => ?_⟩
  · rw [← QuadraticMap.polarBilin_apply_apply]
    exact hx y
  · rw [QuadraticMap.polar_comm, ← QuadraticMap.polarBilin_apply_apply]
    exact hy x

@[expose] noncomputable def toOrth (hf : IsF3Form f) :
    F3.reflGroup f →*
      TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap f) :=
  ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m) (ZMod 3)).toMonoidHom.comp
      (F3.reflGroup f).subtype).codRestrict _ fun g =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype,
        LinearMap.BilinMap.toQuadraticMap_apply,
        CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]
      exact F3.isIsom_of_mem hf g.2 x x

theorem toOrth_apply (hf : IsF3Form f) (g : F3.reflGroup f) (x : Fin m → ZMod 3) :
    ((toOrth hf g : TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap f)) :
      (Fin m → ZMod 3) ≃ₗ[ZMod 3] (Fin m → ZMod 3)) x = F3.act g x :=
  rfl

theorem toOrth_injective (hf : IsF3Form f) : Function.Injective (toOrth hf) := fun _ _ h =>
  Subtype.ext ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m) (ZMod 3)).injective
    (congrArg Subtype.val h))

theorem toOrth_reflElt (hf : IsF3Form f) {v : Fin m → ZMod 3} (hv : f v v = 1)
    [Invertible (LinearMap.BilinMap.toQuadraticMap f v)] :
    toOrth hf (reflElt f v) =
      TauCeti.QuadraticMap.reflectionOrthogonal (LinearMap.BilinMap.toQuadraticMap f) v := by
  have hq : LinearMap.BilinMap.toQuadraticMap f v ≠ 0 := by
    rw [LinearMap.BilinMap.toQuadraticMap_apply, hv]
    exact one_ne_zero
  refine Subtype.ext (LinearEquiv.ext fun x => ?_)
  rw [CFSG.ClassicalInvolution.coe_reflectionOrthogonal_eq_reflect,
    CFSG.ClassicalGroups.Orthogonal.reflect_apply hq, toOrth_apply, coe_reflElt, F3.act_refl hv,
    LinearMap.BilinMap.polar_toQuadraticMap, LinearMap.BilinMap.toQuadraticMap_apply, hv,
    div_one, hf.symm v x]
  linear_combination (norm := module) F3.three_eq_zero • (f x v • v)

theorem detSpinorNorm_toOrth_reflElt (hf : IsF3Form f) [Invertible (2 : ZMod 3)]
    (hQ : (LinearMap.BilinMap.toQuadraticMap f).Nondegenerate) {v : Fin m → ZMod 3}
    (hv : f v v = 1) :
    CFSG.ClassicalInvolution.detSpinorNorm hQ (toOrth hf (reflElt f v)) = (-1, 1) := by
  have hq : LinearMap.BilinMap.toQuadraticMap f v ≠ 0 := by
    rw [LinearMap.BilinMap.toQuadraticMap_apply, hv]
    exact one_ne_zero
  let _ : Invertible (LinearMap.BilinMap.toQuadraticMap f v) := invertibleOfNonzero hq
  rw [toOrth_reflElt hf hv, CFSG.ClassicalInvolution.detSpinorNorm_reflectionOrthogonal]
  have h1 : unitOfInvertible (LinearMap.BilinMap.toQuadraticMap f v) = 1 := by
    ext
    rw [val_unitOfInvertible, Units.val_one, LinearMap.BilinMap.toQuadraticMap_apply, hv]
  rw [h1, map_one]

theorem card_orthogonalGroup_five {f : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3)}
    (hf : IsF3Form f) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap f)) =
      103680 := by
  have hO := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_odd (n := 2)
    (by rw [ZMod.ringChar_zmod_n]; decide) (polarBilin_toQuadraticMap_nondegenerate hf)
    (by rw [Module.finrank_fin_fun])
  rw [Nat.card_zmod] at hO
  have : (2 * (3 : ℤ) ^ (2 ^ 2) * ∏ i ∈ Finset.Icc 1 2, ((3 ^ 2) ^ i - 1)) = 103680 := by
    decide
  exact_mod_cast hO.trans this

theorem card_R3_dvd_of_isSimpleGroup {f : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3)}
    (hf : IsF3Form f) [IsSimpleGroup (R3 f)] (hna : ∃ a b : R3 f, a * b ≠ b * a) :
    Nat.card (R3 f) ∣ 25920 := by
  classical
  let _ : Invertible (2 : ZMod 3) := invertibleOfNonzero (by decide)
  have hQ : (LinearMap.BilinMap.toQuadraticMap f).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (polarBilin_toQuadraticMap_nondegenerate hf)
  obtain ⟨δ, hδ⟩ : ∃ δ : TauCeti.QuadraticMap.orthogonalGroup
      (LinearMap.BilinMap.toQuadraticMap f) →* (ZMod 3)ˣ,
      ∀ x, δ x = (CFSG.ClassicalInvolution.detSpinorNorm hQ x).1 :=
    ⟨(MonoidHom.fst _ _).comp (CFSG.ClassicalInvolution.detSpinorNorm hQ), fun _ => rfl⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : TauCeti.QuadraticMap.orthogonalGroup
      (LinearMap.BilinMap.toQuadraticMap f) →* Multiplicative (TauCeti.SquareClassGroup (ZMod 3)),
      ∀ x, θ x = (CFSG.ClassicalInvolution.detSpinorNorm hQ x).2 :=
    ⟨(MonoidHom.snd _ _).comp (CFSG.ClassicalInvolution.detSpinorNorm hQ), fun _ => rfl⟩
  have hδr : ∀ v, f v v = 1 → δ (toOrth hf (reflElt f v)) = -1 := fun v hv => by
    rw [hδ, detSpinorNorm_toOrth_reflElt hf hQ hv]
  have hθr : ∀ v, f v v = 1 → θ (toOrth hf (reflElt f v)) = 1 := fun v hv => by
    rw [hθ, detSpinorNorm_toOrth_reflElt hf hQ hv]
  obtain ⟨u, hu⟩ := F3.exists_norm_eq hf (by norm_num) (one_ne_zero : (1 : ZMod 3) ≠ 0)
  obtain ⟨w, hw⟩ := F3.exists_norm_eq hf (by norm_num) (by decide : (2 : ZMod 3) ≠ 0)
  have hqw : LinearMap.BilinMap.toQuadraticMap f w = 2 := by
    rw [LinearMap.BilinMap.toQuadraticMap_apply, hw]
  let _ : Invertible (LinearMap.BilinMap.toQuadraticMap f w) :=
    invertibleOfNonzero (by rw [hqw]; decide)
  have hδw : δ (TauCeti.QuadraticMap.reflectionOrthogonal _ w) = -1 := by
    rw [hδ, CFSG.ClassicalInvolution.detSpinorNorm_reflectionOrthogonal]
  have hθw : θ (TauCeti.QuadraticMap.reflectionOrthogonal _ w) =
      TauCeti.squareClassHom (unitOfInvertible (LinearMap.BilinMap.toQuadraticMap f w)) := by
    rw [hθ, CFSG.ClassicalInvolution.detSpinorNorm_reflectionOrthogonal]
  have hν1 : TauCeti.squareClassHom
      (unitOfInvertible (LinearMap.BilinMap.toQuadraticMap f w)) ≠ 1 := by
    rw [Ne, ← MonoidHom.mem_ker, TauCeti.ker_squareClassHom, Subgroup.mem_square]
    rintro ⟨r, hr⟩
    have h2 := congrArg Units.val hr
    rw [val_unitOfInvertible, Units.val_mul, hqw] at h2
    generalize (r : ZMod 3) = x at h2
    revert x
    decide
  have hν2 : TauCeti.squareClassHom
      (unitOfInvertible (LinearMap.BilinMap.toQuadraticMap f w)) ^ 2 = 1 := by
    rw [← map_pow, ← MonoidHom.mem_ker, TauCeti.ker_squareClassHom, Subgroup.mem_square]
    exact ⟨_, pow_two _⟩
  have hm1 : (-1 : (ZMod 3)ˣ) ≠ 1 := by decide
  have h1 : 2 ∣ Nat.card δ.range := by
    have hmem : (-1 : (ZMod 3)ˣ) ∈ δ.range := ⟨_, hδw⟩
    have hord : orderOf (⟨-1, hmem⟩ : δ.range) = 2 :=
      orderOf_eq_prime (Subtype.ext (by simp))
        (fun h => hm1 (by simpa using congrArg Subtype.val h))
    rw [← hord]
    exact orderOf_dvd_natCard _
  have hsuw : TauCeti.QuadraticMap.reflectionOrthogonal _ w * toOrth hf (reflElt f u) ∈
      δ.ker := by
    rw [MonoidHom.mem_ker, map_mul, hδw, hδr u hu]
    decide
  have h2 : 2 ∣ Nat.card (θ.comp δ.ker.subtype).range := by
    have hmem : TauCeti.squareClassHom (unitOfInvertible (LinearMap.BilinMap.toQuadraticMap f w))
        ∈ (θ.comp δ.ker.subtype).range :=
      ⟨⟨_, hsuw⟩, by simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, hθw,
        hθr u hu, mul_one]⟩
    have hord : orderOf (⟨_, hmem⟩ : (θ.comp δ.ker.subtype).range) = 2 :=
      orderOf_eq_prime (Subtype.ext (by simpa using hν2))
        (fun h => hν1 (by simpa using congrArg Subtype.val h))
    rw [← hord]
    exact orderOf_dvd_natCard _
  have hK : Nat.card (θ.comp δ.ker.subtype).ker ∣ 25920 := by
    have e1 := δ.ker.card_mul_index
    have e2 := (θ.comp δ.ker.subtype).ker.card_mul_index
    rw [Subgroup.index_ker] at e1
    rw [Subgroup.index_ker] at e2
    rw [card_orthogonalGroup_five hf] at e1
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    rw [ha] at e1
    rw [hb] at e2
    refine ⟨a * b, ?_⟩
    have h3 : Nat.card (θ.comp δ.ker.subtype).ker * (2 * b) * (2 * a) = 103680 := by
      rw [e2]
      exact e1
    have h4 : Nat.card (θ.comp δ.ker.subtype).ker * (2 * b) * (2 * a) =
        4 * (Nat.card (θ.comp δ.ker.subtype).ker * (a * b)) := by ring
    omega
  have hθι : ∀ g : F3.reflGroup f, θ (toOrth hf g) = 1 := by
    have hle : F3.reflGroup f ≤ ((θ.comp (toOrth hf)).ker).map (F3.reflGroup f).subtype := by
      rw [Subgroup.closure_le]
      intro x hx
      obtain ⟨v, hv, rfl⟩ := F3.mem_reflSet_iff.1 hx
      exact ⟨reflElt f v, MonoidHom.mem_ker.mpr (hθr v hv), rfl⟩
    intro g
    obtain ⟨g', hg', hgg'⟩ := hle g.2
    obtain rfl : g' = g := Subtype.ext hgg'
    exact MonoidHom.mem_ker.mp hg'
  have hH : Nat.card (δ.comp (toOrth hf)).ker ∣ Nat.card (θ.comp δ.ker.subtype).ker := by
    let j : (δ.comp (toOrth hf)).ker →* (θ.comp δ.ker.subtype).ker :=
      { toFun := fun h => ⟨⟨toOrth hf h, MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp h.2)⟩,
          MonoidHom.mem_ker.mpr (hθι h)⟩
        map_one' := Subtype.ext (Subtype.ext (map_one _))
        map_mul' := fun a b => Subtype.ext (Subtype.ext (map_mul _ _ _)) }
    refine Subgroup.card_dvd_of_injective j fun a b hab => Subtype.ext (toOrth_injective hf ?_)
    exact congrArg Subtype.val (congrArg Subtype.val hab)
  have hN : ((δ.comp (toOrth hf)).ker.map
      (QuotientGroup.mk' (center (F3.reflGroup f)))).Normal :=
    (MonoidHom.normal_ker _).map _ (QuotientGroup.mk'_surjective _)
  rcases hN.eq_bot_or_eq_top with hbot | htop
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center (F3.reflGroup f)) a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center (F3.reflGroup f)) b
    apply hab
    have hc : x * y * x⁻¹ * y⁻¹ ∈ (δ.comp (toOrth hf)).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
        mul_comm ((δ.comp (toOrth hf)) x) ((δ.comp (toOrth hf)) y)]
      group
    have hc' := Subgroup.mem_map_of_mem (QuotientGroup.mk' (center (F3.reflGroup f))) hc
    rw [hbot, Subgroup.mem_bot, map_mul, map_mul, map_mul, map_inv, map_inv] at hc'
    calc _ = QuotientGroup.mk' (center (F3.reflGroup f)) x *
          QuotientGroup.mk' (center (F3.reflGroup f)) y *
          (QuotientGroup.mk' (center (F3.reflGroup f)) x)⁻¹ *
          (QuotientGroup.mk' (center (F3.reflGroup f)) y)⁻¹ *
          (QuotientGroup.mk' (center (F3.reflGroup f)) y *
            QuotientGroup.mk' (center (F3.reflGroup f)) x) := by group
      _ = _ := by rw [hc', one_mul]
  · have hsurj : Function.Surjective ((QuotientGroup.mk' (center (F3.reflGroup f))).comp
        (δ.comp (toOrth hf)).ker.subtype) := by
      intro y
      have hy : y ∈ (δ.comp (toOrth hf)).ker.map (QuotientGroup.mk' _) := htop ▸ mem_top y
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨⟨x, hx⟩, rfl⟩
    exact (Subgroup.card_dvd_of_surjective hsurj).trans (hH.trans hK)

end CFSG.LargeExtraspecial.AS35R3
