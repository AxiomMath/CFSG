module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexCosetAction
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.RankOnePair

open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
open scoped IsMulCommutative

variable {G : Type*} [Group G]

theorem existsUnique_map {A B : Type*} [Group A] [Group B] (f : A →* B) (K : Subgroup A)
    {p : B → Prop} (h : ∃! k : K, p (f k)) : ∃! b : K.map f, p b := by
  obtain ⟨k, hk, huniq⟩ := h
  refine ⟨⟨f k, k, k.2, rfl⟩, hk, ?_⟩
  rintro ⟨_, k', hk', rfl⟩ hb
  have h' := huniq ⟨k', hk'⟩ hb
  exact Subtype.ext (congrArg (fun x : K => f x) h')

theorem existsUnique_of_map_of_injective {A B : Type*} [Group A] [Group B] {f : A →* B}
    (hf : Function.Injective f) (K : Subgroup A) {p : B → Prop} {q : A → Prop}
    (hpq : ∀ a, p (f a) ↔ q a) (h : ∃! b : K.map f, p b) : ∃! k : K, q k := by
  obtain ⟨⟨_, k, hk, rfl⟩, hb, huniq⟩ := h
  refine ⟨⟨k, hk⟩, (hpq k).mp hb, fun k' hk' => ?_⟩
  have h' := huniq ⟨f k', k', k'.2, rfl⟩ ((hpq k').mpr hk')
  exact Subtype.ext (hf (congrArg Subtype.val h'))

theorem isCyclic_map {A B : Type*} [Group A] [Group B] (f : A →* B) (K : Subgroup A)
    [IsCyclic K] : IsCyclic (K.map f) :=
  isCyclic_of_surjective (f.subgroupMap K) (f.subgroupMap_surjective K)

theorem isCyclic_of_map_of_injective {A B : Type*} [Group A] [Group B] {f : A →* B}
    (hf : Function.Injective f) (K : Subgroup A) [IsCyclic (K.map f)] : IsCyclic K :=
  isCyclic_of_injective (f.subgroupMap K) fun _ _ hab =>
    Subtype.ext (hf (congrArg Subtype.val hab))

theorem map_eq_map_of_eqOn {A B : Type*} [Group A] [Group B] (K : Subgroup A) {f g : A →* B}
    (hfg : ∀ k ∈ K, f k = g k) : K.map f = K.map g := by
  ext b
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, (hfg k hk).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, hfg k hk⟩

@[expose] def cosetCoordinates (U : Subgroup G) (u : G) :
    Additive U ≃ ((fun v : G => u * v) '' (U : Set G)) where
  toFun v := ⟨u * ((Additive.toMul v : U) : G), (Additive.toMul v : U), (Additive.toMul v).2, rfl⟩
  invFun x := Additive.ofMul ⟨u⁻¹ * x, by
    obtain ⟨v, hv, hx⟩ := x.2
    rw [← hx, inv_mul_cancel_left]
    exact hv⟩
  left_inv v := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact inv_mul_cancel_left u _
  right_inv x := Subtype.ext (mul_inv_cancel_left u (x : G))

theorem cosetCoordinates_apply (U : Subgroup G) (u : G) (v : Additive U) :
    (cosetCoordinates U u v : G) = u * ((Additive.toMul v : U) : G) :=
  rfl

theorem cosetCoordinates_zero (U : Subgroup G) (u : G) :
    (cosetCoordinates U u 0 : G) = u :=
  mul_one u

theorem cosetCoordinates_eq_iff (U : Subgroup G) (u : G) (v : Additive U) :
    (cosetCoordinates U u v : G) = u ↔ v = 0 := by
  rw [cosetCoordinates_apply, mul_eq_left]
  constructor
  · intro h
    exact Additive.toMul.injective (Subtype.ext h)
  · rintro rfl
    rfl

variable (U : Subgroup G) [IsElementaryAbelian 2 U] (u : G)

@[expose] def cosetAffinePerm :
    (Additive U ≃ᵃ[ZMod 2] Additive U) →* Equiv.Perm ((fun v : G => u * v) '' (U : Set G)) where
  toFun g := (cosetCoordinates U u).permCongr g.toEquiv
  map_one' := Equiv.ext fun x => by
    rw [Equiv.permCongr_apply]
    exact (cosetCoordinates U u).apply_symm_apply x
  map_mul' g h := Equiv.ext fun x => by
    simp only [Equiv.permCongr_apply, Equiv.Perm.coe_mul, Function.comp_apply,
      Equiv.symm_apply_apply]
    rfl

theorem cosetAffinePerm_apply (g : Additive U ≃ᵃ[ZMod 2] Additive U) :
    cosetAffinePerm U u g = (cosetCoordinates U u).permCongr g.toEquiv :=
  rfl

theorem cosetAffinePerm_apply_coordinates (g : Additive U ≃ᵃ[ZMod 2] Additive U)
    (v : Additive U) :
    cosetAffinePerm U u g (cosetCoordinates U u v) = cosetCoordinates U u (g v) := by
  rw [cosetAffinePerm_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rfl

theorem cosetAffinePerm_injective : Function.Injective (cosetAffinePerm U u) := by
  intro g h hgh
  refine AffineEquiv.ext fun v => (cosetCoordinates U u).injective ?_
  rw [← cosetAffinePerm_apply_coordinates, ← cosetAffinePerm_apply_coordinates, hgh]

variable {U u}

theorem cosetAffinePerm_comp_eq
    (φ : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)) →*
      (Additive U ≃ᵃ[ZMod 2] Additive U))
    (hφ : ∀ (n : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G))) (v : U),
      (n : G) * (u * v) * (n : G)⁻¹ = u * ((Additive.toMul (φ n (Additive.ofMul v)) : U) : G)) :
    (cosetAffinePerm U u).comp φ = cosetNormalizerPerm ((fun v : G => u * v) '' (U : Set G)) := by
  ext n x
  obtain ⟨v, rfl⟩ := (cosetCoordinates U u).surjective x
  rw [MonoidHom.comp_apply, cosetAffinePerm_apply_coordinates, cosetCoordinates_apply,
    cosetNormalizerPerm_apply, cosetCoordinates_apply, hφ]
  rfl

theorem cosetNormalizerPerm_range_eq_map
    (φ : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)) →*
      (Additive U ≃ᵃ[ZMod 2] Additive U))
    (hφ : ∀ (n : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G))) (v : U),
      (n : G) * (u * v) * (n : G)⁻¹ = u * ((Additive.toMul (φ n (Additive.ofMul v)) : U) : G)) :
    (cosetNormalizerPerm ((fun v : G => u * v) '' (U : Set G))).range =
      φ.range.map (cosetAffinePerm U u) := by
  rw [← cosetAffinePerm_comp_eq φ hφ, MonoidHom.range_comp]

theorem affine_apply_zero_eq_zero_iff
    (φ : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)) →*
      (Additive U ≃ᵃ[ZMod 2] Additive U))
    (hφ : ∀ (n : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G))) (v : U),
      (n : G) * (u * v) * (n : G)⁻¹ = u * ((Additive.toMul (φ n (Additive.ofMul v)) : U) : G))
    (n : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G))) :
    φ n 0 = 0 ↔ (n : G) ∈ Subgroup.centralizer ({u} : Set G) := by
  have h := hφ n 1
  rw [OneMemClass.coe_one, mul_one] at h
  rw [Subgroup.mem_centralizer_singleton_iff]
  change φ n (Additive.ofMul 1) = 0 ↔ _
  constructor
  · intro h0
    rw [h0] at h
    have h' : (n : G) * u * (n : G)⁻¹ = u := by simpa using h
    calc (n : G) * u = (n : G) * u * (n : G)⁻¹ * n := by group
      _ = u * n := by rw [h']
  · intro hnu
    have h' : u * ((Additive.toMul (φ n (Additive.ofMul 1)) : U) : G) = u := by
      rw [← h, hnu, mul_inv_cancel_right]
    exact Additive.toMul.injective (Subtype.ext (mul_eq_left.mp h'))

end CFSG.ProperTwoGeneratedCore.RankOnePair
