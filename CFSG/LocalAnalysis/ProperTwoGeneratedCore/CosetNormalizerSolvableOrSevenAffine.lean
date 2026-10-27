module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerSolvableOrSevenCoordinates
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerSingerAffine

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.RankOnePair

open Module
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
open CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped IsMulCommutative

variable {G : Type*} [Group G]

@[expose] def linearToAffineHom (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] :
    (V ≃ₗ[ZMod 2] V) →* (V ≃ᵃ[ZMod 2] V) where
  toFun g := g.toAffineEquiv
  map_one' := AffineEquiv.ext fun _ => rfl
  map_mul' _ _ := AffineEquiv.ext fun _ => rfl

theorem linearToAffineHom_injective (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] :
    Function.Injective (linearToAffineHom V) := fun _ _ hgh =>
  LinearEquiv.ext fun v => congrArg (fun a : V ≃ᵃ[ZMod 2] V => a v) hgh

local instance factPrimeSevenCoset : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

variable [Finite G] {U : Subgroup G} [IsElementaryAbelian 2 U] {u : G}

theorem coset_normalizer_perm_solvable_or_projective_seven {e : ℕ} (he : 1 ≤ e)
    (hcard : Nat.card U = 2 ^ e)
    (φ : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)) →*
      (Additive U ≃ᵃ[ZMod 2] Additive U))
    (hφ : ∀ (n : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G))) (v : U),
      (n : G) * (u * v) * (n : G)⁻¹ = u * ((Additive.toMul (φ n (Additive.ofMul v)) : U) : G))
    (htrans : ∀ x ∈ (fun v : G => u * v) '' (U : Set G),
      ∀ y ∈ (fun v : G => u * v) '' (U : Set G),
        ∃ n ∈ Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)), n * x * n⁻¹ = y)
    (X : Subgroup (Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G))))
    (hXu : ∀ x ∈ X, (x : G) ∈ Subgroup.centralizer ({u} : Set G))
    (hXn : ∀ m : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)),
      (m : G) ∈ Subgroup.centralizer ({u} : Set G) → ∀ x ∈ X, m * x * m⁻¹ ∈ X)
    (hcyc : IsCyclic (X.map (cosetNormalizerPerm ((fun v : G => u * v) '' (U : Set G)))))
    (hreg : ∀ x y : (fun v : G => u * v) '' (U : Set G), (x : G) ≠ u → (y : G) ≠ u →
      ∃! σ : X.map (cosetNormalizerPerm ((fun v : G => u * v) '' (U : Set G))),
        (σ : Equiv.Perm ((fun v : G => u * v) '' (U : Set G))) x = y) :
    (Group.IsSolvable (cosetNormalizerPerm ((fun v : G => u * v) '' (U : Set G))).range ∧
        ∀ g ∈ translationGroup (Additive U), (cosetCoordinates U u).permCongr g.toEquiv ∈
          (cosetNormalizerPerm ((fun v : G => u * v) '' (U : Set G))).range) ∨
      (Nat.card U = 8 ∧ (∃ b : ((fun v : G => u * v) '' (U : Set G)) ≃ Omega (ZMod 7),
        (fun σ : Equiv.Perm ((fun v : G => u * v) '' (U : Set G)) => b.permCongr σ) ''
            ((cosetNormalizerPerm ((fun v : G => u * v) '' (U : Set G))).range :
              Set (Equiv.Perm ((fun v : G => u * v) '' (U : Set G)))) =
          (coordinateG (ZMod 7) : Set (Equiv.Perm (Omega (ZMod 7))))) ∧
        (coordinatePSLAction (ZMod 7)).range = coordinateG (ZMod 7)) := by
  classical
  let Γ := φ.range
  let T := X.map (AffineEquiv.linearHom.comp φ)
  let f := (cosetAffinePerm U u).comp (linearToAffineHom (Additive U))
  have hf : Function.Injective f :=
    (cosetAffinePerm_injective U u).comp (linearToAffineHom_injective (Additive U))
  have hrange := cosetNormalizerPerm_range_eq_map φ hφ
  have hX0 : ∀ x ∈ X, φ x 0 = 0 := fun x hx => (affine_apply_zero_eq_zero_iff φ hφ x).mpr (hXu x hx)
  have hTC : T.map f = X.map (cosetNormalizerPerm ((fun v : G => u * v) '' (U : Set G))) := by
    rw [Subgroup.map_map]
    refine map_eq_map_of_eqOn X fun x hx => ?_
    change cosetAffinePerm U u (φ x).linear.toAffineEquiv = _
    rw [← eq_toAffineEquiv_linear (hX0 x hx), ← cosetAffinePerm_comp_eq φ hφ]
    rfl
  have happly : ∀ (t : Additive U ≃ₗ[ZMod 2] Additive U) (v : Additive U),
      f t (cosetCoordinates U u v) = cosetCoordinates U u (t v) := fun t v =>
    cosetAffinePerm_apply_coordinates U u t.toAffineEquiv v
  have : Finite (Additive U) := inferInstanceAs (Finite U)
  have : Module.Finite (ZMod 2) (Additive U) := Module.Finite.of_finite
  have hV : finrank (ZMod 2) (Additive U) = e := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive U)
    rw [Nat.card_zmod, show Nat.card (Additive U) = Nat.card U from rfl, hcard] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  have htransΓ : ∀ v w : Additive U, ∃ g ∈ Γ, g v = w := by
    intro v w
    obtain ⟨n, hn, hnvw⟩ := htrans _ (cosetCoordinates U u v).2 _ (cosetCoordinates U u w).2
    refine ⟨φ ⟨n, hn⟩, ⟨⟨n, hn⟩, rfl⟩, ?_⟩
    have h := hφ ⟨n, hn⟩ (Additive.toMul v)
    rw [← cosetCoordinates_apply, ← cosetCoordinates_apply] at h
    change n * _ * n⁻¹ = _ at h
    rw [hnvw] at h
    exact (cosetCoordinates U u).injective (Subtype.ext h.symm)
  have hTΓ : T ≤ zeroStabilizer Γ := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨φ x, ⟨⟨x, rfl⟩, hX0 x hx⟩, rfl⟩
  have hconj : ∀ g ∈ zeroStabilizer Γ, ∀ t ∈ T, g * t * g⁻¹ ∈ T := by
    rintro _ ⟨_, ⟨⟨m, rfl⟩, hm0⟩, rfl⟩ _ ⟨x, hx, rfl⟩
    have hmu := (affine_apply_zero_eq_zero_iff φ hφ m).mp hm0
    exact ⟨m * x * m⁻¹, hXn m hmu x hx, by simp only [MonoidHom.comp_apply, map_mul, map_inv]⟩
  have hTn : (T.subgroupOf (zeroStabilizer Γ)).Normal :=
    (Subgroup.normal_subgroupOf_iff hTΓ).mpr fun t g ht hg => hconj g hg t ht
  have : IsCyclic (T.map f) := hTC ▸ hcyc
  have hTcyc : IsCyclic T := isCyclic_of_map_of_injective hf T
  have hTreg : ∀ v w : Additive U, v ≠ 0 → w ≠ 0 →
      ∃! t : T, (t : Additive U ≃ₗ[ZMod 2] Additive U) v = w := by
    intro v w hv hw
    have h := hreg (cosetCoordinates U u v) (cosetCoordinates U u w)
      (fun h => hv ((cosetCoordinates_eq_iff U u v).mp h))
      (fun h => hw ((cosetCoordinates_eq_iff U u w).mp h))
    rw [← hTC] at h
    refine existsUnique_of_map_of_injective hf T
      (p := fun σ : Equiv.Perm ((fun v : G => u * v) '' (U : Set G)) =>
        σ (cosetCoordinates U u v) = cosetCoordinates U u w)
      (q := fun t : Additive U ≃ₗ[ZMod 2] Additive U => t v = w) (fun t => ?_) h
    rw [happly]
    exact (cosetCoordinates U u).injective.eq_iff
  rcases (binary_affine_normal_singer_solvable_or_projective_seven he hV Γ htransΓ T hTΓ hTn
    hTcyc hTreg).or with ⟨hA, hsolv, -⟩ | ⟨rfl, -, -, ⟨β, hβ⟩, hPSL⟩
  · left
    rw [hrange]
    refine ⟨Group.isSolvable_of_surjective ((cosetAffinePerm U u).subgroupMap_surjective Γ),
      fun g hg => ⟨g, hA hg, rfl⟩⟩
  · right
    refine ⟨by rw [hcard]; rfl, ⟨(cosetCoordinates U u).symm.trans β, ?_⟩, hPSL⟩
    rw [hrange, Subgroup.coe_map, Set.image_image, ← hβ]
    refine Set.image_congr fun g _ => Equiv.ext fun x => ?_
    simp only [Equiv.permCongr_apply, cosetAffinePerm_apply, Equiv.symm_trans_apply,
      Equiv.symm_symm, Equiv.trans_apply, Equiv.symm_apply_apply]

end CFSG.ProperTwoGeneratedCore.RankOnePair
