module

public import CFSG.LieType.Chevalley.E7Three.CentralizerBaseChange
public import CFSG.LieType.AlgebraicGroups.SLFrobeniusFixedField
public import CFSG.LieType.Chevalley.E7Three.CentralizerComponent

public noncomputable section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.Centralizer

open Matrix CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne.KA5L
  CFSG.LocalAnalysis.UniquenessCase.UCK.Insp CFSG.LieType.AlgebraicGroups
open scoped MatrixGroups Pointwise

variable {k : Type} [Field k] [CharP k 2]

theorem cubeSL2_injective_char_two : Function.Injective (cubeSL2 k) := by
  let L := AlgebraicClosure k
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap k L).injective 2
  have : NeZero (3 : L) := ⟨by
    intro h
    have hd : (2 : ℕ) ∣ 3 := (CharP.cast_eq_zero_iff L 2 3).1 h
    norm_num at hd⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.prim (M := L) (n := 3)
  obtain ⟨ζ, rfl⟩ := hz.isUnit (by decide)
  have hζ : IsPrimitiveRoot ζ 3 := IsPrimitiveRoot.coe_units_iff.1 hz
  intro x y hxy
  have h := congrArg (baseChangeGL (algebraMap k L)) hxy
  rw [baseChangeGL_cubeSL2, baseChangeGL_cubeSL2] at h
  have hmap := cubeSL2_injective hζ h
  apply Subtype.ext
  ext i j
  apply (algebraMap k L).injective
  exact congrArg (fun z : SL(2, L) => z i j) hmap

variable [IsAlgClosed k]

section FullCentralizer

theorem cubeCent_fixed_product_of_action {ζ : kˣ} (hζ : IsPrimitiveRoot ζ 3)
    (Φ : SL(2, k) →* SL(2, k)) (Ψ : ModGL .E7 k →* ModGL .E7 k)
    (hΔ : ∀ x : SL(2, k), Ψ (cubeSL2 k x) = cubeSL2 k (Φ x))
    (hE : ∀ e ∈ cubeE ζ hζ.pow_eq_one, Ψ e = e) :
    Nonempty ((Φ.eqLocus (MonoidHom.id _) × cubeE ζ hζ.pow_eq_one) ≃*
      ↥(cubeCent ζ hζ.pow_eq_one ⊓ Ψ.eqLocus (MonoidHom.id _))) := by
  let E := cubeE ζ hζ.pow_eq_one
  let C := Φ.eqLocus (MonoidHom.id _)
  let D := cubeCent ζ hζ.pow_eq_one ⊓ Ψ.eqLocus (MonoidHom.id _)
  have hc : ∀ (x : SL(2, k)) (e : E), Commute (cubeSL2 k x) (E.subtype e) := by
    intro x e
    exact ((Subgroup.mem_centralizer_iff.1
      (range_cubeSL2_le_cubeCent ζ hζ.pow_eq_one ⟨x, rfl⟩).2) e e.2).symm
  let s := (cubeSL2 k).noncommCoprod E.subtype hc
  have hs : Function.Injective s := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨cubeSL2_injective_char_two, Subtype.val_injective, ?_⟩
    rw [Subgroup.range_subtype, disjoint_iff]
    exact range_cubeSL2_inf_cubeE hζ
  let t0 : C × E →* ModGL .E7 k :=
    s.comp (C.subtype.prodMap (MonoidHom.id E))
  have hm : ∀ z, t0 z ∈ D := by
    intro z
    constructor
    · exact (cubeCent ζ hζ.pow_eq_one).mul_mem
        (range_cubeSL2_le_cubeCent ζ hζ.pow_eq_one ⟨z.1, rfl⟩)
        (cubeE_le_cubeCent ζ hζ.pow_eq_one z.2.2)
    · change Ψ (cubeSL2 k z.1 * (z.2 : ModGL .E7 k)) =
        cubeSL2 k z.1 * (z.2 : ModGL .E7 k)
      rw [map_mul, hΔ, hE _ z.2.2,
        show Φ (z.1 : SL(2, k)) = z.1 from z.1.property]
  let t : C × E →* D := t0.codRestrict D hm
  have ht : Function.Bijective t := by
    constructor
    · intro x y hxy
      have hxy' := congrArg (fun z : D => (z : ModGL .E7 k)) hxy
      change s ((x.1 : SL(2, k)), x.2) = s ((y.1 : SL(2, k)), y.2) at hxy'
      have h := hs hxy'
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun z : SL(2, k) × E => z.1) h
      · exact congrArg (fun z : SL(2, k) × E => z.2) h
    · intro y
      have hy : (y : ModGL .E7 k) ∈ ((cubeSL2 k).range : Set (ModGL .E7 k)) *
          (E : Set (ModGL .E7 k)) := by
        rw [← coe_cubeCent_eq_mul hζ]
        exact y.property.1
      obtain ⟨u, hu, e, he, hue⟩ := hy
      obtain ⟨x, hx⟩ := hu
      have hfixed := y.property.2
      change Ψ (y : ModGL .E7 k) = y at hfixed
      rw [← hue, ← hx, map_mul, hΔ, hE _ he] at hfixed
      have hxfix : Φ x = x := cubeSL2_injective_char_two (mul_right_cancel hfixed)
      refine ⟨(⟨x, hxfix⟩, ⟨e, he⟩), Subtype.ext ?_⟩
      change cubeSL2 k x * e = (y : ModGL .E7 k)
      rw [hx]
      exact hue
  exact ⟨MulEquiv.ofBijective t ht⟩

theorem cubeCent_frobenius_fixed_field_extension_of_action
    {F : Type} [Field F] [Finite F] [Algebra F k]
    (f m : ℕ) (hf : 1 ≤ f) (hm : 1 ≤ m) (hF : Nat.card F = 2 ^ f)
    {ζ : kˣ} (hζ : IsPrimitiveRoot ζ 3) (a : SL(2, k))
    (Ψ : ModGL .E7 k →* ModGL .E7 k)
    (hΔ : ∀ x : SL(2, k), Ψ (cubeSL2 k x) = cubeSL2 k
      (a * SpecialLinearGroup.map (iterateFrobenius k 2 (f * m)) x * a⁻¹))
    (hE : ∀ e ∈ cubeE ζ hζ.pow_eq_one, Ψ e = e) :
    let K := (iterateFrobenius k 2 (f * m)).eqLocusField (RingHom.id k)
    ∃ ρ : F →+* K, K.subtype.comp ρ = algebraMap F k ∧
      Nat.card K = Nat.card F ^ m ∧
      Nonempty ((SL(2, K) × cubeE ζ hζ.pow_eq_one) ≃*
        ↥(cubeCent ζ hζ.pow_eq_one ⊓ Ψ.eqLocus (MonoidHom.id _))) := by
  intro K
  let Φ := (conjSLn (SpecialLinearGroup.toGL a)).comp
    (SpecialLinearGroup.map (iterateFrobenius k 2 (f * m)))
  have hΔ' : ∀ x : SL(2, k), Ψ (cubeSL2 k x) = cubeSL2 k (Φ x) := hΔ
  obtain ⟨ρ, hρ, hcard, ⟨E⟩⟩ :=
    sl_inner_frobenius_fixed_field_extension 2 f m hf hm hF (SpecialLinearGroup.toGL a)
  obtain ⟨E'⟩ := cubeCent_fixed_product_of_action hζ Φ Ψ hΔ' hE
  exact ⟨ρ, hρ, hcard, ⟨(MulEquiv.prodCongr E (MulEquiv.refl _)).trans E'⟩⟩

end FullCentralizer

end CFSG.LieType.Chevalley.E7Three.Centralizer
