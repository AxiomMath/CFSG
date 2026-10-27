module

public import CFSG.LieType.Chevalley.E7Three.Multiplicity
public import CFSG.LieType.Chevalley.E7Three.CoordinateActions

public noncomputable section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.FourCube

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SectionRank
  CFSG.RankThree.PartOne.KA5L
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Chevalley.E7Three.Weyl CFSG.LieType.Chevalley.E7Three.Cube
  CFSG.LieType.Chevalley.E7Three.Multiplicity
  CFSG.LieType.Chevalley.E7Three.CoordinateActions

abbrev Four := D × Multiplicative (ZMod 3)

variable {K : Type} [Field K] [CharP K 2]

theorem scalar_multiplicity_commute (ζ : Kˣ) :
    Commute (scalarWord ζ) (multiplicityWord ζ) := by
  rw [scalarWord, multiplicityWord]
  refine Commute.list_prod_left _ _ ?_
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  refine Commute.list_prod_right _ _ ?_
  intro y hy
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hy
  exact torusElement_commute i j _ _

theorem paired_multiplicity_commute (ζ : Kˣ) :
    Commute (pairedWord ζ) (multiplicityWord ζ) := by
  rw [pairedWord, multiplicityWord]
  refine Commute.list_prod_left _ _ ?_
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  refine Commute.list_prod_right _ _ ?_
  intro y hy
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hy
  exact torusElement_commute i j _ _

theorem cyclic_multiplicity_commute (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    Commute (cyclic (K := K)) (multiplicityWord ζ) := by
  change cyclic * multiplicityWord ζ = multiplicityWord ζ * cyclic
  apply Subtype.ext
  change (cyclic (K := K) : ModGL .E7 K) * (multiplicityWord ζ : ModGL .E7 K) =
    (multiplicityWord ζ : ModGL .E7 K) * (cyclic (K := K) : ModGL .E7 K)
  rw [multiplicityWord_val ζ hζ]
  change canonicalRep (coxeterSystem .E7) K gamma * rootDiagUnit .E7 (cubeChar ζ multiplicityExp) =
    rootDiagUnit .E7 (cubeChar ζ multiplicityExp) * canonicalRep (coxeterSystem .E7) K gamma
  exact mul_inv_eq_iff_eq_mul.mp (gamma_conj_multiplicity ζ hζ)

@[expose] def fourthHom (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    Multiplicative (ZMod 3) →* adjointGroup .E7 K :=
  zmodPowHom (multiplicityWord ζ) (multiplicityWord_pow_three ζ hζ)

theorem cube_fourth_commute (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (f : D)
    (t : Multiplicative (ZMod 3)) : Commute (cubeHom ζ hζ f) (fourthHom ζ hζ t) := by
  rw [cubeHom_apply]
  change Commute
    (scalarWord ζ ^ (Multiplicative.toAdd (f 0)).val *
      pairedWord ζ ^ (Multiplicative.toAdd (f 1)).val *
      (cyclic (K := K)) ^ (Multiplicative.toAdd (f 2)).val)
    (multiplicityWord ζ ^ (Multiplicative.toAdd t).val)
  exact (((scalar_multiplicity_commute ζ).pow_pow _ _).mul_left
    ((paired_multiplicity_commute ζ).pow_pow _ _)).mul_left
      ((cyclic_multiplicity_commute ζ hζ).pow_pow _ _)

@[expose] def fourCubeHom (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    Four →* adjointGroup .E7 K :=
  MonoidHom.noncommCoprod (cubeHom ζ hζ) (fourthHom ζ hζ) (cube_fourth_commute ζ hζ)

theorem fourCubeHom_apply (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (p : Four) :
    fourCubeHom ζ hζ p = cubeHom ζ hζ p.1 *
      multiplicityWord ζ ^ (Multiplicative.toAdd p.2).val := rfl

theorem fourCubeHom_inl (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (f : D) :
    fourCubeHom ζ hζ (f, 1) = cubeHom ζ hζ f := by
  rw [fourCubeHom_apply]
  simp

theorem vals_eq_zero_of_fourCubeHom_eq_one (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 3)
    (p : Four) (hp : fourCubeHom ζ hζ.pow_eq_one p = 1) :
    (Multiplicative.toAdd (p.1 0)).val = 0 ∧
      (Multiplicative.toAdd (p.1 1)).val = 0 ∧
      (Multiplicative.toAdd (p.1 2)).val = 0 ∧ (Multiplicative.toAdd p.2).val = 0 := by
  let a := (Multiplicative.toAdd (p.1 0)).val
  let b := (Multiplicative.toAdd (p.1 1)).val
  let c := (Multiplicative.toAdd (p.1 2)).val
  let d := (Multiplicative.toAdd p.2).val
  have he : scalarWord ζ ^ a * pairedWord ζ ^ b * (cyclic (K := K)) ^ c *
      multiplicityWord ζ ^ d = 1 := by
    simpa only [fourCubeHom_apply, cubeHom_apply] using hp
  have hi : (cyclic (K := K)) ^ c =
      (scalarWord ζ ^ a * pairedWord ζ ^ b)⁻¹ * (multiplicityWord ζ ^ d)⁻¹ := by
    calc
      (cyclic (K := K)) ^ c = (scalarWord ζ ^ a * pairedWord ζ ^ b)⁻¹ *
          (scalarWord ζ ^ a * pairedWord ζ ^ b * (cyclic (K := K)) ^ c *
            multiplicityWord ζ ^ d) * (multiplicityWord ζ ^ d)⁻¹ := by group
      _ = _ := by rw [he]; group
  let S := (adjointGroup .E7 K).subtype
  have hi' : (cyclic (K := K) : ModGL .E7 K) ^ c =
      ((scalarWord ζ : ModGL .E7 K) ^ a * (pairedWord ζ : ModGL .E7 K) ^ b)⁻¹ *
        ((multiplicityWord ζ : ModGL .E7 K) ^ d)⁻¹ := by
    simpa only [S, map_pow, map_mul, map_inv, Subgroup.subtype_apply] using congrArg S hi
  have hcT : ((cyclic (K := K)) ^ c : ModGL .E7 K) ∈ torusGroup .E7 K := by
    rw [hi']
    exact (torusGroup .E7 K).mul_mem
      ((torusGroup .E7 K).inv_mem ((torusGroup .E7 K).mul_mem
        ((torusGroup .E7 K).pow_mem (scalarWord_mem_torusGroup ζ) a)
        ((torusGroup .E7 K).pow_mem (pairedWord_mem_torusGroup ζ) b)))
      ((torusGroup .E7 K).inv_mem
        ((torusGroup .E7 K).pow_mem (multiplicityWord_mem_torusGroup ζ) d))
  have hcd : 3 ∣ c := three_dvd_of_cyclic_pow_mem_torusGroup c hcT
  have hc_lt : c < 3 := ZMod.val_lt _
  have hc0 : c = 0 := by
    obtain ⟨t, ht⟩ := hcd
    omega
  have he' : scalarWord ζ ^ a * pairedWord ζ ^ b * multiplicityWord ζ ^ d = 1 := by
    simpa only [hc0, pow_zero, mul_one] using he
  have hcoords : cubeChar ζ scalarExp ^ a * cubeChar ζ pairedExp ^ b *
      cubeChar ζ multiplicityExp ^ d = 1 := by
    apply rootDiagUnit_injective
    change rootDiagUnitHom .E7 K
      (cubeChar ζ scalarExp ^ a * cubeChar ζ pairedExp ^ b * cubeChar ζ multiplicityExp ^ d) =
        rootDiagUnitHom .E7 K 1
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, map_one]
    have e := congrArg S he'
    simp only [S, map_mul, map_pow, map_one, Subgroup.subtype_apply] at e
    rw [scalarWord_val ζ hζ.pow_eq_one, pairedWord_val ζ hζ.pow_eq_one,
      multiplicityWord_val ζ hζ.pow_eq_one] at e
    exact e
  have hbpow : (ζ ^ 2) ^ b = 1 := by
    simpa [cubeChar, scalarExp, pairedExp, multiplicityExp] using
      congrFun hcoords (0 : Fin Tag.E7.rank)
  have hbd : 3 ∣ 2 * b := hζ.dvd_of_pow_eq_one (2 * b) (by
    simpa only [← pow_mul] using hbpow)
  have hb_lt : b < 3 := ZMod.val_lt _
  have hb0 : b = 0 := by
    obtain ⟨t, ht⟩ := hbd
    omega
  have hdpow : (ζ ^ 2) ^ d = 1 := by
    simpa [cubeChar, scalarExp, pairedExp, multiplicityExp, hb0] using
      congrFun hcoords (4 : Fin Tag.E7.rank)
  have hdd : 3 ∣ 2 * d := hζ.dvd_of_pow_eq_one (2 * d) (by
    simpa only [← pow_mul] using hdpow)
  have hd_lt : d < 3 := ZMod.val_lt _
  have hd0 : d = 0 := by
    obtain ⟨t, ht⟩ := hdd
    omega
  have hapow : ζ ^ a = 1 := by
    simpa [cubeChar, scalarExp, pairedExp, multiplicityExp, hb0, hd0] using
      congrFun hcoords (2 : Fin Tag.E7.rank)
  have had : 3 ∣ a := hζ.dvd_of_pow_eq_one a hapow
  have ha_lt : a < 3 := ZMod.val_lt _
  have ha0 : a = 0 := by
    obtain ⟨t, ht⟩ := had
    omega
  exact ⟨ha0, hb0, hc0, hd0⟩

theorem eq_one_of_fourCubeHom_eq_one (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 3)
    (p : Four) (hp : fourCubeHom ζ hζ.pow_eq_one p = 1) : p = 1 := by
  obtain ⟨h0, h1, h2, h3⟩ := vals_eq_zero_of_fourCubeHom_eq_one ζ hζ p hp
  apply Prod.ext
  · funext i
    fin_cases i
    · apply Multiplicative.toAdd.injective
      change Multiplicative.toAdd (p.1 0) = 0
      exact (ZMod.val_eq_zero _).1 h0
    · apply Multiplicative.toAdd.injective
      change Multiplicative.toAdd (p.1 1) = 0
      exact (ZMod.val_eq_zero _).1 h1
    · apply Multiplicative.toAdd.injective
      change Multiplicative.toAdd (p.1 2) = 0
      exact (ZMod.val_eq_zero _).1 h2
  · apply Multiplicative.toAdd.injective
    change Multiplicative.toAdd p.2 = 0
    exact (ZMod.val_eq_zero _).1 h3

theorem fourCubeHom_injective (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 3) :
    Function.Injective (fourCubeHom ζ hζ.pow_eq_one) := by
  exact (injective_iff_map_eq_one (fourCubeHom ζ hζ.pow_eq_one)).2
    (eq_one_of_fourCubeHom_eq_one ζ hζ)

theorem cube_range_le_fourCube_range (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    (cubeHom ζ hζ).range ≤ (fourCubeHom ζ hζ).range := by
  rintro x ⟨f, rfl⟩
  exact ⟨(f, 1), fourCubeHom_inl ζ hζ f⟩

end CFSG.LieType.Chevalley.E7Three.FourCube
