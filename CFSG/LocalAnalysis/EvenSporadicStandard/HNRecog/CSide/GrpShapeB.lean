module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.A5CentBase

@[expose] public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
open scoped Classical

private def gsb_centCard (x : alternatingGroup (Fin 5)) : ℕ :=
  ((Finset.univ : Finset (alternatingGroup (Fin 5))).filter fun y => y * x = x * y).card

private theorem gsb_centCard_eq_five :
    ∀ x : alternatingGroup (Fin 5), x ^ 5 = 1 → x ≠ 1 → gsb_centCard x = 5 := by
  decide +kernel

private theorem gsb_three_conj :
    ∀ x y : alternatingGroup (Fin 5), x ^ 3 = 1 → x ≠ 1 → y ^ 3 = 1 → y ≠ 1 →
      ∃ c : alternatingGroup (Fin 5), c * x * c⁻¹ = y := by
  decide +kernel

private theorem gsb_card_centralizer_five {x : alternatingGroup (Fin 5)}
    (hx5 : x ^ 5 = 1) (hx1 : x ≠ 1) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) = 5 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h := gsb_centCard_eq_five x hx5 hx1
  rw [gsb_centCard] at h
  have hfilter : (Finset.univ.filter fun y : alternatingGroup (Fin 5) =>
        y ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) =
      (Finset.univ.filter fun y : alternatingGroup (Fin 5) => y * x = x * y) := by
    ext y
    simp [Subgroup.mem_centralizer_singleton_iff]
  rw [hfilter]
  exact h

private def gsb_threeCycle : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2,
    Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
      (show Equiv.Perm.IsSwap (Equiv.swap (0 : Fin 5) 1) from ⟨0, 1, by decide, rfl⟩)
      (show Equiv.Perm.IsSwap (Equiv.swap (1 : Fin 5) 2) from ⟨1, 2, by decide, rfl⟩)⟩

private def gsb_fiveCycle : alternatingGroup (Fin 5) :=
  ⟨(Equiv.swap 0 1 * Equiv.swap 1 2) * (Equiv.swap 2 3 * Equiv.swap 3 4), by
    apply Subgroup.mul_mem
    · exact Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
        (show Equiv.Perm.IsSwap (Equiv.swap (0 : Fin 5) 1) from ⟨0, 1, by decide, rfl⟩)
        (show Equiv.Perm.IsSwap (Equiv.swap (1 : Fin 5) 2) from ⟨1, 2, by decide, rfl⟩)
    · exact Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
        (show Equiv.Perm.IsSwap (Equiv.swap (2 : Fin 5) 3) from ⟨2, 3, by decide, rfl⟩)
        (show Equiv.Perm.IsSwap (Equiv.swap (3 : Fin 5) 4) from ⟨3, 4, by decide, rfl⟩)⟩

private theorem gsb_five_not_conj :
    ¬ IsConj gsb_fiveCycle (gsb_fiveCycle ^ 2) := by
  rw [isConj_iff]
  decide +kernel

private theorem gsb_sigma_ne_one :
    (Multiplicative.ofAdd (1 : ZMod 2) : Multiplicative (ZMod 2)) ≠ 1 := by
  decide

private theorem gsb_sigma_mul_self :
    (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd (1 : ZMod 2) = 1 := by
  decide

private theorem gsb_coord_cases (q : Multiplicative (ZMod 2)) :
    q = 1 ∨ q = Multiplicative.ofAdd 1 := by
  rcases (show ∀ e : ZMod 2, e = 0 ∨ e = 1 by decide) (Multiplicative.toAdd q) with h | h
  · left
    rw [← ofAdd_toAdd q, h]
    rfl
  · right
    rw [← ofAdd_toAdd q, h]

private abbrev gsb_swap : A5WrTwo := ⟨1, Multiplicative.ofAdd (1 : ZMod 2)⟩

private theorem gsb_swap_mul_self : gsb_swap * gsb_swap = 1 := by
  apply RegularWreathProduct.ext
  · funext q
    rcases gsb_coord_cases q with rfl | rfl <;>
      simp [gsb_swap, RegularWreathProduct.mul_def, gsb_sigma_mul_self]
  · simp [gsb_swap, RegularWreathProduct.mul_def, gsb_sigma_mul_self]

private theorem gsb_baseEmb_right (p : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) :
    (A5WrTwo.baseEmb p).right = 1 := by
  have hmem : A5WrTwo.baseEmb p ∈ A5WrTwo.baseEmb.range := MonoidHom.mem_range.mpr ⟨p, rfl⟩
  rw [A5WrTwo.range_baseEmb, A5WrTwo.commutator_eq_ker] at hmem
  exact hmem

private theorem gsb_baseEmb_conj (p q : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) :
    A5WrTwo.baseEmb p * A5WrTwo.baseEmb q * (A5WrTwo.baseEmb p)⁻¹ =
      A5WrTwo.baseEmb (p * q * p⁻¹) := by
  rw [← map_mul, ← map_inv, ← map_mul]

private theorem gsb_baseEmb_mul_swap_conj (g h x y : alternatingGroup (Fin 5)) :
    (A5WrTwo.baseEmb (g, h) * gsb_swap) * A5WrTwo.baseEmb (x, y) *
        (A5WrTwo.baseEmb (g, h) * gsb_swap)⁻¹ =
      A5WrTwo.baseEmb (g * y * g⁻¹, h * x * h⁻¹) := by
  have h1 : (A5WrTwo.baseEmb (g, h) * gsb_swap) * A5WrTwo.baseEmb (x, y) *
        (A5WrTwo.baseEmb (g, h) * gsb_swap)⁻¹ =
      A5WrTwo.baseEmb (g, h) * (gsb_swap * A5WrTwo.baseEmb (x, y) * gsb_swap⁻¹) *
        (A5WrTwo.baseEmb (g, h))⁻¹ := by
    group
  rw [h1, A5WrTwo.swap_mul_baseEmb_mul_inv]
  exact gsb_baseEmb_conj (g, h) (y, x)

private theorem gsb_exists_baseEmb_mul_swap_of_right_eq (g : A5WrTwo)
    (hg : g.right = Multiplicative.ofAdd (1 : ZMod 2)) :
    ∃ p : alternatingGroup (Fin 5) × alternatingGroup (Fin 5),
      g = A5WrTwo.baseEmb p * gsb_swap := by
  have hgs : (g * gsb_swap).right = 1 := by
    rw [RegularWreathProduct.mul_right, hg]
    simpa [gsb_swap] using gsb_sigma_mul_self
  have hmem : g * gsb_swap ∈ A5WrTwo.baseEmb.range := by
    rw [A5WrTwo.range_baseEmb, A5WrTwo.commutator_eq_ker]
    exact hgs
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hmem
  refine ⟨p, ?_⟩
  calc g = (g * gsb_swap) * gsb_swap := by rw [mul_assoc, gsb_swap_mul_self, mul_one]
    _ = A5WrTwo.baseEmb p * gsb_swap := by rw [← hp]

theorem cSide_shape_nonconj {x y : alternatingGroup (Fin 5)} (hx : orderOf x = 5)
    (hy : orderOf y = 5) (hxy : ¬ IsConj x y) :
    IsShapeZpTimesZp 5 ↥(Subgroup.centralizer ({A5WrTwo.baseEmb (x, y)} : Set A5WrTwo)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Finite A5WrTwo := inferInstance
  obtain ⟨hx5, hx1⟩ := (orderOf_eq_prime_iff (p := 5) (x := x)).mp hx
  obtain ⟨hy5, hy1⟩ := (orderOf_eq_prime_iff (p := 5) (x := y)).mp hy
  have hCx : Nat.card ↥(Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) = 5 :=
    gsb_card_centralizer_five hx5 hx1
  have hCy : Nat.card ↥(Subgroup.centralizer ({y} : Set (alternatingGroup (Fin 5)))) = 5 :=
    gsb_card_centralizer_five hy5 hy1
  let Cx : Subgroup (alternatingGroup (Fin 5)) :=
    Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))
  let Cy : Subgroup (alternatingGroup (Fin 5)) :=
    Subgroup.centralizer ({y} : Set (alternatingGroup (Fin 5)))
  let M : Subgroup A5WrTwo := (Cx.prod Cy).map A5WrTwo.baseEmb
  have hle : M ≤ Subgroup.centralizer ({A5WrTwo.baseEmb (x, y)} : Set A5WrTwo) := by
    intro w hw
    dsimp only [M] at hw
    rw [Subgroup.mem_map] at hw
    obtain ⟨p, hp, rfl⟩ := hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [Subgroup.mem_prod] at hp
    have hp1 : p.1 * x = x * p.1 := Subgroup.mem_centralizer_singleton_iff.mp hp.1
    have hp2 : p.2 * y = y * p.2 := Subgroup.mem_centralizer_singleton_iff.mp hp.2
    calc A5WrTwo.baseEmb p * A5WrTwo.baseEmb (x, y)
        = A5WrTwo.baseEmb (p * (x, y)) := (map_mul A5WrTwo.baseEmb p (x, y)).symm
      _ = A5WrTwo.baseEmb ((x, y) * p) :=
            congrArg A5WrTwo.baseEmb (Prod.ext hp1 hp2)
      _ = A5WrTwo.baseEmb (x, y) * A5WrTwo.baseEmb p := map_mul A5WrTwo.baseEmb (x, y) p
  have hCbase : Nat.card ↥(Subgroup.centralizer
      ({A5WrTwo.baseEmb (x, y)} : Set A5WrTwo)) = 25 := by
    rw [card_centralizer_baseEmb_of_not_isConj hxy, hCx, hCy]
  have hMcard : Nat.card ↥M = 25 := by
    dsimp only [M]
    rw [Subgroup.card_map_of_injective A5WrTwo.baseEmb_injective,
      Nat.card_congr (Subgroup.prodEquiv Cx Cy).toEquiv, Nat.card_prod]
    dsimp only [Cx, Cy]
    rw [hCx, hCy]
  have hM : M = Subgroup.centralizer ({A5WrTwo.baseEmb (x, y)} : Set A5WrTwo) :=
    Subgroup.eq_of_le_of_card_ge hle (by simp [hCbase, hMcard])
  have hZ5 : Nat.card (Z 5) = 5 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have eX : ↥Cx ≃* Z 5 := mulEquivOfPrimeCardEq hCx hZ5
  have eY : ↥Cy ≃* Z 5 := mulEquivOfPrimeCardEq hCy hZ5
  refine ⟨(MulEquiv.subgroupCongr hM.symm).trans ?_⟩
  exact ((Subgroup.equivMapOfInjective (Cx.prod Cy) A5WrTwo.baseEmb
      A5WrTwo.baseEmb_injective).symm).trans
    ((Subgroup.prodEquiv Cx Cy).trans (MulEquiv.prodCongr eX eY))

theorem cSide_exists_outer_cent_iff (x y : alternatingGroup (Fin 5)) :
    (∃ w : A5WrTwo, w ∉ commutator A5WrTwo ∧
        w * A5WrTwo.baseEmb (x, y) = A5WrTwo.baseEmb (x, y) * w) ↔ IsConj x y := by
  constructor
  · rintro ⟨w, hw, hcomm⟩
    have hwne : w.right ≠ 1 := by
      intro h
      exact hw (by rw [A5WrTwo.commutator_eq_ker]; exact h)
    rcases gsb_coord_cases w.right with h | h
    · exact absurd h hwne
    · obtain ⟨p, hp⟩ := gsb_exists_baseEmb_mul_swap_of_right_eq w h
      have hconj : w * A5WrTwo.baseEmb (x, y) * w⁻¹ = A5WrTwo.baseEmb (x, y) := by
        rw [hcomm]
        group
      rw [hp, gsb_baseEmb_mul_swap_conj p.1 p.2 x y] at hconj
      have hprod : (p.1 * y * p.1⁻¹, p.2 * x * p.2⁻¹) = (x, y) :=
        A5WrTwo.baseEmb_injective hconj
      exact isConj_iff.mpr ⟨p.2, congrArg Prod.snd hprod⟩
  · intro hxy
    obtain ⟨c, hc⟩ := isConj_iff.mp hxy
    refine ⟨A5WrTwo.baseEmb (c⁻¹, c) * gsb_swap, ?_, ?_⟩
    · rw [A5WrTwo.commutator_eq_ker]
      intro h
      have hright : (A5WrTwo.baseEmb (c⁻¹, c) * gsb_swap).right =
          Multiplicative.ofAdd (1 : ZMod 2) := by
        rw [RegularWreathProduct.mul_right, gsb_baseEmb_right, one_mul]
      have h1 : (A5WrTwo.baseEmb (c⁻¹, c) * gsb_swap).right = 1 := MonoidHom.mem_ker.mp h
      rw [hright] at h1
      exact gsb_sigma_ne_one h1
    · have hconj : (A5WrTwo.baseEmb (c⁻¹, c) * gsb_swap) * A5WrTwo.baseEmb (x, y) *
          (A5WrTwo.baseEmb (c⁻¹, c) * gsb_swap)⁻¹ = A5WrTwo.baseEmb (x, y) := by
        rw [gsb_baseEmb_mul_swap_conj]
        congr 1
        exact Prod.ext (by rw [← hc]; group) hc
      calc (A5WrTwo.baseEmb (c⁻¹, c) * gsb_swap) * A5WrTwo.baseEmb (x, y)
          = ((A5WrTwo.baseEmb (c⁻¹, c) * gsb_swap) * A5WrTwo.baseEmb (x, y) *
              (A5WrTwo.baseEmb (c⁻¹, c) * gsb_swap)⁻¹) *
              (A5WrTwo.baseEmb (c⁻¹, c) * gsb_swap) := by group
        _ = A5WrTwo.baseEmb (x, y) * (A5WrTwo.baseEmb (c⁻¹, c) * gsb_swap) := by rw [hconj]

theorem cSide_isConj_of_order_three {x y : alternatingGroup (Fin 5)} (hx : orderOf x = 3)
    (hy : orderOf y = 3) : IsConj x y := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨hx3, hx1⟩ := (orderOf_eq_prime_iff (p := 3) (x := x)).mp hx
  obtain ⟨hy3, hy1⟩ := (orderOf_eq_prime_iff (p := 3) (x := y)).mp hy
  exact isConj_iff.mpr (gsb_three_conj x y hx3 hx1 hy3 hy1)

theorem cSide_exists_orderOf {p : ℕ} (hp : p = 3 ∨ p = 5) :
    ∃ x : alternatingGroup (Fin 5), orderOf x = p := by
  rcases hp with rfl | rfl
  · refine ⟨gsb_threeCycle, ?_⟩
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime (by decide) (by decide)
  · refine ⟨gsb_fiveCycle, ?_⟩
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact orderOf_eq_prime (by decide) (by decide)

theorem cSide_exists_nonconj_five :
    ∃ x y : alternatingGroup (Fin 5), orderOf x = 5 ∧ orderOf y = 5 ∧ ¬ IsConj x y := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hx : orderOf gsb_fiveCycle = 5 := orderOf_eq_prime (by decide) (by decide)
  have hy : orderOf (gsb_fiveCycle ^ 2) = 5 := by
    have hcop : (orderOf gsb_fiveCycle).Coprime 2 := by rw [hx]; norm_num
    rw [hcop.orderOf_pow, hx]
  exact ⟨gsb_fiveCycle, gsb_fiveCycle ^ 2, hx, hy, gsb_five_not_conj⟩

end CFSG.EvenSporadicStandard.HNRecog.CSide
