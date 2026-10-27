module

import CFSG.FeitThompson.OddOrderTheorem
import CFSG.GroupTheory.Gorenstein.MaxCardThompson
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.ABGTheoremB.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection8.theorem_8_1

public section

namespace CFSG.ABGTheoremB.V56

open CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type*} [Group G]

theorem thompsonCenter_map_of_injective {A B : Type*} [Group A] [Group B] [Finite B]
    (f : A →* B) (hf : Function.Injective f) (P : Subgroup A) :
    (CFSG.thompsonCenter P).map f = CFSG.thompsonCenter (P.map f) :=
  CFSG.map_thompsonCenter_of_injective f P (hf.comp P.subtype_injective)

theorem thompsonCenter_map_conj [Finite G] (g : G) (P : Subgroup G) :
    CFSG.thompsonCenter (P.map (MulAut.conj g).toMonoidHom) =
      (CFSG.thompsonCenter P).map (MulAut.conj g).toMonoidHom :=
  (thompsonCenter_map_of_injective _ (MulAut.conj g).injective P).symm

theorem isPGroup_thompsonCenter {p : ℕ} {U : Subgroup G} (hU : IsPGroup p U) :
    IsPGroup p (CFSG.thompsonCenter U) :=
  hU.to_le (CFSG.thompsonCenter_le U)

theorem thompsonCenter_ne_bot [Finite G] {p : ℕ} (hp : p.Prime) {U : Subgroup G}
    (hU : IsPGroup p U) (hne : U ≠ ⊥) : CFSG.thompsonCenter U ≠ ⊥ :=
  have : Fact p.Prime := ⟨hp⟩
  CFSG.section8_centerIn_thompsonSubgroup_ne_bot_of_ne_bot hU hne

theorem normalizer_le_normalizer_thompsonCenter_self [Finite G] (U : Subgroup G) :
    Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (CFSG.thompsonCenter U : Set G) :=
  CFSG.normalizer_le_normalizer_thompsonCenter U

theorem isPLocal_normalizer_thompsonCenter [Finite G] {p : ℕ} (hp : p.Prime) {U : Subgroup G}
    (hU : IsPGroup p U) (hne : U ≠ ⊥) :
    IsPLocal p (Subgroup.normalizer (CFSG.thompsonCenter U : Set G)) :=
  ⟨CFSG.thompsonCenter U, thompsonCenter_ne_bot hp hU hne, isPGroup_thompsonCenter hU, rfl⟩

private theorem coe_sup_eq_mul_of_permutable {U W : Subgroup G}
    (hUW : (U : Set G) * (W : Set G) = (W : Set G) * (U : Set G)) :
    ((U ⊔ W : Subgroup G) : Set G) = (U : Set G) * (W : Set G) := by
  let S : Subgroup G :=
    { carrier := (U : Set G) * (W : Set G)
      mul_mem' := by
        rintro _ _ ⟨u₁, hu₁, w₁, hw₁, rfl⟩ ⟨u₂, hu₂, w₂, hw₂, rfl⟩
        have h : w₁ * u₂ ∈ (U : Set G) * (W : Set G) := by
          rw [hUW]
          exact Set.mul_mem_mul hw₁ hu₂
        obtain ⟨u₃, hu₃, w₃, hw₃, h₃⟩ := h
        refine ⟨u₁ * u₃, U.mul_mem hu₁ hu₃, w₃ * w₂, W.mul_mem hw₃ hw₂, ?_⟩
        calc u₁ * u₃ * (w₃ * w₂) = u₁ * (u₃ * w₃) * w₂ := by group
          _ = u₁ * (w₁ * u₂) * w₂ := by rw [show u₃ * w₃ = w₁ * u₂ from h₃]
          _ = u₁ * w₁ * (u₂ * w₂) := by group
      one_mem' := ⟨1, U.one_mem, 1, W.one_mem, one_mul 1⟩
      inv_mem' := by
        rintro _ ⟨u, hu, w, hw, rfl⟩
        have h : w⁻¹ * u⁻¹ ∈ (U : Set G) * (W : Set G) := by
          rw [hUW]
          exact Set.mul_mem_mul (W.inv_mem hw) (U.inv_mem hu)
        simpa only [mul_inv_rev] using h }
  refine Set.Subset.antisymm ?_ ?_
  · have hle : U ⊔ W ≤ S := sup_le (fun u hu => ⟨u, hu, 1, W.one_mem, mul_one u⟩)
      (fun w hw => ⟨1, U.one_mem, w, hw, one_mul w⟩)
    exact hle
  · rintro _ ⟨u, hu, w, hw, rfl⟩
    exact Subgroup.mul_mem_sup hu hw

private theorem card_sup_eq_mul_of_permutable {U W : Subgroup G}
    (hUW : (U : Set G) * (W : Set G) = (W : Set G) * (U : Set G)) (hdisj : Disjoint U W) :
    Nat.card (U ⊔ W : Subgroup G) = Nat.card U * Nat.card W := by
  have hset := coe_sup_eq_mul_of_permutable hUW
  let φ : U × W → (U ⊔ W : Subgroup G) := fun x =>
    ⟨(x.1 : G) * x.2, Subgroup.mul_mem_sup x.1.2 x.2.2⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ hab
      have h1 : (a : G) * b = a' * b' := congrArg Subtype.val hab
      have h2 : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
        calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
          _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [h1]
          _ = b' * (b : G)⁻¹ := by group
      have hU : (a' : G)⁻¹ * a ∈ U := U.mul_mem (U.inv_mem a'.2) a.2
      have hW : (a' : G)⁻¹ * a ∈ W := by
        rw [h2]
        exact W.mul_mem b'.2 (W.inv_mem b.2)
      have h3 : (a' : G)⁻¹ * a = 1 := Subgroup.disjoint_def.mp hdisj hU hW
      have ha : a = a' := Subtype.ext (inv_mul_eq_one.mp h3).symm
      subst ha
      have hb : b = b' := Subtype.ext (mul_left_cancel h1)
      rw [hb]
    · rintro ⟨x, hx⟩
      have hx' : x ∈ (U : Set G) * (W : Set G) := by
        rw [← hset]
        exact hx
      obtain ⟨u, hu, w, hw, rfl⟩ := hx'
      exact ⟨(⟨u, hu⟩, ⟨w, hw⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_eq_of_bijective φ hφ).symm

theorem le_normalizer_thompsonCenter_of_odd [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {U W : Subgroup G} (hU : IsPGroup p U) (hWp : ¬ p ∣ Nat.card W) (hWodd : Odd (Nat.card W))
    (hUW : (U : Set G) * (W : Set G) = (W : Set G) * (U : Set G))
    (hcore : pPrimeCoreIn p (U ⊔ W) = ⊥) :
    U ⊔ W ≤ Subgroup.normalizer (CFSG.thompsonCenter U : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU
  have hcop : Nat.Coprime (Nat.card U) (Nat.card W) := by
    rw [hk]
    exact Nat.Coprime.pow_left k (hp.coprime_iff_not_dvd.2 hWp)
  have hcard : Nat.card (U ⊔ W : Subgroup G) = Nat.card U * Nat.card W :=
    card_sup_eq_mul_of_permutable hUW (Subgroup.disjoint_of_coprime_natCard hcop)
  have hUodd : Odd (Nat.card U) := by
    rw [hk]
    exact (hp.odd_of_ne_two hp2).pow
  set X : Subgroup G := U ⊔ W
  have hXodd : Odd (Nat.card X) := by
    rw [hcard]
    exact hUodd.mul hWodd
  have : Group.IsSolvable X := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hXodd
  have hUX : U ≤ X := le_sup_left
  set U' : Subgroup X := U.subgroupOf X
  have hU'card : Nat.card U' = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUX).toEquiv
  have hU'p : IsPGroup p U' := hU.comap_subtype
  have hidx : U'.index = Nat.card W := by
    have h := U'.card_mul_index
    rw [hU'card, hcard] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  let S : Sylow p X := hU'p.toSylow (by rw [hidx]; exact hWp)
  have h62 := CFSG.theorem_6_2 hXodd S
  have hcoreX : CFSG.pPrimeCore p X = ⊥ := by
    have h : (CFSG.pPrimeCore p X).map X.subtype = ⊥ := hcore
    exact (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp h
  rw [hcoreX, sup_bot_eq] at h62
  have hN : (CFSG.thompsonCenter U').Normal := h62
  have hmap : (CFSG.thompsonCenter U').map X.subtype = CFSG.thompsonCenter U := by
    rw [thompsonCenter_map_of_injective X.subtype X.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUX]
  have hle := le_normalizer_map_subtype X (CFSG.thompsonCenter U')
  rwa [hmap] at hle

end CFSG.ABGTheoremB.V56
