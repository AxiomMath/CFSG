module

public import CFSG.GroupTheory.HuppertProduct.Quotient
import CFSG.GroupTheory.HuppertProduct.CubeCongruence
import CFSG.GroupTheory.HuppertProduct.RelIndexHom

public section

open scoped commutatorElement

namespace CFSG.GroupTheory.HuppertProduct

variable {G : Type*} [Group G]

theorem exists_cube_hom {H : Subgroup G} (hcomm : ⁅H, H⁆ ≤ mho H 3)
    (hpow : ⁅mho H 3, H⁆ ≤ mho (mho H 3) 3) :
    ∃ φ : H →* (mho H 3) ⧸ (mho (mho H 3) 3).subgroupOf (mho H 3),
      ∀ (x : H) (m : mho H 3), (m : G) = (x : G) ^ 3 →
        φ x = (m : (mho H 3) ⧸ (mho (mho H 3) 3).subgroupOf (mho H 3)) := by
  let c : H → mho H 3 := fun x => ⟨(x : G) ^ 3, pow_mem_mho x.2⟩
  have hmul : ∀ x y : H,
      ((c (x * y) : mho H 3) : (mho H 3) ⧸ (mho (mho H 3) 3).subgroupOf (mho H 3)) =
        ((c x : mho H 3) : (mho H 3) ⧸ (mho (mho H 3) 3).subgroupOf (mho H 3)) *
          ((c y : mho H 3) : (mho H 3) ⧸ (mho (mho H 3) 3).subgroupOf (mho H 3)) := by
    intro x y
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h := (mho (mho H 3) 3).inv_mem (cube_mul_mem hcomm hpow x.2 y.2)
    rw [mul_inv_rev, inv_inv] at h
    exact h
  have hone : ((c 1 : mho H 3) : (mho H 3) ⧸ (mho (mho H 3) 3).subgroupOf (mho H 3)) = 1 := by
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    show ((1 : H) : G) ^ 3 ∈ mho (mho H 3) 3
    rw [Subgroup.coe_one, one_pow]
    exact one_mem _
  let φ : H →* (mho H 3) ⧸ (mho (mho H 3) 3).subgroupOf (mho H 3) :=
    { toFun := fun x => ((c x : mho H 3) : (mho H 3) ⧸ (mho (mho H 3) 3).subgroupOf (mho H 3))
      map_one' := hone
      map_mul' := fun x y => hmul x y }
  refine ⟨φ, fun x m hm => ?_⟩
  have hcm : c x = m := Subtype.ext hm.symm
  calc φ x = ((c x : mho H 3) : (mho H 3) ⧸ (mho (mho H 3) 3).subgroupOf (mho H 3)) := rfl
    _ = ((m : mho H 3) : (mho H 3) ⧸ (mho (mho H 3) 3).subgroupOf (mho H 3)) := by rw [hcm]

theorem cube_hom_surjective {H : Subgroup G}
    {φ : H →* (mho H 3) ⧸ (mho (mho H 3) 3).subgroupOf (mho H 3)}
    (hφ : ∀ (x : H) (m : mho H 3), (m : G) = (x : G) ^ 3 →
      φ x = (m : (mho H 3) ⧸ (mho (mho H 3) 3).subgroupOf (mho H 3))) :
    Function.Surjective φ := by
  have hS : mho H 3 ≤ ((φ.range).comap
      (QuotientGroup.mk' ((mho (mho H 3) 3).subgroupOf (mho H 3)))).map (mho H 3).subtype := by
    refine mho_le_of_forall fun x hx => ?_
    refine Subgroup.mem_map.2 ⟨⟨(x : G) ^ 3, pow_mem_mho hx⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    exact MonoidHom.mem_range.2 ⟨⟨x, hx⟩, hφ ⟨x, hx⟩ ⟨(x : G) ^ 3, pow_mem_mho hx⟩ rfl⟩
  have key : ∀ m : mho H 3,
      ((m : (mho H 3) ⧸ (mho (mho H 3) 3).subgroupOf (mho H 3))) ∈ φ.range := by
    intro m
    obtain ⟨t, ht, htm⟩ := Subgroup.mem_map.1 (hS m.2)
    have htm' : t = m := Subtype.ext htm
    rw [htm'] at ht
    exact Subgroup.mem_comap.1 ht
  intro q
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  exact MonoidHom.mem_range.1 (key m)

theorem relIndex_mul_le [Finite G] {H E : Subgroup G} (hcomm : ⁅H, H⁆ ≤ mho H 3)
    (hpow : ⁅mho H 3, H⁆ ≤ mho (mho H 3) 3) (hEH : E ≤ H) (hE3 : ∀ e ∈ E, e ^ 3 = 1) :
    (mho (mho H 3) 3).relIndex (mho H 3) * (mho H 3).relIndex E ≤ (mho H 3).relIndex H := by
  obtain ⟨φ, hφ⟩ := exists_cube_hom hcomm hpow
  have hsurj := cube_hom_surjective hφ
  have hker : ∀ x : H, (x : G) ^ 3 ∈ mho (mho H 3) 3 → φ x = 1 := by
    intro x hx
    rw [hφ x ⟨(x : G) ^ 3, pow_mem_mho x.2⟩ rfl, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    exact hx
  have h := card_mul_relIndex_le φ hsurj (mho_le H 3) hEH
    (fun x hx => hker x (pow_mem_mho hx))
    (fun x hx => hker x (by rw [hE3 x hx]; exact one_mem _))
  have hcard : Nat.card ((mho H 3) ⧸ (mho (mho H 3) 3).subgroupOf (mho H 3)) =
      (mho (mho H 3) 3).relIndex (mho H 3) :=
    (Subgroup.index_eq_card _).symm
  rwa [hcard] at h

theorem relIndex_mho_mho_le [Finite G] {H : Subgroup G} (hcomm : ⁅H, H⁆ ≤ mho H 3)
    (hpow : ⁅mho H 3, H⁆ ≤ mho (mho H 3) 3) :
    (mho (mho H 3) 3).relIndex (mho H 3) ≤ (mho H 3).relIndex H := by
  have h := relIndex_mul_le hcomm hpow (bot_le : (⊥ : Subgroup G) ≤ H)
    (fun e he => by rw [(Subgroup.mem_bot.1 he)]; exact one_pow 3)
  rwa [Subgroup.relIndex_bot_right, mul_one] at h

end CFSG.GroupTheory.HuppertProduct
