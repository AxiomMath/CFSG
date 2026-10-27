module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Data.Set.Card
import Mathlib.Tactic.Group

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise

namespace CFSG.FeitThompson

variable {G : Type*} [Group G]

theorem exists_mem_prod_mul_eq {H K : Subgroup G} {y : G}
    (hy : y ∈ (H : Set G) * (K : Set G)) : ∃ p : H × K, (p.1 : G) * (p.2 : G) = y := by
  obtain ⟨h, hh, k, hk, hkk⟩ := Set.mem_mul.1 hy
  exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), hkk⟩

def mulFiberEquivInf {H K : Subgroup G} {h₀ k₀ : G} (hh₀ : h₀ ∈ H) (hk₀ : k₀ ∈ K) :
    {x : H × K // (x.1 : G) * (x.2 : G) = h₀ * k₀} ≃ (H ⊓ K : Subgroup G) where
  toFun x := ⟨h₀⁻¹ * (x.1.1 : G), by
    have hx : (x.1.1 : G) * (x.1.2 : G) = h₀ * k₀ := x.2
    have key : h₀⁻¹ * (x.1.1 : G) = k₀ * (x.1.2 : G)⁻¹ := by
      calc h₀⁻¹ * (x.1.1 : G)
          = h₀⁻¹ * ((x.1.1 : G) * (x.1.2 : G) * (x.1.2 : G)⁻¹) := by group
        _ = h₀⁻¹ * (h₀ * k₀ * (x.1.2 : G)⁻¹) := by rw [hx]
        _ = k₀ * (x.1.2 : G)⁻¹ := by group
    refine Subgroup.mem_inf.2 ⟨H.mul_mem (H.inv_mem hh₀) x.1.1.2, ?_⟩
    rw [key]
    exact K.mul_mem hk₀ (K.inv_mem x.1.2.2)⟩
  invFun t := ⟨(⟨h₀ * (t : G), H.mul_mem hh₀ (Subgroup.mem_inf.1 t.2).1⟩,
      ⟨(t : G)⁻¹ * k₀, K.mul_mem (K.inv_mem (Subgroup.mem_inf.1 t.2).2) hk₀⟩), by
    simp [mul_assoc]⟩
  left_inv x := by
    obtain ⟨⟨h, k⟩, hx⟩ := x
    have hx' : (h : G) * (k : G) = h₀ * k₀ := hx
    ext
    · simp
    · change (h₀⁻¹ * (h : G))⁻¹ * k₀ = (k : G)
      have h2 : (h₀⁻¹ * (h : G))⁻¹ * k₀ = (h : G)⁻¹ * (h₀ * k₀) := by group
      rw [h2, ← hx']
      group
  right_inv t := by ext; simp

@[simp]
theorem mulFiberEquivInf_apply_coe {H K : Subgroup G} {h₀ k₀ : G} (hh₀ : h₀ ∈ H) (hk₀ : k₀ ∈ K)
    (x : {x : H × K // (x.1 : G) * (x.2 : G) = h₀ * k₀}) :
    ((mulFiberEquivInf hh₀ hk₀ x : (H ⊓ K : Subgroup G)) : G) = h₀⁻¹ * (x.1.1 : G) := (rfl)

@[simp]
theorem mulFiberEquivInf_symm_apply_fst_coe {H K : Subgroup G} {h₀ k₀ : G} (hh₀ : h₀ ∈ H)
    (hk₀ : k₀ ∈ K) (t : (H ⊓ K : Subgroup G)) :
    ((((mulFiberEquivInf hh₀ hk₀).symm t : {x : H × K // (x.1 : G) * (x.2 : G) = h₀ * k₀}) :
      H × K).1 : G) = h₀ * (t : G) := (rfl)

@[simp]
theorem mulFiberEquivInf_symm_apply_snd_coe {H K : Subgroup G} {h₀ k₀ : G} (hh₀ : h₀ ∈ H)
    (hk₀ : k₀ ∈ K) (t : (H ⊓ K : Subgroup G)) :
    ((((mulFiberEquivInf hh₀ hk₀).symm t : {x : H × K // (x.1 : G) * (x.2 : G) = h₀ * k₀}) :
      H × K).2 : G) = (t : G)⁻¹ * k₀ := (rfl)

theorem natCard_fiber_mul (H K : Subgroup G) {y : G} (hy : y ∈ (H : Set G) * (K : Set G)) :
    Nat.card {x : H × K // (x.1 : G) * (x.2 : G) = y} = Nat.card (H ⊓ K : Subgroup G) := by
  obtain ⟨p, hp⟩ := exists_mem_prod_mul_eq hy
  subst hp
  exact Nat.card_eq_of_bijective _ (mulFiberEquivInf p.1.2 p.2.2).bijective

private noncomputable def fiberEquivInfOfMem (H K : Subgroup G)
    (y : ((H : Set G) * (K : Set G) : Set G)) :
    {x : H × K // (x.1 : G) * (x.2 : G) = (y : G)} ≃ (H ⊓ K : Subgroup G) :=
  (Equiv.subtypeEquivRight (p := fun x : H × K => (x.1 : G) * (x.2 : G) = (y : G))
    (q := fun x : H × K => (x.1 : G) * (x.2 : G)
      = ((exists_mem_prod_mul_eq y.2).choose.1 : G) * ((exists_mem_prod_mul_eq y.2).choose.2 : G))
    (fun x => by rw [(exists_mem_prod_mul_eq y.2).choose_spec])).trans
    (mulFiberEquivInf (exists_mem_prod_mul_eq y.2).choose.1.2
      (exists_mem_prod_mul_eq y.2).choose.2.2)

noncomputable def prodEquivMulProdInf (H K : Subgroup G) :
    (H × K) ≃ (((H : Set G) * (K : Set G) : Set G) × (H ⊓ K : Subgroup G)) :=
  (Equiv.sigmaFiberEquiv (fun x : H × K =>
      (⟨(x.1 : G) * (x.2 : G), Set.mul_mem_mul x.1.2 x.2.2⟩ :
        ((H : Set G) * (K : Set G) : Set G)))).symm.trans
    ((Equiv.sigmaCongrRight fun y => (Equiv.subtypeEquivRight (fun x => by
        simp [Subtype.ext_iff])).trans (fiberEquivInfOfMem H K y)).trans (Equiv.sigmaEquivProd _ _))

theorem natCard_mul_mul_natCard_inf (H K : Subgroup G) :
    Nat.card ((H : Set G) * (K : Set G)) * Nat.card (H ⊓ K : Subgroup G)
      = Nat.card H * Nat.card K := by
  rw [← Nat.card_prod, ← Nat.card_prod,
    Nat.card_eq_of_bijective _ (prodEquivMulProdInf H K).bijective]

theorem natCard_mul_eq_natCard_mul_natCard_div_natCard_inf [Finite G] (H K : Subgroup G) :
    Nat.card ((H : Set G) * (K : Set G))
      = Nat.card H * Nat.card K / Nat.card (H ⊓ K : Subgroup G) :=
  (Nat.div_eq_of_eq_mul_left Nat.card_pos (natCard_mul_mul_natCard_inf H K).symm).symm

theorem ncard_mul_eq_natCard_mul_natCard_div_natCard_inf [Finite G] (H K : Subgroup G) :
    ((H : Set G) * (K : Set G)).ncard
      = Nat.card H * Nat.card K / Nat.card (H ⊓ K : Subgroup G) := by
  rw [← Nat.card_coe_set_eq, natCard_mul_eq_natCard_mul_natCard_div_natCard_inf H K]

end CFSG.FeitThompson
