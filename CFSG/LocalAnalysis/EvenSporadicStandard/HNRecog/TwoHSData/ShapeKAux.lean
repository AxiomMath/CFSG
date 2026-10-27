module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial
public import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.EvenSporadicStandard.HNRecog.TwoHSData

open Subgroup

theorem nonempty_mulEquiv_two_four {Z : Type*} [Group Z] (hcomm : ∀ a b : Z, a * b = b * a)
    (hcard : Nat.card Z = 8) {x y : Z} (hx : orderOf x = 4) (hy : orderOf y = 2)
    (hxy : y ∉ zpowers x) :
    Nonempty (Z ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 4)) := by
  have hy2 : y * y = 1 := by
    have h : y ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hy])
    simpa [pow_two] using h
  let f1 : Multiplicative (ZMod 2) →* Z :=
    { toFun := fun i => y ^ i.toAdd.val
      map_one' := by simp
      map_mul' := fun i j => by
        have hmod : y ^ ((i.toAdd.val + j.toAdd.val) % 2) = y ^ (i.toAdd.val + j.toAdd.val) := by
          have h := pow_mod_orderOf y (i.toAdd.val + j.toAdd.val)
          rwa [hy] at h
        show y ^ (i * j).toAdd.val = y ^ i.toAdd.val * y ^ j.toAdd.val
        rw [show (i * j).toAdd = i.toAdd + j.toAdd by rfl, ZMod.val_add, hmod, pow_add] }
  let f2 : Multiplicative (ZMod 4) →* Z :=
    { toFun := fun j => x ^ j.toAdd.val
      map_one' := by simp
      map_mul' := fun i j => by
        have hmod : x ^ ((i.toAdd.val + j.toAdd.val) % 4) = x ^ (i.toAdd.val + j.toAdd.val) := by
          have h := pow_mod_orderOf x (i.toAdd.val + j.toAdd.val)
          rwa [hx] at h
        show x ^ (i * j).toAdd.val = x ^ i.toAdd.val * x ^ j.toAdd.val
        rw [show (i * j).toAdd = i.toAdd + j.toAdd by rfl, ZMod.val_add, hmod, pow_add] }
  let f : Multiplicative (ZMod 2) × Multiplicative (ZMod 4) →* Z :=
    f1.noncommCoprod f2 fun i j => (commute_iff_eq _ _).mpr (hcomm _ _)
  have hf : ∀ (i : Multiplicative (ZMod 2)) (j : Multiplicative (ZMod 4)),
      f (i, j) = y ^ i.toAdd.val * x ^ j.toAdd.val := by
    intro i j
    rw [MonoidHom.noncommCoprod_apply]
    rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro ij hij
    obtain ⟨i, j⟩ := ij
    rw [hf] at hij
    have hmem : y ^ i.toAdd.val ∈ zpowers x := by
      have hval : y ^ i.toAdd.val = (x ^ j.toAdd.val)⁻¹ := eq_inv_of_mul_eq_one_left hij
      rw [hval]
      exact inv_mem (Subgroup.npow_mem_zpowers x j.toAdd.val)
    have hmod2 : y ^ (i.toAdd.val % 2) = y ^ i.toAdd.val := by
      have h := pow_mod_orderOf y i.toAdd.val
      rwa [hy] at h
    have hi_mod : i.toAdd.val % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one i.toAdd.val with h | h
      · exact h
      · exfalso
        apply hxy
        rw [h] at hmod2
        simp only [pow_one] at hmod2
        rw [hmod2]
        exact hmem
    have hi0 : i.toAdd = 0 := by
      rw [← ZMod.natCast_zmod_val i.toAdd]
      exact (ZMod.natCast_eq_zero_iff _ 2).mpr (Nat.dvd_of_mod_eq_zero hi_mod)
    have hy1 : y ^ i.toAdd.val = 1 := by
      rw [← hmod2, hi_mod, pow_zero]
    have hx1 : x ^ j.toAdd.val = 1 := by
      have h := hij
      rw [hy1, one_mul] at h
      exact h
    have hj0 : j.toAdd = 0 := by
      have hdvd : 4 ∣ j.toAdd.val := by
        have h := orderOf_dvd_iff_pow_eq_one.mpr hx1
        rwa [hx] at h
      rw [← ZMod.natCast_zmod_val j.toAdd]
      exact (ZMod.natCast_eq_zero_iff _ 4).mpr hdvd
    have hi1 : i = 1 := by
      rw [← ofAdd_toAdd i, hi0]
      rfl
    have hj1 : j = 1 := by
      rw [← ofAdd_toAdd j, hj0]
      rfl
    exact Prod.ext hi1 hj1
  haveI : Finite Z := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hcarddom :
      Nat.card (Multiplicative (ZMod 2) × Multiplicative (ZMod 4)) = Nat.card Z := by
    rw [Nat.card_prod (Multiplicative (ZMod 2)) (Multiplicative (ZMod 4)),
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2),
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 4) ≃ ZMod 4),
      Nat.card_zmod 2, Nat.card_zmod 4, hcard]
  have hbij : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, hcarddom⟩
  exact ⟨(MulEquiv.ofBijective f hbij).symm⟩

theorem isExtraspecial_two_of_elements {Γ : Type*} [Group Γ] (c : Γ) (hc1 : c ≠ 1)
    (hc2 : c * c = 1) (hcen : ∀ g : Γ, g * c = c * g)
    (hcen' : ∀ q : Γ, (∀ r : Γ, q * r = r * q) → q = 1 ∨ q = c)
    (hcomm : ∀ q r : Γ, q * r * (r * q)⁻¹ = 1 ∨ q * r * (r * q)⁻¹ = c)
    (hsq : ∀ q : Γ, q * q = 1 ∨ q * q = c) (hnt : ∃ q : Γ, q ≠ 1 ∧ q ≠ c) :
    CFSG.IsExtraspecial 2 Γ := by
  have hc2' : c ^ 2 = 1 := by rwa [pow_two]
  have horder_c : orderOf c = 2 := orderOf_eq_prime hc2' hc1
  have hcenter : Subgroup.center Γ = Subgroup.zpowers c := by
    apply le_antisymm
    · intro q hq
      rw [Subgroup.mem_center_iff] at hq
      rcases hcen' q (fun r => (hq r).symm) with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers c
    · rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
      exact hcen
  have hcard_center : Nat.card (Subgroup.center Γ) = 2 := by
    rw [hcenter, Nat.card_zpowers, horder_c]
  have hcommQ : ∀ x y : Γ ⧸ Subgroup.center Γ, x * y = y * x := by
    intro x y
    refine QuotientGroup.induction_on x ?_
    intro a
    refine QuotientGroup.induction_on y ?_
    intro b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem,
      div_eq_mul_inv]
    rcases hcomm a b with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h, hcenter]; exact Subgroup.mem_zpowers c
  have hexp : Monoid.exponent (Γ ⧸ Subgroup.center Γ) ∣ 2 := by
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_
    intro x
    refine QuotientGroup.induction_on x ?_
    intro a
    change ((a ^ 2 : Γ) : Γ ⧸ Subgroup.center Γ) = 1
    rw [QuotientGroup.eq_one_iff, pow_two]
    rcases hsq a with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h, hcenter]; exact Subgroup.mem_zpowers c
  have hntQ : Nontrivial (Γ ⧸ Subgroup.center Γ) := by
    obtain ⟨q, hq1, hqc⟩ := hnt
    refine nontrivial_iff.mpr ⟨(q : Γ ⧸ Subgroup.center Γ), 1, ?_⟩
    intro h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff] at h
    rcases hcen' q (fun r => (h r).symm) with h1 | hc
    · exact hq1 h1
    · exact hqc hc
  exact
    { center_order_p := hcard_center
      quotient_elementary_abelian :=
        { toIsMulCommutative := IsMulCommutative.of_comm hcommQ
          exponent_dvd_p := hexp }
      quotient_nontrivial := hntQ }

end CFSG.EvenSporadicStandard.HNRecog.TwoHSData
