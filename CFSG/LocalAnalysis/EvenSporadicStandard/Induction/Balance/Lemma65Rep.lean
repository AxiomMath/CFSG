module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.ModuleRep
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Lemma65Basic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup CFSG.Open CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Wong77
open CFSG.Blueprint.NativeSporadic (Carrier)
open scoped IsMulCommutative

theorem exists_rep {K : Type*} [Group K] (N : Subgroup K) [N.Normal] [IsMulCommutative N]
    [Module (ZMod 2) (Additive N)] {Q : Type*} [Group Q] (hC : centralizer (N : Set K) = N)
    (φ : K ⧸ N ≃* Q) :
    ∃ ρ : Q →* (Additive N ≃ₗ[ZMod 2] Additive N), Function.Injective ρ ∧
      ∀ (k : K) (n : N), ρ (φ (QuotientGroup.mk k)) (Additive.ofMul n) =
        Additive.ofMul (MulAut.conjNormal k n) := by
  let r : K →* (Additive N ≃ₗ[ZMod 2] Additive N) := (linearAut N).comp MulAut.conjNormal
  have hker : r.ker = N := by
    ext k
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : (MulAut.conjNormal k : MulAut N) = 1 := by
        apply linearAut_injective
        rw [map_one]
        exact h
      have h2 : k ∈ centralizer (N : Set K) := by
        rw [mem_centralizer_iff]
        intro n hn
        have := congrArg (fun f : MulAut N => (f ⟨n, hn⟩ : K)) h1
        simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
        exact (mul_inv_eq_iff_eq_mul.1 this).symm
      rwa [hC] at h2
    · intro hk
      have h2 : k ∈ centralizer (N : Set K) := by rw [hC]; exact hk
      rw [mem_centralizer_iff] at h2
      have h1 : (MulAut.conjNormal k : MulAut N) = 1 := by
        ext n
        simp only [MulAut.conjNormal_apply, MulAut.one_apply]
        exact mul_inv_eq_iff_eq_mul.2 (h2 n n.2).symm
      show linearAut N (MulAut.conjNormal k) = 1
      rw [h1, map_one]
  refine ⟨(QuotientGroup.lift N r hker.ge).comp φ.symm.toMonoidHom, ?_, ?_⟩
  · exact ((QuotientGroup.injective_lift_iff N r hker.ge).2 hker.symm).comp φ.symm.injective
  · intro k n
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      QuotientGroup.lift_mk]
    exact linearAut_apply _ n

namespace Setting65

variable {Γ : Type} [Group Γ] {E H₁ : Subgroup Γ} {e : Γ} (hS : Setting65 Γ E H₁ e)
include hS

theorem isMulCommutative_N : IsMulCommutative ↥(E.subgroupOf H₁) :=
  ⟨⟨fun a b => Subtype.ext (Subtype.ext
    (hS.comm_of_mem_E (mem_subgroupOf.1 a.2) (mem_subgroupOf.1 b.2)))⟩⟩

theorem sq_N : ∀ x ∈ E.subgroupOf H₁, x ^ 2 = 1 := by
  intro x hx
  apply Subtype.ext
  rw [Subgroup.coe_pow, pow_two, hS.sq_of_mem_E (mem_subgroupOf.1 hx)]
  rfl

theorem centralizer_N :
    centralizer ((E.subgroupOf H₁ : Subgroup ↥H₁) : Set ↥H₁) = E.subgroupOf H₁ := by
  ext k
  rw [mem_centralizer_iff, mem_subgroupOf]
  constructor
  · intro hk
    have hcomm : ∀ y : Γ, y ∈ E → y * (k : Γ) = (k : Γ) * y := by
      intro y hy
      rcases hS.mem_H₁_or_mul_mem_H₁ hy with h | h
      · exact congrArg Subtype.val (hk ⟨y, h⟩ (mem_subgroupOf.2 hy))
      · have hye : y * e ∈ E := E.mul_mem hy hS.mem
        have h1 : y * e * (k : Γ) = (k : Γ) * (y * e) :=
          congrArg Subtype.val (hk ⟨y * e, h⟩ (mem_subgroupOf.2 hye))
        have h2 : (k : Γ) * e = e * k := hS.commute_of_mem_H₁ k.2
        calc y * (k : Γ) = (y * e) * e * k := by rw [mul_assoc y e e, hS.e_mul_e, mul_one]
          _ = (y * e) * (e * k) := mul_assoc _ _ _
          _ = (y * e) * (k * e) := by rw [h2]
          _ = ((y * e) * k) * e := (mul_assoc _ _ _).symm
          _ = (k * (y * e)) * e := by rw [h1]
          _ = k * (y * e * e) := mul_assoc _ _ _
          _ = k * y := by rw [mul_assoc y e e, hS.e_mul_e, mul_one]
    have : (k : Γ) ∈ centralizer (E : Set Γ) := by
      rw [mem_centralizer_iff]
      exact fun y hy => hcomm y hy
    rwa [hS.cent] at this
  · intro hk n hn
    exact Subtype.ext (hS.comm_of_mem_E (mem_subgroupOf.1 hn) hk)

theorem card_N : Nat.card ↥(E.subgroupOf H₁) = 2 ^ 11 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (E.subgroupOf H₁)
  rw [hS.card_H₁, hS.card₁] at h
  exact (Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 10200960) h).symm

end Setting65

end CFSG.EvenSporadicStandard.Induction.Balance
