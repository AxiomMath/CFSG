module

public import Mathlib.Algebra.Order.Ring.Star
public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialOddQuotientAutFaithfulness

public section

namespace CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoQuotientLinearAction

open CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialOddQuotientAutFaithfulness

open scoped commutatorElement

@[expose] def QSpace (E : Type*) [Group E] : Type _ := Additive (E ⧸ Subgroup.center E)

instance instAddGroup (E : Type*) [Group E] : AddGroup (QSpace E) :=
  inferInstanceAs (AddGroup (Additive (E ⧸ Subgroup.center E)))

variable {E : Type*} [Group E] [Finite E]

theorem comm_mem_center (hE : CFSG.IsExtraspecialPGroup 2 E) (a b : E) :
    ⁅a, b⁆ ∈ Subgroup.center E := by
  rw [← hE.2.1]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)

theorem sq_mem_center (hE : CFSG.IsExtraspecialPGroup 2 E) (a : E) :
    a ^ 2 ∈ Subgroup.center E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 E) := ⟨hE.1⟩
  rw [← hE.2.2.1]
  exact CFSG.pth_power_mem_frattini_of_isPGroup (R := E) (p := 2) a

noncomputable instance instAddCommGroup [h : Fact (CFSG.IsExtraspecialPGroup 2 E)] :
    AddCommGroup (QSpace E) :=
  { instAddGroup E with
    add_comm := by
      intro a b
      induction a using Additive.rec with | _ a => ?_
      induction b using Additive.rec with | _ b => ?_
      induction a using QuotientGroup.induction_on with | _ a => ?_
      induction b using QuotientGroup.induction_on with | _ b => ?_
      show Additive.ofMul ((a : E ⧸ Subgroup.center E) * b) =
        Additive.ofMul ((b : E ⧸ Subgroup.center E) * a)
      congr 1
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have := comm_mem_center h.out b⁻¹ a⁻¹
      simpa [commutatorElement_def, mul_assoc] using this }

theorem two_nsmul_eq_zero [h : Fact (CFSG.IsExtraspecialPGroup 2 E)] (x : QSpace E) :
    (2 : ℕ) • x = 0 := by
  induction x using Additive.rec with | _ a => ?_
  induction a using QuotientGroup.induction_on with | _ a => ?_
  show Additive.ofMul (((a : E ⧸ Subgroup.center E)) ^ 2) = Additive.ofMul 1
  congr 1
  rw [← QuotientGroup.mk_pow]
  exact (QuotientGroup.eq_one_iff _).2 (sq_mem_center h.out a)

noncomputable instance instModule [h : Fact (CFSG.IsExtraspecialPGroup 2 E)] :
    Module (ZMod 2) (QSpace E) :=
  AddCommGroup.zmodModule two_nsmul_eq_zero

@[expose] noncomputable def toAddEquiv (E : Type*) [Group E] (α : MulAut E) : QSpace E ≃+ QSpace E :=
  MulEquiv.toAdditive (quotientHom E α)

@[expose] noncomputable def linearAction (E : Type*) [Group E] [Finite E]
    [Fact (CFSG.IsExtraspecialPGroup 2 E)] :
    MulAut E →* (QSpace E ≃ₗ[ZMod 2] QSpace E) where
  toFun α := { toAddEquiv E α with
    map_smul' := fun c x => ZMod.map_smul (toAddEquiv E α).toAddMonoidHom c x }
  map_one' := by
    ext x
    induction x using Additive.rec with | _ a => ?_
    induction a using QuotientGroup.induction_on with | _ a => ?_
    rfl
  map_mul' α β := by
    ext x
    induction x using Additive.rec with | _ a => ?_
    induction a using QuotientGroup.induction_on with | _ a => ?_
    rfl

theorem linearAction_ofMul_mk [Fact (CFSG.IsExtraspecialPGroup 2 E)] (α : MulAut E) (x : E) :
    linearAction E α (Additive.ofMul (x : E ⧸ Subgroup.center E)) =
      Additive.ofMul ((α x : E) : E ⧸ Subgroup.center E) := rfl

theorem finrank_eq [h : Fact (CFSG.IsExtraspecialPGroup 2 E)] {w : ℕ}
    (hcard : Nat.card E = 2 ^ (1 + 2 * w)) :
    Module.finrank (ZMod 2) (QSpace E) = 2 * w := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (QSpace E) := inferInstanceAs (Finite (Additive (E ⧸ Subgroup.center E)))
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center E)
  rw [h.out.2.2.2, hcard] at h1
  have h2 : Nat.card (QSpace E) = 2 ^ (2 * w) := by
    have : Nat.card (QSpace E) = Nat.card (E ⧸ Subgroup.center E) :=
      Nat.card_congr Additive.toMul
    rw [this]
    have h3 : 2 ^ (1 + 2 * w) = 2 ^ (2 * w) * 2 := by ring
    rw [h3] at h1
    exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h1).symm
  have h4 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := QSpace E)
  rw [h2, Nat.card_zmod] at h4
  exact (Nat.pow_right_injective (le_refl 2) h4).symm

end CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoQuotientLinearAction
