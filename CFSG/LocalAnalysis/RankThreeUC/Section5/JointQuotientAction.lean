module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.Quotient.QuotientAction
public import CFSG.LocalAnalysis.RankThreeUC.Section5.BstarFaithful.BstarFaithful
public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialOddQuotientAutFaithfulness

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.JointQuotientAction

open CFSG.LocalAnalysis.RankThreeUC.Section5

variable {G : Type} [Group G] [Finite G]

@[expose] def joint (P T B : Subgroup G) : Subgroup (MulAut ↥P) := Sstar P T B ⊔ Bstar P B

theorem Sstar_le_joint (P T B : Subgroup G) : Sstar P T B ≤ joint P T B := le_sup_left

theorem Bstar_le_joint (P T B : Subgroup G) : Bstar P B ≤ joint P T B := le_sup_right

@[expose] noncomputable def rep (p : ℕ) [Fact p.Prime] {P : Subgroup G} [Fact (⁅⁅P, P⁆, P⁆ = ⊥)]
    [Fact (Monoid.exponent ↥P = p)] (C : Subgroup (MulAut ↥P)) :
    Representation (ZMod p) C (Additive (Quotient.Pbar P)) where
  toFun c := (Quotient.linearOfMulAut (p := p)
    (CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialOddQuotientAutFaithfulness.quotientHom ↥P (c : MulAut ↥P))
    ).toLinearMap
  map_one' := by
    ext x
    induction x using Additive.rec with | _ x => ?_
    induction x using QuotientGroup.induction_on with | _ x => ?_
    rfl
  map_mul' a b := by
    ext x
    induction x using Additive.rec with | _ x => ?_
    induction x using QuotientGroup.induction_on with | _ x => ?_
    rfl

section

variable (p : ℕ) [Fact p.Prime] {P : Subgroup G} [Fact (⁅⁅P, P⁆, P⁆ = ⊥)]
    [Fact (Monoid.exponent ↥P = p)] (C : Subgroup (MulAut ↥P))

theorem rep_apply_mk (c : C) (x : ↥P) :
    rep p C c (Additive.ofMul (QuotientGroup.mk x : Quotient.Pbar P)) =
      Additive.ofMul (QuotientGroup.mk ((c : MulAut ↥P) x)) := rfl

theorem rep_injective_iff :
    Function.Injective (rep p C) ↔
      Function.Injective
        ((CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialOddQuotientAutFaithfulness.quotientHom ↥P).comp
          C.subtype) := by
  rw [injective_iff_map_eq_one, injective_iff_map_eq_one]
  have key : ∀ c : C, rep p C c = 1 ↔
      (CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialOddQuotientAutFaithfulness.quotientHom ↥P).comp
        C.subtype c = 1 := by
    intro c
    constructor
    · intro h
      ext x
      induction x using QuotientGroup.induction_on with | _ x => ?_
      have := LinearMap.congr_fun h (Additive.ofMul (QuotientGroup.mk x : Quotient.Pbar P))
      exact congrArg Additive.toMul this
    · intro h
      ext x
      induction x using Additive.rec with | _ x => ?_
      induction x using QuotientGroup.induction_on with | _ x => ?_
      have := congrArg (fun f => f (QuotientGroup.mk x : Quotient.Pbar P)) h
      exact congrArg Additive.ofMul this
  exact forall_congr' fun c => imp_congr_left (key c) |>.trans (by rfl)

theorem rep_injective_of_quotientHom
    (h : Function.Injective
      ((CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialOddQuotientAutFaithfulness.quotientHom ↥P).comp
        C.subtype)) : Function.Injective (rep p C) :=
  (rep_injective_iff p C).2 h

end
@[expose] noncomputable def bToJoint {p : ℕ} {P T B : Subgroup G} {e : ℕ} (h51 : OddPrimeClassTwoAction G p P T B e) :
    B →* joint P T B :=
  (CFSG.LocalAnalysis.RankThreeUC.Section5.BstarFaithful.bAction h51).codRestrict (joint P T B) (fun b => by
    apply Bstar_le_joint
    rw [CFSG.LocalAnalysis.RankThreeUC.Section5.BstarFaithful.range_eq h51]
    exact ⟨b, rfl⟩)

theorem bToJoint_apply {p : ℕ} {P T B : Subgroup G} {e : ℕ} (h51 : OddPrimeClassTwoAction G p P T B e) (b : B) :
    ((bToJoint h51 b : joint P T B) : MulAut ↥P) =
      CFSG.LocalAnalysis.RankThreeUC.Section5.BstarFaithful.bAction h51 b := rfl

theorem bToJoint_injective {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h51 : OddPrimeClassTwoAction G p P T B e) (h53 : FaithfulBinaryIrreducibleAction G p P T B ρ) :
    Function.Injective (bToJoint h51) := by
  intro a b hab
  exact CFSG.LocalAnalysis.RankThreeUC.Section5.BstarFaithful.injective h51 h53
    (congrArg Subtype.val hab)

end CFSG.LocalAnalysis.RankThreeUC.Section5.JointQuotientAction
