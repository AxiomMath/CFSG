module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
public import CFSG.FeitThompson.Local.FrattiniQuotientAutomorphismKernelPGroup
import CFSG.FeitThompson.Local.OddCriticalExponentSubgroup
import CFSG.FeitThompson.Local.FixedOrderElementaryAbelianCover
import CFSG.FeitThompson.Local.ExponentPrimeFrattiniDimensionTwo

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Matrix Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p n : ℕ} {P : Type*} [Group P]

def autRestrict (A : Subgroup (MulAut P)) (H : Subgroup P) [H.Characteristic] :
    ↥A →* MulAut ↥H := (MulAut.characteristic H).comp A.subtype

@[simp]
theorem coe_autRestrict_apply_apply (A : Subgroup (MulAut P)) (H : Subgroup P) [H.Characteristic]
    (a : ↥A) (x : ↥H) : (autRestrict A H a x : P) = (a : MulAut P) (x : P) :=
  MulAut.characteristic_apply_apply_coe H _ x

def autFrattiniQuotientRep (A : Subgroup (MulAut P)) (H : Subgroup P) [H.Characteristic] :
    ↥A →* MulAut (↥H ⧸ frattini ↥H) :=
  (frattiniQuotientAut ↥H).comp (autRestrict A H)

@[simp]
theorem autFrattiniQuotientRep_apply_mk (A : Subgroup (MulAut P)) (H : Subgroup P)
    [H.Characteristic] (a : ↥A) (x : ↥H) :
    autFrattiniQuotientRep A H a (QuotientGroup.mk x)
      = (QuotientGroup.mk (autRestrict A H a x) : ↥H ⧸ frattini ↥H) :=
  frattiniQuotientAut_apply_mk _ x

theorem ker_autFrattiniQuotientRep (A : Subgroup (MulAut P)) (H : Subgroup P) [H.Characteristic] :
    (autFrattiniQuotientRep A H).ker = (autKerFrattini ↥H).comap (autRestrict A H) := by
  rw [autFrattiniQuotientRep, autKerFrattini_eq_ker, MonoidHom.comap_ker]

theorem mem_ker_autFrattiniQuotientRep {A : Subgroup (MulAut P)} {H : Subgroup P}
    [H.Characteristic] {a : ↥A} :
    a ∈ (autFrattiniQuotientRep A H).ker ↔ ∀ x : ↥H,
      (QuotientGroup.mk (autRestrict A H a x) : ↥H ⧸ frattini ↥H) = QuotientGroup.mk x := by
  rw [ker_autFrattiniQuotientRep, Subgroup.mem_comap, mem_autKerFrattini]

theorem isPGroup_ker_autRestrict {A : Subgroup (MulAut P)} {H : Subgroup P} [H.Characteristic]
    (hfix : IsPGroup p (fixingSubgroup (MulAut P) (H : Set P))) :
    IsPGroup p (autRestrict A H).ker := by
  have hmem : ∀ a : ↥(autRestrict A H).ker,
      (A.subtype.comp (autRestrict A H).ker.subtype) a ∈
        fixingSubgroup (MulAut P) (H : Set P) := by
    intro a
    rw [mem_fixingSubgroup_iff]
    intro x hx
    have h2 : (autRestrict A H (a : ↥A)) ⟨x, hx⟩ = ⟨x, hx⟩ := by
      rw [MonoidHom.mem_ker.1 a.2]; rfl
    exact congrArg Subtype.val h2
  refine IsPGroup.of_injective hfix (MonoidHom.codRestrict _ _ hmem) fun a b hab => ?_
  simp only [Subtype.ext_iff, MonoidHom.codRestrict_apply, MonoidHom.comp_apply,
    Subgroup.coe_subtype] at hab ⊢
  exact hab

theorem isPGroup_ker_autFrattiniQuotientRep {A : Subgroup (MulAut P)} {H : Subgroup P}
    [H.Characteristic] (hp : p.Prime) (hH : Nat.card ↥H = p ^ n)
    (hfix : IsPGroup p (fixingSubgroup (MulAut P) (H : Set P))) :
    IsPGroup p (autFrattiniQuotientRep A H).ker := by
  rw [ker_autFrattiniQuotientRep]
  exact (isPGroup_autKerFrattini hp hH).comap_of_ker_isPGroup _ (isPGroup_ker_autRestrict hfix)

theorem exists_normal_isPGroup_injective_quotient_toGL_of_elementaryAbelianPRank_le_two
    [Finite P] [Nontrivial P] (hp : p.Prime) (hodd : Odd p) (hP : IsPGroup p P)
    (hrank : elementaryAbelianPRank p P ≤ 2) (A : Subgroup (MulAut P)) :
    ∃ (B : Subgroup ↥A) (_ : B.Normal) (d : ℕ), IsPGroup p ↥B ∧ (d = 1 ∨ d = 2) ∧
      ∃ f : (↥A ⧸ B) →* GL (Fin d) (ZMod p), Function.Injective f := by
  have := Fact.mk hp
  obtain ⟨H, hH⟩ := exists_isOddCriticalExponentSubgroup hp hodd hP
  have hchar := hH.characteristic
  have hnt : Nontrivial ↥H := hH.nontrivial
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 (hP.to_subgroup H)
  have hrankH : elementaryAbelianPRank p ↥H ≤ 2 :=
    le_trans (elementaryAbelianPRank_subgroup_le hp.one_lt H) hrank
  obtain ⟨d, hd1, hd2, -, ⟨e⟩⟩ :=
    exists_mulEquiv_quotient_frattini_of_elementaryAbelianPRank_le_two (P := ↥H) hp hrankH
      (fun x => Subtype.ext (by simpa using hH.pow_eq_one x x.2))
  refine ⟨(autFrattiniQuotientRep A H).ker, inferInstance, d,
    isPGroup_ker_autFrattiniQuotientRep hp hm hH.isPGroup_fixingSubgroup, by omega, ?_⟩
  exact ⟨(mulAutMulEquivGL _ (e.trans (MulEquiv.piMultiplicative _).symm)).toMonoidHom.comp
      (QuotientGroup.kerLift _),
    (mulAutMulEquivGL _ _).injective.comp (QuotientGroup.kerLift_injective _)⟩

theorem exists_normal_card_eq_pow_injective_quotient_toGL_of_elementaryAbelianPRank_le_two
    [Nontrivial P] (hp : p.Prime) (hodd : Odd p) (hcard : Nat.card P = p ^ n)
    (hrank : elementaryAbelianPRank p P ≤ 2) (A : Subgroup (MulAut P)) :
    ∃ (B : Subgroup ↥A) (_ : B.Normal) (d k : ℕ), Nat.card ↥B = p ^ k ∧ (d = 1 ∨ d = 2) ∧
      ∃ f : (↥A ⧸ B) →* GL (Fin d) (ZMod p), Function.Injective f := by
  have := Fact.mk hp
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.pos.ne')
  obtain ⟨B, hBnormal, d, hBp, hd, f, hf⟩ :=
    exists_normal_isPGroup_injective_quotient_toGL_of_elementaryAbelianPRank_le_two hp hodd
      (IsPGroup.of_card hcard) hrank A
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hBp
  exact ⟨B, hBnormal, d, k, hk, hd, f, hf⟩

end

end CFSG.FeitThompson
