module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Local.QuadraticActionsDescendSections
import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
import CFSG.FeitThompson.Local.CoprimeActionSelfCentralizingFixedPGroup

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {A V : Type*} [Group A] [Group V] {ρ : A →* MulAut V} {N : Subgroup V}

theorem fixedPoints_range_comp_subtype (ρ : A →* MulAut V) (B : Subgroup A) :
    FixedPoints.subgroup (ρ.comp B.subtype).range V = FixedPoints.subgroup (B.map ρ) V := by
  rw [MonoidHom.range_comp, Subgroup.range_subtype]

theorem mem_fixedPoints_comp_subtype_iff (ρ : A →* MulAut V) (B : Subgroup A) {v : V} :
    v ∈ FixedPoints.subgroup (ρ.comp B.subtype).range V ↔ ∀ b ∈ B, ρ b v = v := by
  rw [mem_fixedPoints_range_iff]
  exact ⟨fun h b hb => h ⟨b, hb⟩, fun h b => h b b.2⟩

theorem IsInvariantSubgroup.comp (hN : IsInvariantSubgroup ρ N) {B : Type*} [Group B]
    (f : B →* A) : IsInvariantSubgroup (ρ.comp f) N :=
  isInvariantSubgroup_iff_forall_map_eq.2 fun b => hN.map_eq (f b)

theorem IsInvariantSubgroup.restrictAut_comp (hN : IsInvariantSubgroup ρ N) {B : Type*} [Group B]
    (f : B →* A) : (hN.comp f).restrictAut = hN.restrictAut.comp f :=
  MonoidHom.ext fun b => MulEquiv.ext fun x => Subtype.ext (by simp)

theorem IsInvariantSubgroup.quotientAut_comp [N.Normal] (hN : IsInvariantSubgroup ρ N)
    {B : Type*} [Group B] (f : B →* A) : (hN.comp f).quotientAut = hN.quotientAut.comp f :=
  MonoidHom.ext fun b => MulEquiv.ext fun x => by
    induction x using QuotientGroup.induction_on with
    | H v => simp

theorem IsInvariantSubgroup.map_subtype_fixedPoints_restrictAut (hN : IsInvariantSubgroup ρ N) :
    (FixedPoints.subgroup hN.restrictAut.range ↥N).map N.subtype
      = N ⊓ FixedPoints.subgroup ρ.range V := by
  ext v
  simp only [Subgroup.mem_map, Subgroup.coe_subtype, Subgroup.mem_inf]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, (mem_fixedPoints_range_iff ρ).2 fun b => ?_⟩
    simpa using congrArg Subtype.val ((mem_fixedPoints_range_iff hN.restrictAut).1 hx b)
  · rintro ⟨hv, hf⟩
    rw [mem_fixedPoints_range_iff ρ] at hf
    exact ⟨⟨v, hv⟩, (mem_fixedPoints_range_iff hN.restrictAut).2
      (fun b => Subtype.ext (by simpa using hf b)), rfl⟩

section Main

variable [Finite A] [Finite V] [Group.IsSolvable A] [Group.IsSolvable V] [N.Normal]

theorem natCard_fixedPoints_range_eq_mul (hN : IsInvariantSubgroup ρ N)
    (hcop : (Nat.card A).Coprime (Nat.card V)) :
    Nat.card (FixedPoints.subgroup ρ.range V)
      = Nat.card (FixedPoints.subgroup hN.restrictAut.range ↥N)
        * Nat.card (FixedPoints.subgroup hN.quotientAut.range (V ⧸ N)) := by
  have hf : ((QuotientGroup.mk' N).comp (FixedPoints.subgroup ρ.range V).subtype).range
      = FixedPoints.subgroup hN.quotientAut.range (V ⧸ N) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, fixedPoints_quotientAut_range hN hcop]
  have hker : ((QuotientGroup.mk' N).comp (FixedPoints.subgroup ρ.range V).subtype).ker
      = N.subgroupOf (FixedPoints.subgroup ρ.range V) := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rfl
  have hcardker : Nat.card ((QuotientGroup.mk' N).comp
        (FixedPoints.subgroup ρ.range V).subtype).ker
      = Nat.card (FixedPoints.subgroup hN.restrictAut.range ↥N) := by
    rw [hker, ← Subgroup.card_subtype (FixedPoints.subgroup ρ.range V)
      (N.subgroupOf (FixedPoints.subgroup ρ.range V)), Subgroup.subgroupOf_map_subtype,
      ← hN.map_subtype_fixedPoints_restrictAut, Subgroup.card_subtype]
  rw [← Subgroup.card_mul_index ((QuotientGroup.mk' N).comp
    (FixedPoints.subgroup ρ.range V).subtype).ker, hcardker, Subgroup.index_ker, hf]

theorem natCard_fixedPoints_comp_subtype_eq_mul (hN : IsInvariantSubgroup ρ N)
    (hcop : (Nat.card A).Coprime (Nat.card V)) (B : Subgroup A) :
    Nat.card (FixedPoints.subgroup (ρ.comp B.subtype).range V)
      = Nat.card (FixedPoints.subgroup (hN.restrictAut.comp B.subtype).range ↥N)
        * Nat.card (FixedPoints.subgroup (hN.quotientAut.comp B.subtype).range (V ⧸ N)) := by
  have h := natCard_fixedPoints_range_eq_mul (hN.comp B.subtype)
    (hcop.coprime_dvd_left (Subgroup.card_subgroup_dvd_card B))
  rwa [hN.restrictAut_comp B.subtype, hN.quotientAut_comp B.subtype] at h

theorem natCard_fixedPoints_map_eq_mul (hN : IsInvariantSubgroup ρ N)
    (hcop : (Nat.card A).Coprime (Nat.card V)) (B : Subgroup A) :
    Nat.card (FixedPoints.subgroup (B.map ρ) V)
      = Nat.card (FixedPoints.subgroup (B.map hN.restrictAut) ↥N)
        * Nat.card (FixedPoints.subgroup (B.map hN.quotientAut) (V ⧸ N)) := by
  rw [← fixedPoints_range_comp_subtype, ← fixedPoints_range_comp_subtype,
    ← fixedPoints_range_comp_subtype]
  exact natCard_fixedPoints_comp_subtype_eq_mul hN hcop B

end Main

end CFSG.FeitThompson
