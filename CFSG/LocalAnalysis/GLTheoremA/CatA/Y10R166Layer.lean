module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase
public import CFSG.LocalAnalysis.GLTheoremA.S10.CaseGamma

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open

section QLayer

variable {X : Type} [Group X] [Finite X]

theorem le_glaPLayer_of_isSubnormal_quasisimple {q : ℕ} (hq : q.Prime) {H L : Subgroup X}
    (hsn : IsSubnormal L H) (hL : CFSG.Open.IsQuasisimple ↥L)
    (hdvd : q ∣ Nat.card (↥L ⧸ Subgroup.center ↥L)) :
    L ≤ GLAPLayer q H :=
  le_sSup (CFSG.LocalAnalysis.GLTheoremA.S10.glaPComponent_of_quasisimple hq hsn hL hdvd)

theorem glaPLayer_ne_bot_of_isSubnormal_quasisimple {q : ℕ} (hq : q.Prime) {H L : Subgroup X}
    (hsn : IsSubnormal L H) (hL : CFSG.Open.IsQuasisimple ↥L)
    (hdvd : q ∣ Nat.card (↥L ⧸ Subgroup.center ↥L)) :
    GLAPLayer q H ≠ ⊥ := by
  haveI : Nontrivial ↥L := CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_nontrivial hL
  have hLne : L ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot L).1 inferInstance
  intro hbot
  exact hLne (le_bot_iff.1 (hbot ▸ le_glaPLayer_of_isSubnormal_quasisimple hq hsn hL hdvd))

theorem glaPLayer_ne_bot_of_normal_quasisimple {q : ℕ} (hq : q.Prime) {H L : Subgroup X}
    (hLH : L ≤ H) (hN : (L.subgroupOf H).Normal) (hL : CFSG.Open.IsQuasisimple ↥L)
    (hdvd : q ∣ Nat.card (↥L ⧸ Subgroup.center ↥L)) :
    GLAPLayer q H ≠ ⊥ :=
  glaPLayer_ne_bot_of_isSubnormal_quasisimple hq
    (IsSubnormal.step hLH hN (IsSubnormal.refl H)) hL hdvd

end QLayer

section Component

variable {X : Type} [Group X]

theorem isComponentOf_and_glaLayer_eq_of_normal_solvable {C J : Subgroup X} (hJC : J ≤ C)
    (hN : (J.subgroupOf C).Normal) (hJ : CFSG.Open.IsQuasisimple ↥J)
    (hsolv : Group.IsSolvable (↥C ⧸ J.subgroupOf C)) :
    CFSG.Open.IsComponentOf J C ∧ GLALayer C = J := by
  haveI : (J.subgroupOf C).Normal := hN
  have hcomp : CFSG.Open.IsComponentOf J C :=
    ⟨hJC, IsSubnormal.step hJC hN (IsSubnormal.refl C), hJ⟩
  haveI : Group.IsSolvable (↥C ⧸ J.subgroupOf C) := hsolv
  refine ⟨hcomp, le_antisymm ?_ (CFSG.LocalAnalysis.GLTheoremA.I142N.le_GLALayer hcomp)⟩
  refine CFSG.LocalAnalysis.GLTheoremA.I142N.GLALayer_le_of fun L hL => ?_
  set π : ↥C →* (↥C ⧸ J.subgroupOf C) := QuotientGroup.mk' _
  haveI : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
  have hperf : Group.IsPerfect ↥(L.subgroupOf C) :=
    Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hL.1).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hL.1).symm.surjective
  have himg : Group.IsPerfect ↥(Subgroup.map π (L.subgroupOf C)) := Group.IsPerfect.map (f := π)
  have hbot : Subgroup.map π (L.subgroupOf C) = ⊥ := by
    by_contra hne
    haveI : Nontrivial ↥(Subgroup.map π (L.subgroupOf C)) :=
      (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isSolvable ↥(Subgroup.map π (L.subgroupOf C)) inferInstance
  intro l hl
  have hπ : π (⟨l, hL.1 hl⟩ : ↥C) = 1 := by
    have hmem : π (⟨l, hL.1 hl⟩ : ↥C) ∈ Subgroup.map π (L.subgroupOf C) :=
      ⟨⟨l, hL.1 hl⟩, (Subgroup.mem_subgroupOf).2 hl, rfl⟩
    rw [hbot] at hmem
    simpa using hmem
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hπ)

theorem isComponentOf_and_glaLayer_eq_of_normal_solvable_of_isQuasisimple {C J : Subgroup X}
    (hJC : J ≤ C) (hN : (J.subgroupOf C).Normal) (hJ : CFSG.IsQuasisimple ↥J)
    (hsolv : Group.IsSolvable (↥C ⧸ J.subgroupOf C)) :
    CFSG.Open.IsComponentOf J C ∧ GLALayer C = J :=
  isComponentOf_and_glaLayer_eq_of_normal_solvable hJC hN
    ⟨hJ.1.commutator_eq_top, hJ.2.1⟩ hsolv

end Component

end CFSG.LocalAnalysis.GLTheoremA.Y10F
