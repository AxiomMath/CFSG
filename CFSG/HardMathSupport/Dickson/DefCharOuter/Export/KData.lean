module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Defs
public import CFSG.HardMathSupport.Dickson.I271.Support.OuterCoreFree
public import CFSG.HardMathSupport.Dickson.I271.Support.OuterKData

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Dickson.I271 (KDOutExc KDOutCoreFree KDOutCentInner fixSubgroup_congr)
open CFSG.Yardstones.Md42047359a2a (lieFamily)

theorem not_glaPComponent_of_solvable {G : Type} [Group G] [Finite G] {p : ℕ} {X I : Subgroup G}
    (hX : Group.IsSolvable ↥X) (hI : GLAPComponent p X I) : False := by
  have hIX : I ≤ X := hI.1
  haveI : Group.IsPerfect ↥I := Subgroup.isPerfect_iff.mpr (glaPComponent_perfect hI)
  haveI : Group.IsSolvable ↥I :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hIX)
      (Subgroup.inclusion_injective hIX)
  haveI : Nontrivial ↥I := (Subgroup.nontrivial_iff_ne_bot I).2 (glaPComponent_ne_bot' hI)
  exact Group.IsPerfect.not_isSolvable (G := ↥I) inferInstance

theorem orderOf_eq_of_pow_eq_one_of_not_inner {S : Type} [Group S] {p : ℕ} (hp : p.Prime)
    {α : MulAut S} (hα : α ^ p = 1) (hout : α ∉ innerAut S) : orderOf α = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact orderOf_eq_prime hα fun h => hout (h ▸ (innerAut S).one_mem)

theorem kdOutChevUnique_of_outerCent (hO : OuterCentAll) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    KDOutChevUnique p := by
  intro d hd α hα hout I J hI hJ
  obtain ⟨hfin, hsimp, hnc⟩ := (hO (lieFamily d.1)).1 d rfl (by rw [hd]; exact hp2)
  haveI := hfin
  haveI := hsimp
  exact ((hO (lieFamily d.1)).2 (TauCeti.CFSGIndex.lie d).Group hsimp hnc d rfl
    ⟨MulEquiv.refl _⟩ p hp hp2 hd.symm α hα hout).unique I J hI hJ

theorem kdOutChev_of_outerCent (hO : OuterCentAll) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    KDOutChev p := by
  intro d hd α hα hout I hI
  obtain ⟨hfin, hsimp, hnc⟩ := (hO (lieFamily d.1)).1 d rfl (by rw [hd]; exact hp2)
  haveI := hfin
  haveI := hsimp
  exact ((hO (lieFamily d.1)).2 (TauCeti.CFSGIndex.lie d).Group hsimp hnc d rfl
    ⟨MulEquiv.refl _⟩ p hp hp2 hd.symm α hα hout).chev I hI

theorem kdOutCoreFree_of_outerCent (hO : OuterCentAll) : KDOutCoreFree := by
  intro S _ _ hS hnc idx he p hp hp2 hchar hexc β hβ hout
  exact ((hO (lieFamily idx.1)).2 S hS hnc idx rfl he p hp hp2 hchar.symm β hβ hout).core hexc

theorem kdOutCentInner_of_outerCent (hO : OuterCentAll) : KDOutCentInner := by
  intro S _ _ hS hnc idx he p hp hp2 hchar hexc β hβ hout w hw hwβ hfix
  exact ((hO (lieFamily idx.1)).2 S hS hnc idx rfl he p hp hp2 hchar.symm β hβ hout).cent
    hexc w hw hwβ hfix

theorem kdOutExc_of_outerCent (hO : OuterCentAll) (hA : KDAmbSolv 3) : KDOutExc := by
  intro S _ _ hS hnc hChev α hα hout I hI
  have hord : orderOf α = 3 := orderOf_eq_of_pow_eq_one_of_not_inner Nat.prime_three hα hout
  rcases hChev with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | lie idx =>
      have hchar : idx.1.characteristic = 3 := hi
      have hdata := (hO (lieFamily idx.1)).2 S hS hnc idx rfl ⟨e⟩ 3 Nat.prime_three (by norm_num)
        hchar.symm α hord hout
      exact ⟨hdata.noHatSix rfl I hI, fun hL β hβ hβα hmap =>
        hdata.l227 rfl I hI hL β hβ hβα hmap⟩
    | cyclic _ _ => exact absurd hi (by simp [onLie])
    | alternating _ _ => exact absurd hi (by simp [onLie])
    | sporadic _ => exact absurd hi (by simp [onLie])
  · exfalso
    have hα' : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hα, map_one]
    have hα1 : MulAut.congr e α ≠ 1 := fun h =>
      hout ((MulAut.congr e).injective (h.trans (map_one _).symm) ▸ (innerAut S).one_mem)
    have hsol := hA i hi (MulAut.congr e α) hα' hα1
    rw [fixSubgroup_congr e α] at hsol
    haveI : Group.IsSolvable ↥((fixSubgroup α).map e.toMonoidHom) := hsol
    haveI : Group.IsSolvable ↥(fixSubgroup α) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.equivMapOfInjective (fixSubgroup α) e.toMonoidHom e.injective).toMonoidHom)
        (Subgroup.equivMapOfInjective (fixSubgroup α) e.toMonoidHom e.injective).injective
    exact not_glaPComponent_of_solvable this hI

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
