module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Quot.Elem

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp
open scoped commutatorElement

variable {G : Type} [Group G] (M : Subgroup G) [M.Normal]

theorem map_lf_conj {Z : Subgroup (CQ M)} (hZp : ⁅Z, Z⁆ = Z) (hZM : Z ≤ M.map (cq M)) (s : G) :
    ((lf M Z).map (MulAut.conj s).toMonoidHom).map (cq M) =
      Z.map (MulAut.conj (cq M s)).toMonoidHom := by
  rw [← Hyp.map_map_conj, map_lf M hZp hZM]

theorem lf_conj_eq_iff {Z : Subgroup (CQ M)} (hZp : ⁅Z, Z⁆ = Z) (hZM : Z ≤ M.map (cq M)) (s : G) :
    (lf M Z).map (MulAut.conj s).toMonoidHom = lf M Z ↔
      Z.map (MulAut.conj (cq M s)).toMonoidHom = Z := by
  constructor
  · intro h
    have := map_lf_conj M hZp hZM s
    rw [h, map_lf M hZp hZM] at this
    exact this.symm
  · intro h
    refine eq_of_map_eq_cq M (map_conj_le_of_normal M (lf_le M Z) s) (lf_le M Z)
      (commutator_map_of_perfect _ (commutator_lf M hZp hZM)) (commutator_lf M hZp hZM) ?_
    rw [map_lf_conj M hZp hZM s, h, map_lf M hZp hZM]

theorem cqEquiv_of_map_cq {P : Subgroup G} (hP : P ≤ M) (hPp : ⁅P, P⁆ = P) {Z : Subgroup (CQ M)}
    (h : P.map (cq M) = Z) :
    Nonempty ((↥P ⧸ center ↥P) ≃* (↥Z ⧸ center ↥Z)) := by
  subst h
  have : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.2 hPp
  exact cqEquiv_of_cover (cqOn M P) (cqOn_surjective M P) (ker_cqOn_le_center M hP)

theorem cqEquiv_lf {Z : Subgroup (CQ M)} (hZp : ⁅Z, Z⁆ = Z) (hZM : Z ≤ M.map (cq M)) :
    Nonempty ((↥(lf M Z) ⧸ center ↥(lf M Z)) ≃* (↥Z ⧸ center ↥Z)) :=
  cqEquiv_of_map_cq M (lf_le M Z) (commutator_lf M hZp hZM) (map_lf M hZp hZM)

theorem link5a_lf {Lp Li : Subgroup (CQ M)} (hLp : ⁅Lp, Lp⁆ = Lp) (hLi : ⁅Li, Li⁆ = Li)
    (hLpM : Lp ≤ M.map (cq M)) (hLiM : Li ≤ M.map (cq M)) (s : G)
    (hne : Li ≠ Li.map (MulAut.conj (cq M s)).toMonoidHom)
    (hiso : Nonempty ((↥Li ⧸ center ↥Li) ≃* (↥Lp ⧸ center ↥Lp))) :
    lf M Li ≠ (lf M Li).map (MulAut.conj s).toMonoidHom ∧
      Nonempty ((↥(lf M Li) ⧸ center ↥(lf M Li)) ≃* (↥(lf M Lp) ⧸ center ↥(lf M Lp))) := by
  refine ⟨fun h => hne ((lf_conj_eq_iff M hLi hLiM s).1 h.symm).symm, ?_⟩
  obtain ⟨e₁⟩ := cqEquiv_lf M hLi hLiM
  obtain ⟨e₂⟩ := hiso
  obtain ⟨e₃⟩ := cqEquiv_lf M hLp hLpM
  exact ⟨(e₁.trans e₂).trans e₃.symm⟩

end CFSG.EvenSporadicStandard.Induction.Junction
