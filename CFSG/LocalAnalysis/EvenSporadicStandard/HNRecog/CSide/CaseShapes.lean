module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.Setup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.GrpShapeA
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.GrpShapeB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.OfMulEquivAux

@[expose] public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open Subgroup CFSG.EvenSporadicStandard.HNRecog.Fpf CFSG.EvenSporadicStandard.HNRecog
  CFSG.EvenSporadicStandard.HNRecog.Section3

variable {C : Type} [Group C] {Q : Subgroup C} [hQn : Q.Normal]
  [Module (ZMod 2) (Additive (Abelianization Q))]

private theorem cs_isConj_orderOf_eq {G : Type*} [Group G] {x y : G} (h : IsConj x y) :
    orderOf x = orderOf y := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc, ← MulAut.conj_apply]
  exact ((MulAut.conj c).orderOf_eq x).symm

private noncomputable def cs_centralizerEquiv (S : CSideSetup C Q) {σ : C}
    (hσL : σ ∈ commutator C) :
    ↥(Subgroup.centralizer ({(σ : C ⧸ Q)} : Set (C ⧸ Q))) ≃*
      ↥(Subgroup.centralizer ({A5WrTwo.baseEmb (S.θ ⟨σ, hσL⟩)} : Set A5WrTwo)) :=
  (TwoHSData.centralizerMulEquiv S.e (σ : C ⧸ Q)).trans
    (MulEquiv.subgroupCongr (by rw [S.emb]))

private theorem cs_orderOf_coords_of_prime {g : A5 × A5} {p : ℕ} (hp : Nat.Prime p)
    (hg : orderOf g = p) (h1 : g.1 ≠ 1) (h2 : g.2 ≠ 1) :
    orderOf g.1 = p ∧ orderOf g.2 = p := by
  constructor
  · have hdvd : orderOf g.1 ∣ p := by rw [← hg]; exact orderOf_fst_dvd_orderOf
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) h1
    · exact h
  · have hdvd : orderOf g.2 ∣ p := by rw [← hg]; exact orderOf_snd_dvd_orderOf
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) h2
    · exact h

private theorem cs_shape_one_coord_baseEmb {p : ℕ} (hp : p = 3 ∨ p = 5) {g : A5 × A5}
    (hg : orderOf g = p) (h1 : g.1 = 1 ∨ g.2 = 1) :
    IsShapeZpTimesA5 p ↥(Subgroup.centralizer ({A5WrTwo.baseEmb g} : Set A5WrTwo)) := by
  rcases h1 with h1 | h1
  · have hg' : g = (1, g.2) := Prod.ext h1 rfl
    have hy : orderOf g.2 = p := by
      have h : orderOf ((1 : A5), g.2) = p := by rw [← hg']; exact hg
      rw [Prod.orderOf_mk, orderOf_one, Nat.lcm_one_left] at h
      exact h
    obtain ⟨e1⟩ := (cSide_shape_one_coord hp hy).2
    refine ⟨(MulEquiv.subgroupCongr ?_).trans e1⟩
    rw [hg']
  · have hg' : g = (g.1, 1) := Prod.ext rfl h1
    have hx : orderOf g.1 = p := by
      have h : orderOf (g.1, (1 : A5)) = p := by rw [← hg']; exact hg
      rw [Prod.orderOf_mk, orderOf_one, Nat.lcm_one_right] at h
      exact h
    obtain ⟨e1⟩ := (cSide_shape_one_coord hp hx).1
    refine ⟨(MulEquiv.subgroupCongr ?_).trans e1⟩
    rw [hg']

theorem CSideSetup.shape_one_coord (S : CSideSetup C Q) {p : ℕ} (hp : p = 3 ∨ p = 5) {σ : C}
    (hσL : σ ∈ commutator C) (hg : orderOf (S.θ ⟨σ, hσL⟩) = p)
    (h1 : (S.θ ⟨σ, hσL⟩).1 = 1 ∨ (S.θ ⟨σ, hσL⟩).2 = 1) :
    IsShapeZpTimesA5 p ↥(Subgroup.centralizer ({(σ : C ⧸ Q)} : Set (C ⧸ Q))) := by
  obtain ⟨e1⟩ := cs_shape_one_coord_baseEmb (g := S.θ ⟨σ, hσL⟩) hp hg h1
  exact ⟨(cs_centralizerEquiv S hσL).trans e1⟩

theorem CSideSetup.shape_conj (S : CSideSetup C Q) {p : ℕ} (hp : p = 3 ∨ p = 5) {σ : C}
    (hσL : σ ∈ commutator C) (hg : orderOf (S.θ ⟨σ, hσL⟩) = p)
    (hc : IsConj (S.θ ⟨σ, hσL⟩).1 (S.θ ⟨σ, hσL⟩).2) :
    IsShapeZpWrTwo p ↥(Subgroup.centralizer ({(σ : C ⧸ Q)} : Set (C ⧸ Q))) := by
  have hge : orderOf (S.θ ⟨σ, hσL⟩).1 = orderOf (S.θ ⟨σ, hσL⟩).2 :=
    cs_isConj_orderOf_eq hc
  have hx : orderOf (S.θ ⟨σ, hσL⟩).1 = p := by
    rw [← hg, Prod.orderOf, hge, Nat.lcm_self]
  have hy : orderOf (S.θ ⟨σ, hσL⟩).2 = p := by rw [← hge]; exact hx
  obtain ⟨e1⟩ := cSide_shape_conj hp hx hy hc
  exact ⟨(cs_centralizerEquiv S hσL).trans e1⟩

theorem CSideSetup.shape_nonconj (S : CSideSetup C Q) {σ : C} (hσL : σ ∈ commutator C)
    (hg : orderOf (S.θ ⟨σ, hσL⟩) = 5) (h1 : (S.θ ⟨σ, hσL⟩).1 ≠ 1) (h2 : (S.θ ⟨σ, hσL⟩).2 ≠ 1)
    (hc : ¬ IsConj (S.θ ⟨σ, hσL⟩).1 (S.θ ⟨σ, hσL⟩).2) :
    IsShapeZpTimesZp 5 ↥(Subgroup.centralizer ({(σ : C ⧸ Q)} : Set (C ⧸ Q))) := by
  obtain ⟨hx, hy⟩ := cs_orderOf_coords_of_prime Nat.prime_five hg h1 h2
  obtain ⟨e1⟩ := cSide_shape_nonconj hx hy hc
  exact ⟨(cs_centralizerEquiv S hσL).trans e1⟩

end CFSG.EvenSporadicStandard.HNRecog.CSide
