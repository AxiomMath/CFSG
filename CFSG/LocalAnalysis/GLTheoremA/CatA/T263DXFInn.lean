module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerLie
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerD4
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutAbstract
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154AmbU
import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXTriv
import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinctShapes

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)

private theorem eq_one_of_mem_range_conj {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hpX : ¬ p ∣ Nat.card X) (hZ : Subgroup.center X = ⊥) {α : MulAut X}
    (hα : α ∈ (MulAut.conj : X →* MulAut X).range) (hαp : α ^ p = 1) : α = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, rfl⟩ := hα
  have hjp : j ^ p = 1 := by
    have hc : j ^ p ∈ Subgroup.center X := Subgroup.mem_center_iff.2 fun x => by
      have hx := congrArg (fun φ : MulAut X => φ x)
        (show MulAut.conj (j ^ p) = 1 by rw [map_pow]; exact hαp)
      simp only [MulAut.conj_apply, MulAut.one_apply] at hx
      calc x * j ^ p = (j ^ p * x * (j ^ p)⁻¹) * j ^ p := by rw [hx]
        _ = j ^ p * x := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  have hj1 : j = 1 := by
    by_contra hj
    have hord : orderOf j = p := orderOf_eq_prime hjp hj
    apply hpX
    rw [← hord]
    exact orderOf_dvd_natCard j
  rw [hj1, map_one]

theorem eq_one_of_mem_innAutDerived_of_lieModel
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n m p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : LieModel X t n 2 m) (hpX : ¬ p ∣ Nat.card X) (hZ : Subgroup.center X = ⊥)
    {α : MulAut X} (hα : α ∈ innAutDerived X) (hαp : α ^ p = 1) : α = 1 := by
  have hrk : CFSG.pRank p X ≤ 1 := by
    unfold CFSG.pRank
    refine csSup_le' ?_
    rintro r ⟨A, -, hcard⟩
    by_contra hr
    apply hpX
    have h1 : p ∣ p ^ r := dvd_pow_self p (by omega)
    rw [← hcard] at h1
    exact h1.trans (Subgroup.card_subgroup_dvd_card A)
  let heq : X ⧸ Subgroup.center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hgood : CFSG.AGLEmbedding.TwoGenInner.PGoodOut p X :=
    CFSG.AGLEmbedding.TwoGenInner.pGoodOut_of_lieModel hp hp5 h.admissible h
      (fun hmod => CFSG.RankThree.PartOne.OutStructure.not_dvd_gcd_psl_of_pRank hp hp5 hrk
        (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv heq.symm hmod))
      (fun hmod => CFSG.RankThree.PartOne.OutStructure.not_dvd_gcd_psu_of_pRank hp hp5 hrk
        (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv heq.symm hmod))
      CFSG.AGLEmbedding.TwoGenInner.d4PGood
  refine eq_one_of_mem_range_conj hp hpX hZ ?_ hαp
  exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.pElement_mem_inner_of_pGoodOut
    hp hgood ⟨1, by rw [pow_one]; exact hαp⟩ (by rw [sup_comm]; exact hα)

theorem mem_centralizer_of_isChevSimple_two
    {G : Type} [Group G] {J : Subgroup G} [Finite J] (hJ : CFSG.Open.IsQuasisimple ↥J) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hchev : IsChevSimple 2 (↥J ⧸ Subgroup.center ↥J))
    (hpJ : ¬ p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J)) {w : G} (hwp : w ^ p = 1)
    (hstab : MulAut.conj w ∈ CFSG.GroupActions.subgroupStabAut J)
    (hα : Nat.card (↥J ⧸ Subgroup.center ↥J) ≠ 360 →
      centerQuotientHom ↥J (CFSG.GroupActions.subgroupStabRestrict J ⟨MulAut.conj w, hstab⟩) ∈
        innAutDerived (↥J ⧸ Subgroup.center ↥J)) :
    w ∈ Subgroup.centralizer (J : Set G) := by
  haveI : Group.IsPerfect ↥J := ⟨hJ.1⟩
  have hZJ := CFSG.LocalAnalysis.GLTheoremA.Y10F.center_centerQuot_eq_bot hJ
  have hpow : (⟨MulAut.conj w, hstab⟩ : CFSG.GroupActions.subgroupStabAut J) ^ p = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, hwp, map_one]
  have hβp : centerQuotientHom ↥J
      (CFSG.GroupActions.subgroupStabRestrict J ⟨MulAut.conj w, hstab⟩) ^ p = 1 := by
    rw [← map_pow, ← map_pow, hpow, map_one, map_one]
  refine mem_centralizer_of_restrict_eq_one hstab ?_
  rcases hchev with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | lie d =>
      obtain ⟨t, n, m, hLM⟩ := CFSG.StandardType.ChevTwo.exists_lieModel_two_of_valid d hi e
      have h360 : Nat.card (↥J ⧸ Subgroup.center ↥J) ≠ 360 :=
        CFSG.Quasithin.H13.EvenOrd.card_ne_of_evenLieType CFSG.Quasithin.H13.EvenOrd.excl_360
          ⟨t, n, m, hLM.admissible, hLM⟩
      exact eq_one_of_mem_innAutDerived_of_lieModel hp hp5 hLM hpJ hZJ (hα h360) hβp
    | cyclic r hr => exact hi.elim
    | alternating n hn => exact hi.elim
    | sporadic s => exact hi.elim
  · have hodd : Odd (orderOf (centerQuotientHom ↥J
        (CFSG.GroupActions.subgroupStabRestrict J ⟨MulAut.conj w, hstab⟩))) :=
      Odd.of_dvd_nat (hp.odd_of_ne_two (by omega)) (orderOf_dvd_of_pow_eq_one hβp)
    obtain ⟨g, hg⟩ : ∃ g : ↥J ⧸ Subgroup.center ↥J, centerQuotientHom ↥J
        (CFSG.GroupActions.subgroupStabRestrict J ⟨MulAut.conj w, hstab⟩) = MulAut.conj g := by
      by_cases hU : CFSG.LocalAnalysis.GLTheoremA.K155X.l154AmbU33 i
      · exact CFSG.LocalAnalysis.GLTheoremA.K155X.l154_oddInner_of_u33 ⟨i, hU, ⟨e⟩⟩ _ hodd
      · exact CFSG.LocalAnalysis.GLTheoremA.K155X.l154_oddInner_of_ambAlt ⟨i, ⟨hi, hU⟩, ⟨e⟩⟩ _
          hodd
    exact eq_one_of_mem_range_conj hp hpJ hZJ ⟨g, hg.symm⟩ hβp

end CFSG.LocalAnalysis.GLTheoremA.T263.DX

end
