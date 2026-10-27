module

import CFSG.GroupTheory.SteinbergBSNormalPlane
import CFSG.Goldschmidt.Steps.Sec82PGroup
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Setting

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

theorem exists_centralizer_rank_three_of_mem_frattini {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hR : IsPGroup p R) {x : R} (hxp : x ^ p = 1)
    {Q : Subgroup R} (hxQ : ∃ h : x ∈ Q, (⟨x, h⟩ : Q) ∈ frattini Q) {A : Subgroup R}
    (hAe : CFSG.IsElementaryAbelian p A) (hAc : Nat.card A = p ^ 3) :
    ∃ E : Subgroup R, E ≤ centralizer ({x} : Set R) ∧ CFSG.IsElementaryAbelian p E ∧
      p ^ 3 ≤ Nat.card E := by
  classical
  have hnc : ¬ IsCyclic (⊤ : Subgroup R) := by
    intro hc
    have : IsCyclic R :=
      isCyclic_of_surjective (Subgroup.topEquiv (G := R)).toMonoidHom
        (Subgroup.topEquiv (G := R)).surjective
    have : IsCyclic A := inferInstance
    have h1 : Monoid.exponent A = Nat.card A := IsCyclic.exponent_eq_card
    have h2 : Monoid.exponent A ∣ p := hAe.exponent_dvd_p
    rw [h1, hAc] at h2
    have h3 := Nat.le_of_dvd hp.out.pos h2
    have h4 : p < p ^ 3 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 3 := Nat.pow_lt_pow_right hp.out.one_lt (by norm_num)
    omega
  obtain ⟨V, -, hVn, hVc, hVp, hVcomm⟩ :=
    CFSG.Goldschmidt.Sec82.exists_normal_plane_le hp2 hR (⊤ : Subgroup R) hnc
  have hVe : CFSG.IsElementaryAbelian p V := CFSG.IsElementaryAbelian.of_forall hVcomm hVp
  have : V.Normal := hVn
  have : CFSG.IsElementaryAbelian p A := hAe
  obtain ⟨hCn, hVC, hidx, -, hUC, -, hUe, hU3, -⟩ :=
    CFSG.GroupTheory.SteinbergBS.normal_plane_centralizer_rank_three hR V A hVc hAc
  have : (centralizer (V : Set R)).Normal := hCn
  have hxC : x ∈ centralizer (V : Set R) := by
    obtain ⟨hxQ', hxfr⟩ := hxQ
    by_cases hQC : Q ≤ centralizer (V : Set R)
    · exact hQC hxQ'
    · set D : Subgroup Q := (centralizer (V : Set R)).subgroupOf Q with hD
      have hDidx : D.index ∣ p := by
        have h1 : D.index = (centralizer (V : Set R)).relIndex Q := rfl
        rw [h1]
        refine (Subgroup.relIndex_dvd_index_of_normal _ _).trans ?_
        obtain ⟨k, hk⟩ := hR.index (centralizer (V : Set R))
        have hk1 : k ≤ 1 := by
          refine (Nat.pow_le_pow_iff_right hp.out.one_lt).mp ?_
          rw [pow_one, ← hk]
          exact hidx
        rw [hk]
        calc p ^ k ∣ p ^ 1 := pow_dvd_pow p hk1
          _ = p := pow_one p
      have hD1 : D.index ≠ 1 := by
        intro h1
        exact hQC (Subgroup.subgroupOf_eq_top.mp (Subgroup.index_eq_one.mp h1))
      have hDp : D.index = p :=
        ((Nat.dvd_prime hp.out).mp hDidx).resolve_left hD1
      have hcoatom : IsCoatom D := Subgroup.isCoatom_of_index_prime (hDp ▸ hp.out)
      exact frattini_le_coatom hcoatom hxfr
  by_cases hxV : x ∈ V
  ·
    refine ⟨(A ⊓ centralizer (V : Set R)) ⊔ V, fun u hu => ?_, hUe, hU3⟩
    refine mem_centralizer_iff.mpr fun h hh => ?_
    rw [Set.mem_singleton_iff.mp hh]
    exact mem_centralizer_iff.mp (hUC hu) x hxV
  ·
    have hxz : zpowers x ≤ centralizer (V : Set R) := zpowers_le.mpr hxC
    have : CFSG.IsElementaryAbelian p (zpowers x) :=
      CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hxp
    have hcomm : ∀ e ∈ V, e * x = x * e := fun e he => mem_centralizer_iff.mp hxC e he
    have hcard : Nat.card ↥(V ⊔ zpowers x) = Nat.card V * p :=
      CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp.out V hxp hxV hcomm
    refine ⟨V ⊔ zpowers x, ?_, CFSG.IsElementaryAbelian.sup_of_le_centralizer hxz, ?_⟩
    · refine sup_le (fun v hv => ?_)
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
      exact mem_centralizer_singleton_iff.mpr (hcomm v hv)
    · rw [hcard, hVc, ← pow_succ]

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem Situation.exists_elemAbelian_cube_of_sylow (hS : Situation G p P M) (R : Sylow p G) :
    ∃ A : Subgroup G, A ≤ (R : Subgroup G) ∧ CFSG.IsElementaryAbelian p A ∧
      Nat.card A = p ^ 3 := by
  have hprime := hS.prime
  have h4 := four_le_pRank_sylow hS.loc.beta R
  obtain ⟨E, hER, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hprime.one_lt (R : Subgroup G)
  have hdvd : p ^ 3 ∣ Nat.card E := hEc ▸ pow_dvd_pow p (by omega)
  obtain ⟨A, hAc, -, hAE⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le hprime (H := ⊥) (L := E) (by simp) hdvd bot_le
  exact ⟨A, hAE.trans hER,
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).2
      (CFSG.Open.IsElemAbelian.mono hE hAE), hAc⟩

theorem x_not_mem_frattini (hS : Situation G p P M) (hx : Point P M x) {Q : Subgroup G}
    (hQ : IsPGroup p Q) : x ∉ (frattini ↥Q).map Q.subtype := by
  classical
  have hprime := hS.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  rintro ⟨q, hqfr, hqx⟩
  obtain ⟨R, hQR⟩ := hQ.exists_le_sylow
  have hxR : x ∈ (R : Subgroup G) := hQR (hqx ▸ q.2)
  obtain ⟨A, hAR, hAe, hAc⟩ := hS.exists_elemAbelian_cube_of_sylow R
  set e := (Subgroup.subgroupOfEquivOfLe hQR).symm with he
  have hxQ : ∃ h : (⟨x, hxR⟩ : ↥(R : Subgroup G)) ∈ Q.subgroupOf (R : Subgroup G),
      (⟨⟨x, hxR⟩, h⟩ : ↥(Q.subgroupOf (R : Subgroup G))) ∈
        frattini ↥(Q.subgroupOf (R : Subgroup G)) := by
    have h1 : (⟨x, hxR⟩ : ↥(R : Subgroup G)) ∈ Q.subgroupOf (R : Subgroup G) :=
      show x ∈ Q from hqx ▸ q.2
    refine ⟨h1, ?_⟩
    have h2 : e q ∈ frattini ↥(Q.subgroupOf (R : Subgroup G)) :=
      Subgroup.mem_comap.mp (frattini_le_comap_frattini_of_surjective (φ := e.toMonoidHom)
        e.surjective (SetLike.mem_coe.mp hqfr))
    have h3 : e q = ⟨⟨x, hxR⟩, h1⟩ := Subtype.ext (Subtype.ext hqx)
    rwa [h3] at h2
  have hA' : CFSG.IsElementaryAbelian p ↥(A.subgroupOf (R : Subgroup G)) :=
    CFSG.IsElementaryAbelian.subgroupOf hAR
  have hAc' : Nat.card ↥(A.subgroupOf (R : Subgroup G)) = p ^ 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAR).toEquiv).trans hAc
  have hxp : (⟨x, hxR⟩ : ↥(R : Subgroup G)) ^ p = 1 := Subtype.ext hx.pow_eq_one
  obtain ⟨E, hEC, hEe, hE3⟩ := exists_centralizer_rank_three_of_mem_frattini hS.ne_two
    R.isPGroup' hxp hxQ hA' hAc'
  have hE : IsElemAbelian p (E.map (R : Subgroup G).subtype) := by
    have h := CFSG.IsElementaryAbelian.map_subtype (p := p) (K := (R : Subgroup G)) (H := E)
    exact ⟨h.toIsMulCommutative, fun y hy => CFSG.elemPow_eq_one_of_isElementaryAbelian y hy⟩
  have hEC' : E.map (R : Subgroup G).subtype ≤ centralizer ({x} : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    have h := mem_centralizer_singleton_iff.mp (hEC he)
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h)
  have hEp : IsPGroup p (E.map (R : Subgroup G).subtype) :=
    fun y => ⟨1, Subtype.ext (by simpa using hE.2 y y.2)⟩
  obtain ⟨n, hn⟩ := hEp.exists_card_eq
  have hn2 : n ≤ 2 := (CFSG.SectionRank.le_pRank hprime.one_lt hEC' hE hn).trans
    (hx.pRank_centralizer_le hS)
  have hcard : p ^ 3 ≤ Nat.card (E.map (R : Subgroup G).subtype) := by
    rw [card_map_of_injective (R : Subgroup G).subtype_injective]
    exact hE3
  rw [hn] at hcard
  have := (Nat.pow_le_pow_iff_right hprime.one_lt).mp hcard
  omega

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
