module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSG.GroupTheory.SteinbergBSNormalPlane
import CFSG.Goldschmidt.Steps.Sec82PGroup
import CFSG.RankThree.PartOne.S9.Planes.Basic
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

private theorem sr630b_isElementaryAbelian_of_pow {R : Type*} [Group R] {p : ℕ} {V : Subgroup R}
    (hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hpow : ∀ a ∈ V, a ^ p = 1) :
    CFSG.IsElementaryAbelian p V := CFSG.IsElementaryAbelian.of_forall hcomm hpow

theorem sr630b_exists_centralizer_rank_three {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hR : IsPGroup p R) {x q : R} (hxp : x ^ p = 1)
    (hq : q ^ p = x) {A : Subgroup R} (hAe : CFSG.IsElementaryAbelian p A)
    (hAc : Nat.card A = p ^ 3) :
    ∃ E : Subgroup R, E ≤ centralizer ({x} : Set R) ∧ CFSG.IsElementaryAbelian p E ∧
      p ^ 3 ≤ Nat.card E := by
  classical
  have hnc : ¬ IsCyclic (⊤ : Subgroup R) := by
    intro hc
    have : IsCyclic (⊤ : Subgroup R) := hc
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
  have hVe : CFSG.IsElementaryAbelian p V := sr630b_isElementaryAbelian_of_pow hVcomm hVp
  have : V.Normal := hVn
  have : CFSG.IsElementaryAbelian p A := hAe
  obtain ⟨hCn, hVC, hidx, -, hUC, -, hUe, hU3, -⟩ :=
    CFSG.GroupTheory.SteinbergBS.normal_plane_centralizer_rank_three hR V A hVc hAc
  have : (centralizer (V : Set R)).Normal := hCn
  have hxC : x ∈ centralizer (V : Set R) := by
    obtain ⟨k, hk⟩ := hR.index (centralizer (V : Set R))
    have hk1 : k ≤ 1 := by
      refine (Nat.pow_le_pow_iff_right hp.out.one_lt).mp ?_
      rw [pow_one, ← hk]
      exact hidx
    have hdvd : (centralizer (V : Set R)).index ∣ p := by
      rw [hk]
      calc p ^ k ∣ p ^ 1 := pow_dvd_pow p hk1
        _ = p := pow_one p
    obtain ⟨m, hm⟩ := hdvd
    rw [← hq, hm, pow_mul]
    exact pow_mem (Subgroup.pow_index_mem _ q) m
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

theorem sr630b_not_pow_of_rank {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {R : Subgroup G} (hR : IsPGroup p R) {x q : G} (hxp : x ^ p = 1) (hqR : q ∈ R)
    (hq : q ^ p = x) (hA : ∃ A : Subgroup G, A ≤ R ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 3)
    (hC : ∀ E : Subgroup G, E ≤ centralizer ({x} : Set G) → IsElemAbelian p E →
      Nat.card E ≤ p ^ 2) : False := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, hAR, ⟨hAc, hApow⟩, hAcard⟩ := hA
  have hxR : x ∈ R := hq ▸ pow_mem hqR p
  have hAe : CFSG.IsElementaryAbelian p A := sr630b_isElementaryAbelian_of_pow
    (fun a ha b hb => congrArg Subtype.val (hAc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)) hApow
  have hA'e : CFSG.IsElementaryAbelian p (A.subgroupOf R) :=
    CFSG.IsElementaryAbelian.subgroupOf hAR
  have hA'c : Nat.card (A.subgroupOf R) = p ^ 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAR).toEquiv).trans hAcard
  have hxp' : (⟨x, hxR⟩ : R) ^ p = 1 := Subtype.ext hxp
  have hq' : (⟨q, hqR⟩ : R) ^ p = ⟨x, hxR⟩ := Subtype.ext hq
  obtain ⟨E', hE'C, hE'e, hE'3⟩ := sr630b_exists_centralizer_rank_three hp2 hR hxp' hq' hA'e hA'c
  have hE : IsElemAbelian p (E'.map R.subtype) := by
    have := hE'e
    have h := CFSG.IsElementaryAbelian.map_subtype (p := p) (K := R) (H := E')
    exact ⟨h.toIsMulCommutative,
      fun y hy => CFSG.elemPow_eq_one_of_isElementaryAbelian y hy⟩
  have hEC : E'.map R.subtype ≤ centralizer ({x} : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    have h := mem_centralizer_singleton_iff.mp (hE'C he)
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h)
  have h1 := hC _ hEC hE
  rw [card_map_of_injective R.subtype_injective] at h1
  have h2 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC
