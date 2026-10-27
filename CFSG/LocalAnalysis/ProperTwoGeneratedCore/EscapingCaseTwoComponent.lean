module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseTwoZStar
public import CFSG.Walter.AStar.Subnormal
import CFSG.Adapters.WholeGroupLayer

public section

namespace CFSG.ProperTwoGeneratedCore.Assembly

open CFSG.Open

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem even_card_of_orderOf_eq_two {K : Subgroup X} {t : X} (htK : t ∈ K) (ht : orderOf t = 2) :
    Even (Nat.card K) :=
  Nat.not_odd_iff_even.mp (not_odd_card_of_orderOf_eq_two htK ht)

theorem even_card_component (hodd : pPrimeCore 2 X = ⊥) {J : Subgroup X}
    (hJ : CFSG.IsComponent J) : Even (Nat.card J) := by
  by_contra h
  have hbot := CFSG.Walter.eq_bot_of_isSubnormal_of_odd hodd hJ.2 (Nat.not_even_iff_odd.mp h)
  have : Nontrivial J := CFSG.ComponentClassification.Quasisimple.nontrivial
    ((CFSG.isComponent_iff_open J).mp hJ).2.2
  exact (J.nontrivial_iff_ne_bot.mp this) hbot

theorem card_le_card_sylow_inf_of_isSubnormal (T : Sylow 2 X) {J : Subgroup X}
    (hJ : J.IsSubnormal) {R : Subgroup X} (hRJ : R ≤ J) (hR : IsPGroup 2 R) :
    Nat.card R ≤ Nat.card ((T : Subgroup X) ⊓ J : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal T hJ
  have h := card_le_card_sylow_of_le P hRJ hR
  rwa [← Subgroup.card_map_of_injective J.subtype_injective, hP] at h

omit [Finite X] in
theorem mem_normalizer_of_map_conj_eq {J : Subgroup X} {x : X}
    (h : J.map (MulAut.conj x).toMonoidHom = J) : x ∈ Subgroup.normalizer (J : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    rw [← h]
    exact ⟨g, hg, rfl⟩
  · intro hg
    rw [← h] at hg
    obtain ⟨g', hg', hgg'⟩ := hg
    have heq : g' = g := by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_left_inj, mul_right_inj]
        using hgg'
    rwa [← heq]

theorem mem_normalizer_component (hodd : pPrimeCore 2 X = ⊥) (T : Sylow 2 X) {x : X}
    (hx : x ∈ Subgroup.centralizer ((T : Subgroup X) : Set X)) {J : Subgroup X}
    (hJ : CFSG.IsComponent J) : x ∈ Subgroup.normalizer (J : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ' := (CFSG.isComponent_iff_open J).mp hJ
  by_cases heq : J.map (MulAut.conj x).toMonoidHom = J
  · exact mem_normalizer_of_map_conj_eq heq
  exfalso
  have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne J _ hJ'
    ((CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj x) J).mpr hJ')
    (Ne.symm heq)
  have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal T hJ.2
  have hPc : (P : Subgroup J) ≤ Subgroup.center J := by
    intro t ht
    have htT : (t : X) ∈ (T : Subgroup X) ⊓ J := hP ▸ Subgroup.mem_map_of_mem J.subtype ht
    have htJ' : (t : X) ∈ J.map (MulAut.conj x).toMonoidHom := by
      refine ⟨t, t.2, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← Subgroup.mem_centralizer_iff.mp hx _ htT.1, mul_inv_cancel_right]
    exact Subgroup.mem_center_iff.mpr fun j =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp (hle j.2) _ htJ').symm
  have : Group.IsPerfect J := ⟨hJ'.2.2.1⟩
  exact not_dvd_card_of_isPerfect_of_sylow_le_center P hPc
    (even_iff_two_dvd.mp (even_card_component hodd hJ))

theorem mem_pCore_of_commute_components (hodd : pPrimeCore 2 X = ⊥) (T : Sylow 2 X) {x : X}
    (hx : x ∈ Subgroup.centralizer ((T : Subgroup X) : Set X))
    (hcomp : ∀ J : Subgroup X, CFSG.IsComponent J → ∀ j ∈ J, Commute x j) :
    x ∈ CFSG.pCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : CFSG.fittingSubgroup X = CFSG.pCore 2 X := CFSG.Fitting_eq_pcore X 2 hodd
  have hO2T : CFSG.pCore 2 X ≤ (T : Subgroup X) :=
    have : (CFSG.pCore 2 X).Normal := CFSG.pCore_normal
    CFSG.pCore_isPGroup.le_sylow_of_normal T
  have hle : CFSG.generalizedFitting X ≤ Subgroup.centralizer ({x} : Set X) := by
    refine sup_le ?_ (sSup_le fun J hJ y hy =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcomp J hJ y hy).eq.symm)
    rw [hF]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hx y (hO2T hy))
  have hxc : x ∈ Subgroup.centralizer (CFSG.generalizedFitting X : Set X) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  rw [← hF]
  exact CFSG.Adapters.centralizer_generalizedFitting_le_fittingSubgroup X hxc

theorem eq_of_pRank_le_one {t : X} (htc : t ∈ Subgroup.center X) (ht : orderOf t = 2)
    {J : Subgroup X} (htJ : t ∈ J) (hrank : CFSG.Open.pRank 2 J ≤ 1) {q : X} (hqJ : q ∈ J)
    (hq : orderOf q = 2) : q = t := by
  by_contra hne
  have := two_le_pRank_of_commuting_involutions hqJ htJ hq ht hne
    (Subgroup.mem_center_iff.mp htc q)
  omega

theorem commute_of_pRank_le_one {t : X} (htc : t ∈ Subgroup.center X) (ht : orderOf t = 2)
    {J : Subgroup X} (hJ : CFSG.IsComponent J) (htJ : t ∈ J) (hrank : CFSG.Open.pRank 2 J ≤ 1)
    {x : X} (hx : orderOf x = 2) (hxN : x ∈ Subgroup.normalizer (J : Set X))
    {Q : Subgroup X} (hQJ : Q ≤ J) (hQ : IsPGroup 2 Q)
    (hQmax : ∀ R : Subgroup X, R ≤ J → IsPGroup 2 R → Nat.card R ≤ Nat.card Q)
    (hxQ : ∀ q ∈ Q, Commute x q) : ∀ j ∈ J, Commute x j := by
  have htcomm : ∀ c ∈ Subgroup.zpowers t, ∀ y : X, Commute y c := by
    intro c hc y
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact (Commute.zpow_right (Subgroup.mem_center_iff.mp htc y) n)
  rcases zStarStep ((CFSG.isComponent_iff_open J).mp hJ).2.2 (even_card_of_orderOf_eq_two htJ ht)
      hx hxN hQJ hQ hQmax hxQ (Subgroup.zpowers_le.mpr htJ)
      (fun c hc => Subgroup.mem_centralizer_iff.mpr fun j _ => (htcomm c hc j))
      (fun c hc => htcomm c hc x) (isPGroup_zpowers_of_orderOf_eq_two ht) with h | h
  · exact h
  · obtain ⟨k, -, q, hqQ, hqC, hqq, -⟩ := h
    have hq1 : q ≠ 1 := fun h1 => hqC (h1 ▸ Subgroup.one_mem _)
    exact absurd (eq_of_pRank_le_one htc ht htJ hrank (hQJ hqQ)
      (orderOf_eq_two_of_mul_self hqq hq1) ▸ Subgroup.mem_zpowers t) hqC

end CFSG.ProperTwoGeneratedCore.Assembly
