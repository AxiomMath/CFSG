module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Transport

public section

namespace CFSG.EvenSporadicStandard.HNRecog.SideF4

open CFSG.EvenSporadicStandard.HNRecog Subgroup

theorem isElementaryAbelian_of_mulEquiv {p : ℕ} {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    [h : CFSG.IsElementaryAbelian p A] : CFSG.IsElementaryAbelian p B where
  toIsMulCommutative := ⟨⟨fun a b => by
    have := congrArg e (mul_comm' (e.symm a) (e.symm b))
    simpa using this⟩⟩
  exponent_dvd_p := by
    rw [← Monoid.exponent_eq_of_mulEquiv e]
    exact CFSG.IsElementaryAbelian.exponent_dvd_p p A

theorem isExtraspecial_of_mulEquiv {p : ℕ} {P P' : Type*} [Group P] [Group P'] (e : P ≃* P')
    [h : CFSG.IsExtraspecial p P] : CFSG.IsExtraspecial p P' where
  center_order_p := by
    rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact CFSG.IsExtraspecial.center_order_p p P
  quotient_elementary_abelian := by
    haveI := CFSG.IsExtraspecial.quotient_elementary_abelian p P
    exact isElementaryAbelian_of_mulEquiv
      (QuotientGroup.congr (Subgroup.center P) (Subgroup.center P') e (Subgroup.map_center_eq e))
  quotient_nontrivial := by
    haveI := CFSG.IsExtraspecial.quotient_nontrivial p P
    exact (QuotientGroup.congr (Subgroup.center P) (Subgroup.center P') e
      (Subgroup.map_center_eq e)).symm.toEquiv.nontrivial

theorem isExtraspecialPlusByA5WrTwo_of_mulEquiv {C C' : Type} [Group C] [Group C']
    (e : C ≃* C') (h : IsExtraspecialPlusByA5WrTwo C) : IsExtraspecialPlusByA5WrTwo C' := by
  obtain ⟨Q, hQ, hw⟩ := h
  haveI hQ' : (Q.map (e : C →* C')).Normal := hQ.map (e : C →* C') e.surjective
  refine ⟨Q.map (e : C →* C'), hQ', ?_⟩
  obtain ⟨hplus, hcent, ⟨q⟩⟩ := hw
  obtain ⟨hext, hcard, E, hEQ, hEab, hEcard⟩ := hplus
  haveI := hext
  refine ⟨⟨isExtraspecial_of_mulEquiv (e.subgroupMap Q), ?_,
    E.map (e : C →* C'), Subgroup.map_mono hEQ, ?_, ?_⟩, ?_, ?_⟩
  · rw [← Nat.card_congr (e.subgroupMap Q).toEquiv]
    exact hcard
  · obtain ⟨hcomm, hexp⟩ := hEab
    refine ⟨inferInstance, ?_⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    change (e y) ^ 2 = 1
    rw [← map_pow, hexp y hy, map_one]
  · rw [← Nat.card_congr (e.subgroupMap E).toEquiv]
    exact hEcard
  · intro y hy
    have hy' : e.symm y ∈ centralizer (Q : Set C) := by
      rw [← TwoHS.mem_centralizer_map_iff e Q, e.apply_symm_apply]
      exact hy
    have := Subgroup.mem_map_of_mem (e : C →* C') (hcent hy')
    simpa using this
  · exact ⟨(QuotientGroup.congr Q (Q.map (e : C →* C')) e rfl).symm.trans q⟩

theorem isExtraspecialPlusByA5WrTwo_of_nonempty_mulEquiv {X G : Type} [Group X] [Group G] {z₀ : X}
    {z : G} (hc : Nonempty (centralizer ({z} : Set G) ≃* centralizer ({z₀} : Set X)))
    (h : IsExtraspecialPlusByA5WrTwo (centralizer ({z₀} : Set X))) :
    IsExtraspecialPlusByA5WrTwo (centralizer ({z} : Set G)) := by
  obtain ⟨e⟩ := hc
  exact isExtraspecialPlusByA5WrTwo_of_mulEquiv e.symm h

theorem isExtraspecialPlusByA5WrTwo_of_isConj {X : Type} [Group X] {t z : X} (h : IsConj t z)
    (hz : IsExtraspecialPlusByA5WrTwo (centralizer ({z} : Set X))) :
    IsExtraspecialPlusByA5WrTwo (centralizer ({t} : Set X)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact isExtraspecialPlusByA5WrTwo_of_mulEquiv
    (TwoHS.centralizerMulEquiv (MulAut.conj c) (by simpa using hc)).symm hz

end CFSG.EvenSporadicStandard.HNRecog.SideF4
