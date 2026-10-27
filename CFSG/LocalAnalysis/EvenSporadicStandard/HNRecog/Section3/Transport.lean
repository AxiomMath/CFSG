module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Defs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog Subgroup

theorem mem_centralizer_map_iff {H H' : Type} [Group H] [Group H'] (f : H ≃* H') (E : Subgroup H)
    (y : H) :
    f y ∈ centralizer ((E.map (f : H →* H') : Subgroup H') : Set H') ↔
      y ∈ centralizer (E : Set H) := by
  rw [mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h e he
    exact f.injective (by
      rw [map_mul, map_mul]
      exact h (f e) (Subgroup.mem_map_of_mem (f : H →* H') he))
  · intro h x hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hx
    change f e * f y = f y * f e
    rw [← map_mul, ← map_mul, h e he]

theorem isHSCover_map {H H' : Type} [Group H] [Group H'] (f : H ≃* H') {E : Subgroup H}
    (h : TwoHS.IsHSCover H E) : TwoHS.IsHSCover H' (E.map (f : H →* H')) where
  normal := h.normal.map (f : H →* H') f.surjective
  index_dvd_two := by
    rw [Subgroup.index_map_equiv]
    exact h.index_dvd_two
  perfect := by
    have := h.perfect
    exact Group.IsPerfect.map (f : H →* H')
  card_center := by
    rw [← Nat.card_congr (centerCongr (f.subgroupMap E)).toEquiv]
    exact h.card_center
  quotient := by
    obtain ⟨q⟩ := h.quotient
    exact ⟨(QuotientGroup.congr _ _ (f.subgroupMap E) (Subgroup.map_center_eq _)).symm.trans q⟩
  centralizer_le := fun y hy => by
    have hy' : f.symm y ∈ centralizer (E : Set H) := by
      rw [← mem_centralizer_map_iff f E, f.apply_symm_apply]
      exact hy
    have := Subgroup.mem_map_of_mem (f : H →* H') (h.centralizer_le hy')
    simpa using this

@[expose] def centralizerMulEquiv {G J : Type} [Group G] [Group J] (e : G ≃* J) {z : G} {w : J}
    (h : e z = w) : centralizer ({z} : Set G) ≃* centralizer ({w} : Set J) where
  toFun x := ⟨e x.1, by
    rw [mem_centralizer_singleton_iff, ← h, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.1 x.2]⟩
  invFun y := ⟨e.symm y.1, by
    rw [mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply, h, mem_centralizer_singleton_iff.1 y.2]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul e x.1 y.1)

theorem isElementaryAbelian_of_mulEquiv' {p : ℕ} {A B : Type*} [Group A] [Group B] (e : A ≃* B)
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
    exact isElementaryAbelian_of_mulEquiv'
      (QuotientGroup.congr (Subgroup.center P) (Subgroup.center P') e (Subgroup.map_center_eq e))
  quotient_nontrivial := by
    haveI := CFSG.IsExtraspecial.quotient_nontrivial p P
    exact (QuotientGroup.congr (Subgroup.center P) (Subgroup.center P') e
      (Subgroup.map_center_eq e)).symm.toEquiv.nontrivial

theorem isF5Centralizer_map' {H H' : Type} [Group H] [Group H'] (f : H ≃* H') {E : Subgroup H}
    (h : TwoHS.IsF5Centralizer H E) : TwoHS.IsF5Centralizer H' (E.map (f : H →* H')) where
  toIsHSCover := isHSCover_map f h.toIsHSCover
  index_eq_two := by rw [Subgroup.index_map_equiv]; exact h.index_eq_two
  exists_outer_involution := by
    obtain ⟨v, hv, hv2⟩ := h.exists_outer_involution
    refine ⟨f v, fun hm => hv ?_, by rw [← map_pow, hv2, map_one]⟩
    obtain ⟨x, hx, hxv⟩ := Subgroup.mem_map.1 hm
    exact (f.injective hxv) ▸ hx

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
      rw [← mem_centralizer_map_iff e Q, e.apply_symm_apply]
      exact hy
    have := Subgroup.mem_map_of_mem (e : C →* C') (hcent hy')
    simpa using this
  · exact ⟨(QuotientGroup.congr Q (Q.map (e : C →* C')) e rfl).symm.trans q⟩

theorem isF5Type_of_isConj {G : Type} [Group G] {a z a' w : G} (h : IsF5Type a z)
    (ha : IsConj a a') (hz : IsConj z w) : IsF5Type a' w := by
  obtain ⟨c, hc⟩ := isConj_iff.1 ha
  obtain ⟨d, hd⟩ := isConj_iff.1 hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hc]
    simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj c) a).trans h.orderOf_a
  · rw [← hd]
    simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj d) z).trans h.orderOf_z
  · obtain ⟨E, hE⟩ := h.cent_a
    exact ⟨_, isF5Centralizer_map'
      (centralizerMulEquiv (MulAut.conj c) (by simpa using hc)) hE⟩
  · exact isExtraspecialPlusByA5WrTwo_of_mulEquiv
      (centralizerMulEquiv (MulAut.conj d) (by simpa using hd)) h.cent_z

end CFSG.EvenSporadicStandard.HNRecog.Section3
