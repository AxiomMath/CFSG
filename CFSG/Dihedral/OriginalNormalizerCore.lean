module

public import CFSG.Dihedral.OriginalOddKernelMaximality
public import CFSG.Dihedral.OriginalOddCore

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (d : OriginalData G)

omit [IsSimpleGroup G] in
theorem R_le_oddCoreOf_of_le_normalizer (H : Subgroup G) (hCH : d.C ≤ H)
    (hHN : H ≤ d.N) : d.R ≤ oddCoreOf H := by
  exact normal_odd_le_oddCoreOf d.R H (d.R_le.trans hCH)
    (Subgroup.normal_subgroupOf_of_le_normalizer hHN) d.R_odd

theorem oddCoreOf_eq_R_of_contains (hc : d.CanonicalNormalizers)
    (H : Subgroup G) (hCH : d.C ≤ H) (hR : d.R ≤ oddCoreOf H) :
    oddCoreOf H = d.R := by
  exact d.odd_overgroup_eq hc (oddCoreOf H) (oddCoreOf_odd H)
    ((d.sylow_le_centralizer.trans hCH).trans (oddCoreOf_normalized H)) hR

theorem overgroup_le_normalizer_iff (hc : d.CanonicalNormalizers)
    (H : Subgroup G) (hCH : d.C ≤ H) :
    H ≤ d.N ↔ d.R ≤ oddCoreOf H := by
  constructor
  · exact d.R_le_oddCoreOf_of_le_normalizer H hCH
  · intro hR
    have heq := d.oddCoreOf_eq_R_of_contains hc H hCH hR
    have hn := oddCoreOf_normalized H
    rwa [heq] at hn

theorem oddCoreOf_eq_R_of_le_normalizer (hc : d.CanonicalNormalizers)
    (H : Subgroup G) (hCH : d.C ≤ H) (hHN : H ≤ d.N) : oddCoreOf H = d.R :=
  d.oddCoreOf_eq_R_of_contains hc H hCH
    (d.R_le_oddCoreOf_of_le_normalizer H hCH hHN)

theorem normalizer_oddCore (hc : d.CanonicalNormalizers) : oddCoreOf d.N = d.R :=
  d.oddCoreOf_eq_R_of_le_normalizer hc d.N d.centralizer_le_normalizer le_rfl

theorem normalizer_ne_top (hR : d.R ≠ ⊥) : d.N ≠ ⊤ := by
  intro hN
  have hn : d.R.Normal := Subgroup.normalizer_eq_top_iff.mp hN
  rcases hn.eq_bot_or_eq_top with hbot | htop
  · exact hR hbot
  · have htwo : 2 ∣ Nat.card G := by
      have := orderOf_dvd_natCard d.t
      rwa [d.t_order] at this
    have hodd := d.R_odd
    rw [htop, Subgroup.card_top] at hodd
    exact hodd.not_two_dvd_nat htwo

theorem eq_centralizer_of_two_quotient (hc : d.CanonicalNormalizers)
    (H : Subgroup G) (hCH : d.C ≤ H)
    (hquot : IsPGroup 2 (H ⧸ Assembly.oddCore H)) : H = d.C := by
  let J := Assembly.oddCore H
  let f := QuotientGroup.mk' J
  have hRH := d.R_le.trans hCH
  have hRcore : d.R ≤ oddCoreOf H :=
    odd_le_normal_of_two_quotient d.R H hRH J d.R_odd hquot
  have hcore := d.oddCoreOf_eq_R_of_contains hc H hCH hRcore
  have hSH := d.sylow_le_centralizer.trans hCH
  let T := d.S.subtype hSH
  have himage : (T : Subgroup H).map f = ⊤ := by
    let Q := T.mapSurjective (QuotientGroup.mk'_surjective J)
    have htop : (Q : Subgroup (H ⧸ J)) = ⊤ :=
      (Q.is_maximal' (hquot.to_subgroup ⊤) le_top).symm
    simpa only [Q, Sylow.coe_mapSurjective] using htop
  have hJle : J ≤ d.C.subgroupOf H := by
    intro x hx
    apply d.R_le
    rw [← hcore]
    exact Subgroup.mem_map_of_mem H.subtype hx
  have hTC : (T : Subgroup H) ≤ d.C.subgroupOf H := by
    dsimp only [T]
    rw [Sylow.coe_subtype]
    intro x hx
    exact d.sylow_le_centralizer hx
  have hCimage : (d.C.subgroupOf H).map f = ⊤ :=
    top_le_iff.mp (himage ▸ Subgroup.map_mono hTC)
  have hpre : d.C.subgroupOf H = ⊤ := by
    have h := congrArg (Subgroup.comap f) hCimage
    rwa [Subgroup.comap_map_eq_self (by simpa only [f, QuotientGroup.ker_mk'] using hJle),
      Subgroup.comap_top] at h
  exact (Subgroup.subgroupOf_eq_top.mp hpre).antisymm hCH

theorem centralizer_two_quotient (hc : d.CanonicalNormalizers) :
    IsPGroup 2 (d.C ⧸ Assembly.oddCore d.C) := by
  have hcore := d.oddCoreOf_eq_R_of_le_normalizer hc d.C le_rfl
    d.centralizer_le_normalizer
  have hcard : Nat.card (Assembly.oddCore d.C) = Nat.card d.R := by
    have h := congrArg (fun U : Subgroup G => Nat.card U) hcore
    rwa [oddCoreOf, Subgroup.card_map_of_injective d.C.subtype_injective] at h
  have heq := (Assembly.oddCore d.C).card_eq_card_quotient_mul_card_subgroup
  rw [d.centralizer_card, hcard, mul_comm (Nat.card d.R)] at heq
  apply IsPGroup.of_card
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := d.R)) heq.symm

theorem two_quotient_iff_eq_centralizer (hc : d.CanonicalNormalizers)
    (H : Subgroup G) (hCH : d.C ≤ H) :
    IsPGroup 2 (H ⧸ Assembly.oddCore H) ↔ H = d.C := by
  constructor
  · exact d.eq_centralizer_of_two_quotient hc H hCH
  · rintro rfl
    exact d.centralizer_two_quotient hc

end CFSG.DihedralBlueprint.OriginalData
