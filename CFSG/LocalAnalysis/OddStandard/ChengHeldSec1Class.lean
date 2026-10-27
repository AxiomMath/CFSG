module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec1Weak
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec1Quot

public section

namespace CFSG.OddStandard.ChengHeld.Sec1

open Subgroup CFSG.OddStandard.ChengHeldData
open CFSG.OddStandard.ChengHeld.ChartShape (cj_mul cj_inv cj_cj cj_of_commute cm_eq_one_iff)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

omit [Finite G] in
theorem isConj_cj {a b : G} (h : IsConj a b) (c : G) : IsConj (cj a c) (cj b c) := by
  obtain ⟨c₀, rfl⟩ := isConj_iff.1 h
  exact isConj_iff.2 ⟨c⁻¹ * c₀ * c, by unfold cj; group⟩

theorem q_mem_center (d : Datum A) : (⟨d.q, d.q_mem⟩ : ↥A) ∈ center ↥A := by
  rw [mem_center_iff]
  intro g
  apply Subtype.ext
  exact mem_centralizer_iff.1 d.q_cent g g.2

theorem cj_q_of_mem_A (d : Datum A) {a : G} (ha : a ∈ A) : cj d.q a = d.q :=
  cj_of_commute (show Commute d.q a from (mem_centralizer_iff.1 d.q_cent a ha).symm)

namespace Cfg

variable {d : Datum A} (K : Cfg d)

include K

theorem eq_one_or_q_of_mem_center {z : ↥A} (hz : z ∈ center ↥A) (hz2 : (z : G) * z = 1) :
    (z : G) = 1 ∨ (z : G) = d.q := by
  by_cases h1 : (z : G) = 1
  · exact Or.inl h1
  · refine Or.inr (d.eq_q_of_mem_centralizer K.h (mem_centralizer_iff.2 fun g hg => ?_) ?_)
    · exact congrArg Subtype.val (mem_center_iff.1 hz ⟨g, hg⟩)
    · exact orderOf_eq_prime (by rw [pow_two]; exact hz2) h1

theorem not_mem_center {x : G} (hx : x ∈ A) (hx2 : x * x = 1) (h1 : x ≠ 1) (hq : x ≠ d.q) :
    (⟨x, hx⟩ : ↥A) ∉ center ↥A := fun h => by
  rcases K.eq_one_or_q_of_mem_center h hx2 with h' | h'
  · exact h1 h'
  · exact hq h'

theorem conj_into_pi {x : G} (hxS : x ∈ d.S) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hxq : x ≠ d.q) :
    ∃ a ∈ A, cj x a = K.c.pi ∨ cj x a = d.q * K.c.pi := by
  have hπq : K.c.pi ≠ d.q := by
    intro h
    apply K.q_pi_ne_one
    rw [← h]
    exact K.pi_sq
  have hπ1 := K.pi_ne_one
  obtain ⟨a', z, hz, h⟩ := exists_conj_of_orderOf_two K.invol_conj
    (x := ⟨x, d.S_le_A hxS⟩) (y := ⟨K.c.pi, d.S_le_A K.pi_mem_S⟩)
    (Subtype.ext hx2) (Subtype.ext K.pi_sq) (K.not_mem_center _ hx2 hx1 hxq)
    (K.not_mem_center _ K.pi_sq hπ1 hπq)
  refine ⟨(a' : G), a'.2, ?_⟩
  have h' : cj x (a' : G) = (z : G) * K.c.pi := congrArg Subtype.val h
  have hzπ : K.c.pi * (z : G) = (z : G) * K.c.pi :=
    congrArg Subtype.val (mem_center_iff.1 hz ⟨K.c.pi, d.S_le_A K.pi_mem_S⟩)
  have hc : (z : G) * K.c.pi * ((z : G) * K.c.pi) = 1 := by
    rw [← h']
    unfold cj
    calc (a' : G)⁻¹ * x * a' * ((a' : G)⁻¹ * x * a') = (a' : G)⁻¹ * (x * x) * a' := by group
      _ = 1 := by rw [hx2]; group
  have hz2 : (z : G) * z = 1 := by
    calc (z : G) * z = (z : G) * z * (K.c.pi * K.c.pi) := by rw [K.pi_sq, mul_one]
      _ = (z : G) * (K.c.pi * (z : G)) * K.c.pi := by rw [hzπ]; simp only [mul_assoc]
      _ = 1 := by rw [← hc]; simp only [mul_assoc]
  rcases K.eq_one_or_q_of_mem_center hz hz2 with h1 | h1
  · left; rw [h', h1, one_mul]
  · right; rw [h', h1]

theorem no_fuse_pi {a : G} (ha : a ∈ A) : cj K.c.pi a ≠ d.q * K.c.pi := by
  intro h
  have hπq : K.c.pi ≠ d.q := by
    intro h'
    apply K.q_pi_ne_one
    rw [← h']
    exact K.pi_sq
  set p : ↥A := ⟨K.c.pi, d.S_le_A K.pi_mem_S⟩ with hp
  have hconj : (⟨a, ha⟩ : ↥A)⁻¹ * p * ⟨a, ha⟩ = ⟨d.q, d.q_mem⟩ * p := Subtype.ext h
  have hord : orderOf (QuotientGroup.mk p : ↥A ⧸ center ↥A) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ← QuotientGroup.mk_mul, show p * p = 1 from Subtype.ext K.pi_sq,
        QuotientGroup.mk_one]
    · intro h1
      exact K.not_mem_center _ K.pi_sq K.pi_ne_one hπq ((QuotientGroup.eq_one_iff p).mp h1)
  have hcc := CFSG.Sporadic.HN.Local.card_conj_mul_card_centralizer
    (QuotientGroup.mk p : ↥A ⧸ center ↥A)
  rw [K.invol_card _ hord, K.h.card_quotient] at hcc
  have hCp : IsPGroup 2 (centralizer {(QuotientGroup.mk p : ↥A ⧸ center ↥A)}) :=
    IsPGroup.of_card (n := 6) (by norm_num; omega)
  obtain ⟨P, hP⟩ := d.S_sylow.exists_sylow_eq_subgroupOf
  have hle : (P.mapSurjective (QuotientGroup.mk'_surjective (center ↥A)) :
      Subgroup (↥A ⧸ center ↥A)) ≤ centralizer {(QuotientGroup.mk p : ↥A ⧸ center ↥A)} := by
    rw [Sylow.coe_mapSurjective, hP]
    rintro _ ⟨s, hs, rfl⟩
    have hsp : s * p = p * s := Subtype.ext (K.D_central K.pi_mem_D (mem_subgroupOf.1 hs))
    rw [mem_centralizer_singleton_iff, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, hsp]
  have haC : (QuotientGroup.mk (⟨a, ha⟩ : ↥A) : ↥A ⧸ center ↥A) ∈
      centralizer {(QuotientGroup.mk p : ↥A ⧸ center ↥A)} := by
    have hmk : (QuotientGroup.mk ((⟨a, ha⟩ : ↥A)⁻¹ * p * ⟨a, ha⟩) : ↥A ⧸ center ↥A) =
        QuotientGroup.mk p := by
      rw [hconj, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr (q_mem_center d),
        one_mul]
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at hmk
    rw [mem_centralizer_singleton_iff]
    calc (QuotientGroup.mk (⟨a, ha⟩ : ↥A) : ↥A ⧸ center ↥A) * QuotientGroup.mk p
        = QuotientGroup.mk (⟨a, ha⟩ : ↥A) *
          ((QuotientGroup.mk (⟨a, ha⟩ : ↥A))⁻¹ * QuotientGroup.mk p *
            QuotientGroup.mk (⟨a, ha⟩ : ↥A)) := by rw [hmk]
      _ = QuotientGroup.mk p * QuotientGroup.mk (⟨a, ha⟩ : ↥A) := by group
  rw [(P.mapSurjective (QuotientGroup.mk'_surjective (center ↥A))).is_maximal' hCp hle,
    Sylow.coe_mapSurjective, hP] at haC
  obtain ⟨s, hs, hsa⟩ := Subgroup.mem_map.1 haC
  rw [QuotientGroup.mk'_apply] at hsa
  have hz : s⁻¹ * ⟨a, ha⟩ ∈ center ↥A := QuotientGroup.eq.1 hsa
  have hsp : s * p = p * s := Subtype.ext (K.D_central K.pi_mem_D (mem_subgroupOf.1 hs))
  have hzp : p * (s⁻¹ * ⟨a, ha⟩) = s⁻¹ * ⟨a, ha⟩ * p := mem_center_iff.1 hz p
  have hfix : (⟨a, ha⟩ : ↥A)⁻¹ * p * ⟨a, ha⟩ = p := by
    calc (⟨a, ha⟩ : ↥A)⁻¹ * p * ⟨a, ha⟩
        = (s⁻¹ * ⟨a, ha⟩)⁻¹ * (s⁻¹ * (p * s)) * (s⁻¹ * ⟨a, ha⟩) := by group
      _ = (s⁻¹ * ⟨a, ha⟩)⁻¹ * (p * (s⁻¹ * ⟨a, ha⟩)) := by rw [← hsp]; group
      _ = p := by rw [hzp]; group
  rw [hfix] at hconj
  have hq1 : d.q * K.c.pi = K.c.pi := (congrArg Subtype.val hconj).symm
  exact (q_ne_one d) (mul_eq_right.1 hq1)

theorem exists_mul_of_mem_normalizer {n : G} (hn : n ∈ normalizer (A : Set G)) :
    ∃ x ∈ d.X, ∃ a ∈ A, ∃ k ∈ centralizer (A : Set G), n = x * a * k := by
  have h1 : (A : Set G) * (centralizer (A : Set G) : Set G) = ↑(A ⊔ centralizer (A : Set G)) :=
    (Subgroup.coe_mul_of_right_le_normalizer_left A _ (centralizer_le_normalizer _)).symm
  have h2 : (d.X : Set G) * ↑(A ⊔ centralizer (A : Set G)) =
      ↑(d.X ⊔ (A ⊔ centralizer (A : Set G))) :=
    (Subgroup.coe_mul_of_left_le_normalizer_right d.X _
      (d.X_sylow.le.trans (normalizer_le_normalizer_sup_centralizer K.h))).symm
  have h3 : n ∈ (d.X : Set G) * ↑(A ⊔ centralizer (A : Set G)) := by
    rw [h2, SetLike.mem_coe, sup_comm d.X, ← K.hN]
    exact hn
  obtain ⟨x, hx, m, hm, rfl⟩ := h3
  rw [← h1] at hm
  obtain ⟨a, ha, k, hk, rfl⟩ := hm
  exact ⟨x, hx, a, ha, k, hk, (mul_assoc _ _ _).symm⟩

theorem three_classes : ¬ IsConj d.q K.c.pi ∧ ¬ IsConj d.q (d.q * K.c.pi) ∧
    ¬ IsConj K.c.pi (d.q * K.c.pi) := by
  have hqD := K.q_mem_D
  have hπD := K.pi_mem_D
  have hqπD : d.q * K.c.pi ∈ K.c.D := K.c.D.mul_mem hqD hπD
  have hnorm : ∀ {n : G}, n ∈ normalizer (d.S : Set G) → cj d.q n = d.q := fun {n} hn =>
    K.cj_q_of_map (mem_normalizer_iff_map_conj_eq.1 (inv_mem hn))
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨n, hn, hqn⟩ := K.fuse_D hqD hπD h
    rw [hnorm hn] at hqn
    apply K.q_pi_ne_one
    rw [hqn]
    exact K.pi_sq
  · obtain ⟨n, hn, hqn⟩ := K.fuse_D hqD hqπD h
    rw [hnorm hn] at hqn
    exact K.pi_ne_one (mul_left_cancel (a := d.q) (by rw [mul_one]; exact hqn.symm))
  · obtain ⟨n, hn, hπn⟩ := K.fuse_D hπD hqπD h
    have hqc := hnorm hn
    have hnA : n ∈ normalizer (A : Set G) := by
      rw [← d.centralizer_q K.h, mem_centralizer_singleton_iff]
      have h1 : n⁻¹ * d.q * n = d.q := hqc
      calc n * d.q = n * (n⁻¹ * d.q * n) := by rw [h1]
        _ = d.q * n := by group
    obtain ⟨x, hx, a, ha, k, hk, rfl⟩ := K.exists_mul_of_mem_normalizer hnA
    have hxπ := (K.act_D hx).2.1
    have hk' : cj (cj K.c.pi a) k = cj K.c.pi a := cj_of_commute
      (mem_centralizer_iff.1 hk _ (A.mul_mem (A.mul_mem (A.inv_mem ha)
        (d.S_le_A K.pi_mem_S)) ha))
    have : cj K.c.pi a = d.q * K.c.pi := by
      rw [← cj_cj, ← cj_cj, hxπ, hk'] at hπn
      exact hπn
    exact K.no_fuse_pi ha this

theorem iso {x : G} (hx : x ∈ d.QS) (hxq : x ≠ d.q) : ¬ IsConj d.q x := by
  intro h
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have hx2 : x * x = 1 := by
    rw [← hc]
    calc c * d.q * c⁻¹ * (c * d.q * c⁻¹) = c * (d.q * d.q) * c⁻¹ := by group
      _ = 1 := by rw [(q_mul_self d)]; group
  have hxS : x ∈ d.S := K.c.involutions_in_S K.h K.sf K.hc hx hx2
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1] at hc
    apply (q_ne_one d)
    calc d.q = c⁻¹ * (c * d.q * c⁻¹) * c := by group
      _ = 1 := by rw [hc]; group
  obtain ⟨a, ha, hcase⟩ := K.conj_into_pi hxS hx2 hx1 hxq
  have h' : IsConj d.q (cj x a) := by
    have := isConj_cj h a
    rwa [cj_q_of_mem_A d ha] at this
  rcases hcase with h1 | h1 <;> rw [h1] at h'
  · exact K.three_classes.1 h'
  · exact K.three_classes.2.1 h'

end Cfg

end CFSG.OddStandard.ChengHeld.Sec1
