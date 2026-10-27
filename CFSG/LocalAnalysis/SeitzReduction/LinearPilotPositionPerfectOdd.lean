module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotZCentral
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.SeitzReduction.Inheritance
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.OuterAutomorphisms

section OddCore

variable {Q : Type*} [Group Q] [Finite Q]

theorem oddCore_le_center_of_even (hQ : CFSG.Open.IsQuasisimple Q) (heven : Even (Nat.card Q)) :
    oddCore Q ≤ center Q := by
  rcases Quasisimple.normal_le_center_or_eq_top hQ (oddCore Q) with h | h
  · exact h
  · exfalso
    have hodd : Odd (Nat.card (oddCore Q)) :=
      CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
    rw [h, card_top] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) heven

theorem card_quotient_center_le_card_quotient_oddCore (hQ : CFSG.Open.IsQuasisimple Q)
    (heven : Even (Nat.card Q)) : Nat.card (Q ⧸ center Q) ≤ Nat.card (Q ⧸ oddCore Q) :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero index_ne_zero_of_finite)
    (index_dvd_of_le (oddCore_le_center_of_even hQ heven))

end OddCore

section Image

variable {H : Type*} [Group H] [Finite H] {D : Subgroup H}

theorem ker_subgroupMap_mk_oddCore_le_center (hDq : CFSG.Open.IsQuasisimple D) {y : H}
    (hyD : y ∈ D) (hy : orderOf y = 2) :
    ((QuotientGroup.mk' (oddCore H)).subgroupMap D).ker ≤ center D := by
  rcases Quasisimple.normal_le_center_or_eq_top hDq
      ((QuotientGroup.mk' (oddCore H)).subgroupMap D).ker with h | h
  · exact h
  · exfalso
    have h1 : (QuotientGroup.mk' (oddCore H)).subgroupMap D ⟨y, hyD⟩ = 1 :=
      MonoidHom.mem_ker.1 (h ▸ mem_top _)
    have h2 : QuotientGroup.mk' (oddCore H) y = 1 := congrArg Subtype.val h1
    have h3 := orderOf_mk_oddCore hy
    rw [h2, orderOf_one] at h3
    exact absurd h3 (by decide)

theorem odd_card_center_map_oddCore (hDq : CFSG.Open.IsQuasisimple D)
    (hZD : Odd (Nat.card (center D))) {y : H} (hyD : y ∈ D) (hy : orderOf y = 2) :
    Odd (Nat.card (center (D.map (QuotientGroup.mk' (oddCore H))))) := by
  have : Group.IsPerfect D := Group.isPerfect_def.2 hDq.1
  rw [← Quasisimple.center_map_of_central_kernel _
    ((QuotientGroup.mk' (oddCore H)).subgroupMap_surjective D)
    (ker_subgroupMap_mk_oddCore_le_center hDq hyD hy)]
  exact hZD.of_dvd_nat (card_map_dvd (center D) _)

theorem card_quotient_center_map_oddCore (hDq : CFSG.Open.IsQuasisimple D) {y : H}
    (hyD : y ∈ D) (hy : orderOf y = 2) :
    Nat.card (D.map (QuotientGroup.mk' (oddCore H)) ⧸
        center (D.map (QuotientGroup.mk' (oddCore H)))) = Nat.card (D ⧸ center D) := by
  have : Group.IsPerfect D := Group.isPerfect_def.2 hDq.1
  exact (Nat.card_congr (PerfectCentralQuotient.equivalence _
    ((QuotientGroup.mk' (oddCore H)).subgroupMap_surjective D)
    (ker_subgroupMap_mk_oddCore_le_center hDq hyD hy)).toEquiv).symm

theorem isSolvable_outer_map_oddCore (hDq : CFSG.Open.IsQuasisimple D)
    (hOut : Group.IsSolvable (Outer (D ⧸ center D))) {y : H} (hyD : y ∈ D) (hy : orderOf y = 2) :
    Group.IsSolvable (Outer (D.map (QuotientGroup.mk' (oddCore H)))) := by
  have : Group.IsPerfect D := Group.isPerfect_def.2 hDq.1
  have hfs := (QuotientGroup.mk' (oddCore H)).subgroupMap_surjective D
  have := hOut
  have : Group.IsSolvable (Outer (D.map (QuotientGroup.mk' (oddCore H)) ⧸
      center (D.map (QuotientGroup.mk' (oddCore H))))) :=
    solvable_of_equiv (PerfectCentralQuotient.equivalence _ hfs
      (ker_subgroupMap_mk_oddCore_le_center hDq hyD hy))
  have : Group.IsPerfect (D.map (QuotientGroup.mk' (oddCore H))) :=
    Group.IsPerfect.ofSurjective hfs
  exact solvable_of_centerQuotient _

theorem mk_not_mem_center_map_oddCore (hDq : CFSG.Open.IsQuasisimple D)
    (hZD : Odd (Nat.card (center D))) {y : H} (hyD : y ∈ D) (hy : orderOf y = 2) :
    (⟨QuotientGroup.mk' (oddCore H) y, y, hyD, rfl⟩ : D.map (QuotientGroup.mk' (oddCore H))) ∉
      center (D.map (QuotientGroup.mk' (oddCore H))) := by
  intro hyc
  have h1 := (center (D.map (QuotientGroup.mk' (oddCore H)))).orderOf_dvd_natCard hyc
  have h2 : orderOf (⟨QuotientGroup.mk' (oddCore H) y, y, hyD, rfl⟩ :
      D.map (QuotientGroup.mk' (oddCore H))) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_mk_oddCore hy
  rw [h2] at h1
  exact (Nat.not_even_iff_odd.2 (odd_card_center_map_oddCore hDq hZD hyD hy))
    (even_iff_two_dvd.2 h1)

end Image

section LemmaA

variable {H : Type*} [Group H] [Finite H]

theorem map_le_inf_centralizer_of_normal_of_odd_center {t : H} (ht : orderOf t = 2)
    {D : Subgroup H} (hDq : CFSG.Open.IsQuasisimple D)
    (hOut : Group.IsSolvable (Outer (D ⧸ center D))) (hDt : D ≤ centralizer ({t} : Set H))
    (hsyl : ∀ U : Subgroup (H ⧸ oddCore H), IsPGroup 2 U →
      U ≤ centralizer (D.map (QuotientGroup.mk' (oddCore H)) : Set (H ⧸ oddCore H)) →
      Nat.card U ≤ 2)
    {y : H} (hyD : y ∈ D) (hy : orderOf y = 2) {t' : H} (ht' : t' = y ∨ t' = t * y)
    {P : Subgroup H} (hP : ⁅P, P⁆ = P) (hPt' : P ≤ centralizer ({t'} : Set H))
    (hnorm : (D.map (QuotientGroup.mk' (oddCore H))).Normal) :
    P.map (QuotientGroup.mk' (oddCore H)) ≤ D.map (QuotientGroup.mk' (oddCore H)) ⊓
      centralizer ({QuotientGroup.mk' (oddCore H) y} : Set (H ⧸ oddCore H)) := by
  set π := QuotientGroup.mk' (oddCore H)
  have hOutbar := isSolvable_outer_map_oddCore hDq hOut hyD hy
  have htc := F4Pilot.mk_mem_center_of_normal_map_oddCore hDt hsyl hnorm
  have hCD := F4Pilot.centralizer_map_oddCore_eq_zpowers ht hDt hsyl hnorm
  refine le_inf ?_ ?_
  · have hsolv : Group.IsSolvable (centralizer (D.map π : Set (H ⧸ oddCore H)) ⊓ ⊤ :
        Subgroup (H ⧸ oddCore H)) := by
      rw [inf_top_eq, hCD]
      infer_instance
    have hN : (⊤ : Subgroup (H ⧸ oddCore H)) ≤ normalizer (D.map π : Set (H ⧸ oddCore H)) := by
      rw [normalizer_eq_top_iff.2 hnorm]
    exact perfect_le_of_isSolvable_outer hOutbar le_top hN hsolv
      (by rw [← map_commutator, hP]) le_top
  · have htc' : π t ∈ center (H ⧸ oddCore H) := htc
    rintro _ ⟨p, hp, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h := mem_centralizer_singleton_iff.1 (hPt' hp)
    rcases ht' with rfl | rfl
    · have h' := congrArg π h
      simpa only [map_mul] using h'
    · have h' := congrArg π h
      simp only [map_mul] at h'
      have hc : π p * π t = π t * π p := mem_center_iff.1 htc' (π p)
      have key : π t * (π p * π y) = π t * (π y * π p) := by
        calc π t * (π p * π y) = (π t * π p) * π y := by rw [mul_assoc]
          _ = (π p * π t) * π y := by rw [hc]
          _ = π p * (π t * π y) := by rw [mul_assoc]
          _ = π t * π y * π p := h'
          _ = π t * (π y * π p) := by rw [mul_assoc]
      exact mul_left_cancel key

theorem not_normal_map_oddCore_of_perfect_le_of_odd_center {t : H} (ht : orderOf t = 2)
    {D : Subgroup H} (hDq : CFSG.Open.IsQuasisimple D) (hZD : Odd (Nat.card (center D)))
    (hOut : Group.IsSolvable (Outer (D ⧸ center D))) (hDt : D ≤ centralizer ({t} : Set H))
    (hsyl : ∀ U : Subgroup (H ⧸ oddCore H), IsPGroup 2 U →
      U ≤ centralizer (D.map (QuotientGroup.mk' (oddCore H)) : Set (H ⧸ oddCore H)) →
      Nat.card U ≤ 2)
    {y : H} (hyD : y ∈ D) (hy : orderOf y = 2) {t' : H} (ht' : t' = y ∨ t' = t * y)
    {P : Subgroup H} (hP : ⁅P, P⁆ = P) (hPt' : P ≤ centralizer ({t'} : Set H))
    (hcard : Nat.card (D ⧸ center D) ≤ Nat.card (P ⧸ oddCore P)) :
    ¬ (D.map (QuotientGroup.mk' (oddCore H))).Normal := by
  intro hnorm
  set π := QuotientGroup.mk' (oddCore H)
  have hO : Odd (Nat.card (oddCore H)) := CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  have hZodd := odd_card_center_map_oddCore hDq hZD hyD hy
  have hle := map_le_inf_centralizer_of_normal_of_odd_center ht hDq hOut hDt hsyl hyD hy ht' hP
    hPt' hnorm
  have hPbar : P.map π ≤ D.map π := hle.trans inf_le_left
  have hPy : P.map π ≤ centralizer ({π y} : Set (H ⧸ oddCore H)) := hle.trans inf_le_right
  set θ : P →* (D.map π) ⧸ center (D.map π) :=
    (QuotientGroup.mk' (center (D.map π))).comp ((inclusion hPbar).comp (π.subgroupMap P))
  have hθker : Odd (Nat.card θ.ker) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hev)
    have hxH : orderOf ((x : P) : H) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
    have hw : inclusion hPbar (π.subgroupMap P (x : P)) ∈ center (D.map π) := by
      have h := x.2
      rw [MonoidHom.mem_ker] at h
      exact (QuotientGroup.eq_one_iff _).1 h
    have hpow : π (((x : P) : H) ^ Nat.card (center (D.map π))) = 1 := by
      have h := orderOf_dvd_iff_pow_eq_one.1 ((center (D.map π)).orderOf_dvd_natCard hw)
      rw [map_pow]
      exact congrArg Subtype.val h
    have hmem : ((x : P) : H) ^ Nat.card (center (D.map π)) ∈ oddCore H :=
      (QuotientGroup.eq_one_iff _).1 hpow
    have h3 := orderOf_dvd_iff_pow_eq_one.1 ((oddCore H).orderOf_dvd_natCard hmem)
    rw [← pow_mul] at h3
    have h4 := orderOf_dvd_of_pow_eq_one h3
    rw [hxH] at h4
    exact (Nat.not_even_iff_odd.2 (hZodd.mul hO)) (even_iff_two_dvd.2 h4)
  have hkerle : θ.ker ≤ oddCore P := le_sSup ⟨inferInstance, hθker⟩
  have hrange : θ.range = ⊤ := by
    apply eq_top_of_le_card
    have h1 := card_ker_mul_card_range θ
    have h2 := (oddCore P).card_mul_index
    have h3 : Nat.card θ.ker ≤ Nat.card (oddCore P) := card_le_of_le hkerle
    have hpos : 0 < Nat.card (oddCore P) := Nat.card_pos
    have h4 : (oddCore P).index ≤ Nat.card θ.range := by
      refine Nat.le_of_mul_le_mul_left ?_ hpos
      rw [h2, ← h1]
      exact Nat.mul_le_mul_right _ h3
    calc Nat.card ((D.map π) ⧸ center (D.map π)) = Nat.card (D ⧸ center D) :=
          card_quotient_center_map_oddCore hDq hyD hy
      _ ≤ Nat.card (P ⧸ oddCore P) := hcard
      _ ≤ Nat.card θ.range := h4
  apply mk_not_mem_center_map_oddCore hDq hZD hyD hy
  rw [mem_center_iff]
  intro d
  obtain ⟨p, hp⟩ := MonoidHom.range_eq_top.1 hrange (QuotientGroup.mk' (center (D.map π)) d)
  set w : D.map π := inclusion hPbar (π.subgroupMap P p)
  have hwd : w⁻¹ * d ∈ center (D.map π) := by
    have h : QuotientGroup.mk' (center (D.map π)) w = QuotientGroup.mk' (center (D.map π)) d := hp
    rwa [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h
  have hwy : w * ⟨π y, y, hyD, rfl⟩ = ⟨π y, y, hyD, rfl⟩ * w :=
    Subtype.ext (mem_centralizer_singleton_iff.1 (hPy ⟨(p : H), p.2, rfl⟩))
  have hz := mem_center_iff.1 hwd ⟨π y, y, hyD, rfl⟩
  calc d * ⟨π y, y, hyD, rfl⟩ = w * ((w⁻¹ * d) * ⟨π y, y, hyD, rfl⟩) := by group
    _ = w * (⟨π y, y, hyD, rfl⟩ * (w⁻¹ * d)) := by rw [hz]
    _ = (w * ⟨π y, y, hyD, rfl⟩) * (w⁻¹ * d) := by group
    _ = (⟨π y, y, hyD, rfl⟩ * w) * (w⁻¹ * d) := by rw [hwy]
    _ = ⟨π y, y, hyD, rfl⟩ * d := by group

theorem not_normal_map_oddCore_of_mulEquiv_of_odd_center {t : H} (ht : orderOf t = 2)
    {D : Subgroup H} (hDq : CFSG.Open.IsQuasisimple D) (hZD : Odd (Nat.card (center D)))
    (hOut : Group.IsSolvable (Outer (D ⧸ center D))) (hDt : D ≤ centralizer ({t} : Set H))
    (hsyl : ∀ U : Subgroup (H ⧸ oddCore H), IsPGroup 2 U →
      U ≤ centralizer (D.map (QuotientGroup.mk' (oddCore H)) : Set (H ⧸ oddCore H)) →
      Nat.card U ≤ 2)
    {y : H} (hyD : y ∈ D) (hy : orderOf y = 2) {t' : H} (ht' : t' = y ∨ t' = t * y)
    {P : Subgroup H} (hPt' : P ≤ centralizer ({t'} : Set H)) (hPD : Nonempty (P ≃* D)) :
    ¬ (D.map (QuotientGroup.mk' (oddCore H))).Normal := by
  obtain ⟨e⟩ := hPD
  have hPq : CFSG.Open.IsQuasisimple P := Components.quasisimple_of_equiv e hDq
  have hevenD : Even (Nat.card D) := by
    have h := D.orderOf_dvd_natCard hyD
    rw [hy] at h
    exact even_iff_two_dvd.2 h
  have hevenP : Even (Nat.card P) := by
    rw [Nat.card_congr e.toEquiv]
    exact hevenD
  refine not_normal_map_oddCore_of_perfect_le_of_odd_center ht hDq hZD hOut hDt hsyl hyD hy ht'
    (isPerfect_iff.1 (Group.isPerfect_def.2 hPq.1)) hPt' ?_
  calc Nat.card (D ⧸ center D) = Nat.card (P ⧸ center P) :=
        Nat.card_congr (QuotientGroup.congr (center D) (center P) e.symm
          (map_center_eq e.symm)).toEquiv
    _ ≤ Nat.card (P ⧸ oddCore P) := card_quotient_center_le_card_quotient_oddCore hPq hevenP

theorem not_normal_map_oddCore_subgroupOf_of_mulEquiv_of_odd_center {G : Type*} [Group G]
    [Finite G] {H : Subgroup G} {t : G} (htH : t ∈ H) (ht : orderOf t = 2) {D : Subgroup G}
    (hDH : D ≤ H) (hDq : CFSG.Open.IsQuasisimple D) (hZD : Odd (Nat.card (center D)))
    (hOut : Group.IsSolvable (Outer (D ⧸ center D))) (hDt : D ≤ centralizer ({t} : Set G))
    (hsyl : ∀ U : Subgroup (H ⧸ oddCore H), IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)) :
        Set (H ⧸ oddCore H)) → Nat.card U ≤ 2)
    {y : G} (hyD : y ∈ D) (hy : orderOf y = 2) {t' : G} (ht' : t' = y ∨ t' = t * y)
    {P : Subgroup G} (hPH : P ≤ H) (hPt' : P ≤ centralizer ({t'} : Set G))
    (hPD : Nonempty (P ≃* D)) :
    ¬ ((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H))).Normal := by
  obtain ⟨ePD⟩ := hPD
  have eD : D ≃* D.subgroupOf H := (subgroupOfEquivOfLe hDH).symm
  have eP : P ≃* P.subgroupOf H := (subgroupOfEquivOfLe hPH).symm
  have hDq' : CFSG.Open.IsQuasisimple (D.subgroupOf H) :=
    Components.quasisimple_of_equiv eD.symm hDq
  have hZD' : Odd (Nat.card (center (D.subgroupOf H))) := by
    rw [← map_center_eq eD, card_map_of_injective eD.injective]
    exact hZD
  have hOut' : Group.IsSolvable (Outer (D.subgroupOf H ⧸ center (D.subgroupOf H))) := by
    have := hOut
    exact solvable_centerQuotient_of_equiv eD
  have hDt' : D.subgroupOf H ≤ centralizer ({⟨t, htH⟩} : Set H) := fun d hd =>
    mem_centralizer_singleton_iff.2 (Subtype.ext
      (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd))))
  have hyH : y ∈ H := hDH hyD
  have ht'H : t' ∈ H := by
    rcases ht' with rfl | rfl
    · exact hyH
    · exact H.mul_mem htH hyH
  have hPt'' : P.subgroupOf H ≤ centralizer ({⟨t', ht'H⟩} : Set H) := fun p hp =>
    mem_centralizer_singleton_iff.2 (Subtype.ext
      (mem_centralizer_singleton_iff.1 (hPt' (mem_subgroupOf.1 hp))))
  refine not_normal_map_oddCore_of_mulEquiv_of_odd_center (H := H) (t := ⟨t, htH⟩) ?_ hDq' hZD'
    hOut' hDt' hsyl (y := ⟨y, hyH⟩) (mem_subgroupOf.2 hyD) ?_ (t' := ⟨t', ht'H⟩) ?_ hPt''
    ⟨eP.symm.trans (ePD.trans eD)⟩
  · rw [orderOf_mk, ht]
  · rw [orderOf_mk, hy]
  · rcases ht' with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

theorem not_normal_map_oddCore_centralizer_of_mulEquiv_of_odd_center {G : Type*} [Group G]
    [Finite G] {X : Subgroup G} {t : G} (htX : t ∈ centralizer (X : Set G)) (ht : orderOf t = 2)
    {D : Subgroup G} (hDX : D ≤ centralizer (X : Set G)) (hDq : CFSG.Open.IsQuasisimple D)
    (hZD : Odd (Nat.card (center D))) (hOut : Group.IsSolvable (Outer (D ⧸ center D)))
    (hDt : D ≤ centralizer ({t} : Set G))
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2)
    {y : G} (hyD : y ∈ D) (hy : orderOf y = 2) {t' : G} (ht' : t' = y ∨ t' = t * y)
    {P : Subgroup G} (hP : P ≤ centralizer (X : Set G) ⊓ centralizer ({t'} : Set G))
    (hPD : Nonempty (P ≃* D)) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal :=
  not_normal_map_oddCore_subgroupOf_of_mulEquiv_of_odd_center htX ht hDX hDq hZD hOut hDt hsyl
    hyD hy ht' (hP.trans inf_le_left) (hP.trans inf_le_right) hPD

end LemmaA

end CFSG.SeitzReduction.LinearPilot
