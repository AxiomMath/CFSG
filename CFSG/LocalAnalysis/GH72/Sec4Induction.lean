module

public import CFSG.LocalAnalysis.GH72.Sec4Split
public import CFSG.LocalAnalysis.GH72.Sec4A
public import CFSG.LocalAnalysis.GH72.AutRank
public import CFSG.LocalAnalysis.GH72.RelativeZJAmbient
import CFSG.LocalAnalysis.GH72.Alignment
import CFSG.LocalAnalysis.GH72.Sec2
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.LocalAnalysis.GH72.Sec4Residual

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools
open CFSG.GorensteinWalter (twoResidualOf)
open CFSG.CGT.Foote81L6.TStruct (IsFourIn isElemAbelian_two_iff)

section Transfer

variable {G : Type*} [Group G] [Finite G] {H : Subgroup G}

theorem orderOf_mk_eq {P : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup 2 P) {x : G} (hx : x ∈ P) :
    orderOf (QuotientGroup.mk ⟨x, hPH hx⟩ : Bar H) = orderOf x := by
  let φ : P →* Bar H := (QuotientGroup.mk' (CFSG.oddCore H)).comp (inclusion hPH)
  have hφ : Function.Injective φ := fun a b hab =>
    inclusion_injective hPH (mk_inj_of_isPGroup hP a.2 b.2 hab)
  have h := orderOf_injective φ hφ ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at h
  exact h

theorem mk_mem_bar_iff {P Q : Subgroup G} (hPQ : P ≤ Q) (hQ : IsPGroup 2 Q) {x : G} (hxH : x ∈ H)
    (hxQ : x ∈ Q) : (QuotientGroup.mk ⟨x, hxH⟩ : Bar H) ∈ bar H P ↔ x ∈ P :=
  ⟨mem_of_mk_mem_bar hPQ hQ hxH hxQ, mk_mem_bar hxH⟩

theorem isAStarFactor_of_mulEquiv {X Y : Type*} [Group X] [Group Y] {L : Subgroup X}
    {M : Subgroup Y} (e : L ≃* M) (h : IsAStarFactor M) : IsAStarFactor L := by
  rcases h with ⟨⟨f⟩⟩ | ⟨p, k, hp, hp2, hq, ⟨f⟩⟩ | hV
  · exact Or.inl ⟨e.trans f⟩
  · exact Or.inr (Or.inl ⟨p, k, hp, hp2, hq, ⟨e.trans f⟩⟩)
  · exact Or.inr (Or.inr (IsKleinFour.mk (by rw [Nat.card_congr e.toEquiv]; exact hV.card_four)
      (by rw [Monoid.exponent_eq_of_mulEquiv e]; exact hV.exponent_two)))

end Transfer

section Generic

variable {Y : Type*} [Group Y] [Finite Y]

theorem inf_centralizer_ne_bot_of_isPGroup {R N : Subgroup Y} (hR : IsPGroup 2 R) (hNR : N ≤ R)
    (hRN : R ≤ normalizer (N : Set Y)) (hN : N ≠ ⊥) : N ⊓ centralizer (R : Set Y) ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent R := hR.isNilpotent
  haveI : (N.subgroupOf R).Normal := (normal_subgroupOf_iff_le_normalizer hNR).2 hRN
  have hne : N.subgroupOf R ≠ ⊥ := by
    intro h
    apply hN
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hNR hx⟩ : R) ∈ N.subgroupOf R := hx
    rw [h, mem_bot] at hx'
    exact (mem_bot).2 (congrArg Subtype.val hx')
  intro hbot
  apply Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  rw [eq_bot_iff]
  rintro x hx
  obtain ⟨hxN, hxZ⟩ := mem_inf.1 hx
  have hx' : (x : Y) ∈ N ⊓ centralizer (R : Set Y) := by
    refine mem_inf.2 ⟨hxN, mem_centralizer_iff.2 fun r hr => ?_⟩
    exact congrArg Subtype.val (mem_center_iff.1 hxZ ⟨r, hr⟩)
  rw [hbot, mem_bot] at hx'
  exact (mem_bot).2 (Subtype.ext hx')

theorem exists_orderOf_eq_two_of_isPGroup {N : Subgroup Y} (hN : IsPGroup 2 N) (hne : N ≠ ⊥) :
    ∃ t ∈ N, orderOf t = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hN
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, card_eq_one] at hk
    exact hne hk
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 2 (by rw [hk]; exact dvd_pow_self 2 hk0)
  exact ⟨t, t.2, by rwa [Subgroup.orderOf_coe]⟩

theorem exists_mem_center_of_normal_le_centralizer {R N : Subgroup Y} (hR : IsSylowOf 2 R ⊤)
    (hNn : N.Normal) (hN : IsPGroup 2 N)
    (hNC : N ≤ centralizer (twoResidualOf (⊤ : Subgroup Y) : Set Y)) (hne : N ≠ ⊥) :
    ∃ t ∈ R, orderOf t = 2 ∧ t ∈ center Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hNn
  have hNR : N ≤ R := by
    have h := hR.eq_of_le le_sup_left le_top (hR.isPGroup.to_sup_of_normal_right hN)
    rw [← h]
    exact le_sup_right
  obtain ⟨t, ht, ht2⟩ := exists_orderOf_eq_two_of_isPGroup (hN.to_le inf_le_left)
    (inf_centralizer_ne_bot_of_isPGroup hR.isPGroup hNR (le_normalizer_of_normal) hne)
  obtain ⟨htN, htR⟩ := mem_inf.1 ht
  refine ⟨t, hNR htN, ht2, mem_center_iff.2 fun g => ?_⟩
  obtain ⟨n, hn⟩ := exists_relIndex_twoResidualOf (⊤ : Subgroup Y)
  have htop : (⊤ : Subgroup Y) ≤ R ⊔ twoResidualOf ⊤ := le_sup_of_isSylowOf_of_relIndex hR hn
  have hle : R ⊔ twoResidualOf ⊤ ≤ centralizer ({t} : Set Y) := by
    refine sup_le (fun r hr => ?_) (fun k hk => ?_)
    · rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.1 htR r hr
    · rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.1 (hNC htN) k hk
  exact mem_centralizer_singleton_iff.1 (hle (htop (mem_top g)))

theorem exists_mem_center_of_centralizer {R : Subgroup Y} (hR : IsSylowOf 2 R ⊤)
    (hinf : twoResidualOf ⊤ ⊓ centralizer (twoResidualOf (⊤ : Subgroup Y) : Set Y) = ⊥)
    (hne : centralizer (twoResidualOf (⊤ : Subgroup Y) : Set Y) ≠ ⊥) :
    ∃ t ∈ R, orderOf t = 2 ∧ t ∈ center Y := by
  haveI : (twoResidualOf (⊤ : Subgroup Y)).Normal := twoResidualOf_top_normal
  have hC2 : IsPGroup 2 (centralizer (twoResidualOf (⊤ : Subgroup Y) : Set Y)) := by
    intro c
    obtain ⟨k, hk⟩ := exists_pow_mem_twoResidualOf (mem_top (c : Y))
    refine ⟨k, Subtype.ext ?_⟩
    have h : (c : Y) ^ 2 ^ k ∈
        twoResidualOf ⊤ ⊓ centralizer (twoResidualOf (⊤ : Subgroup Y) : Set Y) :=
      mem_inf.2 ⟨hk, pow_mem c.2 _⟩
    rw [hinf, mem_bot] at h
    simpa using h
  exact exists_mem_center_of_normal_le_centralizer hR inferInstance hC2 le_rfl hne

theorem eq_bot_of_isCyclic_of_isSylowOf {L T : Subgroup Y}
    (hT : IsSylowOf 2 T (twoResidualOf L)) (hcyc : IsCyclic T) : T = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hT
  have hQc : IsCyclic Q := by
    let e : (Q : Subgroup ↥(twoResidualOf L)) ≃* T :=
      ((Q : Subgroup ↥(twoResidualOf L)).equivMapOfInjective _
        (twoResidualOf L).subtype_injective).trans (MulEquiv.subgroupCongr hQ)
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  obtain ⟨N, hNn, hNc⟩ := CFSG.exists_normal_isComplement'_of_isCyclic_sylow_two Q hQc
  haveI := hNn
  have hidx : N.index = Nat.card Q := hNc.symm.index_eq_card
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 Q.isPGroup'
  have hle : twoResidualOf L ≤ N.map (twoResidualOf L).subtype := by
    have h := twoResidualOf_le_of_forall (H := twoResidualOf L)
      (L := N.map (twoResidualOf L).subtype) fun x hx hodd =>
        ⟨⟨x, hx⟩, mem_of_odd_of_index_eq_two_pow (hidx.trans hk)
          (by rwa [Subgroup.orderOf_mk]), rfl⟩
    rwa [twoResidualOf_twoResidualOf] at h
  have hNtop : N = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨y', hy', hyy⟩ := hle y.2
    have e : y' = y := Subtype.ext hyy
    rwa [← e]
  rw [hNtop, index_top] at hidx
  have hQbot : (Q : Subgroup ↥(twoResidualOf L)) = ⊥ := (card_eq_one.1 hidx.symm)
  rw [← hQ, hQbot, Subgroup.map_bot]

theorem odd_card_of_isSylowOf_bot {K : Subgroup Y} (hT : IsSylowOf 2 ⊥ K) : Odd (Nat.card K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (isSylowOf_iff.1 hT).2.2
  rw [relIndex_bot_left] at h
  exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h)

end Generic

section GW

variable {G : Type} [Group G] [Finite G]

theorem exists_isIsolatedIn_of_mem_center {H R : Subgroup G} (hR : IsSylowOf 2 R H) {t : Bar H}
    (htR : t ∈ bar H R) (ht2 : orderOf t = 2) (htZ : t ∈ center (Bar H)) :
    ∃ x, IsIsolatedIn H x := by
  obtain ⟨⟨x, hxH⟩, hxR, rfl⟩ := htR
  have hxR' : x ∈ R := hxR
  have hx2 : orderOf x = 2 := by
    rw [← orderOf_mk_eq hR.le hR.isPGroup hxR']
    exact ht2
  exact ⟨x, isIsolatedIn_of_mk_mem_center hxH hx2 htZ⟩

theorem exists_isIsolatedIn_of_normal_le_centralizer {H : Subgroup G} {N : Subgroup (Bar H)}
    (hNn : N.Normal) (hN : IsPGroup 2 N)
    (hNC : N ≤ centralizer (twoResidualOf (⊤ : Subgroup (Bar H)) : Set (Bar H))) (hne : N ≠ ⊥) :
    ∃ t, IsIsolatedIn H t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := exists_isSylowOf 2 H
  have hRbar : IsSylowOf 2 (bar H R) ⊤ := by
    rw [← bar_self]
    exact isSylowOf_bar le_rfl hR
  obtain ⟨t, htR, ht2, htZ⟩ := exists_mem_center_of_normal_le_centralizer hRbar hNn hN hNC hne
  exact exists_isIsolatedIn_of_mem_center hR htR ht2 htZ

theorem O_le_O_of_le_normalizer {K H : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ normalizer (K : Set G)) : O K ≤ O H := by
  have hconj : ∀ h ∈ H, ∀ x ∈ O K, h * x * h⁻¹ ∈ O K := by
    intro h hh x hx
    have hK : ∀ y, y ∈ K ↔ h * y * h⁻¹ ∈ K := mem_normalizer_iff.1 (hHK hh)
    let φ : K →* K :=
      ((MulAut.conj h).toMonoidHom.comp K.subtype).codRestrict K fun y => (hK y).1 y.2
    have hφs : Function.Surjective φ := by
      intro y
      have hy : h⁻¹ * y * h ∈ K := by
        rw [hK]
        have e : h * (h⁻¹ * (y : G) * h) * h⁻¹ = y := by group
        rw [e]
        exact y.2
      refine ⟨⟨h⁻¹ * y * h, hy⟩, Subtype.ext ?_⟩
      show h * (h⁻¹ * (y : G) * h) * h⁻¹ = y
      group
    have hle : (CFSG.oddCore K).map φ ≤ CFSG.oddCore K :=
      le_oddCore_of_normal ((CFSG.oddCore_normal K).map φ hφs)
        (Odd.of_dvd_nat odd_card_oddCore (card_map_dvd _ _))
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨φ y, hle ⟨y, hy, rfl⟩, rfl⟩
  have hnorm : H ≤ normalizer (O K : Set G) := fun h hh => mem_normalizer_iff.2 fun x =>
    ⟨fun hx => hconj h hh x hx, fun hx => by
      have h1 := hconj h⁻¹ (inv_mem hh) _ hx
      have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
      rwa [e] at h1⟩
  have hOKH : O K ≤ H := (map_subtype_le _).trans hKH
  have hsub : (O K).subgroupOf H ≤ CFSG.oddCore H :=
    le_oddCore_of_normal ((normal_subgroupOf_iff_le_normalizer hOKH).2 hnorm) (by
      rw [show Nat.card ((O K).subgroupOf H) = Nat.card (O K) from
        Nat.card_congr (subgroupOfEquivOfLe hOKH).toEquiv]
      exact card_O_odd K)
  intro x hx
  exact ⟨⟨x, hOKH hx⟩, hsub hx, rfl⟩

theorem exists_isIsolatedIn_of_isIsolatedIn_twoResidualOf {H : Subgroup G} {z : G}
    (hz : IsIsolatedIn (twoResidualOf H) z) : ∃ t, IsIsolatedIn H t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (twoResidualOf (⊤ : Subgroup (Bar H))).Normal := twoResidualOf_top_normal
  set K := twoResidualOf (⊤ : Subgroup (Bar H)) with hK
  have hLH : twoResidualOf H ≤ H := twoResidualOf_le_self H
  have hzL : z ∈ twoResidualOf H := hz.1
  have hzH : z ∈ H := hLH hzL
  have hOO : O (twoResidualOf H) ≤ O H := O_le_O_of_le_normalizer hLH (le_normalizer_twoResidualOf H)
  have hzK : (QuotientGroup.mk ⟨z, hzH⟩ : Bar H) ∈ K := by
    rw [hK, ← bar_twoResidualOf]
    exact mk_mem_bar hzH hzL
  have hzC : (QuotientGroup.mk ⟨z, hzH⟩ : Bar H) ∈ centralizer (K : Set (Bar H)) := by
    rw [mem_centralizer_iff]
    intro x hx
    rw [hK, ← bar_twoResidualOf] at hx
    obtain ⟨⟨k, hkH⟩, hk, rfl⟩ := hx
    have hk' : k ∈ twoResidualOf H := hk
    have hc := hOO (hz.conj_mul_inv_mem_O hk')
    obtain ⟨o, ho, hoe⟩ := hc
    have h1 : (⟨k, hkH⟩ : H) * ⟨z, hzH⟩ * (⟨k, hkH⟩ : H)⁻¹ * (⟨z, hzH⟩ : H)⁻¹ = o :=
      Subtype.ext hoe.symm
    have h2 : (QuotientGroup.mk ((⟨k, hkH⟩ : H) * ⟨z, hzH⟩ * (⟨k, hkH⟩ : H)⁻¹ *
        (⟨z, hzH⟩ : H)⁻¹) : Bar H) = 1 := by
      rw [h1]
      exact (QuotientGroup.eq_one_iff o).2 ho
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv] at h2
    have h3 := mul_inv_eq_one.1 h2
    show (QuotientGroup.mk' (CFSG.oddCore H) ⟨k, hkH⟩) * QuotientGroup.mk ⟨z, hzH⟩ =
      QuotientGroup.mk ⟨z, hzH⟩ * QuotientGroup.mk' (CFSG.oddCore H) ⟨k, hkH⟩
    rw [QuotientGroup.mk'_apply]
    calc (QuotientGroup.mk ⟨k, hkH⟩ : Bar H) * QuotientGroup.mk ⟨z, hzH⟩ =
        QuotientGroup.mk ⟨k, hkH⟩ * QuotientGroup.mk ⟨z, hzH⟩ *
          (QuotientGroup.mk ⟨k, hkH⟩)⁻¹ * QuotientGroup.mk ⟨k, hkH⟩ := by group
      _ = QuotientGroup.mk ⟨z, hzH⟩ * QuotientGroup.mk ⟨k, hkH⟩ := by rw [h3]
  have hz2 : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz.2.1, pow_two] at h
  have hzbar2 : (QuotientGroup.mk ⟨z, hzH⟩ : Bar H) * QuotientGroup.mk ⟨z, hzH⟩ = 1 := by
    rw [← QuotientGroup.mk_mul]
    have e : (⟨z, hzH⟩ : H) * ⟨z, hzH⟩ = 1 := Subtype.ext hz2
    rw [e, QuotientGroup.mk_one]
  have hzbar1 : (QuotientGroup.mk ⟨z, hzH⟩ : Bar H) ≠ 1 := by
    intro h
    have hzO : z ∈ O H := ⟨_, (QuotientGroup.eq_one_iff _).1 h, rfl⟩
    have h1 := eq_one_of_mul_self_of_odd (card_O_odd H) hzO hz2
    have h2 := hz.2.1
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  let Ω : Subgroup (Bar H) :=
    { carrier := {x | x ∈ K ⊓ centralizer (K : Set (Bar H)) ∧ x * x = 1}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        have hab : a * b = b * a :=
          mem_centralizer_iff.1 (mem_inf.1 hb.1).2 a (mem_inf.1 ha.1).1
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hab]
          _ = (a * a) * (b * b) := by group
          _ = 1 := by rw [ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨one_mem _, mul_one 1⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [← mul_inv_rev, ha.2, inv_one]⟩ }
  have hΩn : Ω.Normal := by
    constructor
    rintro n ⟨hnKC, hn2⟩ g
    haveI : (centralizer (K : Set (Bar H))).Normal := inferInstance
    refine ⟨mem_inf.2 ⟨(inferInstance : K.Normal).conj_mem n (mem_inf.1 hnKC).1 g,
      (inferInstance : (centralizer (K : Set (Bar H))).Normal).conj_mem n
        (mem_inf.1 hnKC).2 g⟩, ?_⟩
    calc g * n * g⁻¹ * (g * n * g⁻¹) = g * (n * n) * g⁻¹ := by group
      _ = 1 := by rw [hn2]; group
  have hΩ2 : IsPGroup 2 Ω := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, pow_two]
    exact x.2.2)⟩
  have hΩC : Ω ≤ centralizer (K : Set (Bar H)) := fun x hx => (mem_inf.1 hx.1).2
  have hΩne : Ω ≠ ⊥ := by
    intro h
    have hmem : (QuotientGroup.mk ⟨z, hzH⟩ : Bar H) ∈ Ω := ⟨mem_inf.2 ⟨hzK, hzC⟩, hzbar2⟩
    rw [h, mem_bot] at hmem
    exact hzbar1 hmem
  exact exists_isIsolatedIn_of_normal_le_centralizer hΩn hΩ2 hΩC hΩne

theorem exists_isIsolatedIn_of_isCyclic_or_isDih
    {H E T : Subgroup G} (hEH : E ≤ H) (hE : IsE16 E) (hT : IsSylowOf 2 T (twoResidualOf H))
    (hTc : IsCyclic T ∨ IsDih T) : ∃ t, IsIsolatedIn H t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (twoResidualOf (⊤ : Subgroup (Bar H))).Normal := twoResidualOf_top_normal
  have hLH : twoResidualOf H ≤ H := twoResidualOf_le_self H
  have hTbar : IsSylowOf 2 (bar H T) (twoResidualOf (⊤ : Subgroup (Bar H))) := by
    rw [← bar_twoResidualOf]
    exact isSylowOf_bar hLH hT
  have hO : CFSG.oddCore (Bar H) = ⊥ := oddCore_quotient_oddCore_eq_bot H
  have hEbar : IsE16 (bar H E) := hE.bar hEH
  have key : twoResidualOf ⊤ ⊓
      centralizer (twoResidualOf (⊤ : Subgroup (Bar H)) : Set (Bar H)) = ⊥ ∧
      centralizer (twoResidualOf (⊤ : Subgroup (Bar H)) : Set (Bar H)) ≠ ⊥ := by
    rcases hTc with hcyc | hdih
    · have hT1 : T = ⊥ := eq_bot_of_isCyclic_of_isSylowOf hT hcyc
      rw [hT1, bar_bot] at hTbar
      have hKodd := odd_card_of_isSylowOf_bot hTbar
      have hKbot : twoResidualOf (⊤ : Subgroup (Bar H)) = ⊥ := by
        rw [eq_bot_iff, ← hO]
        exact le_oddCore_of_normal inferInstance hKodd
      refine ⟨by rw [hKbot, bot_inf_eq], fun h => ?_⟩
      have hle : bar H E ≤ centralizer (twoResidualOf (⊤ : Subgroup (Bar H)) : Set (Bar H)) := by
        rw [hKbot]
        intro x _
        rw [mem_centralizer_iff]
        intro y hy
        rw [SetLike.mem_coe, mem_bot] at hy
        rw [hy, one_mul, mul_one]
      rw [h, le_bot_iff] at hle
      have h16 := hEbar.2
      rw [hle, card_bot] at h16
      norm_num at h16
    · have hD : CFSG.GorensteinWalter.HasDihedralSylowTwo ↥(twoResidualOf (⊤ : Subgroup (Bar H))) :=
        hasDihedralSylowTwo_of_isSylowOf hTbar (hdih.bar (hT.le.trans hLH))
      have hOK := CFSG.ABGDGroups.oddCore_eq_bot_of_normal hO (twoResidualOf (⊤ : Subgroup (Bar H)))
      have h2 : ∀ N : Subgroup ↥(twoResidualOf (⊤ : Subgroup (Bar H))), N.Normal → N.index ≠ 2 :=
        index_ne_two_of_twoResidualOf ⊤
      refine ⟨gw_inf_centralizer_eq_bot _ hOK h2 hD, fun h => ?_⟩
      have h3 := gw_inf_centralizer_ne_bot_of_isE16 _ hOK h2 hD hEbar
      rw [h, inf_bot_eq] at h3
      exact h3 rfl
  obtain ⟨R, hR⟩ := exists_isSylowOf 2 H
  have hRbar : IsSylowOf 2 (bar H R) ⊤ := by
    rw [← bar_self]
    exact isSylowOf_bar le_rfl hR
  obtain ⟨t, htR, ht2, htZ⟩ := exists_mem_center_of_centralizer hRbar key.1 key.2
  obtain ⟨⟨x, hxH⟩, hxR, rfl⟩ := htR
  have hxR' : x ∈ R := hxR
  have hx2 : orderOf x = 2 := by
    rw [← orderOf_mk_eq hR.le hR.isPGroup hxR']
    exact ht2
  exact ⟨x, isIsolatedIn_of_mk_mem_center hxH hx2 htZ⟩

end GW

section Factors

variable {Y : Type*} [Group Y]

theorem DDDecomp.subgroupOf {K T T₁ T₂ : Subgroup Y} (hd : DDDecomp T T₁ T₂) (hTK : T ≤ K) :
    DDDecomp (T.subgroupOf K) (T₁.subgroupOf K) (T₂.subgroupOf K) := by
  have h₁ : T₁ ≤ K := hd.le_left.trans hTK
  have h₂ : T₂ ≤ K := hd.le_right.trans hTK
  refine ⟨by rw [← subgroupOf_sup h₁ h₂, hd.sup_eq], ?_, ?_, ?_, ?_⟩
  · rw [show T₁.subgroupOf K ⊓ T₂.subgroupOf K = (T₁ ⊓ T₂).subgroupOf K from
      (comap_inf _ _ _).symm, hd.inf_eq, bot_subgroupOf]
  · intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (mem_centralizer_iff.1 (hd.commute hx) y hy)
  · obtain ⟨a, ha, ⟨e⟩⟩ := hd.dih₁
    exact ⟨a, ha, ⟨(subgroupOfEquivOfLe h₁).trans e⟩⟩
  · obtain ⟨a, ha, ⟨e⟩⟩ := hd.dih₂
    exact ⟨a, ha, ⟨(subgroupOfEquivOfLe h₂).trans e⟩⟩

theorem isDDShape_of_ddDecomp {T T₁ T₂ : Subgroup Y} (hd : DDDecomp T T₁ T₂) : IsDDShape T := by
  obtain ⟨μ, -⟩ := hd.exists_mulEquiv
  obtain ⟨a, ha, ⟨e₁⟩⟩ := hd.dih₁
  obtain ⟨b, hb, ⟨e₂⟩⟩ := hd.dih₂
  exact ⟨a, b, ha, by omega, by omega, ⟨μ.symm.trans (MulEquiv.prodCongr e₁ e₂)⟩⟩

end Factors

section Factors2

variable {G : Type} [Group G]

theorem exists_factors_of
    (hWalter : ∀ {X : Type} [Group X] [Finite X], CFSG.oddCore X = ⊥ →
      (∀ N : Subgroup X, N.Normal → N.index ≠ 2) → ∀ (T T₁ T₂ : Subgroup X),
      CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ → IsE16 T → IsKleinFour T₁ → IsKleinFour T₂ →
      T₁ ⊔ T₂ = T → T₁ ⊓ T₂ = ⊥ →
      (∀ x ∈ T, ∀ y ∈ T, orderOf x = 2 → IsConj x y → (x ∈ T₁ ↔ y ∈ T₁) ∧ (x ∈ T₂ ↔ y ∈ T₂)) →
      ∃ F₁ F₂ : Subgroup X, F₁.Normal ∧ F₂.Normal ∧ F₁ ⊓ F₂ = ⊥ ∧ Odd (F₁ ⊔ F₂).index ∧
        (IsL2OrA7 F₁ 5 ∨ F₁ = T₁) ∧ (IsL2OrA7 F₂ 5 ∨ F₂ = T₂) ∧
        CFSG.ABGLocalTools.IsSylowOf 2 T₁ F₁ ∧ CFSG.ABGLocalTools.IsSylowOf 2 T₂ F₂)
    (ih : ∀ (X : Type) [Group X] [Finite X], Nat.card X < Nat.card G → AStarHyp X →
      AStarConclusion X)
    {Y : Type} [Group Y] [Finite Y] (hO : CFSG.oddCore Y = ⊥) {T T₁ T₂ : Subgroup Y}
    (hT : IsSylowOf 2 T (twoResidualOf ⊤)) (hsup : T₁ ⊔ T₂ = T) (hinf : T₁ ⊓ T₂ = ⊥)
    (hcomm : T₂ ≤ centralizer (T₁ : Set Y)) (hd₁ : IsDih T₁) (hd₂ : IsDih T₂)
    (hfus : ∀ x ∈ T, ∀ y ∈ T, orderOf x = 2 →
      (∃ k ∈ twoResidualOf (⊤ : Subgroup Y), k * x * k⁻¹ = y) →
      (x ∈ T₁ ↔ y ∈ T₁) ∧ (x ∈ T₂ ↔ y ∈ T₂))
    (hcard : Nat.card (twoResidualOf (⊤ : Subgroup Y)) < Nat.card G) :
    ∃ F₁ F₂ : Subgroup Y, F₁ ≤ twoResidualOf ⊤ ∧ F₂ ≤ twoResidualOf ⊤ ∧
      (F₁.subgroupOf (twoResidualOf ⊤)).Normal ∧ (F₂.subgroupOf (twoResidualOf ⊤)).Normal ∧
      F₁ ⊓ F₂ = ⊥ ∧ Odd ((F₁ ⊔ F₂).relIndex (twoResidualOf ⊤)) ∧
      IsAStarFactor F₁ ∧ IsAStarFactor F₂ ∧ IsSylowOf 2 T₁ F₁ ∧ IsSylowOf 2 T₂ F₂ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (twoResidualOf (⊤ : Subgroup Y)).Normal := twoResidualOf_top_normal
  set K := twoResidualOf (⊤ : Subgroup Y) with hK
  have hTK : T ≤ K := hT.le
  have h₁K : T₁ ≤ K := (le_sup_left.trans hsup.le).trans hTK
  have h₂K : T₂ ≤ K := (le_sup_right.trans hsup.le).trans hTK
  have hOX : CFSG.oddCore K = ⊥ := CFSG.ABGDGroups.oddCore_eq_bot_of_normal hO K
  have h2X : ∀ N : Subgroup K, N.Normal → N.index ≠ 2 := index_ne_two_of_twoResidualOf ⊤
  have hT' : IsSylowOf 2 (T.subgroupOf K) ⊤ := by
    rw [← isSylowOf_map_subtype_iff K, map_subgroupOf_eq_of_le hTK, ← MonoidHom.range_eq_map,
      range_subtype]
    exact hT
  have hsup' : T₁.subgroupOf K ⊔ T₂.subgroupOf K = T.subgroupOf K := by
    rw [← subgroupOf_sup h₁K h₂K, hsup]
  have hinf' : T₁.subgroupOf K ⊓ T₂.subgroupOf K = ⊥ := by
    rw [show T₁.subgroupOf K ⊓ T₂.subgroupOf K = (T₁ ⊓ T₂).subgroupOf K from
      (comap_inf _ _ _).symm, hinf, bot_subgroupOf]
  have hfus' : ∀ x ∈ T.subgroupOf K, ∀ y ∈ T.subgroupOf K, orderOf x = 2 → IsConj x y →
      (x ∈ T₁.subgroupOf K ↔ y ∈ T₁.subgroupOf K) ∧ (x ∈ T₂.subgroupOf K ↔ y ∈ T₂.subgroupOf K) := by
    intro x hx y hy hx2 hxy
    obtain ⟨c, hc⟩ := isConj_iff.1 hxy
    exact hfus x hx y hy (by rwa [Subgroup.orderOf_coe]) ⟨c, c.2, by rw [← hc]; rfl⟩
  have hback : ∀ F : Subgroup K, (F.map K.subtype).subgroupOf K = F := fun F => by
    rw [subgroupOf, comap_map_eq_self_of_injective K.subtype_injective]
  have hfinish : ∀ F₁ F₂ : Subgroup K, F₁.Normal → F₂.Normal → F₁ ⊓ F₂ = ⊥ →
      Odd (F₁ ⊔ F₂).index → IsAStarFactor F₁ → IsAStarFactor F₂ →
      IsSylowOf 2 (T₁.subgroupOf K) F₁ → IsSylowOf 2 (T₂.subgroupOf K) F₂ →
      ∃ F₁ F₂ : Subgroup Y, F₁ ≤ K ∧ F₂ ≤ K ∧ (F₁.subgroupOf K).Normal ∧
        (F₂.subgroupOf K).Normal ∧ F₁ ⊓ F₂ = ⊥ ∧ Odd ((F₁ ⊔ F₂).relIndex K) ∧
        IsAStarFactor F₁ ∧ IsAStarFactor F₂ ∧ IsSylowOf 2 T₁ F₁ ∧ IsSylowOf 2 T₂ F₂ := by
    intro F₁ F₂ hn₁ hn₂ hi ho ha₁ ha₂ hs₁ hs₂
    refine ⟨F₁.map K.subtype, F₂.map K.subtype, map_subtype_le _, map_subtype_le _,
      by rw [hback]; exact hn₁, by rw [hback]; exact hn₂, ?_, ?_,
      isAStarFactor_of_mulEquiv (F₁.equivMapOfInjective _ K.subtype_injective).symm ha₁,
      isAStarFactor_of_mulEquiv (F₂.equivMapOfInjective _ K.subtype_injective).symm ha₂, ?_, ?_⟩
    · rw [← map_inf_eq _ _ _ K.subtype_injective, hi, Subgroup.map_bot]
    · rw [← Subgroup.map_sup, relIndex, hback]
      exact ho
    · rw [← map_subgroupOf_eq_of_le h₁K]
      exact (isSylowOf_map_subtype_iff K).2 hs₁
    · rw [← map_subgroupOf_eq_of_le h₂K]
      exact (isSylowOf_map_subtype_iff K).2 hs₂
  have hnonab : (DDDecomp T T₁ T₂ ∨ DDDecomp T T₂ T₁) →
      ∃ F₁ F₂ : Subgroup Y, F₁ ≤ K ∧ F₂ ≤ K ∧ (F₁.subgroupOf K).Normal ∧
        (F₂.subgroupOf K).Normal ∧ F₁ ⊓ F₂ = ⊥ ∧ Odd ((F₁ ⊔ F₂).relIndex K) ∧
        IsAStarFactor F₁ ∧ IsAStarFactor F₂ ∧ IsSylowOf 2 T₁ F₁ ∧ IsSylowOf 2 T₂ F₂ := by
    intro hdd
    have hdd' : DDDecomp (T.subgroupOf K) (T₁.subgroupOf K) (T₂.subgroupOf K) ∨
        DDDecomp (T.subgroupOf K) (T₂.subgroupOf K) (T₁.subgroupOf K) :=
      hdd.imp (fun h => h.subgroupOf hTK) (fun h => h.subgroupOf hTK)
    have hshape : IsDDShape (T.subgroupOf K) := by
      rcases hdd' with h | h
      exacts [isDDShape_of_ddDecomp h, isDDShape_of_ddDecomp h]
    obtain ⟨-, hT'p, hT'idx⟩ := isSylowOf_iff.1 hT'
    rw [relIndex_top_right] at hT'idx
    have hyp : AStarHyp K := ⟨hOX, h2X, ⟨hT'p.toSylow hT'idx, by
      rw [IsPGroup.toSylow_coe]
      exact hshape⟩⟩
    obtain ⟨L₁, L₂, hL₁, hL₂, hLi, hLo, hA₁, hA₂⟩ := ih K hcard hyp
    rcases alignment h2X L₁ L₂ _ _ _ hL₁ hL₂ hLi hLo hA₁ hA₂ hT' hdd' hfus' with
      ⟨hs₁, hs₂⟩ | ⟨hs₁, hs₂⟩
    · exact hfinish L₁ L₂ hL₁ hL₂ hLi hLo hA₁ hA₂ hs₁ hs₂
    · exact hfinish L₂ L₁ hL₂ hL₁ (by rw [inf_comm]; exact hLi) (by rw [sup_comm]; exact hLo)
        hA₂ hA₁ hs₁ hs₂
  rcases hd₁.isKleinFour_or_isDihNonab with hk₁ | hn₁
  · rcases hd₂.isKleinFour_or_isDihNonab with hk₂ | hn₂
    ·
      have hk₁' : IsKleinFour (T₁.subgroupOf K) := IsKleinFour.mk
        (by rw [Nat.card_congr (subgroupOfEquivOfLe h₁K).toEquiv]; exact hk₁.card_four)
        (by rw [Monoid.exponent_eq_of_mulEquiv (subgroupOfEquivOfLe h₁K)]; exact hk₁.exponent_two)
      have hk₂' : IsKleinFour (T₂.subgroupOf K) := IsKleinFour.mk
        (by rw [Nat.card_congr (subgroupOfEquivOfLe h₂K).toEquiv]; exact hk₂.card_four)
        (by rw [Monoid.exponent_eq_of_mulEquiv (subgroupOfEquivOfLe h₂K)]; exact hk₂.exponent_two)
      have hc' : ∀ x ∈ T₁.subgroupOf K, ∀ y ∈ T₂.subgroupOf K, x * y = y * x := fun x hx y hy =>
        Subtype.ext (mem_centralizer_iff.1 (hcomm hy) x hx)
      have hE : IsE16 (T.subgroupOf K) := by
        have hsq : ∀ x ∈ T.subgroupOf K, x * x = 1 := by
          rw [← hsup']
          intro x hx
          exact CFSG.CGT.Foote81L6.TStruct.mul_self_of_mem_sup (G := ↥K)
            (fun x hx => congrArg Subtype.val (IsKleinFour.mul_self (⟨x, hx⟩ : T₁.subgroupOf K)))
            (fun x hx => congrArg Subtype.val (IsKleinFour.mul_self (⟨x, hx⟩ : T₂.subgroupOf K)))
            hc' hx
        refine ⟨isElemAbelian_two_iff.2 hsq, ?_⟩
        rw [← hsup', CFSG.CGT.Foote81L6.card_sup_of_le_normalizer
          (CFSG.CGT.Foote81L6.le_normalizer_of_comm hc') hinf', hk₁'.card_four, hk₂'.card_four]
      obtain ⟨F₁, F₂, hn₁, hn₂, hi, ho, hF₁, hF₂, hs₁, hs₂⟩ :=
        hWalter hOX h2X _ _ _ hT' hE hk₁' hk₂' hsup' hinf' hfus'
      have hA : ∀ F P : Subgroup K, IsKleinFour P → (IsL2OrA7 F 5 ∨ F = P) → IsAStarFactor F := by
        rintro F P hP (h | rfl)
        · rcases h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr hP)
      exact hfinish F₁ F₂ hn₁ hn₂ hi ho (hA _ _ hk₁' hF₁) (hA _ _ hk₂' hF₂) hs₁ hs₂
    · exact hnonab (Or.inl ⟨hsup, hinf, hcomm, hd₁, hn₂⟩)
  · exact hnonab (Or.inr ⟨by rw [sup_comm]; exact hsup, by rw [inf_comm]; exact hinf,
      le_centralizer_iff.1 hcomm, hd₂, hn₁⟩)

end Factors2

namespace Sec4Setting

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G)

theorem isCyclic_or_isDih_of_inf_eq_bot {T : Subgroup G} (hTS : T ≤ 𝔖.S) {P : Subgroup G}
    (hP : P = 𝔖.S₁ ∨ P = 𝔖.S₂) (hTP : T ⊓ P = ⊥) : IsCyclic T ∨ IsDih T := by
  obtain ⟨D, hD, f, hf⟩ : ∃ D : Subgroup G, IsDih D ∧ ∃ f : ↥T →* ↥D, Function.Injective f := by
    rcases hP with rfl | rfl
    · obtain ⟨f, hf, -⟩ := 𝔖.decomp.exists_injective_of_inf_left_eq_bot hTS hTP
      exact ⟨_, 𝔖.decomp.isDih₂, f, hf⟩
    · obtain ⟨f, hf, -⟩ := 𝔖.decomp.exists_injective_of_inf_right_eq_bot hTS hTP
      exact ⟨_, 𝔖.decomp.dih₁, f, hf⟩
  let e : ↥T ≃* ↥(f.range.map D.subtype) :=
    (MonoidHom.ofInjective hf).trans (f.range.equivMapOfInjective _ D.subtype_injective)
  have hMD : f.range.map D.subtype ≤ D := map_subtype_le _
  by_cases h4 : ∃ V, IsFourIn D V ∧ V ≤ f.range.map D.subtype
  · obtain ⟨V, hV, hVM⟩ := h4
    obtain ⟨a, ha, ⟨e'⟩⟩ := hD.of_le hMD hV hVM
    exact Or.inr ⟨a, ha, ⟨e.trans e'⟩⟩
  · push Not at h4
    haveI := hD.isCyclic_of_le hMD h4
    exact Or.inl (isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective)

theorem prop_4_3_core_of
    (h315 : ∀ z₁ z₂ : G, (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
      (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) →
      (∃ H₁ : Subgroup (Bar (C z₁)), bar (C z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧ bar (C z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧
        H₁ ≤ centralizer (bar (C z₁) 𝔖.S₁ : Set (Bar (C z₁))) ∧
        bar (C z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧ IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C z₁))) 7) ∧
      (∃ K₁ : Subgroup (Bar (C z₂)), bar (C z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧ bar (C z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧
        K₁ ≤ centralizer (bar (C z₂) 𝔖.S₂ : Set (Bar (C z₂))) ∧
        bar (C z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
        (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C z₂) 𝔖.S₁)))
    (h317 : ∀ z₁ z₂ : G, (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
      (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) → HasNormalTwoComplement (C (z₁ * z₂)))
    (hWalter : ∀ {X : Type} [Group X] [Finite X], CFSG.oddCore X = ⊥ →
      (∀ N : Subgroup X, N.Normal → N.index ≠ 2) → ∀ (T T₁ T₂ : Subgroup X),
      CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ → IsE16 T → IsKleinFour T₁ → IsKleinFour T₂ →
      T₁ ⊔ T₂ = T → T₁ ⊓ T₂ = ⊥ →
      (∀ x ∈ T, ∀ y ∈ T, orderOf x = 2 → IsConj x y → (x ∈ T₁ ↔ y ∈ T₁) ∧ (x ∈ T₂ ↔ y ∈ T₂)) →
      ∃ F₁ F₂ : Subgroup X, F₁.Normal ∧ F₂.Normal ∧ F₁ ⊓ F₂ = ⊥ ∧ Odd (F₁ ⊔ F₂).index ∧
        (IsL2OrA7 F₁ 5 ∨ F₁ = T₁) ∧ (IsL2OrA7 F₂ 5 ∨ F₂ = T₂) ∧
        CFSG.ABGLocalTools.IsSylowOf 2 T₁ F₁ ∧ CFSG.ABGLocalTools.IsSylowOf 2 T₂ F₂)
    {H : Subgroup G} (hH : H ≠ ⊤) {E : Subgroup G} (hEH : E ≤ H) (hE : IsE16 E)
    (hiso : ∀ t, ¬ IsIsolatedIn H t) {T : Subgroup G} (hT : IsSylowOf 2 T (twoResidualOf H))
    (hTS : T ≤ 𝔖.S) :
    (∃ V, IsFourIn 𝔖.S₁ V ∧ V ≤ T) ∧ (∃ V, IsFourIn 𝔖.S₂ V ∧ V ≤ T) ∧
      T = (T ⊓ 𝔖.S₁) ⊔ (T ⊓ 𝔖.S₂) ∧
      ∃ F₁ F₂ : Subgroup (Bar H), F₁ ≤ twoResidualOf ⊤ ∧ F₂ ≤ twoResidualOf ⊤ ∧
        (F₁.subgroupOf (twoResidualOf ⊤)).Normal ∧ (F₂.subgroupOf (twoResidualOf ⊤)).Normal ∧
        F₁ ⊓ F₂ = ⊥ ∧ Odd ((F₁ ⊔ F₂).relIndex (twoResidualOf ⊤)) ∧
        IsAStarFactor F₁ ∧ IsAStarFactor F₂ ∧
        IsSylowOf 2 (bar H (T ⊓ 𝔖.S₁)) F₁ ∧ IsSylowOf 2 (bar H (T ⊓ 𝔖.S₂)) F₂ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := 𝔖.decomp
  have hLH : twoResidualOf H ≤ H := twoResidualOf_le_self H
  have hTH : T ≤ H := hT.le.trans hLH
  have hTp : IsPGroup 2 T := hT.isPGroup
  have hfour : ∀ P : Subgroup G, P = 𝔖.S₁ ∨ P = 𝔖.S₂ → ∃ V, IsFourIn P V ∧ V ≤ T := by
    intro P hP
    have hPd : IsDih P := by
      rcases hP with rfl | rfl
      exacts [hd.dih₁, hd.isDih₂]
    by_contra hno
    push Not at hno
    by_cases hbot : T ⊓ P = ⊥
    · obtain ⟨t, ht⟩ := exists_isIsolatedIn_of_isCyclic_or_isDih hEH hE hT
        (𝔖.isCyclic_or_isDih_of_inf_eq_bot hTS hP hbot)
      exact hiso t ht
    · obtain ⟨z, hz, hz2, huniq⟩ := hPd.exists_unique_involution inf_le_right hbot
        fun V hV hVT => hno V hV (hVT.trans inf_le_left)
      obtain ⟨hzT, hzP⟩ := mem_inf.1 hz
      have hzK := 𝔖.isIsolatedIn_of_unique hT hTS le_normalizer hP
        (mem_inf.2 ⟨mem_inf.2 ⟨hzT, hT.le hzT⟩, hzP⟩) hz2 fun t ht ht2 =>
          huniq t (mem_inf.2 ⟨(mem_inf.1 (mem_inf.1 ht).1).1, (mem_inf.1 ht).2⟩) ht2
      obtain ⟨t, ht⟩ := exists_isIsolatedIn_of_isIsolatedIn_twoResidualOf hzK
      exact hiso t ht
  obtain ⟨V₁, hV₁, hV₁T⟩ := hfour _ (Or.inl rfl)
  obtain ⟨V₂, hV₂, hV₂T⟩ := hfour _ (Or.inr rfl)
  have hsplit : T = (T ⊓ 𝔖.S₁) ⊔ (T ⊓ 𝔖.S₂) :=
    𝔖.eq_inf_sup_inf_of_isSylowOf_of h315 h317 (index_ne_two_of_twoResidualOf H) hT hTS hV₁
      hV₁T hV₂ hV₂T
  refine ⟨⟨V₁, hV₁, hV₁T⟩, ⟨V₂, hV₂, hV₂T⟩, hsplit, ?_⟩
  have h₁T : T ⊓ 𝔖.S₁ ≤ T := inf_le_left
  have h₂T : T ⊓ 𝔖.S₂ ≤ T := inf_le_left
  have hTbar : IsSylowOf 2 (bar H T) (twoResidualOf (⊤ : Subgroup (Bar H))) := by
    have h := isSylowOf_bar hLH hT
    rwa [bar_twoResidualOf] at h
  have hsupb : bar H (T ⊓ 𝔖.S₁) ⊔ bar H (T ⊓ 𝔖.S₂) = bar H T := by
    rw [← bar_sup (h₁T.trans hTH) (h₂T.trans hTH), ← hsplit]
  have hinfb : bar H (T ⊓ 𝔖.S₁) ⊓ bar H (T ⊓ 𝔖.S₂) = ⊥ := by
    rw [← bar_inf_of_isPGroup h₁T h₂T hTp hTH]
    have h : (T ⊓ 𝔖.S₁) ⊓ (T ⊓ 𝔖.S₂) = ⊥ := eq_bot_iff.2 fun x hx => by
      have h' : x ∈ 𝔖.S₁ ⊓ 𝔖.S₂ :=
        mem_inf.2 ⟨(mem_inf.1 (mem_inf.1 hx).1).2, (mem_inf.1 (mem_inf.1 hx).2).2⟩
      rwa [hd.inf_eq] at h'
    rw [h, bar_bot]
  have hcommb : bar H (T ⊓ 𝔖.S₂) ≤ centralizer (bar H (T ⊓ 𝔖.S₁) : Set (Bar H)) :=
    bar_le_centralizer fun x hx => mem_centralizer_iff.2 fun y hy =>
      hd.comm (mem_inf.1 hy).2 (mem_inf.1 hx).2
  have hd₁ : IsDih (bar H (T ⊓ 𝔖.S₁)) :=
    (hd.dih₁.of_le inf_le_right hV₁ (le_inf hV₁T hV₁.1)).bar (h₁T.trans hTH)
  have hd₂ : IsDih (bar H (T ⊓ 𝔖.S₂)) :=
    (hd.isDih₂.of_le inf_le_right hV₂ (le_inf hV₂T hV₂.1)).bar (h₂T.trans hTH)
  have hfus : ∀ x ∈ bar H T, ∀ y ∈ bar H T, orderOf x = 2 →
      (∃ k ∈ twoResidualOf (⊤ : Subgroup (Bar H)), k * x * k⁻¹ = y) →
      (x ∈ bar H (T ⊓ 𝔖.S₁) ↔ y ∈ bar H (T ⊓ 𝔖.S₁)) ∧
        (x ∈ bar H (T ⊓ 𝔖.S₂) ↔ y ∈ bar H (T ⊓ 𝔖.S₂)) := by
    rintro _ ⟨⟨x, hxH⟩, hx, rfl⟩ _ ⟨⟨y, hyH⟩, hy, rfl⟩ hx2 ⟨k, -, hk⟩
    have hx' : x ∈ T := hx
    have hy' : y ∈ T := hy
    have hx2' : orderOf x = 2 := by
      rw [← orderOf_mk_eq hTH hTp hx']
      exact hx2
    have hsep := 𝔖.separate_of_mk_isConj hTH hTS hx' hy' hx2' (isConj_iff.2 ⟨k, hk⟩)
    have key : ∀ P : Subgroup G, (x ∈ P ↔ y ∈ P) →
        ((QuotientGroup.mk ⟨x, hxH⟩ : Bar H) ∈ bar H (T ⊓ P) ↔
          (QuotientGroup.mk ⟨y, hyH⟩ : Bar H) ∈ bar H (T ⊓ P)) := by
      intro P hxy
      rw [mk_mem_bar_iff inf_le_left hTp hxH hx', mk_mem_bar_iff inf_le_left hTp hyH hy', mem_inf,
        mem_inf]
      exact ⟨fun h => ⟨hy', hxy.1 h.2⟩, fun h => ⟨hx', hxy.2 h.2⟩⟩
    exact ⟨key _ hsep.1, key _ hsep.2⟩
  have hcard : Nat.card (twoResidualOf (⊤ : Subgroup (Bar H))) < Nat.card G := by
    calc Nat.card (twoResidualOf (⊤ : Subgroup (Bar H))) ≤ Nat.card (Bar H) :=
          card_le_card_group _
      _ ≤ Nat.card H := Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
      _ < Nat.card G := by
        have h := card_lt_of_lt (lt_top_iff_ne_top.2 hH)
        rwa [card_top] at h
  exact exists_factors_of hWalter 𝔖.mc.ih (oddCore_quotient_oddCore_eq_bot H) hTbar hsupb
    hinfb hcommb hd₁ hd₂ hfus hcard

end Sec4Setting

end CFSG.GH72
