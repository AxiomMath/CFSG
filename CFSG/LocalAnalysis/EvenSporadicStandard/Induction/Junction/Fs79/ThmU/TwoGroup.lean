module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.ThmU.Basic
public import CFSG.GH74.GLS.C3.Layer1.St1RigTwoGrp
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.EvenSporadicStandard.Induction.ThmU

open Subgroup CFSG.EvenSporadicStandard.Induction
open scoped commutatorElement

variable {G : Type} [Group G]

theorem isPGroup_two_sup_zpowers {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : a * b = b * a) : IsPGroup 2 ↥(zpowers a ⊔ zpowers b) := by
  have hTa : IsPGroup 2 ↥(zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha]; norm_num)
  have hTb : IsPGroup 2 ↥(zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb]; norm_num)
  have hNorm : zpowers b ≤ Subgroup.normalizer (zpowers a : Subgroup G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer ((zpowers a : Subgroup G) : Set G))
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    have hle : (zpowers a : Subgroup G) ≤ Subgroup.centralizer ({b} : Set G) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.2 hab
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)
  exact hTa.to_sup_of_normal_left' hTb hNorm

theorem exists_max_bad [Finite G] {B T : Subgroup G} (h : ∃ y ∈ T, BadInv B y) :
    ∃ y ∈ T, BadInv B y ∧ ∀ y' ∈ T, BadInv B y' →
      Nat.card ↥(T ⊓ centralizer ({y'} : Set G)) ≤
        Nat.card ↥(T ⊓ centralizer ({y} : Set G)) := by
  obtain ⟨y₀, hy₀T, hy₀⟩ := h
  obtain ⟨y, hy, hmax⟩ := Set.exists_max_image {y | y ∈ T ∧ BadInv B y}
    (fun y => Nat.card ↥(T ⊓ centralizer ({y} : Set G))) (Set.toFinite _) ⟨y₀, hy₀T, hy₀⟩
  exact ⟨y, hy.1, hy.2, fun y' hy'T hy' => hmax y' ⟨hy'T, hy'⟩⟩

theorem exists_central_involution [Finite G] {T : Subgroup G} (hT : IsPGroup 2 T) {u : G}
    (hu : u ∈ T) (hu2 : orderOf u = 2) :
    ∃ z ∈ T, orderOf z = 2 ∧ ∀ t ∈ T, z * t = t * z := by
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu2
    omega
  haveI : Nontrivial ↥T := ⟨⟨u, hu⟩, 1, fun h => hu1 (Subtype.ext_iff.mp h)⟩
  obtain ⟨w, hw2, hwc⟩ :=
    CFSG.GH74.GLS.C3.Layer1.PumpRigid.exists_central_involution_of_isPGroup_two (P := ↥T) hT
  refine ⟨(w : G), w.2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact hw2
  · intro t ht
    exact congrArg Subtype.val (hwc ⟨t, ht⟩).eq

theorem exists_mem_normalizer_sq_mem [Finite G] {T P : Subgroup G} (hT : IsPGroup 2 T)
    (hPT : P ≤ T) (hne : P ≠ T) :
    ∃ g ∈ T, g ∈ normalizer (P : Set G) ∧ g ∉ P ∧ g * g ∈ P := by
  classical
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  haveI : Group.IsNilpotent ↥T := IsPGroup.isNilpotent hT
  have hnc : NormalizerCondition ↥T := Group.normalizerCondition_of_isNilpotent
  set P' : Subgroup ↥T := P.subgroupOf T with hP'
  have hP'ne : P' ≠ ⊤ := by
    rw [hP']
    intro h
    exact hne (le_antisymm hPT (Subgroup.subgroupOf_eq_top.mp h))
  have hP'lt : P' < ⊤ := lt_of_le_of_ne le_top hP'ne
  have hNlt : P' < Subgroup.normalizer P' := hnc P' hP'lt
  obtain ⟨g', hg'N, hg'P⟩ : ∃ x : ↥T, x ∈ Subgroup.normalizer P' ∧ x ∉ P' := by
    by_contra hcon
    push Not at hcon
    exact hNlt.2 hcon
  obtain ⟨m, hm⟩ := hT.exists_orderOf_eq_pow g'
  have hex : ∃ k : ℕ, g' ^ 2 ^ k ∈ P' :=
    ⟨m, by rw [← hm, pow_orderOf_eq_one]; exact P'.one_mem⟩
  set k := Nat.find hex with hk
  have hkP : g' ^ 2 ^ k ∈ P' := by
    rw [hk]
    exact Nat.find_spec hex
  have hkmin : ∀ j < k, g' ^ 2 ^ j ∉ P' := by
    intro j hj
    rw [hk] at hj
    exact Nat.find_min hex hj
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · exfalso
      rw [h0, pow_zero, pow_one] at hkP
      exact hg'P hkP
    · exact hpos
  set h : ↥T := g' ^ 2 ^ (k - 1) with hh
  have hN : h ∈ Subgroup.normalizer P' := by
    rw [hh]
    exact pow_mem hg'N _
  have hPn : h ∉ P' := by
    intro hh'
    have hlt : k - 1 < k := by omega
    exact hkmin (k - 1) hlt (hh ▸ hh')
  have hsq : h * h ∈ P' := by
    have harith : 2 ^ (k - 1) * 2 = 2 ^ k := by
      rw [← pow_succ]
      congr 1
      omega
    have hh2 : h * h = g' ^ 2 ^ k := by
      rw [hh, ← pow_two, ← pow_mul, harith]
    rw [hh2]
    exact hkP
  refine ⟨(h : G), h.2, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxT : x ∈ T := hPT hx
      have hx' : (⟨x, hxT⟩ : ↥T) ∈ P' := Subgroup.mem_subgroupOf.mpr hx
      exact Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hN ⟨x, hxT⟩).mp hx')
    · intro hx
      have hxT : x ∈ T := by
        have hxeq : x = (h : G)⁻¹ * ((h : G) * x * (h : G)⁻¹) * (h : G) := by group
        rw [hxeq]
        exact T.mul_mem (T.mul_mem (T.inv_mem h.2) (hPT hx)) h.2
      have hmem' : h * ⟨x, hxT⟩ * h⁻¹ ∈ P' := by
        rw [Subgroup.mem_subgroupOf]
        simpa using hx
      exact Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hN ⟨x, hxT⟩).mpr hmem')
  · intro hx
    exact hPn (Subgroup.mem_subgroupOf.mpr hx)
  · simpa using Subgroup.mem_subgroupOf.mp hsq

theorem four_le_card_of_involutions [Finite G] {P : Subgroup G} {y z : G} (hy : orderOf y = 2)
    (hz : orderOf z = 2) (hyz : y ≠ z) (hcomm : y * z = z * y) (hyP : y ∈ P) (hzP : z ∈ P) :
    4 ≤ Nat.card P := by
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy
    omega
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    omega
  have hyz1 : y * z ≠ 1 := by
    intro h
    have hyz' : y = z := by
      calc y = y * 1 := (mul_one y).symm
        _ = y * (z * z) := by rw [mul_self_eq_one_of_orderOf hz]
        _ = (y * z) * z := by rw [mul_assoc]
        _ = 1 * z := by rw [h]
        _ = z := one_mul z
    exact hyz hyz'
  have h1 : y * z ∉ ({y, z, (1 : G)} : Set G) := mul_notMem_of_orderOf_eq_two hy hz hyz
  have h2 : y ∉ ({z, (1 : G)} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hyz, hy1⟩
  have h3 : z ∉ ({(1 : G)} : Set G) := by simpa using hz1
  have hcard : ({y * z, y, z, (1 : G)} : Set G).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
      Set.ncard_insert_of_notMem h3]
    norm_num
  have hsub : ({y * z, y, z, (1 : G)} : Set G) ⊆ (P : Set G) := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact P.mul_mem hyP hzP
    · exact hyP
    · exact hzP
    · exact P.one_mem
  have hle : 4 ≤ (P : Set G).ncard := hcard ▸ Set.ncard_le_ncard hsub
  rwa [← Nat.card_coe_set_eq] at hle

theorem eight_le_card [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P) (h4 : 4 ≤ Nat.card P)
    (hne : Nat.card P ≠ 4) : 8 ≤ Nat.card P := by
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hk3 : 3 ≤ k := by
    by_contra h
    have hk2 : k ≤ 2 := by omega
    interval_cases k
    · rw [hk] at h4
      norm_num at h4
    · rw [hk] at h4
      norm_num at h4
    · rw [hk] at hne
      norm_num at hne
  rw [hk]
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3

theorem exists_involution_inf [Finite G] {P R R' : Subgroup G} (hP : IsPGroup 2 P)
    (h8 : 8 ≤ Nat.card P) (hR : R ≤ P) (hR' : R' ≤ P) (hi : R.relIndex P = 2)
    (hi' : R'.relIndex P = 2) : ∃ w ∈ R ⊓ R', orderOf w = 2 := by
  set S : Subgroup G := R ⊓ R' with hS
  have hSP : S ≤ P := by
    rw [hS]
    exact inf_le_left.trans hR
  have hidx : S.relIndex P ≤ 4 := by
    have h := Subgroup.relIndex_inf_le (H := R) (K := R') (L := P)
    rw [← hS, hi, hi'] at h
    omega
  have hcardP : Nat.card P = S.relIndex P * Nat.card S := by
    have h := Subgroup.relIndex_mul_card (H := S) (K := P)
    rw [inf_eq_left.mpr hSP] at h
    exact h.symm
  have hScard_ne1 : Nat.card S ≠ 1 := by
    intro h1
    have hrel : S.relIndex P = Nat.card P := by
      have h := hcardP
      rw [h1, mul_one] at h
      exact h.symm
    omega
  have h2dvd : 2 ∣ Nat.card S := by
    rcases (hP.to_le hSP).card_eq_or_dvd with h | h
    · exact absurd h hScard_ne1
    · exact h
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥S) 2 (by simpa using h2dvd)
  exact ⟨(w : G), w.2, by rwa [Subgroup.orderOf_coe]⟩

theorem exists_conj_in_center [Finite G] {T : Subgroup G} (hT : IsPGroup 2 T) {y : G}
    (hyT : y ∈ T) (hy : orderOf y = 2) (hne : ∃ t ∈ T, y * t ≠ t * y) :
    ∃ g ∈ T, g ∉ T ⊓ centralizer ({y} : Set G) ∧
      g * y * g⁻¹ ∈ T ⊓ centralizer ({y} : Set G) ∧
      (∀ p ∈ T ⊓ centralizer ({y} : Set G), p * (g * y * g⁻¹) = (g * y * g⁻¹) * p) ∧
      orderOf (y * (g * y * g⁻¹)) = 2 ∧
      Nat.card ↥(T ⊓ centralizer ({y} : Set G)) <
        Nat.card ↥(T ⊓ centralizer ({y * (g * y * g⁻¹)} : Set G)) := by
  set P : Subgroup G := T ⊓ centralizer ({y} : Set G) with hP
  have hyP : y ∈ P := by
    rw [hP]
    exact ⟨hyT, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hPne : P ≠ T := by
    intro hPT
    obtain ⟨t, htT, hyt⟩ := hne
    have htP : t ∈ P := by rw [hPT]; exact htT
    exact hyt (Subgroup.mem_centralizer_singleton_iff.mp htP.2).symm
  obtain ⟨g, hgT, hgN, hgP, hggP⟩ := exists_mem_normalizer_sq_mem hT inf_le_left hPne
  have hy'P : g * y * g⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hgN y).mp hyP
  have hy'2 : orderOf (g * y * g⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hy]
  have hcent : ∀ p ∈ P, p * (g * y * g⁻¹) = (g * y * g⁻¹) * p := by
    intro p hp
    have hginv : g⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
      (Subgroup.normalizer (P : Set G)).inv_mem hgN
    have hp'P : g⁻¹ * p * g ∈ P := by
      have h := (Subgroup.mem_normalizer_iff.mp hginv p).mp hp
      simpa using h
    have hp'c : (g⁻¹ * p * g) * y = y * (g⁻¹ * p * g) :=
      Subgroup.mem_centralizer_singleton_iff.mp hp'P.2
    calc p * (g * y * g⁻¹) = g * ((g⁻¹ * p * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * p * g)) * g⁻¹ := by rw [hp'c]
      _ = (g * y * g⁻¹) * p := by group
  have hord : orderOf (y * (g * y * g⁻¹)) = 2 := by
    have hy'c : (g * y * g⁻¹) * y = y * (g * y * g⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.mp hy'P.2
    have hcomm : Commute y (g * y * g⁻¹) := hy'c.symm
    refine orderOf_eq_prime ?_ ?_
    · rw [hcomm.mul_pow, pow_two, pow_two, mul_self_eq_one_of_orderOf hy,
        mul_self_eq_one_of_orderOf hy'2, mul_one]
    · intro h1
      have hy'eq : g * y * g⁻¹ = y := by
        rw [eq_inv_of_mul_eq_one_right h1, inv_eq_self_of_orderOf_eq_two hy]
      have hgy : g * y = y * g := by
        calc g * y = (g * y * g⁻¹) * g := by group
          _ = y * g := by rw [hy'eq]
      exact hgP ⟨hgT, Subgroup.mem_centralizer_singleton_iff.mpr hgy⟩
  set Q : Subgroup G := T ⊓ centralizer ({y * (g * y * g⁻¹)} : Set G) with hQ
  have hPQ : P ≤ Q := by
    intro p hp
    have hpy : Commute p y := Subgroup.mem_centralizer_singleton_iff.mp hp.2
    have hpy' : Commute p (g * y * g⁻¹) := hcent p hp
    exact ⟨hp.1, Subgroup.mem_centralizer_singleton_iff.mpr (hpy.mul_right hpy').eq⟩
  have hgQ : g ∈ Q := by
    have hgg2 : (g * g) * y = y * (g * g) :=
      Subgroup.mem_centralizer_singleton_iff.mp hggP.2
    have hy'conj : g * (g * y * g⁻¹) * g⁻¹ = y := by
      rw [show g * (g * y * g⁻¹) * g⁻¹ = (g * g) * y * (g * g)⁻¹ by group, hgg2]
      group
    refine ⟨hgT, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc g * (y * (g * y * g⁻¹))
        = (g * (y * (g * y * g⁻¹)) * g⁻¹) * g := by group
      _ = ((g * y * g⁻¹) * (g * (g * y * g⁻¹) * g⁻¹)) * g := by
            rw [show g * (y * (g * y * g⁻¹)) * g⁻¹
                = (g * y * g⁻¹) * (g * (g * y * g⁻¹) * g⁻¹) by group]
      _ = ((g * y * g⁻¹) * y) * g := by rw [hy'conj]
      _ = (y * (g * y * g⁻¹)) * g := by
            rw [Subgroup.mem_centralizer_singleton_iff.mp hy'P.2]
  have hPQlt : P < Q := by
    refine lt_of_le_of_ne hPQ ?_
    intro hEQ
    have hmem : g ∈ P := hEQ.symm ▸ hgQ
    exact hgP hmem
  have hlt : Nat.card P < Nat.card Q := Subgroup.card_lt_of_lt hPQlt
  exact ⟨g, hgT, hgP, hy'P, hcent, hord, hlt⟩

theorem pRank_le_two_of_centralizer_card_four' [Finite G] {T : Subgroup G} (hT : IsPGroup 2 T)
    {y : G} (hyT : y ∈ T) (hy : orderOf y = 2)
    (hc : Nat.card ↥(T ⊓ centralizer ({y} : Set G)) = 4) : CFSG.Open.pRank 2 T ≤ 2 := by
  have h := CFSG.GH74.GLS.C3.Layer1.PumpRigid.pRank_le_two_of_centralizer_card_four hT hyT hy hc
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top 2 ↥T,
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup T] at h
  exact h

end CFSG.EvenSporadicStandard.Induction.ThmU
