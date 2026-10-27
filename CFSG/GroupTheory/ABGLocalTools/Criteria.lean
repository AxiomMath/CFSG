module

public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.GroupTheory.ABGLocalTools.ZJFactorization
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
import CFSG.FeitThompson.OddOrderTheorem

public section

open Subgroup
open scoped Pointwise

namespace CFSG.ABGLocalTools

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]

theorem mem_centralizer_of_mem_sup_of_coprime {M Q : Subgroup H} [hMn : M.Normal]
    (hM : Nat.Coprime p (Nat.card M)) (hQ : IsPGroup p Q) {t : H}
    (htL : t ∈ centralizer (Q : Set H) ⊔ M) (htQ : t ∈ normalizer (Q : Set H)) :
    t ∈ centralizer (Q : Set H) := by
  rw [Subgroup.mem_sup_of_normal_right] at htL
  obtain ⟨c, hc, m, hm, rfl⟩ := htL
  have hcQ : c ∈ normalizer (Q : Set H) := Subgroup.centralizer_le_normalizer _ hc
  have hmQ : m ∈ normalizer (Q : Set H) := by
    have : m = c⁻¹ * (c * m) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hcQ) htQ
  have hQM : Q ⊓ M = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
    apply (Subgroup.disjoint_of_coprime_natCard _).eq_bot
    rw [hk]
    exact Nat.Coprime.pow_left k hM
  have hmC : m ∈ centralizer (Q : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 : m * x * m⁻¹ * x⁻¹ ∈ Q := Q.mul_mem
      ((Subgroup.mem_normalizer_iff.mp hmQ x).mp hx) (Q.inv_mem hx)
    have h2 : m * x * m⁻¹ * x⁻¹ ∈ M := by
      have : x * m⁻¹ * x⁻¹ ∈ M := hMn.conj_mem _ (M.inv_mem hm) x
      have := M.mul_mem hm this
      simpa [mul_assoc] using this
    have h3 : m * x * m⁻¹ * x⁻¹ = 1 := by
      have : m * x * m⁻¹ * x⁻¹ ∈ Q ⊓ M := ⟨h1, h2⟩
      rwa [hQM, Subgroup.mem_bot] at this
    calc x * m = (m * x * m⁻¹ * x⁻¹)⁻¹ * (m * x) := by group
      _ = m * x := by rw [h3, inv_one, one_mul]
  exact Subgroup.mul_mem _ hc hmC

theorem centralizer_sup_eq_comap {M Q : Subgroup H} [hMn : M.Normal]
    (hM : Nat.Coprime p (Nat.card M)) (hQ : IsPGroup p Q) :
    centralizer (Q : Set H) ⊔ M =
      (centralizer ((Q.map (QuotientGroup.mk' M) : Subgroup (H ⧸ M)) : Set (H ⧸ M))).comap
        (QuotientGroup.mk' M) := by
  have : Fact (IsPGroup p Q) := ⟨hQ⟩
  have hcent := centralizer_map_quotient_eq_map_centralizer p Q M hMn hM
  rw [hcent, Subgroup.comap_map_eq, QuotientGroup.ker_mk']

theorem centralizer_sup_normal_of_sup_eq {M E Q : Subgroup H} [hMn : M.Normal] [hEn : E.Normal]
    (hM : Nat.Coprime p (Nat.card M)) (hQ : IsPGroup p Q) (hMQ : M ⊔ Q = E) :
    (centralizer (Q : Set H) ⊔ M).Normal := by
  set q : H →* H ⧸ M := QuotientGroup.mk' M with hq
  have : Fact (IsPGroup p Q) := ⟨hQ⟩
  have hcent := centralizer_map_quotient_eq_map_centralizer p Q M hMn hM
  have hL : centralizer (Q : Set H) ⊔ M =
      (centralizer ((Q.map q : Subgroup (H ⧸ M)) : Set (H ⧸ M))).comap q := by
    rw [hcent, Subgroup.comap_map_eq, hq, QuotientGroup.ker_mk']
  have hQE : Q.map q = E.map q := by
    rw [← hMQ, Subgroup.map_sup, hq, QuotientGroup.map_mk'_self, bot_sup_eq]
  rw [hL, hQE]
  have : (E.map q).Normal := Subgroup.Normal.map hEn q (QuotientGroup.mk'_surjective M)
  infer_instance

theorem centralizer_sup_pPrimeCore_normal {P : Subgroup H} (hP : IsSylowOf p P (Op_p'p p H)) :
    (centralizer (P : Set H) ⊔ pPrimeCore p H).Normal :=
  centralizer_sup_normal_of_sup_eq pPrimeCore_coprime_card hP.isPGroup
    ((sup_eq_Op_p'p_iff_isSylowOf hP.isPGroup).mpr hP)

theorem mem_centralizer_of_mem_sup_pPrimeCore {P : Subgroup H}
    (hP : IsSylowOf p P (Op_p'p p H)) {t : H}
    (htL : t ∈ centralizer (P : Set H) ⊔ pPrimeCore p H) (htP : t ∈ normalizer (P : Set H)) :
    t ∈ centralizer (P : Set H) :=
  mem_centralizer_of_mem_sup_of_coprime pPrimeCore_coprime_card hP.isPGroup htL htP

theorem exists_central_involution_of_even {S : Sylow 2 H} {L : Subgroup H} [L.Normal]
    (hL : 2 ∣ Nat.card L) :
    ∃ w ∈ center S, w ≠ 1 ∧ w ^ 2 = 1 ∧ (w : H) ∈ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSsyl : IsSylowOf 2 (S : Subgroup H) ⊤ := by
    rw [isSylowOf_iff, Subgroup.relIndex_top_right]
    exact ⟨le_top, S.isPGroup', S.not_dvd_index⟩
  have hSL : IsSylowOf 2 ((S : Subgroup H) ⊓ L) L :=
    hSsyl.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top])
  have hSLne : (S : Subgroup H) ⊓ L ≠ ⊥ := by
    intro hbot
    have hcard := hSL.card_eq
    rw [hbot, Subgroup.card_bot] at hcard
    have h2 : 2 ^ 1 ∣ Nat.card L := by rwa [pow_one]
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne'] at h2
    have : (2 : ℕ) ^ (Nat.card L).factorization 2 ≠ 1 :=
      (Nat.one_lt_pow (by omega) (by norm_num)).ne'
    exact this hcard.symm
  set SL : Subgroup S := L.subgroupOf S with hSLdef
  have hSLnormal : SL.Normal := Subgroup.normal_subgroupOf
  have hSLne' : SL ≠ ⊥ := by
    intro hbot
    apply hSLne
    rw [eq_bot_iff]
    intro x ⟨hxS, hxL⟩
    have : (⟨x, hxS⟩ : S) ∈ SL := hxL
    rw [hbot, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)
  have hnil : Group.IsNilpotent S := S.isPGroup'.isNilpotent
  have hW := Group.IsNilpotent.inf_center_ne_bot_of_normal hSLne'
  set W : Subgroup S := SL ⊓ center S with hWdef
  have hWp : IsPGroup 2 W := S.isPGroup'.to_subgroup W
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hWp
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact hW ((Subgroup.card_eq_one).mp hn)
  have h2W : 2 ∣ Nat.card W := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := W) 2 h2W
  refine ⟨w, w.2.2, ?_, ?_, w.2.1⟩
  · intro h1
    have : orderOf (w : S) = 2 := by rw [Subgroup.orderOf_coe, hw]
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  · have hord : orderOf (w : S) = 2 := by rw [Subgroup.orderOf_coe, hw]
    have h := pow_orderOf_eq_one (w : S)
    rw [hord] at h
    exact h

theorem pConstrainedWithin_oddCore_four_group_criteria (hp : p ≠ 2)
    (T : Subgroup H) [IsKleinFour T] (S : Sylow 2 H) (_hTS : T ≤ S)
    (hZT : ∀ z ∈ center S, (z : S) ^ 2 = 1 → ((z : S) : H) ∈ T)
    (htrans : ∀ t ∈ T, ∀ t' ∈ T, t ≠ 1 → t' ≠ 1 →
      ∃ h ∈ normalizer (T : Set H), h * t * h⁻¹ = t')
    (hcore : pPrimeCore p H ≤ oddCore H) {P : Subgroup H}
    (hP : IsSylowOf p P ((Op_p'p p (oddCore H)).map (oddCore H).subtype))
    (hTP : T ≤ normalizer (P : Set H)) :
    (PConstrainedWithin p H (oddCore H) → T ⊓ centralizer (P : Set H) = ⊥) ∧
      (¬ PConstrainedWithin p H (oddCore H) → T ≤ centralizer (P : Set H)) := by
  have hEO : Op_p'p p H ≤ oddCore H := Op_p'p_le_oddCore hp hcore
  have hE : (Op_p'p p (oddCore H)).map (oddCore H).subtype = Op_p'p p H := by
    rw [Op_p'p_map_subtype_eq_inf (oddCore_normal H), inf_eq_right.mpr hEO]
  rw [hE] at hP
  constructor
  · rintro ⟨-, hcon⟩
    have hC : centralizer (P : Set H) ≤ Op_p'p p H := hcon P hP
    have h1 : Nat.card (T ⊓ centralizer (P : Set H) : Subgroup H) ∣ 4 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : T ⊓ centralizer (P : Set H) ≤ T)
      rwa [IsKleinFour.card_four (G := T)] at this
    have h2 : Nat.card (T ⊓ centralizer (P : Set H) : Subgroup H) ∣ Nat.card (oddCore H) :=
      Subgroup.card_dvd_of_le (inf_le_right.trans (hC.trans hEO))
    have hcop : Nat.Coprime 4 (Nat.card (oddCore H)) := by
      have := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr (odd_card_oddCore (H := H)))
      simpa using this
    exact Subgroup.card_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  · intro hncon
    have hCE : ¬ centralizer (P : Set H) ≤ Op_p'p p H := fun h =>
      hncon ⟨hEO, isPConstrained_of_centralizer_le hP h⟩
    set L : Subgroup H := centralizer (P : Set H) ⊔ pPrimeCore p H with hLdef
    have hLn : L.Normal := centralizer_sup_pPrimeCore_normal hP
    have hLO : ¬ L ≤ oddCore H := by
      intro hLO
      apply hCE
      intro x hx
      have hxO : x ∈ oddCore H := hLO (le_sup_left (a := centralizer (P : Set H)) hx)
      have hsolv : Group.IsSolvable (oddCore H) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ odd_card_oddCore
      have hPO : P ≤ oddCore H := hP.le.trans hEO
      have hP' : IsSylowOf p (P.subgroupOf (oddCore H)) (Op_p'p p (oddCore H)) := by
        rw [← isSylowOf_map_subtype_iff (oddCore H), Subgroup.subgroupOf_map_subtype,
          inf_eq_left.mpr hPO, hE]
        exact hP
      have hle := isPConstrained_of_isSolvable hsolv _ hP'
      have hx' : (⟨x, hxO⟩ : oddCore H) ∈
          centralizer ((P.subgroupOf (oddCore H) : Subgroup (oddCore H)) : Set (oddCore H)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_iff.mp hx) y hy
      rw [← hE]
      exact ⟨_, hle hx', rfl⟩
    have hLeven : 2 ∣ Nat.card L := by
      by_contra h
      exact hLO (le_oddCore_of_normal hLn (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)))
    obtain ⟨w, hwZ, hw1, hw2, hwL⟩ := exists_central_involution_of_even (S := S) hLeven
    have hwT : ((w : S) : H) ∈ T := hZT w hwZ hw2
    have hw1' : ((w : S) : H) ≠ 1 := fun h => hw1 (Subtype.ext h)
    intro t ht
    by_cases ht1 : t = 1
    · rw [ht1]
      exact one_mem _
    obtain ⟨h, hh, hht⟩ := htrans _ hwT t ht hw1' ht1
    apply mem_centralizer_of_mem_sup_pPrimeCore hP _ (hTP ht)
    rw [← hht]
    exact hLn.conj_mem _ hwL h

theorem two_subgroup_inf_sup_eq {S O Z : Subgroup H} [O.Normal] (hS : IsPGroup 2 S)
    (hO : Odd (Nat.card O)) (hZS : Z ≤ S) : S ⊓ (O ⊔ Z) = Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · intro s hs
    obtain ⟨hsS, hsR⟩ := Subgroup.mem_inf.mp hs
    rw [Subgroup.mem_sup_of_normal_left] at hsR
    obtain ⟨o, ho, z, hz, rfl⟩ := hsR
    have hoS : o ∈ S := by
      have : o = o * z * z⁻¹ := by group
      rw [this]
      exact S.mul_mem hsS (S.inv_mem (hZS hz))
    have hdisj : S ⊓ O = ⊥ := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
      apply (Subgroup.disjoint_of_coprime_natCard _).eq_bot
      rw [hk]
      exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hO)
    have ho1 : o = 1 := by
      have : o ∈ S ⊓ O := ⟨hoS, ho⟩
      rwa [hdisj, Subgroup.mem_bot] at this
    rw [ho1, one_mul]
    exact hz
  · exact le_inf hZS le_sup_right

theorem le_solvableRadical_of_sylow_inf_le {L : Subgroup H} [hLn : L.Normal] (S : Sylow 2 H)
    (hSL : (S : Subgroup H) ⊓ L ≤ solvableRadical H) : L ≤ solvableRadical H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRn : (solvableRadical H).Normal := solvableRadical_normal
  have hRs : Group.IsSolvable (solvableRadical H) := solvableRadical_isSolvable
  have hSsyl : IsSylowOf 2 (S : Subgroup H) ⊤ := by
    rw [isSylowOf_iff, Subgroup.relIndex_top_right]
    exact ⟨le_top, S.isPGroup', S.not_dvd_index⟩
  have hSL' : IsSylowOf 2 ((S : Subgroup H) ⊓ L) L :=
    hSsyl.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top])
  have hodd : ¬ 2 ∣ (solvableRadical H).relIndex L := by
    obtain ⟨-, -, hnd⟩ := isSylowOf_iff.mp hSL'
    intro h2
    apply hnd
    have htower := Subgroup.relIndex_mul_relIndex ((S : Subgroup H) ⊓ L)
      (solvableRadical H ⊓ L) L (le_inf hSL inf_le_right) inf_le_right
    rw [← htower, Subgroup.inf_relIndex_right]
    exact h2.mul_left _
  set X : Subgroup H := L ⊔ solvableRadical H with hX
  have hRX : ((solvableRadical H).subgroupOf X).Normal := Subgroup.normal_subgroupOf
  have hsolvR : Group.IsSolvable ((solvableRadical H).subgroupOf X) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (le_sup_right : solvableRadical H ≤ X)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe le_sup_right).injective
  have hquot : Odd (Nat.card (X ⧸ (solvableRadical H).subgroupOf X)) := by
    change Odd ((solvableRadical H).relIndex X)
    rw [hX, Subgroup.relIndex_sup_right]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
  have hsolvQ : Group.IsSolvable (X ⧸ (solvableRadical H).subgroupOf X) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ hquot
  have hsolvX : Group.IsSolvable X :=
    Group.isSolvable_of_subgroup_quotient ((solvableRadical H).subgroupOf X)
  have hXn : X.Normal := Subgroup.sup_normal _ _
  have hXR : X ≤ solvableRadical H := le_sSup ⟨hXn, hsolvX⟩
  exact le_sup_left.trans hXR

theorem not_dvd_relIndex_of_le_sup {O Z E : Subgroup H} [O.Normal] (hp2 : p ≠ 2)
    (hZ : IsPGroup 2 Z) (hE : E ≤ O ⊔ Z) : ¬ p ∣ O.relIndex E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : E →* H ⧸ O := (QuotientGroup.mk' O).comp E.subtype
  have hker : f.ker = O.subgroupOf E := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rfl
  have hrange : f.range = E.map (QuotientGroup.mk' O) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcard : O.relIndex E = Nat.card (E.map (QuotientGroup.mk' O)) := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, hrange]
  have hle : E.map (QuotientGroup.mk' O) ≤ Z.map (QuotientGroup.mk' O) := by
    have := Subgroup.map_mono (f := QuotientGroup.mk' O) hE
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at this
  have h2 : IsPGroup 2 (E.map (QuotientGroup.mk' O)) := (hZ.map _).to_le hle
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
  rw [hcard, hn]
  intro hdvd
  have := (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
    ((Fact.out : p.Prime).dvd_of_dvd_pow hdvd)
  exact hp2 this

theorem pConstrainedWithin_criteria_of_solvableRadical_eq (hp : p ≠ 2) (S : Sylow 2 H)
    (hrad : solvableRadical H = oddCore H ⊔ (center S).map (S : Subgroup H).subtype)
    {P : Subgroup H} (hP : IsSylowOf p P (oddCore H))
    (hSP : (S : Subgroup H) ≤ normalizer (P : Set H)) :
    (PConstrainedWithin p H (solvableRadical H) ↔
        IsSylowOf 2 ((center S).map (S : Subgroup H).subtype ⊓ centralizer (P : Set H))
          (centralizer (P : Set H))) ∧
      (PConstrainedWithin p H (oddCore H) ↔ Odd (Nat.card (centralizer (P : Set H)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup H := oddCore H with hOdef
  set Z : Subgroup H := (center S).map (S : Subgroup H).subtype with hZdef
  set M₀ : Subgroup H := (pPrimeCore p O).map O.subtype with hM₀def
  set E₀ : Subgroup H := (Op_p'p p O).map O.subtype with hE₀def
  set Q : Subgroup H := P ⊓ E₀ with hQdef
  set L : Subgroup H := centralizer (Q : Set H) ⊔ M₀ with hLdef
  have hOn : O.Normal := oddCore_normal H
  have hOodd : Odd (Nat.card O) := odd_card_oddCore
  have hM₀n : M₀.Normal := ConjAct.normal_of_characteristic_of_normal
  have hE₀n : E₀.Normal := ConjAct.normal_of_characteristic_of_normal
  have hM₀cop : Nat.Coprime p (Nat.card M₀) := by
    rw [hM₀def, Subgroup.card_map_of_injective O.subtype_injective]
    exact pPrimeCore_coprime_card
  have hE₀O : E₀ ≤ O := Subgroup.map_subtype_le _
  have hPO : P ≤ O := hP.le
  have hQsyl : IsSylowOf p Q E₀ :=
    hP.inf_of_le_normalizer hE₀O (le_normalizer_map_subtype O _)
  have hQp : IsPGroup p Q := hQsyl.isPGroup
  have hQO : Q ≤ O := hQsyl.le.trans hE₀O
  have hM₀Q : M₀ ⊔ Q = E₀ := by
    have hQ' : IsSylowOf p (Q.subgroupOf O) (Op_p'p p O) := by
      rw [← isSylowOf_map_subtype_iff O, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQO]
      exact hQsyl
    have h := (sup_eq_Op_p'p_iff_isSylowOf hQ'.isPGroup).mpr hQ'
    have := congrArg (Subgroup.map O.subtype) h
    rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQO] at this
  have hLn : L.Normal := centralizer_sup_normal_of_sup_eq hM₀cop hQp hM₀Q
  have hnorm : ∀ (N : Subgroup H) [N.Normal] (g : H), g ∈ normalizer (N : Set H) := by
    intro N _ g
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top g
  have hSQ : (S : Subgroup H) ≤ normalizer (Q : Set H) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hSP hs, hnorm E₀ s⟩
  set S₀ : Subgroup H := (S : Subgroup H) ⊓ L with hS₀def
  have hS₀Q : S₀ ≤ centralizer (Q : Set H) := fun s hs =>
    mem_centralizer_of_mem_sup_of_coprime hM₀cop hQp hs.2 (hSQ hs.1)
  have hS₀p : IsPGroup 2 S₀ := S.isPGroup'.to_le inf_le_left
  have hS₀P : S₀ ≤ centralizer (P : Set H) := by
    apply (two_group_centralizes_sylow_iff (K := O) (S := S₀) hOodd hS₀p
      (fun s _ => hnorm O s) hP (fun s hs => hSP hs.1)).mpr
    exact hS₀Q
  have hSsyl : IsSylowOf 2 (S : Subgroup H) ⊤ := by
    rw [isSylowOf_iff, Subgroup.relIndex_top_right]
    exact ⟨le_top, S.isPGroup', S.not_dvd_index⟩
  have hS₀L : IsSylowOf 2 S₀ L :=
    hSsyl.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top])
  have hCPCQ : centralizer (P : Set H) ≤ centralizer (Q : Set H) :=
    Subgroup.centralizer_le (fun x hx => (inf_le_left : Q ≤ P) hx)
  have hCPL : centralizer (P : Set H) ≤ L := hCPCQ.trans le_sup_left
  have hS₀CP : IsSylowOf 2 S₀ (centralizer (P : Set H)) := hS₀L.of_le hS₀P hCPL
  have hML : pPrimeCore p H ≤ L := by
    intro m hm
    have hMcap : pPrimeCore p H ⊓ E₀ ≤ M₀ := by
      intro y ⟨hyM, hyE⟩
      have hyO : y ∈ O := hE₀O hyE
      have hle : (pPrimeCore p H ⊓ E₀).subgroupOf O ≤ pPrimeCore p O := by
        have hn : ((pPrimeCore p H ⊓ E₀).subgroupOf O).Normal := Subgroup.normal_subgroupOf
        apply le_sSup
        refine ⟨hn, ?_⟩
        have hcard : Nat.card ((pPrimeCore p H ⊓ E₀).subgroupOf O) =
            Nat.card (pPrimeCore p H ⊓ E₀ : Subgroup H) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hE₀O)).toEquiv
        rw [hcard]
        exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
          pPrimeCore_coprime_card
      exact ⟨⟨y, hyO⟩, hle ⟨hyM, hyE⟩, rfl⟩
    rw [hLdef, centralizer_sup_eq_comap hM₀cop hQp]
    change QuotientGroup.mk' M₀ m ∈ centralizer _
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    apply hMcap
    have hMn : (pPrimeCore p H).Normal := inferInstance
    have hxE : x ∈ E₀ := hx.2
    constructor
    · have : m⁻¹ * (x⁻¹ * m * x) ∈ pPrimeCore p H :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hm)
          (by simpa using hMn.conj_mem m hm x⁻¹)
      simpa [mul_assoc] using this
    · have : (m⁻¹ * x⁻¹ * m) * x ∈ E₀ :=
        E₀.mul_mem (by simpa using hE₀n.conj_mem _ (E₀.inv_mem hxE) m⁻¹) hxE
      simpa [mul_assoc] using this
  have hQ' : IsSylowOf p (Q.subgroupOf O) (Op_p'p p O) := by
    rw [← isSylowOf_map_subtype_iff O, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQO]
    exact hQsyl
  have hCQO : ∀ x ∈ centralizer (Q : Set H), x ∈ O → x ∈ E₀ := by
    intro x hx hxO
    have hsolv : Group.IsSolvable O := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hOodd
    have hle := isPConstrained_of_isSolvable hsolv _ hQ'
    have hx' : (⟨x, hxO⟩ : O) ∈
        centralizer ((Q.subgroupOf O : Subgroup O) : Set O) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hx) y hy
    exact ⟨_, hle hx', rfl⟩
  have hM₀O : M₀ ≤ O := Subgroup.map_subtype_le _
  have hii : PConstrainedWithin p H O ↔ Odd (Nat.card (centralizer (P : Set H))) := by
    constructor
    · rintro ⟨hEO, hcon⟩
      have hE : E₀ = Op_p'p p H := by
        rw [hE₀def, Op_p'p_map_subtype_eq_inf hOn, inf_eq_right.mpr hEO]
      have hQE : IsSylowOf p Q (Op_p'p p H) := hE ▸ hQsyl
      exact hOodd.of_dvd_nat (Subgroup.card_dvd_of_le ((hCPCQ.trans (hcon Q hQE)).trans hEO))
    · intro hodd
      have hS₀1 : Nat.card S₀ = 1 := by
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS₀p
        have hdvd : Nat.card S₀ ∣ Nat.card (centralizer (P : Set H)) :=
          Subgroup.card_dvd_of_le hS₀P
        rw [hk] at hdvd ⊢
        cases k with
        | zero => rfl
        | succ k =>
          exfalso
          have : 2 ∣ Nat.card (centralizer (P : Set H)) :=
            (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans hdvd
          exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
      have hLodd : Odd (Nat.card L) := by
        have hcard := hS₀L.card_eq
        rw [hS₀1] at hcard
        have h0 : (Nat.card L).factorization 2 = 0 := by
          by_contra h0
          have : 1 < 2 ^ (Nat.card L).factorization 2 := Nat.one_lt_pow h0 (by norm_num)
          omega
        rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
        intro h2
        have := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two Nat.card_pos.ne').mp h2
        omega
      have hLO : L ≤ O := le_oddCore_of_normal hLn hLodd
      have hMO : pPrimeCore p H ≤ O := hML.trans hLO
      have hEO : Op_p'p p H ≤ O := Op_p'p_le_oddCore hp hMO
      have hE : E₀ = Op_p'p p H := by
        rw [hE₀def, Op_p'p_map_subtype_eq_inf hOn, inf_eq_right.mpr hEO]
      have hCQ : centralizer (Q : Set H) ≤ Op_p'p p H := fun x hx =>
        hE ▸ hCQO x hx (hLO (le_sup_left (a := centralizer (Q : Set H)) hx))
      exact ⟨hEO, isPConstrained_of_centralizer_le (hE ▸ hQsyl) hCQ⟩
  have hZS : Z ≤ S := Subgroup.map_subtype_le _
  have hZp : IsPGroup 2 Z := S.isPGroup'.to_le hZS
  have hSR : (S : Subgroup H) ⊓ solvableRadical H = Z := by
    rw [hrad]
    exact two_subgroup_inf_sup_eq S.isPGroup' hOodd hZS
  have hOR : O ≤ solvableRadical H := hrad ▸ le_sup_left
  have hZR : Z ≤ solvableRadical H := hrad ▸ le_sup_right
  have hQE : Op_p'p p H ≤ solvableRadical H → IsSylowOf p Q (Op_p'p p H) := by
    intro hER
    have hE₀E : E₀ = O ⊓ Op_p'p p H := Op_p'p_map_subtype_eq_inf hOn
    have hE₀le : E₀ ≤ Op_p'p p H := hE₀E ▸ inf_le_right
    rw [isSylowOf_iff] at hQsyl ⊢
    obtain ⟨hle, hpQ, hnd⟩ := hQsyl
    refine ⟨hle.trans hE₀le, hpQ, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex Q E₀ (Op_p'p p H) hle hE₀le]
    intro hdvd
    rcases (Nat.Prime.dvd_mul Fact.out).mp hdvd with h | h
    · exact hnd h
    · rw [hE₀E, Subgroup.inf_relIndex_right] at h
      exact not_dvd_relIndex_of_le_sup hp hZp (hrad ▸ hER) h
  have hZCS₀ : Z ⊓ centralizer (P : Set H) ≤ S₀ := fun x hx => ⟨hZS hx.1, hCPL hx.2⟩
  refine ⟨⟨?_, ?_⟩, hii⟩
  · rintro ⟨hER, hcon⟩
    have hLR : L ≤ solvableRadical H :=
      sup_le ((hcon Q (hQE hER)).trans hER) (hM₀O.trans hOR)
    have hS₀Z : S₀ ≤ Z := by
      rw [← hSR]
      exact inf_le_inf_left _ hLR
    have heq : Z ⊓ centralizer (P : Set H) = S₀ := le_antisymm hZCS₀ (le_inf hS₀Z hS₀P)
    rw [heq]
    exact hS₀CP
  · intro hsyl
    have heq : S₀ = Z ⊓ centralizer (P : Set H) := hsyl.eq_of_le hZCS₀ hS₀CP.le hS₀p
    have hS₀R : (S : Subgroup H) ⊓ L ≤ solvableRadical H := by
      change S₀ ≤ solvableRadical H
      rw [heq]
      exact inf_le_left.trans hZR
    have hLR : L ≤ solvableRadical H := le_solvableRadical_of_sylow_inf_le S hS₀R
    have hMR : pPrimeCore p H ≤ solvableRadical H := hML.trans hLR
    have hER : Op_p'p p H ≤ solvableRadical H := Op_p'p_le_solvableRadical hMR
    have hQE' := hQE hER
    have hCQ : centralizer (Q : Set H) ≤ Op_p'p p H := by
      intro x hx
      have hxR : x ∈ solvableRadical H := hLR (le_sup_left (a := centralizer (Q : Set H)) hx)
      have hsolvR : Group.IsSolvable (solvableRadical H) := solvableRadical_isSolvable
      have hER' : (Op_p'p p (solvableRadical H)).map (solvableRadical H).subtype =
          Op_p'p p H := by
        rw [Op_p'p_map_subtype_eq_inf solvableRadical_normal, inf_eq_right.mpr hER]
      have hQR : Q ≤ solvableRadical H := hQO.trans hOR
      have hQ'' : IsSylowOf p (Q.subgroupOf (solvableRadical H))
          (Op_p'p p (solvableRadical H)) := by
        rw [← isSylowOf_map_subtype_iff (solvableRadical H), Subgroup.subgroupOf_map_subtype,
          inf_eq_left.mpr hQR, hER']
        exact hQE'
      have hle := isPConstrained_of_isSolvable hsolvR _ hQ''
      have hx' : (⟨x, hxR⟩ : solvableRadical H) ∈
          centralizer ((Q.subgroupOf (solvableRadical H) : Subgroup (solvableRadical H)) :
            Set (solvableRadical H)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_iff.mp hx) y hy
      rw [← hER']
      exact ⟨_, hle hx', rfl⟩
    exact ⟨hER, isPConstrained_of_centralizer_le hQE' hCQ⟩

theorem pConstrainedWithin_criteria_of_qgroup_data (hp : p ≠ 2)
    (S : Sylow 2 H) (_hZ : IsCyclic (center S))
    (hrad : solvableRadical H = oddCore H ⊔ (center S).map (S : Subgroup H).subtype)
    (_hthree : ∀ N : Subgroup H, N.Normal → ¬ N ≤ solvableRadical H → 3 ∣ Nat.card N)
    (_hcent : 3 < p → ∀ S₁ Q₁ : Subgroup H, S₁ ≤ S → IsPGroup p Q₁ →
      Q₁ ≤ normalizer (S₁ : Set H) → Q₁ ≤ centralizer (S₁ : Set H))
    {P : Subgroup H} (hP : IsSylowOf p P (oddCore H))
    (hSP : (S : Subgroup H) ≤ normalizer (P : Set H)) :
    (PConstrainedWithin p H (solvableRadical H) ↔
        IsSylowOf 2 ((center S).map (S : Subgroup H).subtype ⊓ centralizer (P : Set H))
          (centralizer (P : Set H))) ∧
      (PConstrainedWithin p H (oddCore H) ↔ Odd (Nat.card (centralizer (P : Set H)))) :=
  pConstrainedWithin_criteria_of_solvableRadical_eq hp S hrad hP hSP

end CFSG.ABGLocalTools
