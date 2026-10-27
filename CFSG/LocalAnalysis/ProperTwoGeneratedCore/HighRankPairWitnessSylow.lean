module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFixedRootCentralizers
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorLift
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorNontrivial
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeNormalizedSylowIntersection

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG
open CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator
open CFSG.ProperTwoGeneratedCore.LocalCriterionFixedRoot

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem centralizer_pair_join (x t : G) :
    Subgroup.centralizer ((Subgroup.zpowers x ⊔ Subgroup.zpowers t : Subgroup G) : Set G) =
      Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({t} : Set G) := by
  ext y
  rw [Subgroup.mem_inf, ← centralizer_zpowers_eq_singleton, ← centralizer_zpowers_eq_singleton,
    Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨fun a ha => h a (Subgroup.mem_sup_left ha),
      fun a ha => h a (Subgroup.mem_sup_right ha)⟩
  · rintro ⟨hx, ht⟩ a ha
    have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers t ≤
        Subgroup.centralizer ({y} : Set G) := by
      refine sup_le (fun b hb => ?_) (fun b hb => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hx b hb)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (ht b hb)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha)

theorem four_group_centralizer_card_identity (P : Subgroup G) (hP : Odd (Nat.card P))
    {x t : G} (hx : orderOf x = 2) (ht : orderOf t = 2) (hxt : Commute x t) (hne : x ≠ t)
    (hxP : x ∈ Subgroup.normalizer (P : Set G)) (htP : t ∈ Subgroup.normalizer (P : Set G)) :
    Nat.card P * Nat.card (P ⊓ Subgroup.centralizer ({x} : Set G) ⊓
        Subgroup.centralizer ({t} : Set G) : Subgroup G) ^ 2 =
      Nat.card (P ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) *
        Nat.card (P ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) *
          Nat.card (P ⊓ Subgroup.centralizer ({x * t} : Set G) : Subgroup G) := by
  let V := Subgroup.zpowers x ⊔ Subgroup.zpowers t
  obtain ⟨helem, hcard, -⟩ := CFSG.ProperTwoGeneratedCore.commuting_distinct_involutions_four_group
    hx ht hxt hne.symm
  let : IsElementaryAbelian 2 V :=
    { toIsMulCommutative := helem.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun w => by
        apply Subtype.ext
        exact helem.2 w w.property) }
  let : IsKleinFour V := isKleinFour_of_elementary_card_four hcard
  have hV : V ≤ Subgroup.normalizer (P : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hxP) (Subgroup.zpowers_le.mpr htP)
  let : MulDistribMulAction V P := normalizedSubgroupAction P V hV
  let a : V := ⟨x, Subgroup.mem_sup_left (Subgroup.mem_zpowers x)⟩
  let b : V := ⟨t, Subgroup.mem_sup_right (Subgroup.mem_zpowers t)⟩
  have ha : a ≠ 1 := fun h => by
    have : x = 1 := congrArg Subtype.val h
    rw [this, orderOf_one] at hx
    omega
  have hb : b ≠ 1 := fun h => by
    have : t = 1 := congrArg Subtype.val h
    rw [this, orderOf_one] at ht
    omega
  have hab : a ≠ b := fun h => hne (congrArg Subtype.val h)
  have hid := four_group_order_identity a b ha hb hab hP
  have hfix : ∀ c : V, Nat.card (actorFixedSubgroup (I := P) c) =
      Nat.card (P ⊓ Subgroup.centralizer ({(c : G)} : Set G) : Subgroup G) := by
    intro c
    rw [← normalized_fixed_map P V hV c, Subgroup.card_map_of_injective P.subtype_injective]
  have hcommon : Nat.card (fixedPointSubgroup V P) =
      Nat.card (P ⊓ Subgroup.centralizer ({x} : Set G) ⊓
        Subgroup.centralizer ({t} : Set G) : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective P.subtype_injective, normalized_common_fixed_map P V hV,
      centralizer_pair_join, inf_assoc]
  rw [hfix, hfix, hfix, hcommon] at hid
  exact hid


theorem exists_sylow_normalized {I : Subgroup G} (hI : Odd (Nat.card I)) {E : Subgroup G}
    (hE : IsPGroup 2 E) (hEI : E ≤ Subgroup.normalizer (I : Set G)) {p : ℕ} (hp : p.Prime) :
    ∃ R : Sylow p I, E ≤ Subgroup.normalizer (((R : Subgroup I).map I.subtype : Subgroup G) : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨R, -, hR⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.exists_normalized_sylow_containing_normalized_pSubgroup
      2 Nat.prime_two p hp E I ⊥ hE hI.not_two_dvd_nat hEI bot_le IsPGroup.of_bot
      (fun g _ => Subgroup.mem_normalizer_iff.mpr fun h => by
        simp only [Subgroup.mem_bot]
        constructor
        · rintro rfl
          group
        · intro hh
          rw [mul_inv_eq_one, mul_eq_left] at hh
          exact hh)
  exact ⟨R, hR⟩

theorem exists_sylow_inf_centralizer {O : Subgroup G} (hO : Odd (Nat.card O)) {y : G}
    (hy : orderOf y = 2) (hyO : y ∈ Subgroup.normalizer (O : Set G)) {p : ℕ} (hp : p.Prime)
    (R : Sylow p O)
    (hyR : y ∈ Subgroup.normalizer (((R : Subgroup O).map O.subtype : Subgroup G) : Set G)) :
    ∃ R' : Sylow p (O ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G),
      (R' : Subgroup _).map (O ⊓ Subgroup.centralizer ({y} : Set G)).subtype =
        (R : Subgroup O).map O.subtype ⊓ Subgroup.centralizer ({y} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpgroup : IsPGroup 2 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  have hyC : y ∈ Subgroup.normalizer
      (Subgroup.centralizer ({y} : Set G) : Set G) :=
    Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hsub : Subgroup.zpowers y ≤ Subgroup.normalizer
      ((O ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.inf_normalizer_le_normalizer_inf ⟨hyO, hyC⟩)
  have hfixed : O ⊓ Subgroup.centralizer (Subgroup.zpowers y : Set G) ≤ Subgroup.normalizer
      ((O ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) := by
    rw [centralizer_zpowers_eq_singleton]
    exact Subgroup.le_normalizer
  obtain ⟨R', hR'⟩ := CFSG.RankThreeEvenClassification.Helpers.coprime_normalized_sylow_intersection
    2 Nat.prime_two (Subgroup.zpowers y) O hpgroup hO.not_two_dvd_nat
    (Subgroup.zpowers_le.mpr hyO) p hp R (Subgroup.zpowers_le.mpr hyR)
    (O ⊓ Subgroup.centralizer ({y} : Set G)) inf_le_left hsub hfixed
  refine ⟨R', hR'.trans ?_⟩
  rw [← inf_assoc, inf_eq_left.mpr (Subgroup.map_subtype_le (R : Subgroup O))]

theorem card_sylow_map {O : Subgroup G} {p : ℕ} [Fact p.Prime] (R : Sylow p O) :
    Nat.card ((R : Subgroup O).map O.subtype : Subgroup G) =
      p ^ (Nat.card O).factorization p := by
  rw [Subgroup.card_map_of_injective O.subtype_injective, Sylow.card_eq_multiplicity]


theorem prime_index_identity {I : Subgroup G} (hI : Odd (Nat.card I)) {x t : G}
    (hx : orderOf x = 2) (ht : orderOf t = 2) (hxt : Commute x t) (hne : x ≠ t)
    (hxI : x ∈ Subgroup.normalizer (I : Set G)) (htI : t ∈ Subgroup.normalizer (I : Set G))
    {p : ℕ} (hp : p.Prime) (R : Sylow p I)
    (hxR : x ∈ Subgroup.normalizer (((R : Subgroup I).map I.subtype : Subgroup G) : Set G))
    (htR : t ∈ Subgroup.normalizer (((R : Subgroup I).map I.subtype : Subgroup G) : Set G)) :
    (Subgroup.centralizer ({t} : Set G)).relIndex
        ((R : Subgroup I).map I.subtype ⊓ Subgroup.centralizer ({x * t} : Set G)) *
      p ^ ((Subgroup.centralizer ({t} : Set G)).relIndex
        (I ⊓ Subgroup.centralizer ({x} : Set G))).factorization p =
    p ^ ((Subgroup.centralizer ({t} : Set G)).relIndex I).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  set P := (R : Subgroup I).map I.subtype with hPdef
  set Cx := Subgroup.centralizer ({x} : Set G)
  set Ct := Subgroup.centralizer ({t} : Set G)
  have hPodd : Odd (Nat.card P) := hI.of_dvd_nat (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _))
  have hIx : Odd (Nat.card (I ⊓ Cx : Subgroup G)) := hI.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  obtain ⟨Rt, hRt⟩ := exists_sylow_inf_centralizer hI ht htI hp R htR
  obtain ⟨Rx, hRx⟩ := exists_sylow_inf_centralizer hI hx hxI hp R hxR
  have htIx : t ∈ Subgroup.normalizer ((I ⊓ Cx : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨htI, CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.commute_normalizes_centralizer t x hxt.symm⟩
  have htRx : t ∈ Subgroup.normalizer
      (((Rx : Subgroup (I ⊓ Cx : Subgroup G)).map (I ⊓ Cx).subtype : Subgroup G) : Set G) := by
    rw [hRx]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨htR, CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.commute_normalizes_centralizer t x hxt.symm⟩
  obtain ⟨Rxt, hRxt⟩ := exists_sylow_inf_centralizer hIx ht htIx hp Rx htRx
  have hcP := card_sylow_map R
  have hct : Nat.card (P ⊓ Ct : Subgroup G) = p ^ (Nat.card (I ⊓ Ct : Subgroup G)).factorization p := by
    rw [← hRt, card_sylow_map]
  have hcx : Nat.card (P ⊓ Cx : Subgroup G) = p ^ (Nat.card (I ⊓ Cx : Subgroup G)).factorization p := by
    rw [← hRx, card_sylow_map]
  have hcxt : Nat.card (P ⊓ Cx ⊓ Ct : Subgroup G) =
      p ^ (Nat.card (I ⊓ Cx ⊓ Ct : Subgroup G)).factorization p := by
    rw [← hRx, ← hRxt, card_sylow_map]
  have hBW := four_group_centralizer_card_identity P hPodd hx ht hxt hne hxR htR
  set J := P ⊓ Subgroup.centralizer ({x * t} : Set G)
  have hJt : Ct ⊓ J = P ⊓ Cx ⊓ Ct := by
    ext y
    simp only [J, Subgroup.mem_inf, Cx, Ct, Subgroup.mem_centralizer_singleton_iff]
    have key : ∀ y : G, y * t = t * y → (y * (x * t) = x * t * y ↔ y * x = x * y) := by
      intro y hyt
      have hc : Commute y t := hyt
      constructor
      · intro h
        have h0 : Commute y (x * t) := h
        have h' : Commute y (x * t * t⁻¹) := h0.mul_right hc.inv_right
        rw [mul_inv_cancel_right] at h'
        exact h'.eq
      · intro h
        have h0 : Commute y x := h
        exact (h0.mul_right hc).eq
    constructor
    · rintro ⟨hyt, hyP, hyxt⟩
      exact ⟨⟨hyP, (key y hyt).mp hyxt⟩, hyt⟩
    · rintro ⟨⟨hyP, hyx⟩, hyt⟩
      exact ⟨hyt, hyP, (key y hyt).mpr hyx⟩
  have hJcard : Ct.relIndex J * Nat.card (P ⊓ Cx ⊓ Ct : Subgroup G) = Nat.card J := by
    rw [← hJt]
    exact Subgroup.relIndex_mul_card Ct J
  have hIcard : Ct.relIndex I * Nat.card (I ⊓ Ct : Subgroup G) = Nat.card I := by
    rw [inf_comm]
    exact Subgroup.relIndex_mul_card Ct I
  have hIxcard : Ct.relIndex (I ⊓ Cx) * Nat.card (I ⊓ Cx ⊓ Ct : Subgroup G) =
      Nat.card (I ⊓ Cx : Subgroup G) := by
    rw [inf_comm (I ⊓ Cx)]
    exact Subgroup.relIndex_mul_card Ct (I ⊓ Cx)
  have hfac : ∀ a b : ℕ, a ≠ 0 → b ≠ 0 →
      (a * b).factorization p = a.factorization p + b.factorization p := by
    intro a b ha hb
    rw [Nat.factorization_mul ha hb, Finsupp.add_apply]
  have hm0 : Ct.relIndex I ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hIcard
    exact Nat.card_pos.ne' hIcard.symm
  have hδ0 : Ct.relIndex (I ⊓ Cx) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hIxcard
    exact Nat.card_pos.ne' hIxcard.symm
  have h1 := hfac _ _ hm0 (Nat.card_pos (α := (I ⊓ Ct : Subgroup G))).ne'
  rw [hIcard] at h1
  have h2 := hfac _ _ hδ0 (Nat.card_pos (α := (I ⊓ Cx ⊓ Ct : Subgroup G))).ne'
  rw [hIxcard] at h2
  rw [hcP, hcxt, hcx, hct, ← hJcard, hcxt, h1, h2, pow_add, pow_add] at hBW
  set X := p ^ (Nat.card (I ⊓ Ct : Subgroup G)).factorization p
  set Y := p ^ (Nat.card (I ⊓ Cx ⊓ Ct : Subgroup G)).factorization p
  have hX : 0 < X := pow_pos hp.pos _
  have hY : 0 < Y := pow_pos hp.pos _
  apply Nat.eq_of_mul_eq_mul_right (mul_pos hX (pow_pos hY 2))
  linarith [hBW]

end CFSG.ProperTwoGeneratedCore.HighRankPair
