module

import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporMLocal
import CFSG.LocalAnalysis.StandardType.GGSporKM7Gmat
import CFSG.Mathlib.GroupTheory.ExtraspecialCount
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.StandardType.GGSporKBMPreds
public import CFSG.Monster.B.Pinned.Primes.Extraspecial
public import CFSG.RankThree.PartOne.SPOR.OuterM

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporBig

open CFSG.Blueprint
open CFSG.StandardType.SporadicShape
open CFSG.Monster.Generated (Gmat)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenCensus (gq)

private theorem seven_cubed_zmod_nineteen : (7 : ZMod 19) ^ 3 = 1 := by decide

private theorem seven_ne_one_zmod_nineteen : (7 : ZMod 19) ≠ 1 := by decide

private theorem seven_sq_ne_one_zmod_five : ¬ (7 : ZMod 5) ^ 2 ^ 1 = 1 := by decide

private theorem seven_fourth_zmod_five : (7 : ZMod 5) ^ 2 ^ (1 + 1) = 1 := by decide

private theorem le_normalizer_bmOpCent {L : Type} [Group L] (z : L) :
    Subgroup.centralizer ({z} : Set L) ≤
      Subgroup.normalizer ((BMOpCent 7 z : Subgroup L) : Set L) := by
  set C := Subgroup.centralizer ({z} : Set L)
  have hQle : BMOpCent 7 z ≤ C := Subgroup.map_subtype_le _
  have hsub : (BMOpCent 7 z).subgroupOf C = CFSG.pCore 7 C := by
    rw [BMOpCent]
    exact Subgroup.comap_map_eq_self_of_injective C.subtype_injective (CFSG.pCore 7 C)
  have hnorm : ((BMOpCent 7 z).subgroupOf C).Normal := by
    rw [hsub]
    exact CFSG.pCore_normal
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hQle).1 hnorm

private theorem monsterOrder_factorization_seven :
    CFSG.Open.monsterOrder.factorization 7 = 6 := by
  have h : CFSG.Open.monsterOrder = 7 ^ 6 *
      (2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 11 ^ 2 * 13 ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 *
        59 * 71) := by
    unfold CFSG.Open.monsterOrder
    ring
  rw [h, Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_seven, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

private theorem pCore_le_sylow_of_le_centralizer {L : Type} [Group L] {z : L}
    (S : Sylow 7 L) (hSleC : (S : Subgroup L) ≤ Subgroup.centralizer ({z} : Set L)) :
    BMOpCent 7 z ≤ (S : Subgroup L) := by
  let S' : Sylow 7 ↥(Subgroup.centralizer ({z} : Set L)) := S.subtype hSleC
  have hqc : CFSG.pCore 7 ↥(Subgroup.centralizer ({z} : Set L)) ≤
      (S' : Subgroup ↥(Subgroup.centralizer ({z} : Set L))) :=
    CFSG.pCore_isPGroup.le_sylow_of_normal S'
  rw [BMOpCent]
  calc (CFSG.pCore 7 ↥(Subgroup.centralizer ({z} : Set L))).map
        (Subgroup.centralizer ({z} : Set L)).subtype
      ≤ (S' : Subgroup ↥(Subgroup.centralizer ({z} : Set L))).map
          (Subgroup.centralizer ({z} : Set L)).subtype := Subgroup.map_mono hqc
    _ = (S : Subgroup L) := by
        rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hSleC]

section Certificates

private theorem card_bmOpCent_dvd_pow_six {L : Type} [Group L] [Finite L]
    (e : L ≃* NativeSporadic.Carrier .M) (z : L) :
    Nat.card (BMOpCent 7 z) ∣ 7 ^ 6 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hQ7 : IsPGroup 7 ↥(BMOpCent 7 z) := by
    rw [BMOpCent]
    exact IsPGroup.map (CFSG.pCore_isPGroup (p := 7)
      (G := ↥(Subgroup.centralizer ({z} : Set L))))
      (Subgroup.centralizer ({z} : Set L)).subtype
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ7
  have hL := CFSG.AGLEmbedding.MonsterRows.card_eq_monsterOrder CFSG.Milestones.fam_m_finiteness e
  have hdvd : 7 ^ k ∣ CFSG.Open.monsterOrder := by
    rw [← hL, ← hk, ← Subgroup.card_top (G := L)]
    exact Subgroup.card_dvd_of_le (le_top : BMOpCent 7 z ≤ ⊤)
  have hk6 : k ≤ 6 := by
    by_contra h
    have h7 : 7 ≤ k := by omega
    exact (by norm_num [CFSG.Open.monsterOrder] : ¬ 7 ^ 7 ∣ CFSG.Open.monsterOrder)
      ((pow_dvd_pow 7 h7).trans hdvd)
  rw [hk]
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).2 hk6

section Exponent

theorem exists_exponent_seven_M {L : Type} [Group L]
    (e : L ≃* NativeSporadic.Carrier .M) :
    ∃ F : Subgroup L, Nat.card F = 7 ^ 5 ∧ ∀ g ∈ F, g ^ 7 = 1 := by
  have : Finite CFSG.Open.MonsterY443Derived :=
    Nat.finite_of_card_ne_zero (by
      rw [CFSG.Milestones.fam_m_finiteness]
      norm_num [CFSG.Open.monsterOrder])
  have hbij : Function.Bijective CFSG.YGroups.Y443.fM :=
    CFSG.RankThree.PartOne.SPOR.fM_surjective.bijective_of_nat_card_le
      (by rw [CFSG.Milestones.fam_m_finiteness,
        CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder])
  let f : L ≃* Gmat :=
    (e.trans CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv).trans
      (MulEquiv.ofBijective CFSG.YGroups.Y443.fM hbij)
  let F₀ : Subgroup Gmat := Subgroup.closure (Set.range ![gq 1, gq 2, gq 3, gq 4])
  have hD : CFSG.Monster.B.Pinned.CommData 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5)
      CFSG.StandardType.SporadicShape.m7M :=
    CFSG.StandardType.SporadicShape.gq_commData
  refine ⟨F₀.map f.symm.toMonoidHom, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective f.symm.injective]
    exact hD.card_eq
  · intro g hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
    rw [← map_pow,
      CFSG.StandardType.SporadicShape.commData_pow_p (p := 7) (n := 4) (by norm_num) hD y hy,
      map_one]

end Exponent

theorem not_nineteen_dvd_card_centralizer_M {L : Type} [Group L] [Finite L]
    (e : L ≃* NativeSporadic.Carrier .M) {z : L} (hz : orderOf z = 7)
    (h76 : 7 ^ 6 ∣ Nat.card (Subgroup.centralizer ({z} : Set L))) :
    ¬ 19 ∣ Nat.card (Subgroup.centralizer ({z} : Set L)) := by
  have hF1 := bmPCentralF1At_of_seven_central_M e hz h76
  obtain ⟨hzQ, hQQ, hZ, hle⟩ := hF1
  have hQ6 := card_bmOpCent_dvd_pow_six e z
  have hCnorm := le_normalizer_bmOpCent (z := z)
  intro h19
  set C := Subgroup.centralizer ({z} : Set L) with hC
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  have : Fintype ↥C := Fintype.ofFinite _
  have hdvd : 19 ∣ Fintype.card ↥C := by
    rw [Nat.card_eq_fintype_card] at h19
    exact h19
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card 19 hdvd
  let u : L := v
  have hu19 : orderOf u = 19 := by
    change orderOf (v : L) = 19
    rw [Subgroup.orderOf_coe]
    exact hv
  have huC : u ∈ C := v.2
  have huz : u * z = z * u := Subgroup.mem_centralizer_singleton_iff.1 huC
  have huQ : u ∈ Subgroup.normalizer ((BMOpCent 7 z : Subgroup L) : Set L) := hCnorm huC
  have hpr : orderOf (7 : ZMod 19) = 3 :=
    orderOf_eq_prime seven_cubed_zmod_nineteen seven_ne_one_zmod_nineteen
  have huCQ : u ∈ Subgroup.centralizer ((BMOpCent 7 z : Subgroup L) : Set L) :=
    CFSG.Extraspecial.mem_centralizer_of_orderOf_eq_three (p := 7) (r := 19)
      hz hQQ.le hZ hQ6 hpr hu19 huQ huz
  have huQmem : u ∈ BMOpCent 7 z := hle ⟨huC, huCQ⟩
  have hdvdOrder : orderOf u ∣ Nat.card (BMOpCent 7 z) :=
    Subgroup.orderOf_dvd_natCard _ huQmem
  rw [hu19] at hdvdOrder
  have h19Q : ¬ 19 ∣ Nat.card (BMOpCent 7 z) := by
    intro h
    exact (by norm_num : ¬ (19 : ℕ) ∣ 7 ^ 6) (h.trans hQ6)
  exact h19Q hdvdOrder

theorem mem_zpowers_of_commute_five_M {L : Type} [Group L] [Finite L]
    (e : L ≃* NativeSporadic.Carrier .M) {z f y : L} (hz : orderOf z = 7)
    (h76 : 7 ^ 6 ∣ Nat.card (Subgroup.centralizer ({z} : Set L)))
    (hf : orderOf f = 5) (hfz : f * z = z * f) (hy : y ^ 7 = 1) (hyz : y * z = z * y)
    (hyf : y * f = f * y) : y ∈ Subgroup.zpowers z := by
  have hF1 := bmPCentralF1At_of_seven_central_M e hz h76
  obtain ⟨hzQ, hQQ, hZ, hle⟩ := hF1
  have hQ6 := card_bmOpCent_dvd_pow_six e z
  have hCnorm := le_normalizer_bmOpCent (z := z)
  have hfQnorm : f ∈ Subgroup.normalizer ((BMOpCent 7 z : Subgroup L) : Set L) :=
    hCnorm (Subgroup.mem_centralizer_singleton_iff.2 hfz)
  have hyQnorm : y ∈ Subgroup.normalizer ((BMOpCent 7 z : Subgroup L) : Set L) :=
    hCnorm (Subgroup.mem_centralizer_singleton_iff.2 hyz)
  have hfC : f ∉ Subgroup.centralizer ((BMOpCent 7 z : Subgroup L) : Set L) := by
    intro hfc
    have hfQ : f ∈ BMOpCent 7 z :=
      hle ⟨Subgroup.mem_centralizer_singleton_iff.2 hfz, hfc⟩
    have hdvd : orderOf f ∣ Nat.card (BMOpCent 7 z) :=
      Subgroup.orderOf_dvd_natCard _ hfQ
    have h5 : 5 ∣ 7 ^ 6 := by
      rw [← hf]
      exact hdvd.trans hQ6
    norm_num at h5
  have hy1 : ∃ k : ℕ, y ^ 7 ^ k = 1 := ⟨1, by simpa using hy⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hps : orderOf (7 : ZMod 5) = 4 :=
    orderOf_eq_prime_pow seven_sq_ne_one_zmod_five seven_fourth_zmod_five
  have hyCQ : y ∈ Subgroup.centralizer ((BMOpCent 7 z : Subgroup L) : Set L) :=
    CFSG.Extraspecial.mem_centralizer_of_orderOf_eq_four (p := 7) (s := 5)
      hz hQQ.le hZ hQ6 hps hf hfQnorm hfz hfC hy1 hyQnorm hyz hyf
  have hyQmem : y ∈ BMOpCent 7 z :=
    hle ⟨Subgroup.mem_centralizer_singleton_iff.2 hyz, hyCQ⟩
  have hinf := CFSG.Extraspecial.inf_centralizer_eq_zpowers_of_orderOf_eq_four
    (p := 7) (s := 5) hz hQQ.le hZ hQ6 hps hf hfQnorm hfz hfC
  have hyinf : y ∈ BMOpCent 7 z ⊓ Subgroup.centralizer ({f} : Set L) :=
    ⟨hyQmem, Subgroup.mem_centralizer_singleton_iff.2 hyf⟩
  rwa [hinf] at hyinf

private theorem center_sylow_map_le_zpowers {L : Type} [Group L] [Finite L]
    (e : L ≃* NativeSporadic.Carrier .M) (S : Sylow 7 L) {z : L} (hz : orderOf z = 7)
    (hScard : Nat.card ↥(S : Subgroup L) = 7 ^ 6)
    (hSleC : (S : Subgroup L) ≤ Subgroup.centralizer ({z} : Set L)) :
    (Subgroup.center ↥(S : Subgroup L)).map (S : Subgroup L).subtype ≤ Subgroup.zpowers z := by
  have h76 : 7 ^ 6 ∣ Nat.card ↥(Subgroup.centralizer ({z} : Set L)) := by
    rw [← hScard]
    exact Subgroup.card_dvd_of_le hSleC
  have hF1 := bmPCentralF1At_of_seven_central_M e hz h76
  obtain ⟨hzQ, hQQ, hZ, hle⟩ := hF1
  have hQleS := pCore_le_sylow_of_le_centralizer S hSleC
  let Z := Subgroup.center ↥(S : Subgroup L)
  have hZleQ : Z.map (S : Subgroup L).subtype ≤ BMOpCent 7 z := by
    rintro x ⟨w, hw, rfl⟩
    have hwCz : ((w : ↥(S : Subgroup L)) : L) ∈ Subgroup.centralizer ({z} : Set L) :=
      hSleC w.2
    have hwCQ : ((w : ↥(S : Subgroup L)) : L) ∈
        Subgroup.centralizer ((BMOpCent 7 z : Subgroup L) : Set L) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hw (⟨q, hQleS hq⟩ : ↥S))
    exact hle ⟨hwCz, hwCQ⟩
  have hZleCQ : Z.map (S : Subgroup L).subtype ≤
      Subgroup.centralizer ((BMOpCent 7 z : Subgroup L) : Set L) := by
    rintro x ⟨w, hw, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hw (⟨q, hQleS hq⟩ : ↥S))
  have h1 : Z.map (S : Subgroup L).subtype ≤
      BMOpCent 7 z ⊓ Subgroup.centralizer ((BMOpCent 7 z : Subgroup L) : Set L) :=
    le_inf hZleQ hZleCQ
  rwa [hZ] at h1

theorem card_center_sylow_M {L : Type} [Group L] [Finite L]
    (e : L ≃* NativeSporadic.Carrier .M) :
    ∀ Q : Sylow 7 L, Nat.card (Subgroup.center ↥(Q : Subgroup L)) = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hL := CFSG.AGLEmbedding.MonsterRows.card_eq_monsterOrder CFSG.Milestones.fam_m_finiteness e
  have hfac : (Nat.card L).factorization 7 = 6 := by
    rw [hL, monsterOrder_factorization_seven]
  intro Q
  let S : Sylow 7 L := Q
  have hScard : Nat.card ↥(S : Subgroup L) = 7 ^ 6 := by
    rw [Sylow.card_eq_multiplicity S, hfac]
  have h7dvdS : 7 ∣ Nat.card ↥(S : Subgroup L) := by
    rw [hScard]
    exact dvd_pow_self 7 (by norm_num)
  have : Group.IsNilpotent ↥(S : Subgroup L) := S.isPGroup'.isNilpotent
  have h7center : 7 ∣ Nat.card ↥(Subgroup.center ↥(S : Subgroup L)) :=
    Group.IsNilpotent.prime_dvd_card_center h7dvdS
  have : Fintype ↥(Subgroup.center ↥(S : Subgroup L)) := Fintype.ofFinite _
  have hdvd' : 7 ∣ Fintype.card ↥(Subgroup.center ↥(S : Subgroup L)) := by
    rwa [Nat.card_eq_fintype_card] at h7center
  obtain ⟨zS, hzS⟩ := exists_prime_orderOf_dvd_card 7 hdvd'
  let z : L := (zS : ↥S)
  have hz : orderOf z = 7 := by
    have h2 : orderOf z = orderOf zS := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    rw [h2]
    exact hzS
  have hSleC : (S : Subgroup L) ≤ Subgroup.centralizer ({z} : Set L) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp zS.2 (⟨s, hs⟩ : ↥S))
  have hZleZp := center_sylow_map_le_zpowers e S hz hScard hSleC
  let Z := Subgroup.center ↥(S : Subgroup L)
  have hz_mem : z ∈ Z.map (S : Subgroup L).subtype := ⟨zS, zS.2, rfl⟩
  have hle1 : Nat.card ↥(Subgroup.zpowers z) ≤
      Nat.card ↥(Z.map (S : Subgroup L).subtype) :=
    Subgroup.card_le_of_le (Subgroup.zpowers_le.2 hz_mem)
  have hle2 : Nat.card ↥(Z.map (S : Subgroup L).subtype) ≤
      Nat.card ↥(Subgroup.zpowers z) :=
    Subgroup.card_le_of_le hZleZp
  have hmapcard : Nat.card ↥(Z.map (S : Subgroup L).subtype) = Nat.card ↥Z :=
    Subgroup.card_map_of_injective (S : Subgroup L).subtype_injective
  rw [hmapcard] at hle1 hle2
  have hEq : Nat.card ↥Z = Nat.card ↥(Subgroup.zpowers z) := le_antisymm hle2 hle1
  show Nat.card ↥Z = 7
  rw [hEq, Nat.card_zpowers, hz]

end Certificates

end CFSG.LocalAnalysis.AGL81I.Section3.SporBig
