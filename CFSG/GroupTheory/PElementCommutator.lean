module

import CFSG.GroupTheory.CommutatorMemSubgroup
import CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux
public import CFSG.LieType.BorelTits.Basic
public import CFSG.RankThree.PartOne.S12.Hyp

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem mem_pCoreOf_of_mul_pow {K O : Subgroup G}
    (hO : O = CFSG.Open.pCoreOf 2 K) {c t : G} (hcK : c ∈ K) (htK : t ∈ K)
    (hcO : ∀ m ∈ K, ⁅c, m⁆ ∈ O) {j : ℕ}
    (hct : (c * t) ^ 2 ^ j = 1) (ht : t ^ 2 ^ j = 1) : c ∈ O := by
  subst hO
  let OK : Subgroup ↥K := CFSG.pCore 2 ↥K
  let f : ↥K →* ↥K ⧸ OK := QuotientGroup.mk' OK
  let cK : ↥K := ⟨c, hcK⟩
  let tK : ↥K := ⟨t, htK⟩
  have hcomm_mem : ∀ m : ↥K, ⁅cK, m⁆ ∈ OK := by
    intro m
    refine (Subgroup.mem_map_iff_mem K.subtype_injective).mp ?_
    change (⁅c, (m : G)⁆ : G) ∈ CFSG.Open.pCoreOf 2 K
    exact hcO (m : G) m.2
  have hcenter : f cK ∈ Subgroup.center (↥K ⧸ OK) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective OK y
    have hcm : Commute (f cK) (f m) := by
      rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff (N := OK) ⁅cK, m⁆).mpr (hcomm_mem m)
    exact hcm.symm.eq
  have hcomm_ct : Commute (f cK) (f tK) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff (N := OK) ⁅cK, tK⁆).mpr (hcomm_mem tK)
  have hctK : (cK * tK) ^ 2 ^ j = 1 := Subtype.ext (by simpa [cK, tK] using hct)
  have htKpow : tK ^ 2 ^ j = 1 := Subtype.ext (by simpa [tK] using ht)
  have hpow : f cK ^ 2 ^ j = 1 := by
    have h1 : (f cK * f tK) ^ 2 ^ j = 1 := by
      rw [← map_mul, ← map_pow, hctK, map_one]
    rw [hcomm_ct.mul_pow] at h1
    have h2 : f tK ^ 2 ^ j = 1 := by
      rw [← map_pow, htKpow, map_one]
    simpa [h2] using h1
  have hzp : IsPGroup 2 (Subgroup.zpowers (f cK)) := by
    intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨j, ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hpow, one_zpow]
  have hzp_normal : (Subgroup.zpowers (f cK)).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hcenter)
  have hbot : CFSG.pCore 2 (↥K ⧸ OK) = ⊥ :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux.pCore_quotient_pCore_eq_bot
  have hle : Subgroup.zpowers (f cK) ≤ CFSG.pCore 2 (↥K ⧸ OK) :=
    CFSG.LieType.BorelTits.le_pCore 2 hzp_normal hzp
  have hfc : f cK = 1 := by
    have hmem := hle (Subgroup.mem_zpowers (f cK))
    rw [hbot] at hmem
    simpa using hmem
  have hcOK : cK ∈ OK := (QuotientGroup.eq_one_iff (N := OK) cK).mp hfc
  change c ∈ (CFSG.pCore 2 ↥K).map K.subtype
  exact Subgroup.mem_map_of_mem K.subtype hcOK

private theorem commutator_mem_pCoreOf_of_pow {K X : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (K : Set G)) {t : G} (htK : t ∈ K) {j : ℕ}
    (ht : orderOf t = 2 ^ j) {x : G} (hx : x ∈ X)
    (h : ⁅⁅K, X⁆, K⁆ ≤ CFSG.Open.pCoreOf 2 K) :
    ⁅t, x⁆ ∈ CFSG.Open.pCoreOf 2 K := by
  let c : G := ⁅x, t⁆
  have hcK : c ∈ K := by
    have hxt : x * t * x⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hX hx) t).mp htK
    simpa [c, commutatorElement_def] using K.mul_mem hxt (K.inv_mem htK)
  have hKX : ⁅x, t⁆ ∈ ⁅K, X⁆ := by
    have hXK : ⁅x, t⁆ ∈ ⁅X, K⁆ := Subgroup.commutator_mem_commutator hx htK
    rwa [Subgroup.commutator_comm] at hXK
  have hcKX : c ∈ ⁅K, X⁆ := by simpa [c] using hKX
  have hcO : ∀ m ∈ K, ⁅c, m⁆ ∈ CFSG.Open.pCoreOf 2 K :=
    fun m hm => (Subgroup.commutator_le.mp h) c hcKX m hm
  have htpow : t ^ 2 ^ j = 1 := by
    rw [← ht]
    exact pow_orderOf_eq_one t
  have hct : (c * t) ^ 2 ^ j = 1 := by
    have hct_eq : c * t = x * t * x⁻¹ := by
      rw [show c = x * t * x⁻¹ * t⁻¹ from rfl]
      group
    rw [hct_eq, conj_pow, htpow, mul_one]
    group
  have hcO' : c ∈ CFSG.Open.pCoreOf 2 K :=
    mem_pCoreOf_of_mul_pow (O := CFSG.Open.pCoreOf 2 K) rfl hcK htK hcO hct htpow
  have htx : ⁅t, x⁆ = c⁻¹ := by
    rw [show c = ⁅x, t⁆ from rfl, ← commutatorElement_inv]
  rw [htx]
  exact (CFSG.Open.pCoreOf 2 K).inv_mem hcO'

theorem commutator_le_pCoreOf_of_commutator_commutator_le {K X : Subgroup G}
    (hK : CFSG.RankThree.PartOne.pElementSubgroup 2 K = K)
    (hX : X ≤ normalizer (K : Set G)) (h : ⁅⁅K, X⁆, K⁆ ≤ CFSG.Open.pCoreOf 2 K) :
    ⁅K, X⁆ ≤ CFSG.Open.pCoreOf 2 K := by
  refine Subgroup.commutator_le.mpr ?_
  intro k hk x hx
  have hKO : K ≤ normalizer (CFSG.Open.pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hgen : CFSG.RankThree.PartOne.pElementSubgroup 2 K ≤
      CFSG.GroupTheory.commMemSubgroup K (CFSG.Open.pCoreOf 2 K) hKO x := by
    rw [CFSG.RankThree.PartOne.pElementSubgroup, Subgroup.closure_le]
    rintro t ⟨htK, j, ht⟩
    exact ⟨htK, commutator_mem_pCoreOf_of_pow hX htK ht hx h⟩
  have hkP : k ∈ CFSG.RankThree.PartOne.pElementSubgroup 2 K := by
    rw [hK]
    exact hk
  exact ((CFSG.GroupTheory.mem_commMemSubgroup hKO x k).mp (hgen hkP)).2

private theorem eq_one_of_conj_eq_inv_mul {Q : Type*} [Group Q] {z t b : Q} {j : ℕ}
    (hz : z ∈ Subgroup.center Q) (hzodd : Odd (orderOf z))
    (ht : t ^ 2 ^ j = 1) (h : b * t * b⁻¹ = z⁻¹ * t) : z = 1 := by
  have hcop : Nat.Coprime (orderOf z⁻¹) (orderOf t) := by
    rw [orderOf_inv]
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one ht)
      (Nat.Coprime.pow_right j (Odd.coprime_two_right hzodd))
  have hcomm : Commute z⁻¹ t :=
    ((commute_iff_eq z t).mpr (Subgroup.mem_center_iff.mp hz t).symm).inv_left
  have horder : orderOf (z⁻¹ * t) = orderOf z⁻¹ * orderOf t :=
    Commute.orderOf_mul_eq_mul_orderOf_of_coprime hcomm hcop
  have hconj : orderOf (b * t * b⁻¹) = orderOf t := by
    rw [show b * t * b⁻¹ = MulAut.conj b t by rw [MulAut.conj_apply]]
    exact MulEquiv.orderOf_eq (MulAut.conj b) t
  have heq : orderOf z⁻¹ * orderOf t = orderOf t := by
    rw [← horder, ← h]
    exact hconj
  have hpos : 0 < orderOf t :=
    Nat.pos_of_dvd_of_pos (orderOf_dvd_of_pow_eq_one ht) (pow_pos (by norm_num) j)
  have hz1 : orderOf z⁻¹ = 1 := Nat.eq_of_mul_eq_mul_right hpos (by simpa using heq)
  have hzpow : orderOf z = 1 := by
    rw [← orderOf_inv]
    exact hz1
  exact orderOf_eq_one_iff.mp hzpow

private theorem mem_of_conj_eq_inv_mul_sup {O Z : Subgroup G}
    (hZ : Z ≤ Subgroup.center G) (hZodd : Odd (Nat.card Z))
    {o z t b : G} (hoO : o ∈ O) (hzZ : z ∈ Z)
    (htO : t ∈ Subgroup.normalizer (O : Set G))
    (hbO : b ∈ Subgroup.normalizer (O : Set G)) {j : ℕ}
    (ht : t ^ 2 ^ j = 1) (hbt : b * t * b⁻¹ = (o * z)⁻¹ * t) : z ∈ O := by
  let N : Subgroup G := Subgroup.normalizer (O : Set G)
  have hON : O ≤ N := Subgroup.le_normalizer
  have hZN : Z ≤ N := hZ.trans (Subgroup.center_le_normalizer (O : Set G))
  let ON : Subgroup N := O.subgroupOf N
  have hONnormal : ON.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hON).mpr le_rfl
  let f : N →* N ⧸ ON := QuotientGroup.mk' ON
  let bN : N := ⟨b, hbO⟩
  let tN : N := ⟨t, htO⟩
  let zN : N := ⟨z, hZN hzZ⟩
  let oN : N := ⟨o, hON hoO⟩
  have hfo : f oN = 1 := by
    change (oN : ↥N ⧸ ON) = 1
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hoO
  have hNconj : f bN * f tN * (f bN)⁻¹ = (f zN)⁻¹ * f tN := by
    have hbtN : bN * tN * bN⁻¹ = (oN * zN)⁻¹ * tN := by
      apply Subtype.ext
      change b * t * b⁻¹ = (o * z)⁻¹ * t
      exact hbt
    have h := congrArg f hbtN
    simpa [map_mul, map_inv, hfo] using h
  have hzcenter : f zN ∈ Subgroup.center (N ⧸ ON) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective ON y
    have hzm : zN * m = m * zN := by
      apply Subtype.ext
      change z * (m : G) = (m : G) * z
      exact (Subgroup.mem_center_iff.mp (hZ hzZ) (m : G)).symm
    have hfm : f zN * f m = f m * f zN := by
      simpa [map_mul] using congrArg f hzm
    exact hfm.symm
  have hfz_dvd : orderOf (f zN) ∣ Nat.card Z := by
    refine (orderOf_map_dvd f zN).trans ?_
    have hzNorder : orderOf zN = orderOf z := by
      simp [zN]
    rw [hzNorder]
    exact Subgroup.orderOf_dvd_natCard Z hzZ
  have hzodd : Odd (orderOf (f zN)) := Odd.of_dvd_nat hZodd hfz_dvd
  have htNpow : tN ^ 2 ^ j = 1 := Subtype.ext (by simpa [tN] using ht)
  have hft_pow : f tN ^ 2 ^ j = 1 := by
    rw [← map_pow, htNpow, map_one]
  have hz1 : f zN = 1 := eq_one_of_conj_eq_inv_mul hzcenter hzodd hft_pow hNconj
  have hz1' : (zN : ↥N ⧸ ON) = 1 := by simpa [f] using hz1
  have hzON : zN ∈ ON := (QuotientGroup.eq_one_iff (N := ON) zN).mp hz1'
  rw [Subgroup.mem_subgroupOf] at hzON
  exact hzON

private theorem commutator_mem_of_pow {A B O Z : Subgroup G}
    (hAO : A ≤ Subgroup.normalizer (O : Set G))
    (hBO : B ≤ Subgroup.normalizer (O : Set G))
    (hZ : Z ≤ Subgroup.center G) (hZodd : Odd (Nat.card Z))
    (h : ⁅A, B⁆ ≤ O ⊔ Z) {t : G} (htA : t ∈ A) {j : ℕ} (ht : orderOf t = 2 ^ j)
    {b : G} (hbB : b ∈ B) : ⁅t, b⁆ ∈ O := by
  have hZnormal : Z.Normal := Subgroup.normal_of_le_center hZ
  have hd : ⁅t, b⁆ ∈ O ⊔ Z := h (Subgroup.commutator_mem_commutator htA hbB)
  obtain ⟨o, hoO, z, hzZ, hd_eq⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := O) (t := Z)).mp hd
  have htpow : t ^ 2 ^ j = 1 := by
    rw [← ht]
    exact pow_orderOf_eq_one t
  have hbt : b * t * b⁻¹ = (o * z)⁻¹ * t := by
    rw [show b * t * b⁻¹ = MulAut.conj b t by rw [MulAut.conj_apply]]
    rw [conj_eq_commutatorElement_mul, ← commutatorElement_inv, ← hd_eq]
  have hzO : z ∈ O :=
    mem_of_conj_eq_inv_mul_sup hZ hZodd hoO hzZ (hAO htA) (hBO hbB) htpow hbt
  rw [← hd_eq]
  exact O.mul_mem hoO hzO

theorem commutator_le_of_le_sup_of_le_center {A B O Z : Subgroup G}
    (hA : A = CFSG.RankThree.PartOne.pElementSubgroup 2 A ⊔ O)
    (hAO : A ≤ normalizer (O : Set G)) (hBO : B ≤ normalizer (O : Set G))
    (hZ : Z ≤ center G) (hZodd : Odd (Nat.card Z)) (h : ⁅A, B⁆ ≤ O ⊔ Z) : ⁅A, B⁆ ≤ O := by
  refine Subgroup.commutator_le.mpr ?_
  intro a haA b hbB
  have hgen : CFSG.RankThree.PartOne.pElementSubgroup 2 A ≤
      CFSG.GroupTheory.commMemSubgroup A O hAO b := by
    rw [CFSG.RankThree.PartOne.pElementSubgroup, Subgroup.closure_le]
    rintro t ⟨htA, j, ht⟩
    exact ⟨htA, commutator_mem_of_pow hAO hBO hZ hZodd h htA ht hbB⟩
  have hOle : O ≤ CFSG.GroupTheory.commMemSubgroup A O hAO b := by
    intro o hoO
    refine ⟨?_, ?_⟩
    · rw [hA]
      exact Subgroup.mem_sup_right hoO
    · have hbo : ⁅b, o⁆ ∈ O := by
        have h1 : b * o * b⁻¹ ∈ O :=
          (Subgroup.mem_normalizer_iff.mp (hBO hbB) o).mp hoO
        have h2 : b * o * b⁻¹ * o⁻¹ ∈ O := O.mul_mem h1 (O.inv_mem hoO)
        simpa [commutatorElement_def] using h2
      simpa [commutatorElement_inv] using O.inv_mem hbo
  have hAle : A ≤ CFSG.GroupTheory.commMemSubgroup A O hAO b := by
    calc A = CFSG.RankThree.PartOne.pElementSubgroup 2 A ⊔ O := hA
      _ ≤ CFSG.GroupTheory.commMemSubgroup A O hAO b := sup_le hgen hOle
  exact ((CFSG.GroupTheory.mem_commMemSubgroup hAO b a).mp (hAle haA)).2

end CFSG.GroupTheory
