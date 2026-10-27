module

public import CFSG.CGT.PushingUpLit.SolKAb.Setup
public import CFSG.LocalAnalysis.ComponentClassification.AS76bInputs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement
import CFSG.LieType.BorelTits.Basic
import CFSG.RankThree.GF2n.Tim78Normal

public section

open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly (pCoreOf)
open CFSG.ComponentClassification.AS76b (oUpperTwoPrime)
open CFSG.ComponentClassification.AschbacherTheorem3 (centerOf frattiniOf
  exists_rightConjugate_le_of_isSylowOf)
open CFSG.ComponentClassification.AschbacherTightEmbedding (mem_rightConjugate_iff)
open scoped commutatorElement

namespace CFSG.CGT.PushingUpLit.SolKNA

private theorem pow_eq_one_of_conj_eq_comm_mul {G : Type} [Group G] {k q u : G}
    (hku : u * k = k * u) (h : q⁻¹ * k * q = u * k) {m : ℕ} (hm : k ^ m = 1) : u ^ m = 1 := by
  have h1 : (q⁻¹ * k * q) ^ m = 1 := by
    have h2 := conj_pow (a := q⁻¹) (b := k) (i := m)
    rw [inv_inv, hm] at h2
    have e : q⁻¹ * 1 * q = (1 : G) := by group
    rw [e] at h2
    exact h2
  rw [h, (show Commute u k from hku).mul_pow, hm, mul_one] at h1
  exact h1

theorem eq_of_forall_comm_mem {G : Type} [Group G] [Finite G] {K R N : Subgroup G}
    (hK : oUpperTwoPrime K = K) (hR : IsSylowOf 2 R K)
    (hC : K ⊓ Subgroup.centralizer (pCoreOf 2 K : Set G) ≤ pCoreOf 2 K)
    (hN : (N.subgroupOf K).Normal) (hNR : N ≤ R)
    (hcomm : ∀ x ∈ R, ∀ y ∈ R, x * y * x⁻¹ * y⁻¹ ∈ N)
    (hZ : ∀ n ∈ N, ∀ r ∈ R, n * r = r * n) : K = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRK : R ≤ K := hR.le
  have hNK : N ≤ K := hNR.trans hRK
  have hN2 : IsPGroup 2 N := hR.isPGroup.to_le hNR
  have hP2 : IsPGroup 2 (pCoreOf 2 K) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hKP : K ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hPR : pCoreOf 2 K ≤ R := by
    obtain ⟨Q, hQ⟩ := hR
    have hnorm : (CFSG.Open.pCore 2 K).Normal := CFSG.LieType.BorelTits.pCore_normal 2
    rw [← hQ]
    exact Subgroup.map_mono
      ((CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := K)).le_sylow_of_normal Q)
  have hconjN : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N := by
    intro k hk n hn
    exact Subgroup.mem_subgroupOf.mp
      (hN.conj_mem ⟨n, hNK hn⟩ (Subgroup.mem_subgroupOf.mpr hn) ⟨k, hk⟩)
  have hconjP : ∀ k ∈ K, ∀ q ∈ pCoreOf 2 K, k * q * k⁻¹ ∈ pCoreOf 2 K := fun k hk q hq =>
    (Subgroup.mem_normalizer_iff.mp (hKP hk) q).mp hq
  have hA : ∀ s ∈ K, (∃ j : ℕ, s ^ 2 ^ j = 1) →
      (∀ n ∈ N, s * n = n * s) ∧ ∀ q ∈ pCoreOf 2 K, q * s * q⁻¹ * s⁻¹ ∈ N := by
    rintro s hsK ⟨j, hj⟩
    have hzp : IsPGroup 2 (Subgroup.zpowers s) := by
      refine IsPGroup.of_card_dvd_pow (n := j) ?_
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hj
    obtain ⟨c, hcK, hc⟩ :=
      exists_rightConjugate_le_of_isSylowOf hR hzp (Subgroup.zpowers_le.mpr hsK)
    have hrR : c⁻¹ * s * c ∈ R := by
      refine hc ((mem_rightConjugate_iff _ c _).mpr ?_)
      have e : c * (c⁻¹ * s * c) * c⁻¹ = s := by group
      rw [e]
      exact Subgroup.mem_zpowers s
    obtain ⟨r, hrR', rfl⟩ : ∃ r ∈ R, s = c * r * c⁻¹ := ⟨c⁻¹ * s * c, hrR, by group⟩
    refine ⟨fun n hn => ?_, fun q hq => ?_⟩
    · have hn' : c⁻¹ * n * c ∈ N := by
        have := hconjN c⁻¹ (K.inv_mem hcK) n hn
        rwa [inv_inv] at this
      have h1 := hZ _ hn' r hrR'
      calc c * r * c⁻¹ * n = c * (r * (c⁻¹ * n * c)) * c⁻¹ := by group
        _ = c * (c⁻¹ * n * c * r) * c⁻¹ := by rw [h1]
        _ = n * (c * r * c⁻¹) := by group
    · have hq' : c⁻¹ * q * c ∈ pCoreOf 2 K := by
        have := hconjP c⁻¹ (K.inv_mem hcK) q hq
        rwa [inv_inv] at this
      have h1 := hconjN c hcK _ (hcomm _ (hPR hq') r hrR')
      convert h1 using 1
      group
  let U : Subgroup G :=
    { carrier := {k | k ∈ K ∧ (∀ n ∈ N, k * n = n * k) ∧
        ∀ q ∈ pCoreOf 2 K, q * k * q⁻¹ * k⁻¹ ∈ N}
      mul_mem' := by
        rintro a b ⟨ha, ha1, ha2⟩ ⟨hb, hb1, hb2⟩
        refine ⟨K.mul_mem ha hb, fun n hn => ?_, fun q hq => ?_⟩
        · calc a * b * n = a * (b * n) := mul_assoc _ _ _
            _ = a * (n * b) := by rw [hb1 n hn]
            _ = a * n * b := (mul_assoc _ _ _).symm
            _ = n * a * b := by rw [ha1 n hn]
            _ = n * (a * b) := mul_assoc _ _ _
        · have h1 := N.mul_mem (ha2 q hq) (hconjN a ha _ (hb2 q hq))
          convert h1 using 1
          group
      one_mem' := ⟨K.one_mem, fun n _ => by simp, fun q _ => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha1, ha2⟩
        refine ⟨K.inv_mem ha, fun n hn => ?_, fun q hq => ?_⟩
        · exact (Commute.inv_left (show Commute a n from ha1 n hn)).eq
        · have h1 := hconjN a⁻¹ (K.inv_mem ha) _ (N.inv_mem (ha2 q hq))
          convert h1 using 1
          group }
  have hKU : K ≤ U := by
    have h : oUpperTwoPrime K ≤ U := by
      refine (Subgroup.closure_le U).mpr ?_
      rintro s ⟨hsK, hs2⟩
      exact ⟨hsK, hA s hsK hs2⟩
    rwa [hK] at h
  have hodd : ∀ k ∈ K, Odd (orderOf k) → k = 1 := by
    intro k hk hko
    obtain ⟨-, hk1, hk2⟩ := hKU hk
    have hcent : ∀ q ∈ pCoreOf 2 K, q * k = k * q := by
      intro q hq
      have hn : q⁻¹ * k * q * k⁻¹ ∈ N := by
        have := hk2 q⁻¹ (inv_mem hq)
        rwa [inv_inv] at this
      have hnk : q⁻¹ * k * q * k⁻¹ * k = k * (q⁻¹ * k * q * k⁻¹) := (hk1 _ hn).symm
      have hpow := pow_eq_one_of_conj_eq_comm_mul (k := k) (q := q) hnk (by group)
        (pow_orderOf_eq_one k)
      have hn1 : q⁻¹ * k * q * k⁻¹ = 1 :=
        CFSG.RankThree.GF2n.Tim78.eq_one_of_odd_of_isPGroup hN2 hn
          (Odd.of_dvd_nat hko (orderOf_dvd_of_pow_eq_one hpow))
      have h2 : k * q = q * k := by
        calc k * q = q * (q⁻¹ * k * q * k⁻¹) * k := by group
          _ = q * k := by rw [hn1]; group
      exact h2.symm
    have hkP : k ∈ pCoreOf 2 K := hC ⟨hk, Subgroup.mem_centralizer_iff.mpr hcent⟩
    exact CFSG.RankThree.GF2n.Tim78.eq_one_of_odd_of_isPGroup hP2 hkP hko
  have h2elt : ∀ x ∈ K, ∃ j : ℕ, x ^ 2 ^ j = 1 := by
    intro x hx
    obtain ⟨a, hao, ha1⟩ := CFSG.RankThree.GF2n.Tim78.exists_odd_orderOf_pow x
    exact ha1 (hodd _ (K.pow_mem hx _) hao)
  have hK2 : IsPGroup 2 K := by
    intro x
    obtain ⟨j, hj⟩ := h2elt x x.2
    exact ⟨j, Subtype.ext (by simpa using hj)⟩
  exact hR.eq_of_le hRK le_rfl hK2

end CFSG.CGT.PushingUpLit.SolKNA

namespace CFSG.CGT.PushingUpLit.SolKAb

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

theorem STSetting.inf_centralizer_pCoreOf_le (S : STSetting G K) :
    K ⊓ Subgroup.centralizer (pCoreOf 2 K : Set G) ≤ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (K : Set G) with hM
  have hKM : K ≤ M := Subgroup.le_normalizer
  have hQ2 : IsPGroup 2 (pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hQM : pCoreOf 2 M ≤ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M
  have hMQ : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hKP : K ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hQK : pCoreOf 2 M ⊓ K ≤ pCoreOf 2 K := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      (hQ2.to_le inf_le_left)
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxQ, hxK⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hMQ (hKM hk)) x).mp hxQ,
        K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk)⟩
    · rintro ⟨hxQ, hxK⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hMQ (hKM hk)) x).mpr hxQ, ?_⟩
      have := K.mul_mem (K.mul_mem (K.inv_mem hk) hxK) hk
      simpa [mul_assoc] using this
  have hodd : ∀ a ∈ K ⊓ Subgroup.centralizer (pCoreOf 2 K : Set G), Odd (orderOf a) → a = 1 := by
    rintro a ⟨haK, haC⟩ hao
    have hcommq : ∀ q ∈ pCoreOf 2 M, q * a = a * q := by
      intro q hq
      have hqM : q ∈ M := hQM hq
      have h1 : a⁻¹ * q * a ∈ pCoreOf 2 M := by
        have := (Subgroup.mem_normalizer_iff.mp (hMQ (hKM (K.inv_mem haK))) q).mp hq
        simpa [mul_assoc] using this
      have huQ : q⁻¹ * a⁻¹ * q * a ∈ pCoreOf 2 M := by
        have : q⁻¹ * a⁻¹ * q * a = q⁻¹ * (a⁻¹ * q * a) := by group
        rw [this]; exact mul_mem (inv_mem hq) h1
      have huK : q⁻¹ * a⁻¹ * q * a ∈ K := by
        have h2 : q⁻¹ * a⁻¹ * q ∈ K := by
          have := (Subgroup.mem_normalizer_iff.mp (M.inv_mem hqM) a⁻¹).mp (K.inv_mem haK)
          simpa [mul_assoc] using this
        exact K.mul_mem h2 haK
      have huP : q⁻¹ * a⁻¹ * q * a ∈ pCoreOf 2 K := hQK ⟨huQ, huK⟩
      generalize hu : q⁻¹ * a⁻¹ * q * a = u at huQ huK huP
      have hw : a⁻¹ * q * a = q * u := by rw [← hu]; group
      have hcu : u * a = a * u := Subgroup.mem_centralizer_iff.mp haC _ huP
      have hu1 : u ^ orderOf a = 1 :=
        CFSG.CGT.PushingUpLit.SolKNA.pow_eq_one_of_conj_eq_comm_mul (k := a⁻¹) (q := q) (u := u)
          (Commute.inv_right (show Commute u a from hcu)).eq (by rw [← hu]; group)
          (by rw [inv_pow, pow_orderOf_eq_one, inv_one])
      have hou : Odd (orderOf u) := Odd.of_dvd_nat hao (orderOf_dvd_of_pow_eq_one hu1)
      have hu' : u = 1 := CFSG.RankThree.GF2n.Tim78.eq_one_of_odd_of_isPGroup hQ2 huQ hou
      have h2 : a⁻¹ * q * a = q := by rw [hw, hu', mul_one]
      calc q * a = a * (a⁻¹ * q * a) := by group
        _ = a * q := by rw [h2]
    have haQ : a ∈ pCoreOf 2 M := S.fstar ⟨hKM haK, Subgroup.mem_centralizer_iff.mpr hcommq⟩
    exact CFSG.RankThree.GF2n.Tim78.eq_one_of_odd_of_isPGroup hQ2 haQ hao
  set C := K ⊓ Subgroup.centralizer (pCoreOf 2 K : Set G) with hC
  have hC2 : IsPGroup 2 C := by
    intro c
    obtain ⟨n, hn, hn'⟩ := CFSG.RankThree.GF2n.Tim78.exists_odd_orderOf_pow (c : G)
    have hcn : (c : G) ^ 2 ^ n ∈ C := C.pow_mem c.2 _
    have := hodd _ hcn hn
    obtain ⟨k, hk⟩ := hn' this
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hCK : C ≤ K := inf_le_left
  have hnormC : (C.subgroupOf K).Normal := by
    constructor
    intro x hx k
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨K.mul_mem (K.mul_mem k.2 hx.1) (K.inv_mem k.2), Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    have hy' : (k : G)⁻¹ * y * k ∈ pCoreOf 2 K := by
      have := (Subgroup.mem_normalizer_iff.mp (hKP (K.inv_mem k.2)) y).mp hy
      simpa [mul_assoc] using this
    have hc := Subgroup.mem_centralizer_iff.mp hx.2 _ hy'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc y * (↑k * ↑x * (↑k)⁻¹) = ↑k * (((k : G)⁻¹ * y * k) * ↑x) * (↑k)⁻¹ := by group
      _ = ↑k * (↑x * ((k : G)⁻¹ * y * k)) * (↑k)⁻¹ := by rw [hc]
      _ = (↑k * ↑x * (↑k)⁻¹) * y := by group
  exact CFSG.LieType.BorelTits.le_pCoreOf 2 hCK hnormC hC2

end CFSG.CGT.PushingUpLit.SolKAb
