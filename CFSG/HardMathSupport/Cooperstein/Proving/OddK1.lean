module

public import CFSG.HardMathSupport.Cooperstein.Proving.CharTwoCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving.K1

open Subgroup
open CFSG.Open (pCoreOf)

variable {G : Type} [Group G]

theorem pCoreOf_eq (X : Subgroup G) : pCoreOf 2 X = (CFSG.pCore 2 ↥X).map X.subtype :=
  CFSG.openPCoreOf_eq_map_pCore 2 X

theorem comm_of_normal {B P Q : Subgroup G} (hBP : B ≤ P) (hBn : (B.subgroupOf P).Normal)
    (hBQ : B ⊓ Q = ⊥) (hQn : ∀ x ∈ P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) {b q : G} (hb : b ∈ B)
    (hq : q ∈ Q) (hqP : q ∈ P) : b * q = q * b := by
  have hb' : (⟨b, hBP hb⟩ : P) ∈ B.subgroupOf P := Subgroup.mem_subgroupOf.2 hb
  have hB1 : q * b * q⁻¹ ∈ B := by
    have := hBn.conj_mem _ hb' ⟨q, hqP⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have hz : q * b * q⁻¹ * b⁻¹ ∈ B ⊓ Q := by
    constructor
    · exact B.mul_mem hB1 (B.inv_mem hb)
    · have h1 : b * q⁻¹ * b⁻¹ ∈ Q := hQn b (hBP hb) q⁻¹ (Q.inv_mem hq)
      have := Q.mul_mem hq h1
      simpa [mul_assoc] using this
  rw [hBQ, Subgroup.mem_bot, mul_inv_eq_one] at hz
  have h3 : q * b * q⁻¹ * q = b * q := by rw [hz]
  rw [mul_assoc, inv_mul_cancel, mul_one] at h3
  exact h3.symm

theorem odd_mem_of_commute {B P Q : Subgroup G} (hBP : B ≤ P) (hBQ : B ⊓ Q = ⊥)
    (hPQ : ∀ p ∈ P, ∃ b ∈ B, ∃ q ∈ Q, p = b * q)
    (hQ2 : ∀ q ∈ Q, ∃ k : ℕ, q ^ 2 ^ k = 1)
    (hcomm : ∀ b ∈ B, ∀ q ∈ Q, q ∈ P → b * q = q * b)
    {p : G} (hp : p ∈ P) (hodd : Odd (orderOf p)) : p ∈ B := by
  obtain ⟨b, hb, q, hq, rfl⟩ := hPQ p hp
  have hqP : q ∈ P := by
    have : b⁻¹ * (b * q) ∈ P := P.mul_mem (P.inv_mem (hBP hb)) hp
    simpa using this
  have hcommute : Commute b q := hcomm b hb q hq hqP
  have hpm : (b * q) ^ orderOf (b * q) = 1 := pow_orderOf_eq_one _
  rw [hcommute.mul_pow] at hpm
  have hbq : b ^ orderOf (b * q) = (q ^ orderOf (b * q))⁻¹ := eq_inv_of_mul_eq_one_left hpm
  have hbQ : b ^ orderOf (b * q) ∈ Q := by
    rw [hbq]
    exact Q.inv_mem (Q.pow_mem hq _)
  have h1 : b ^ orderOf (b * q) = 1 := by
    have : b ^ orderOf (b * q) ∈ B ⊓ Q := ⟨B.pow_mem hb _, hbQ⟩
    rw [hBQ, Subgroup.mem_bot] at this
    exact this
  have hqm : q ^ orderOf (b * q) = 1 := by
    rw [h1, one_mul] at hpm
    exact hpm
  obtain ⟨k, hk⟩ := hQ2 q hq
  have hcop : Nat.Coprime (2 ^ k) (orderOf (b * q)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  have hq1 : q = 1 := by
    have hg : q ^ Nat.gcd (2 ^ k) (orderOf (b * q)) = 1 := pow_gcd_eq_one.2 ⟨hk, hqm⟩
    rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at hg
    exact hg
  rw [hq1, mul_one]
  exact hb

theorem normal_step {B P P' Q : Subgroup G} (hBP : B ≤ P) (hPP' : P ≤ P') (hBQ : B ⊓ Q = ⊥)
    (hPQ : ∀ p ∈ P, ∃ b ∈ B, ∃ q ∈ Q, p = b * q)
    (hQ2 : ∀ q ∈ Q, ∃ k : ℕ, q ^ 2 ^ k = 1)
    (hQn : ∀ x ∈ P', ∀ q ∈ Q, x * q * x⁻¹ ∈ Q)
    (hBn : (B.subgroupOf P).Normal) (hPn : (P.subgroupOf P').Normal)
    (hgen : Subgroup.closure {x : G | x ∈ B ∧ Odd (orderOf x)} = B) :
    (B.subgroupOf P').Normal := by
  have hcomm : ∀ b ∈ B, ∀ q ∈ Q, q ∈ P → b * q = q * b := fun b hb q hq hqP =>
    comm_of_normal hBP hBn hBQ (fun x hx q hq => hQn x (hPP' hx) q hq) hb hq hqP
  have hodd_sub : ∀ p ∈ P, Odd (orderOf p) → p ∈ B := fun p hp ho =>
    odd_mem_of_commute hBP hBQ hPQ hQ2 hcomm hp ho
  have hconj : ∀ x ∈ P', ∀ t ∈ B, x * t * x⁻¹ ∈ B := by
    intro x hx
    let K : Subgroup G := B.comap (MulAut.conj x).toMonoidHom
    have hT : Subgroup.closure {t : G | t ∈ B ∧ Odd (orderOf t)} ≤ K := by
      apply (Subgroup.closure_le _).2
      rintro t ⟨htB, hto⟩
      show x * t * x⁻¹ ∈ B
      apply hodd_sub
      · have ht : (⟨t, hPP' (hBP htB)⟩ : P') ∈ P.subgroupOf P' :=
          Subgroup.mem_subgroupOf.2 (hBP htB)
        have := hPn.conj_mem _ ht ⟨x, hx⟩
        simpa [Subgroup.mem_subgroupOf] using this
      · have hpow : (x * t * x⁻¹) ^ orderOf t = 1 := by
          rw [conj_pow, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
        exact Odd.of_dvd_nat hto (orderOf_dvd_of_pow_eq_one hpow)
    have hBK : B ≤ K := hgen ▸ hT
    intro t ht
    exact hBK ht
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simpa using hconj (g : G) g.2 n hn

theorem normal_of_chain {B Y Q : Subgroup G} (hBQ : B ⊓ Q = ⊥)
    (hPQ : ∀ p ∈ Y, ∃ b ∈ B, ∃ q ∈ Q, p = b * q)
    (hQ2 : ∀ q ∈ Q, ∃ k : ℕ, q ^ 2 ^ k = 1)
    (hQn : ∀ x ∈ Y, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q)
    (hgen : Subgroup.closure {x : G | x ∈ B ∧ Odd (orderOf x)} = B)
    {P : Subgroup G}
    (hch : Relation.ReflTransGen (fun H K : Subgroup G => H ≤ K ∧ (H.subgroupOf K).Normal) B P) :
    P ≤ Y → B ≤ P ∧ (B.subgroupOf P).Normal := by
  induction hch with
  | refl =>
    intro _
    refine ⟨le_rfl, ⟨fun n hn g => ?_⟩⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using B.mul_mem (B.mul_mem g.2 hn) (B.inv_mem g.2)
  | tail hab hst ih =>
    rename_i a c
    intro hc
    have ha : a ≤ Y := le_trans hst.1 hc
    obtain ⟨hBa, hBna⟩ := ih ha
    refine ⟨hBa.trans hst.1, ?_⟩
    exact normal_step hBa hst.1 hBQ (fun p hp => hPQ p (ha hp)) hQ2
      (fun x hx q hq => hQn x (hc hx) q hq) hBna hst.2 hgen

theorem pCoreOf_conj_mem {X : Subgroup G} {x q : G} (hx : x ∈ X) (hq : q ∈ pCoreOf 2 X) :
    x * q * x⁻¹ ∈ pCoreOf 2 X := by
  rw [pCoreOf_eq] at hq ⊢
  obtain ⟨y, hy, hyq⟩ := Subgroup.mem_map.1 hq
  have hN : (CFSG.pCore 2 ↥X).Normal := CFSG.pCore_normal
  refine Subgroup.mem_map.2 ⟨(⟨x, hx⟩ : X) * y * (⟨x, hx⟩ : X)⁻¹,
    hN.conj_mem y hy ⟨x, hx⟩, ?_⟩
  rw [← hyq]
  simp

theorem pCoreOf_two_pow {X : Subgroup G} {q : G} (hq : q ∈ pCoreOf 2 X) :
    ∃ k : ℕ, q ^ 2 ^ k = 1 := by
  rw [pCoreOf_eq] at hq
  obtain ⟨y, hy, hyq⟩ := Subgroup.mem_map.1 hq
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)) ⟨y, hy⟩
  refine ⟨k, ?_⟩
  have hk' : y ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  rw [← hyq, ← map_pow, hk', map_one]

theorem eq_bot_of_K1 {X B Y : Subgroup G} (hX : CFSG.QuasithinUnique.CharTwo X) (hBX : B ≤ X)
    (hYX : Y ≤ X) (hBY : B ≤ Y) (hQY : pCoreOf 2 X ≤ Y)
    (hY : ∀ p ∈ Y, ∃ b ∈ B, ∃ q ∈ pCoreOf 2 X, p = b * q)
    (hBQ : B ⊓ pCoreOf 2 X = ⊥)
    (hgen : Subgroup.closure {x : G | x ∈ B ∧ Odd (orderOf x)} = B)
    (hch : Relation.ReflTransGen (fun H K : Subgroup G => H ≤ K ∧ (H.subgroupOf K).Normal) B Y) :
    B = ⊥ := by
  have hQn : ∀ x ∈ Y, ∀ q ∈ pCoreOf 2 X, x * q * x⁻¹ ∈ pCoreOf 2 X :=
    fun x hx q hq => pCoreOf_conj_mem (hYX hx) hq
  have hBn : (B.subgroupOf Y).Normal :=
    (normal_of_chain hBQ hY (fun q hq => pCoreOf_two_pow hq) hQn hgen hch le_rfl).2
  have hcomm : ∀ b ∈ B, ∀ q ∈ pCoreOf 2 X, b * q = q * b := fun b hb q hq =>
    comm_of_normal hBY hBn hBQ hQn hb hq (hQY hq)
  have hBQ' : B ≤ pCoreOf 2 X := le_pCoreOf_two_of_centralizes hX hBX hcomm
  have h := inf_eq_left.2 hBQ'
  rw [hBQ] at h
  exact h.symm

end CFSG.HardMathSupport.Cooperstein.Proving.K1

end
