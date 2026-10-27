module

public import CFSG.LieType.Ree.LargeReeSimplePairGeneration
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.QuasithinUnique.Setup.X6

open CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.ABGLocalTools
open scoped Pointwise commutatorElement

section CharTwo

variable {τ : Tag} {K : Type} [Field K] [CharP K 2]

theorem neg_one_units_charTwo : (-1 : Kˣ) = 1 :=
  Units.ext (CharTwo.neg_eq (1 : K))

theorem weylElt_mul_canonicalRep_charTwo
    (i : Fin τ.rank) (w : WeylGroup τ) :
    weylElt τ K i 1 * canonicalRep (coxeterSystem τ) K w =
      canonicalRep (coxeterSystem τ) K ((coxeterSystem τ).simple i * w) := by
  rw [weylElt_mul_canonicalRep]
  split_ifs
  · rfl
  · rw [neg_one_units_charTwo, torusElt_one, one_mul]

theorem canonicalRep_wordProd_mul_charTwo
    (ω : List (Fin τ.rank)) (v : WeylGroup τ) :
    canonicalRep (coxeterSystem τ) K ((coxeterSystem τ).wordProd ω * v) =
      (ω.map fun i => weylElt τ K i 1).prod * canonicalRep (coxeterSystem τ) K v := by
  induction ω with
  | nil => rw [CoxeterSystem.wordProd_nil, one_mul, List.map_nil, List.prod_nil, one_mul]
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_assoc, ← weylElt_mul_canonicalRep_charTwo, ih,
      List.map_cons, List.prod_cons, mul_assoc]

theorem canonicalRep_mul_charTwo
    (w v : WeylGroup τ) :
    canonicalRep (coxeterSystem τ) K (w * v) =
      canonicalRep (coxeterSystem τ) K w * canonicalRep (coxeterSystem τ) K v := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  rw [canonicalRep_wordProd_mul_charTwo, canonicalRep_wordProd hω]

theorem canonicalRep_mul_self_charTwo
    {w : WeylGroup τ} (hw : w * w = 1) :
    canonicalRep (coxeterSystem τ) K w * canonicalRep (coxeterSystem τ) K w = 1 := by
  rw [← canonicalRep_mul_charTwo, hw, canonicalRep_one]

end CharTwo

section LargeReeBlocks

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

omit [Finite K] in
theorem canonicalRep_fixedOrbitElement_mul_self
    (j : Fin F4.fixedOrbitCount) :
    canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) *
      canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) = 1 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  exact canonicalRep_mul_self_charTwo (fixedOrbitElement_mul_self j)

theorem exists_canonicalRep_fixedOrbitElement_eq
    (j : Fin F4.fixedOrbitCount) :
    ∃ m ∈ F4.reeLocalBlock K a j, ∃ h ∈ F4.reeFixedTorus K a,
      ∃ x ∈ F4.reeFixedOrbitUnipotent K a j,
        canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) = m * (h * x) := by
  obtain ⟨m, hm, hmn⟩ := exists_mem_reeLocalBlock_mk_eq (K := K) (a := a) j
  have hb : m⁻¹ * canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈
      F4.reeFixedBorel K a := QuotientGroup.eq.1 hmn
  have hbL : m⁻¹ * canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈
      rootLevi F4.tag K (F4.fixedOrbitSet j) :=
    mul_mem (inv_mem (reeLocalBlock_le_rootLevi j hm))
      (canonicalRep_mem_rootLevi (fixedOrbitElement_mem_fixedOrbitWeyl j))
  obtain ⟨h, hh, x, hx, hhx⟩ := exists_mul_of_mem_rootLevi_of_mem_reeFixedBorel hbL hb
  exact ⟨m, hm, h, hh, x, hx, by rw [← hhx, mul_inv_cancel_left]⟩

theorem canonicalRep_fixedOrbitElement_mem_reeLocalBlock
    (j : Fin F4.fixedOrbitCount) :
    canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈
      F4.reeLocalBlock K a j := by
  obtain ⟨m, hm, h, hh, x, hx, hnmhx⟩ := exists_canonicalRep_fixedOrbitElement_eq (a := a) (K := K) j
  have : CharP K 2 := ‹CharP K F4.prime›
  have hxh : h * x * h⁻¹ ∈ F4.reeLocalBlock K a j :=
    reeFixedOrbitUnipotent_le_reeLocalBlock j
      ((Subgroup.mem_normalizer_iff.1 (reeFixedTorus_le_normalizer_reeFixedOrbitUnipotent j hh) x).1
        hx)
  obtain ⟨m', hm'M, hnm'⟩ : ∃ m' ∈ F4.reeLocalBlock K a j,
      canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) = m' * h :=
    ⟨m * (h * x * h⁻¹), mul_mem hm hxh, by rw [hnmhx]; group⟩
  have hnN : canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈
      Subgroup.normalizer (F4.reeLocalBlock K a j : Set (ModGL F4.tag K)) := by
    rw [hnm']
    exact mul_mem (Subgroup.le_normalizer hm'M) (reeFixedTorus_le_normalizer_reeLocalBlock j hh)
  have hsq := canonicalRep_fixedOrbitElement_mul_self (K := K) j
  have hh2 : h * h ∈ F4.reeLocalBlock K a j := by
    have e : h * h = m'⁻¹ * (canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) * m'⁻¹ *
        (canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j))⁻¹) *
        (canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) *
          canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j)) := by
      have hh' : h = m'⁻¹ * canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) := by
        rw [hnm']; group
      conv_lhs => rw [hh']
      group
    rw [e, hsq, mul_one]
    exact mul_mem (inv_mem hm'M) ((Subgroup.mem_normalizer_iff.1 hnN m'⁻¹).1 (inv_mem hm'M))
  have hhT : h ∈ torusGroup F4.tag K := (Subgroup.mem_inf.1 hh).1
  have hodd : ¬ 2 ∣ orderOf h := by
    intro h2
    exact not_dvd_card_torusGroup (τ := F4.tag) (K := K) 2
      (h2.trans (Subgroup.orderOf_dvd_natCard _ hhT))
  have hhM : h ∈ F4.reeLocalBlock K a j := by
    obtain ⟨k, hk⟩ : Odd (orderOf h) := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hodd)
    have hpow : h ^ orderOf h = 1 := pow_orderOf_eq_one h
    have e : (h * h) ^ (k + 1) = h := by
      rw [← sq, ← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, ← hk, hpow,
        one_mul]
    rw [← e]
    exact pow_mem hh2 (k + 1)
  rw [hnm']
  exact mul_mem hm'M hhM

end LargeReeBlocks

end CFSG.QuasithinUnique.Setup.X6
