module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.ComponentClassification.CatLeafProof.X10Sp

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Open CFSG.ComponentClassification.CatLeaf
open Subgroup

theorem lieOrder_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp) (hp2 : p ≠ 2) (hn : n ≠ 0) (h : LieModel X t n p f) :
    Nat.card X * lieOrderDivisor t n (p ^ f) = lieOrderNumerator t n (p ^ f) ∧
      (Nat.card X).factorization p = lieSylowExponent t n * f := by
  have hadm : StatedLieAdmissible t n p f := (GH74.statedClassicalModel_of_lieModel hn h).1
  have hp : p.Prime := hadm.1
  have hc : Nat.card X = lieOrderNumerator t n (p ^ f) / lieOrderDivisor t n (p ^ f) := by
    rcases ht with rfl | rfl | rfl
    · rw [GH74.card_of_lieModel_PSL hn h, ordA, Nat.sub_add_cancel (by omega : 1 ≤ n),
        mul_comm (n - 1) n]
      rfl
    · rw [GH74.card_of_lieModel_PSU hn hp2 h, ordTwistedA, Nat.sub_add_cancel (by omega : 1 ≤ n),
        mul_comm (n - 1) n, Finset.prod_congr rfl fun i _ =>
          toNat_pow_sub_neg_one_pow (Nat.one_le_pow _ _ hp.pos) i]
      rfl
    · rw [GH74.card_of_lieModel_PSp hn hp2 h, ordBC, ← sq]
      rfl
  have hmul : Nat.card X * lieOrderDivisor t n (p ^ f) = lieOrderNumerator t n (p ^ f) := by
    rw [hc, Nat.div_mul_cancel (lieOrderDivisor_dvd_numerator hadm)]
  have hnum : lieOrderNumerator t n (p ^ f) ≠ 0 := by
    rw [lieOrderNumerator_eq hadm]
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hp.ne_zero)) (lieOrderCofactor_ne_zero hadm)
  have hX : Nat.card X ≠ 0 := fun h0 => hnum (by rw [← hmul, h0, zero_mul])
  refine ⟨hmul, ?_⟩
  have hfac := congrArg (fun m => m.factorization p) hmul
  rwa [Nat.factorization_mul hX (lieOrderDivisor_ne_zero hadm), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (not_dvd_lieOrderDivisor hadm), add_zero,
    factorization_lieOrderNumerator hadm] at hfac

theorem lieOrder_of_two_lieModels {Y : Type} [Group Y] {t t' : StatedLieTag} {n n' p e e' : ℕ}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp) (ht' : t' = .PSL ∨ t' = .PSU ∨ t' = .PSp)
    (hp2 : p ≠ 2) (hn : n ≠ 0) (hn' : n' ≠ 0) (h : LieModel Y t n p e)
    (h' : LieModel Y t' n' p e') :
    Nat.card Y * lieOrderDivisor t n (p ^ e) = lieOrderNumerator t n (p ^ e) ∧
      Nat.card Y * lieOrderDivisor t' n' (p ^ e') = lieOrderNumerator t' n' (p ^ e') ∧
        lieSylowExponent t n * e = lieSylowExponent t' n' * e' := by
  obtain ⟨h1, h1p⟩ := lieOrder_of_lieModel ht hp2 hn h
  obtain ⟨h2, h2p⟩ := lieOrder_of_lieModel ht' hp2 hn' h'
  exact ⟨h1, h2, h1p.symm.trans h2p⟩

theorem isSimpleGroup_of_lieModel_psl {X : Type} [Group X] {n p f : ℕ} (hn : n ≠ 0)
    (h : LieModel X .PSL n p f) : IsSimpleGroup X :=
  (LieType.Simplicity.fam_PSL_simplicity X n p f (GH74.statedClassicalModel_of_lieModel hn h)).2

theorem eq_one_of_mem_center {L : Type*} [Group L] [Finite L] (hZO : center L = pPrimeCore 2 L)
    {z : L} (hz : z ∈ center L) (hzz : z * z = 1) : z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop := LocalAnalysis.ComponentInitial.coprime_orderOf_of_mem_pPrimeCore (p := 2)
    (hZO ▸ hz)
  have h2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hzz])
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop.symm h2)

end CFSG.ComponentClassification.CatLeafProof.X10Sp
