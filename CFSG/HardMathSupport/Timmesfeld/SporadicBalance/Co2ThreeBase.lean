
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2ThreeInputs
public import CFSG.Sporadic.Co2Cert.Order
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import Certificates.Data.ExceptionalSL3

@[expose] public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.Native CFSG.RankThree.PartOne
  CFSG.Sporadic.Co2Cert CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu
  CFSG.Sporadic.Schreier.Co3.Native CFSG.RankThree.PartTwo.Sec4.Item434SporE81

section Facts

end Facts

section Chain

theorem mem_co2P_of_inP {g : Array ℕ} {G : Equiv.Perm (Fin 2300)} (hG : Rep 2300 g G)
    (h : inP (levels ()) g = true) : G ∈ co2P := by
  rw [← co2Q_originalSubgroup]
  exact (siftA_iff_mem_originalSubgroup co2Q_chainArrays (by norm_num) co2Chain_check.1 hG).1 h

end Chain

theorem qKeys_lt : ∀ q ∈ co2E81.qKeys, q < 2300 := by decide

theorem factorization_card_co2P_three :
    (Nat.card co2P).factorization 3 = 6 := by
  rw [card_co2P, show (42305421312000 : ℕ) = 3 ^ 6 * 58032128000 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

def vec (k : ℕ) : Fin 4 → ZMod 3 := fun i => (digit3 k i : ZMod 3)

theorem vec_val (k : ℕ) (i : Fin 4) : (vec k i).val = digit3 k i := by
  rw [vec, ZMod.val_natCast]
  unfold digit3
  exact Nat.mod_mod _ _

def idx (a : Fin 4 → ZMod 3) : ℕ :=
  (a 0).val + 3 * (a 1).val + 9 * (a 2).val + 27 * (a 3).val

theorem idx_lt (a : Fin 4 → ZMod 3) : idx a < 81 := by
  have h0 := ZMod.val_lt (a 0)
  have h1 := ZMod.val_lt (a 1)
  have h2 := ZMod.val_lt (a 2)
  have h3 := ZMod.val_lt (a 3)
  unfold idx
  omega

theorem digit3_idx (a : Fin 4 → ZMod 3) (i : Fin 4) : digit3 (idx a) i = (a i).val := by
  have h0 := ZMod.val_lt (a 0)
  have h1 := ZMod.val_lt (a 1)
  have h2 := ZMod.val_lt (a 2)
  have h3 := ZMod.val_lt (a 3)
  fin_cases i <;> simp only [digit3, idx, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    pow_zero, pow_one, Nat.reducePow, Nat.div_one] <;> omega

theorem vec_idx (a : Fin 4 → ZMod 3) : vec (idx a) = a := by
  funext i
  rw [vec, digit3_idx, ZMod.natCast_zmod_val]

theorem idx_eq_zero_iff (a : Fin 4 → ZMod 3) : idx a = 0 ↔ a = 0 := by
  constructor
  · intro h
    rw [← vec_idx a, h]
    funext i
    simp [vec, digit3]
  · rintro rfl
    simp [idx]

noncomputable def dPerm (i : Fin 4) : Equiv.Perm (Fin 2300) :=
  permOfArr 2300 (dGens ())[(i : ℕ)]!

section D

theorem vecProd_eq (a : Fin 4 → ZMod 3) : Co3T.vecProd dPerm a =
    dPerm 0 ^ (a 0).val * (dPerm 1 ^ (a 1).val * (dPerm 2 ^ (a 2).val * dPerm 3 ^ (a 3).val)) := by
  simp [Co3T.vecProd, List.finRange_succ]

end D

theorem dot3_eq_zero_iff (a : Fin 4 → ZMod 3) (k : ℕ) :
    dot3 (idx a) k = 0 ↔ ∑ i, a i * vec k i = 0 := by
  have hc : ∀ i : Fin 4, ((digit3 (idx a) i * digit3 k i : ℕ) : ZMod 3) = a i * vec k i := by
    intro i
    rw [Nat.cast_mul, digit3_idx, ZMod.natCast_zmod_val]
    rfl
  rw [Fin.sum_univ_four, ← hc 0, ← hc 1, ← hc 2, ← hc 3]
  simp only [← Nat.cast_add, ZMod.natCast_eq_zero_iff]
  unfold dot3
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
  exact Nat.dvd_iff_mod_eq_zero.symm

section HypCard

end HypCard

section DCore

theorem isPGroup_of_map_le {K : Subgroup ↥co2P} {X : Subgroup (Equiv.Perm (Fin 2300))}
    (hX : IsPGroup 3 ↥X) (hK : ∀ c ∈ K, (c : Equiv.Perm (Fin 2300)) ∈ X) : IsPGroup 3 ↥K :=
  (hX.comap_of_injective co2P.subtype co2P.subtype_injective).to_le fun c hc => hK c hc

end DCore

section Fusion

end Fusion

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Blueprint CFSG.Sporadic.Co2Cert

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
