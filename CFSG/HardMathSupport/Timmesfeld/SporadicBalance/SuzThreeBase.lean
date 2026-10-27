
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzThreeInputs
public import CFSG.Sporadic.SuzOddCore.SmallChain
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import Certificates.Data.ExceptionalSL3

@[expose] public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.Native CFSG.RankThree.PartOne
  CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu CFSG.Sporadic.Schreier.Co3.Native
  CFSG.RankThree.PartTwo.Sec4.Item434SporE81
open CFSG.Sporadic.SuzOddCore (suzM smallChain smallChain_arrays smallChain_check smallChain_valid
  smallChain_baseCount smallChain_originalSubgroup mem_suzM_iff_siftA suzM_card_chain
  smallStrongArrs smallBaseNat)

section Chain

theorem mem_suzM_of_inP {g : Array ℕ} {G : Equiv.Perm (Fin 1782)} (hG : Rep 1782 g G)
    (h : inP (levels ()) g = true) : G ∈ suzM :=
  (mem_suzM_iff_siftA hG).1 h

end Chain

@[expose] noncomputable def Qg : Subgroup (Equiv.Perm (Fin 1782)) :=
  Subgroup.closure (permsA 1782 (qGensS ()))

theorem factorization_card_suzM_three :
    (Nat.card suzM).factorization 3 = 7 := by
  rw [suzM_card_chain, show (448345497600 : ℕ) = 3 ^ 7 * 205004800 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

@[expose] def vec (k : ℕ) : Fin 5 → ZMod 3 := fun i => (digit3 k i : ZMod 3)

theorem vec_val (k : ℕ) (i : Fin 5) : (vec k i).val = digit3 k i := by
  rw [vec, ZMod.val_natCast]
  unfold digit3
  exact Nat.mod_mod _ _

@[expose] def idx (a : Fin 5 → ZMod 3) : ℕ :=
  (a 0).val + 3 * (a 1).val + 9 * (a 2).val + 27 * (a 3).val + 81 * (a 4).val

theorem idx_lt (a : Fin 5 → ZMod 3) : idx a < 243 := by
  have h0 := ZMod.val_lt (a 0)
  have h1 := ZMod.val_lt (a 1)
  have h2 := ZMod.val_lt (a 2)
  have h3 := ZMod.val_lt (a 3)
  have h4 := ZMod.val_lt (a 4)
  unfold idx
  omega

theorem digit3_idx (a : Fin 5 → ZMod 3) (i : Fin 5) : digit3 (idx a) i = (a i).val := by
  have h0 := ZMod.val_lt (a 0)
  have h1 := ZMod.val_lt (a 1)
  have h2 := ZMod.val_lt (a 2)
  have h3 := ZMod.val_lt (a 3)
  have h4 := ZMod.val_lt (a 4)
  fin_cases i <;> simp only [digit3, idx, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    pow_zero, pow_one, Nat.reducePow, Nat.div_one] <;> omega

theorem vec_idx (a : Fin 5 → ZMod 3) : vec (idx a) = a := by
  funext i
  rw [vec, digit3_idx, ZMod.natCast_zmod_val]

theorem idx_eq_zero_iff (a : Fin 5 → ZMod 3) : idx a = 0 ↔ a = 0 := by
  constructor
  · intro h
    rw [← vec_idx a, h]
    funext i
    simp [vec, digit3]
  · rintro rfl
    simp [idx]

@[expose] noncomputable def dPerm (i : Fin 5) : Equiv.Perm (Fin 1782) :=
  permOfArr 1782 (dGens ())[(i : ℕ)]!

section D

theorem vecProd_eq (a : Fin 5 → ZMod 3) : Co3T.vecProd dPerm a =
    dPerm 0 ^ (a 0).val * (dPerm 1 ^ (a 1).val * (dPerm 2 ^ (a 2).val *
      (dPerm 3 ^ (a 3).val * dPerm 4 ^ (a 4).val))) := by
  simp [Co3T.vecProd, List.finRange_succ]

end D

section DCore

theorem isPGroup_of_map_le {K : Subgroup ↥suzM} {X : Subgroup (Equiv.Perm (Fin 1782))}
    (hX : IsPGroup 3 ↥X) (hK : ∀ c ∈ K, (c : Equiv.Perm (Fin 1782)) ∈ X) : IsPGroup 3 ↥K :=
  (hX.comap_of_injective suzM.subtype suzM.subtype_injective).to_le fun c hc => hK c hc

end DCore

@[expose] noncomputable def yPerm : Equiv.Perm (Fin 1782) := permOfArr 1782 (yArr (levels ()))

theorem cKeys_lt : ∀ q ∈ cKeys, q < 1782 := by decide

section Cy

theorem centralizer_pow_two_eq {x : Equiv.Perm (Fin 1782)} (hx : x ^ 3 = 1) :
    Subgroup.centralizer ({x ^ 2} : Set (Equiv.Perm (Fin 1782))) = Subgroup.centralizer {x} := by
  apply le_antisymm
  · intro z hz
    have hz' : z * x ^ 2 = x ^ 2 * z := Subgroup.mem_centralizer_singleton_iff.1 hz
    have hx4 : x = (x ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hx, one_mul, pow_one]
    rw [Subgroup.mem_centralizer_singleton_iff, hx4]
    exact Commute.pow_right hz' 2
  · intro z hz
    have hz' : z * x = x * z := Subgroup.mem_centralizer_singleton_iff.1 hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Commute.pow_right hz' 2

end Cy

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT

