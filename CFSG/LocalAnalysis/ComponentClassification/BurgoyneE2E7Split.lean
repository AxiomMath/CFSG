module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2Three
public import CFSG.LieType.AlgebraicGroups.RationalInnerInvolution

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)
open CFSG.LieType.AlgebraicGroups (signMaskTuple)

@[expose] def e7BitsThree : Fin (Tag.rank .E7) → Bool :=
  listMask [true, true, false, false, false, false, false]

theorem e7SignOrbit_bitsSix_entry : ∀ e ∈ e7SignOrbit,
    e.1 = [false, false, false, false, false, false, true] → e.2.1 = 3 := by
  decide +kernel

theorem ofFn_e7BitsSix :
    List.ofFn e7BitsSix = [false, false, false, false, false, false, true] := by
  decide

theorem signMaskTuple_one {K : Type} [Field K] :
    signMaskTuple .E7 K 1 = bitsTuple e7BitsOne := by
  funext j
  fin_cases j <;> simp [signMaskTuple, bitsTuple, e7BitsOne, listMask]

theorem signMaskTuple_two {K : Type} [Field K] :
    signMaskTuple .E7 K 2 = bitsTuple e7BitsTwo := by
  funext j
  fin_cases j <;> simp [signMaskTuple, bitsTuple, e7BitsTwo, listMask]

theorem signMaskTuple_three {K : Type} [Field K] :
    signMaskTuple .E7 K 3 = bitsTuple e7BitsThree := by
  funext j
  fin_cases j <;> simp [signMaskTuple, bitsTuple, e7BitsThree, listMask]


theorem e7SignOrbit_bitsSix {K : Type} [Field K] (hK : ringChar K ≠ 2) :
    ∃ w : WeylGroup .E7, ∀ v : Fin (Tag.rank .E7) → ℤ,
      rootChar (bitsTuple (K := K) e7BitsSix) (w • v) =
        rootChar (bitsTuple (K := K) e7BitsThree) v := by
  obtain ⟨e, he, he1, -, hact⟩ := e7SignOrbit_check e7BitsSix
  have hρ : e.2.1 = 3 := e7SignOrbit_bitsSix_entry e he (he1.trans ofFn_e7BitsSix)
  set w := (coxeterSystem .E7).wordProd (toFinWord e.2.2) with hw
  have hconj : ∀ v : Fin (Tag.rank .E7) → ℤ, maskChar e7BitsSix (Multiplicative.ofAdd v) =
      maskChar e7BitsThree (Multiplicative.ofAdd (w⁻¹ • v)) := by
    intro v
    rw [← List.ofFn_injective hact, maskChar_maskAct, hρ]
    rfl
  refine ⟨w, fun v => ?_⟩
  rw [rootChar_eq_intUnitsMap hK (bitsTuple_mem _), rootChar_eq_intUnitsMap hK (bitsTuple_mem _),
    signTupleBits_bitsTuple hK, signTupleBits_bitsTuple hK, hconj (w • v), inv_smul_smul]

theorem exists_conj_rootDiagAut_three {K : Type} [Field K] (hK : ringChar K ≠ 2) :
    ∃ n : adjointGroup .E7 K, rootDiagAut .E7 K (bitsTuple e7BitsThree) =
      MulAut.conj n * rootDiagAut .E7 K (bitsTuple e7BitsSix) * (MulAut.conj n)⁻¹ := by
  obtain ⟨w, hw⟩ := e7SignOrbit_bitsSix (K := K) hK
  have hd := (rootDiagUnit_eq_conj_canonicalRep_iff (K := K) (bitsTuple e7BitsSix)
    (bitsTuple e7BitsThree) w).2 hw
  set N := canonicalRep (coxeterSystem .E7) K w with hN
  refine ⟨⟨N, canonicalRep_mem_adjointGroup (coxeterSystem .E7) K w⟩⁻¹,
    MulEquiv.ext fun g => Subtype.ext ?_⟩
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, coe_rootDiagAut,
    Subgroup.coe_mul, InvMemClass.coe_inv, inv_inv]
  rw [hd]
  group

theorem burgRow_E7_split {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) {m : ℕ} (hm : m = 1 ∨ m = 2 ∨ m = 3) :
    BurgCoreFor (rootDiagAut .E7 K (signMaskTuple .E7 K m)) ∨
      BurgTorusFor (rootDiagAut .E7 K (signMaskTuple .E7 K m)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
    (one_le_and_three_le_of_card hp hp2 hK).1 hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  rcases hm with rfl | rfl | rfl
  · exact Or.inl (by rw [signMaskTuple_one]; exact burgCoreFor_E7_t1 hK2)
  · exact Or.inl (by rw [signMaskTuple_two]; exact burgCoreFor_E7_t4 hK2)
  · rw [signMaskTuple_three]
    obtain ⟨n, hn⟩ := exists_conj_rootDiagAut_three (K := K) hK2
    rw [hn]
    obtain ⟨-, h3⟩ := one_le_and_three_le_of_card hp hp2 hK
    have hodd : Odd (Nat.card K) := by
      rw [hK]
      exact (hp.eq_two_or_odd'.resolve_left hp2).pow
    rcases Nat.lt_or_ge (Nat.card K) 5 with h | h
    · have hc3 : Nat.card K = 3 := by
        obtain ⟨k, hk⟩ := hodd
        omega
      exact Or.inl ((burgCoreFor_E7_t7_three hc3).conj _)
    · exact Or.inr ((burgTorusFor_E7_t7 hp hp2 hK h).conj _)

end CFSG.ComponentClassification.Burgoyne.E2
