module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3
public import CFSG.GH74.KGroups.Generic2
public import Certificates.Certificate919240
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3CheckInputs

public section

namespace CFSG.CGT.Foote82.Proof511

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Certificates CFSG.ComponentClassification.J2Cover
  CFSG.ClassicalInvolution.J3Proof CFSG.ClassicalInvolution.J3Data

namespace J3Syl

private theorem invoOK_iff_sq {n : ℕ} {T : Table} {g : Equiv.Perm (Fin n)} (hT : Rep n T g) :
    invoOK n T = true ↔ g ^ 2 = 1 := by
  constructor
  · intro h
    refine perm_faithful _ fun i => Fin.ext ?_
    have := idx_sq_of_invoOK hT h i.val i.2
    rw [idx_of_lt _ i.2] at this
    exact this
  · intro h
    rw [invoOK, allIn_eq_true]
    intro i _ hi
    rw [beq_iff_eq, hT i hi, hT _ (idx_lt g hi), ← idx_mul, ← pow_two, h, idx_one]

theorem card_sq_sChain :
    Nat.card {x : sChain.originalSubgroup // (x : Equiv.Perm (Fin 20520)) ^ 2 = 1} = 36 := by
  have hQ : ValidSchreier sChain := ofArrays_valid (by norm_num) sChain_ok
  have hn : (20520 : ℕ) < 2 ^ 32 := by norm_num
  have hcount : Nat.card {x : sChain.originalSubgroup // (x : Equiv.Perm (Fin 20520)) ^ 2 = 1} =
      countProducts 20520 (invoOK 20520) (levelTables sChain) (idT 20520) := by
    rw [countProducts_spec (fun T g hT => invoOK_iff_sq hT) (forall₂_levelTables hn sChain)
        (Rep.idT hn),
      card_subtype_eq_countP sChain.originalSubgroup (enumeration sChain)
        (enumeration_nodup sChain hQ) (mem_enumeration_iff sChain hQ)
        fun g : Equiv.Perm (Fin 20520) => g ^ 2 = 1]
    simp only [one_mul, List.map_id']
    rfl
  rw [hcount, sChain, ofArrays_levelTables sChain_ok]
  exact Certificates.certificate919240

end J3Syl

open J3Syl in
theorem sqOne_card_J3
    {Y : Type} [Group Y] [Finite Y]
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic Y .J3) (P : Sylow 2 Y) :
    Nat.card {x : ↥(P : Subgroup Y) // x ^ 2 = 1} = 36 := by
  obtain ⟨e⟩ := h
  have e₀ : Y ≃* CFSG.Blueprint.NativeSporadic.J3 := e
  have hY : Nat.card Y = 2 ^ 7 * 392445 := by
    rw [Nat.card_congr e₀.toEquiv, CFSG.Sporadic.J3.card_J3]
    norm_num
  obtain ⟨φ⟩ := CFSG.GH74.KGroups.sylow_equiv_of_model P3 (e₀.trans nativeEquivP3)
    sChain.originalSubgroup sChain_le_P3 (by rw [card_sChain]; norm_num) hY (by decide)
    (P : Subgroup Y) P.isPGroup' P.not_dvd_index
  rw [← card_sq_sChain]
  refine Nat.card_congr (φ.toEquiv.subtypeEquiv fun x => ?_)
  rw [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ← SubmonoidClass.coe_pow,
    OneMemClass.coe_eq_one, ← map_pow, MulEquiv.map_eq_one_iff]

end CFSG.CGT.Foote82.Proof511
