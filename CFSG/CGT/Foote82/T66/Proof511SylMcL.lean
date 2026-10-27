module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.McL
public import CFSG.GH74.KGroups.Generic2
public import Certificates.Certificate919241

public section

namespace CFSG.CGT.Foote82.Proof511

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.ClassicalInvolution.McLData CFSG.ClassicalInvolution.McLProof

namespace McLSyl

private theorem invoOK_iff_sq {n : ℕ} {T : Table} {g : Equiv.Perm (Fin n)} (hT : Rep n T g) :
    invoOK n T = true ↔ g ^ 2 = 1 := by
  constructor
  · exact sq_eq_one_of_invoOK hT
  · intro h
    rw [invoOK, allIn_eq_true]
    intro i _ hi
    rw [beq_iff_eq, hT i hi, hT _ (idx_lt g hi), ← idx_mul, ← pow_two, h, idx_one]

theorem card_sq_S : Nat.card {x : S // (x : Equiv.Perm (Fin 275)) ^ 2 = 1} = 36 := by
  obtain ⟨-, hrep, hcov, hdist⟩ := enumOK_spec hn sgens_perm sylow_check.1
  set E := (mulClosureH 275 sgens.toArray capK).1 with hE
  have hnodup := nodup_of_hkeysDistinct (forall₂_tablePerm fun k hk => (hrep k hk).1) hdist
  have hmemL : ∀ g, g ∈ E.toList.map (tablePerm 275) ↔ g ∈ S := by
    intro g
    constructor
    · intro hg
      obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm (fun k hk => (hrep k hk).1) hg
      exact (hrep k hk).2
    · intro hg
      obtain ⟨k, hk, hkrep⟩ := hcov g hg
      refine List.mem_map.mpr ⟨E[k]!, ?_, tablePerm_eq hkrep⟩
      rw [getElem!_pos E k hk]
      exact Array.mem_toList_iff.mpr (Array.getElem_mem hk)
  rw [card_subtype_eq_countP S (E.toList.map (tablePerm 275)) hnodup hmemL
    fun g : Equiv.Perm (Fin 275) => g ^ 2 = 1, List.countP_map,
    ← Certificates.certificate919241, sqOneCount]
  apply List.countP_congr
  intro T hT
  obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hT)
  have hk' := (hrep k hk).1
  rw [getElem!_pos E k hk] at hk'
  simp only [Function.comp_apply, decide_eq_true_eq]
  exact (invoOK_iff_sq hk').symm

end McLSyl

theorem sqOne_card_McL
    {Y : Type} [Group Y] [Finite Y]
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic Y .McL) (P : Sylow 2 Y) :
    Nat.card {x : ↥(P : Subgroup Y) // x ^ 2 = 1} = 36 := by
  obtain ⟨e⟩ := h
  have e₀ : Y ≃* CFSG.Blueprint.NativeSporadic.McL := e
  have hY : Nat.card Y = 2 ^ 7 * 7016625 := by
    rw [Nat.card_congr e₀.toEquiv, CFSG.Sporadic.McL.card_McL]
    norm_num
  obtain ⟨φ⟩ := CFSG.GH74.KGroups.sylow_equiv_of_model CFSG.ClassicalInvolution.McLProof.P
    (e₀.trans mclEquivP) S (S_le_K.trans K_le_P) (by rw [card_S]; norm_num) hY (by decide)
    (P : Subgroup Y) P.isPGroup' P.not_dvd_index
  rw [← McLSyl.card_sq_S]
  refine Nat.card_congr (φ.toEquiv.subtypeEquiv fun x => ?_)
  rw [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ← SubmonoidClass.coe_pow,
    OneMemClass.coe_eq_one, ← map_pow, MulEquiv.map_eq_one_iff]

end CFSG.CGT.Foote82.Proof511
