module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinCk
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Schreier.Outer

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinCk

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  Certificates.BTFinCk

variable {n : ℕ}

theorem le_card_of_centFourOK (hn : n < 2 ^ 32) {gens : List Table}
    {gg : ℕ → Equiv.Perm (Fin n)} {K : Subgroup (Equiv.Perm (Fin n))}
    (hg : ∀ l < gens.length, Rep n gens[l]! (gg l) ∧ gg l ∈ K) {a : Table} {ord cap bound : ℕ}
    (h : centFourOK n gens a ord cap bound = true) : ord ≤ Nat.card K := by
  classical
  simp only [centFourOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨htree, hdist⟩, hsize⟩, -⟩ := h
  set CL := mulClosureH n gens.toArray cap with hCL
  have hg' : ∀ l < gens.toArray.size, Rep n gens.toArray[l]! (gg l) ∧ gg l ∈ K := by
    intro l hl
    have hl' : l < gens.length := by simpa using hl
    have := hg l hl'
    simpa [List.getElem!_toArray] using this
  have hmem := mulTreeOK_spec hn K hg' htree
  have hrep : ∀ k < CL.1.size, Rep n CL.1[k]! (tablePerm n CL.1[k]!) ∧
      tablePerm n CL.1[k]! ∈ K := by
    intro k hk
    obtain ⟨c, hc, hr⟩ := hmem k hk
    rw [tablePerm_eq hr]
    exact ⟨hr, hc⟩
  have hF : List.Forall₂ (Rep n) CL.1.toList (CL.1.toList.map (tablePerm n)) := by
    rw [List.forall₂_map_right_iff]
    refine List.forall₂_same.2 fun T hT => ?_
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hT
    rw [Array.length_toList] at hk
    have := (hrep k hk).1
    rwa [Array.getElem_toList, ← getElem!_pos CL.1 k hk]
  have hnd := nodup_of_hkeysDistinct hF hdist
  have := Fintype.ofFinite ↥K
  let f : Fin CL.1.size → K := fun k => ⟨tablePerm n CL.1[k.val]!, (hrep k k.2).2⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hij' : tablePerm n CL.1[i.val]! = tablePerm n CL.1[j.val]! := congrArg Subtype.val hij
    have hi' : i.val < (CL.1.toList.map (tablePerm n)).length := by simp
    have hj' : j.val < (CL.1.toList.map (tablePerm n)).length := by simp
    refine Fin.ext ((List.Nodup.getElem_inj_iff hnd (hi := hi') (hj := hj')).mp ?_)
    simpa [getElem!_pos CL.1 i.val i.2, getElem!_pos CL.1 j.val j.2] using hij'
  have hle := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin, ← Nat.card_eq_fintype_card] at hle
  rw [← hsize]
  exact hle

theorem centralizerIn_eq_of_ge {M : Type*} [Group M] (H : Subgroup M) [Finite H] (u : M)
    {K : Subgroup M} (hK : K ≤ centralizerIn H u) {c ord : ℕ}
    (hc : c ≤ (CFSG.Sporadic.Schreier.conjClass H u).ncard)
    (hcard : c * ord = Nat.card H) (hord : ord ≤ Nat.card K) :
    centralizerIn H u = K ∧ Nat.card K = ord := by
  have hos := CFSG.Sporadic.Schreier.ncard_conjClass_mul_card H u
  have hfin : Finite (centralizerIn H u) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  have hKC : Nat.card K ≤ Nat.card (centralizerIn H u) := Subgroup.card_le_of_le hK
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h, zero_mul] at hcard; omega
    · exact h
  have hle : Nat.card (centralizerIn H u) ≤ ord := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 : c * ord < c * Nat.card (centralizerIn H u) := Nat.mul_lt_mul_of_pos_left hlt hc0
    have h2 : c * Nat.card (centralizerIn H u) ≤
        (CFSG.Sporadic.Schreier.conjClass H u).ncard * Nat.card (centralizerIn H u) :=
      Nat.mul_le_mul_right _ hc
    omega
  exact ⟨(Subgroup.eq_of_le_of_card_ge hK (by omega)).symm, by omega⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinCk
