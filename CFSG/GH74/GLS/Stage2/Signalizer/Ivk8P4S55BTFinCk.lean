module

public import Certificates.Data.GH74.BTFinCk
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.Sporadic.Schreier.MathieuOddCoreOuter

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinCk

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  Certificates.BTFinCk

variable {n : ℕ}

theorem complete_of_card {K : Subgroup (Equiv.Perm (Fin n))} {m : ℕ}
    {e : ℕ → Equiv.Perm (Fin n)} (hK : ∀ k < m, e k ∈ K)
    (hd : ∀ i < m, ∀ j < m, e i = e j → i = j) (hc : m = Nat.card K) :
    ∀ g ∈ K, ∃ k < m, g = e k := by
  classical
  have := Fintype.ofFinite ↥K
  let f : Fin m → K := fun k => ⟨e k, hK k k.2⟩
  have hf : Function.Injective f := fun i j h =>
    Fin.ext (hd i i.2 j j.2 (congrArg Subtype.val h))
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr
      ⟨hf, by rw [Fintype.card_fin, hc, Nat.card_eq_fintype_card]⟩
  intro g hg
  obtain ⟨k, hk⟩ := hbij.2 ⟨g, hg⟩
  exact ⟨k, k.2, (congrArg Subtype.val hk).symm⟩

theorem card_centralizer_eq_count {K : Subgroup (Equiv.Perm (Fin n))} {L : Array Table}
    {e : ℕ → Equiv.Perm (Fin n)} (hL : ∀ k < L.size, Rep n L[k]! (e k) ∧ e k ∈ K)
    (hd : ∀ i < L.size, ∀ j < L.size, e i = e j → i = j)
    (hall : ∀ g ∈ K, ∃ k < L.size, g = e k) {w : Equiv.Perm (Fin n)} {wT : Table}
    (hw : Rep n wT w) :
    Nat.card ↥(K ⊓ centralizer ({w} : Set (Equiv.Perm (Fin n)))) = commCount n L wT := by
  classical
  have hcomm : ∀ k < L.size, commT n L[k]! wT = true ↔ e k * w = w * e k := fun k hk =>
    commT_iff (hL k hk).1 hw
  let f : {k : ℕ // k < L.size ∧ commT n L[k]! wT = true} →
      ↥(K ⊓ centralizer ({w} : Set (Equiv.Perm (Fin n)))) := fun k =>
    ⟨e k.1, (hL k.1 k.2.1).2, mem_centralizer_singleton_iff.mpr ((hcomm k.1 k.2.1).mp k.2.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun i j h => Subtype.ext (hd i.1 i.2.1 j.1 j.2.1 (congrArg Subtype.val h)),
      fun y => ?_⟩
    obtain ⟨k, hk, hyk⟩ := hall y y.2.1
    have hc : commT n L[k]! wT = true := (hcomm k hk).mpr (by
      rw [← hyk]
      exact mem_centralizer_singleton_iff.mp y.2.2)
    exact ⟨⟨k, hk, hc⟩, Subtype.ext hyk.symm⟩
  have h2 := Nat.count_eq_card_fintype (fun k => commT n L[k]! wT = true) L.size
  rw [Fintype.card_eq_nat_card] at h2
  rw [← Nat.card_congr (Equiv.ofBijective f hf), ← h2, Nat.count, commCount]
  simp

theorem invoOK_of_mul_self {T : Table} {w : Equiv.Perm (Fin n)} (hT : Rep n T w)
    (hw : w * w = 1) : invoOK n T = true := by
  rw [invoOK, allIn_eq_true]
  intro i _ hi
  rw [beq_iff_eq, hT i hi, hT _ (idx_lt w hi), ← idx_mul, hw, idx_one]

theorem centFourOK_spec (hn : n < 2 ^ 32) {gens : List Table} {gg : ℕ → Equiv.Perm (Fin n)}
    {K : Subgroup (Equiv.Perm (Fin n))}
    (hg : ∀ l < gens.length, Rep n gens[l]! (gg l) ∧ gg l ∈ K) {a : Table}
    {t : Equiv.Perm (Fin n)} (ha : Rep n a t) {ord cap bound : ℕ} (hord : Nat.card K = ord)
    (h : centFourOK n gens a ord cap bound = true) :
    ∀ w ∈ K, w * w = 1 → w ≠ 1 → w ≠ t →
      Nat.card ↥(K ⊓ centralizer ({w} : Set (Equiv.Perm (Fin n)))) ∣ bound := by
  simp only [centFourOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨htree, hdist⟩, hsize⟩, hfour⟩ := h
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
  have hd : ∀ i < CL.1.size, ∀ j < CL.1.size,
      tablePerm n CL.1[i]! = tablePerm n CL.1[j]! → i = j := by
    intro i hi j hj hij
    have hi' : i < (CL.1.toList.map (tablePerm n)).length := by simpa using hi
    have hj' : j < (CL.1.toList.map (tablePerm n)).length := by simpa using hj
    refine (List.Nodup.getElem_inj_iff hnd (i := i) (j := j) (hi := hi') (hj := hj')).mp ?_
    simpa [getElem!_pos CL.1 i hi, getElem!_pos CL.1 j hj] using hij
  have hall := complete_of_card (m := CL.1.size) (fun k hk => (hrep k hk).2) hd
    (by rw [hsize, hord])
  intro w hw hww hw1 hwt
  obtain ⟨k, hk, rfl⟩ := hall w hw
  have hfk := (allIn_eq_true.1 hfour) k (Nat.zero_le _) hk
  have hinvo : invoOK n CL.1[k]! = true := invoOK_of_mul_self (hrep k hk).1 hww
  have hid : tblEq n CL.1[k]! (idT n) = false := by
    by_contra hc
    rw [Bool.not_eq_false] at hc
    exact hw1 (rep_unique (hrep k hk).1 (rep_of_tblEq (Rep.idT hn) hc))
  have hat : tblEq n CL.1[k]! a = false := by
    by_contra hc
    rw [Bool.not_eq_false] at hc
    exact hwt (rep_unique (hrep k hk).1 (rep_of_tblEq ha hc))
  simp only [hinvo, hid, hat, Bool.not_true, Bool.false_or, beq_iff_eq] at hfk
  rw [card_centralizer_eq_count hrep hd hall (hrep k hk).1]
  exact Nat.dvd_of_mod_eq_zero hfk

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinCk
