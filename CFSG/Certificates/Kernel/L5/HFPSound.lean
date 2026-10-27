module

public import Certificates.Data.Kernel.L5.HFP

public section

namespace CFSG.Certificates.Kernel.L5H

open Equiv Perm CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.L5S
  CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.L5.HF CFSG.GH74.GLS.C3.Layer2.Model

theorem idxN_map (G : List (CV 16)) (x : CV 16) : idxN (G.map Subtype.val) x = G.idxOf x := by
  unfold idxN
  induction G with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.idxOf_cons, List.idxOf_cons, ih]
    have e : (a.1 == x.1) = (a == x) := by
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Subtype.ext_iff]
    rw [e]

theorem mem_map_val (G : List (CV 16)) (x : CV 16) : x.1 ∈ G.map Subtype.val ↔ x ∈ G := by
  rw [List.mem_map]
  constructor
  · rintro ⟨a, ha, e⟩
    rwa [Subtype.ext e] at ha
  · intro h
    exact ⟨x, h, rfl⟩

theorem mG_eq : mG = mulN mulGP := rfl

theorem covN_eq (x : CV 16) : covN (G72C.map Subtype.val) mulGP x = covC x := by
  unfold covN covC
  by_cases h : x ∈ G72C
  · rw [if_pos ((mem_map_val _ _).2 h), if_pos h]
    unfold covIdxN covIdx idx72
    simp only [idxN_map, mG_eq]
  · rw [if_neg (mt (mem_map_val _ _).1 h), if_neg h]

theorem cHatN_eq (x : CV 16) : cHatN (G72C.map Subtype.val) mulGP x = cHatC x := by
  unfold cHatN cHatC
  by_cases h : x ∈ G72C
  · rw [if_pos ((mem_map_val _ _).2 h), if_pos h]
    unfold idx72
    simp only [idxN_map, mG_eq]
  · rw [if_neg (mt (mem_map_val _ _).1 h), if_neg h]

theorem n24TailN_eq (x : CV 16) (o : List Nat) :
    n24TailN (G72C.map Subtype.val) mulGP x o = n24TailC x o := by
  unfold n24TailN n24TailC
  rw [covN_eq, covN_eq]

theorem n24EntryN_eq (x : CV 16) : n24EntryN (G72C.map Subtype.val) mulGP x = n24EntryC x := by
  unfold n24EntryN n24EntryC n24ChkN n24ChkC
  simp only [n24TailN_eq]

theorem famEntryN_eq (x : CV 16) : famEntryN (G72C.map Subtype.val) mulGP x = famEntryC x := by
  unfold famEntryN famEntryC
  rw [cHatN_eq, decide_eq_decide.2 (mem_map_val G72C x)]

theorem g72Pin {GN : List Nat} {MP : Nat} (h : g72PinChk GN MP = true) :
    GN = G72C.map Subtype.val ∧ MP = mulGP := by
  unfold g72PinChk at h
  rw [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.symm, (Nat.eq_of_beq_eq_true h.2).symm⟩

end CFSG.Certificates.Kernel.L5H

end
