module

public import Certificates.Data.Kernel.Co1PW
public import CFSG.Certificates.Kernel.LocalCompCo1EndSound
public import CFSG.Certificates.Kernel.SporSch.Co1MatSound

public section

namespace CFSG.KC.Co1PW

open CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.Sporadic.Co1Schreier.Native CFSG.KC.Co1End
open CFSG.ComponentClassification.RankTwoSporadic.Co1

noncomputable abbrev rowsOf (M : Nat → Nat) (N : Nat) : List Rows :=
  (List.range N).map fun i => unpack 24 24 (M i)

theorem okK_iff {N k : Nat} : okK N k = true ↔ 1 ≤ k ∧ k ≤ N := by
  simp [okK]

theorem entryR_rows {M : Nat → Nat} {N k : Nat} (h : okK N k = true) :
    entryR (rowsOf M N) k = unpack 24 24 (M (k - 1)) := by
  rw [okK_iff] at h
  have hk : k - 1 < N := by omega
  simp [entryR, List.getD_eq_getElem?_getD, List.getElem?_range, hk]

theorem inv_of_dagK {M MI : Nat → Nat} {nb N : Nat} {ws : List (List Nat)}
    (h : dagK M MI nb N ws = true) {k : Nat} (hk : k < N) :
    inv (unpack 24 24 (M k)) = unpack 24 24 (MI k) := by
  obtain ⟨_, h⟩ := MatS.bAnd_split h
  obtain ⟨hall, _⟩ := MatS.bAnd_split h
  exact (invOKK_sound (MatL.allN_iff.1 hall k hk)).2

theorem conjProdR_eq {M MI : Nat → Nat} {nb N : Nat} {ws : List (List Nat)}
    (hd : dagK M MI nb N ws = true) (z : Nat) {ps : List Nat} (hps : ∀ k ∈ ps, okK N k = true) :
    conjProdR (rowsOf M N) (unpack 24 24 z) ps = unpack 24 24 (conjPK M MI z ps) := by
  unfold conjProdR conjPK
  rw [← MatL.unpack_idM]
  generalize idM = a
  induction ps generalizing a with
  | nil => rfl
  | cons k ps ih =>
    have hk := hps k List.mem_cons_self
    have hk' : k - 1 < N := by
      rw [okK_iff] at hk
      omega
    rw [List.foldl_cons, List.foldl_cons, entryR_rows hk, inv_of_dagK hd hk',
      ← MatL.unpack_mulK, ← MatL.unpack_mulK, ← MatL.unpack_mulK]
    exact ih (fun k' hk'' => hps k' (List.mem_cons_of_mem _ hk'')) _

theorem decOK_eq {M MI : Nat → Nat} {nb N : Nat} {ws : List (List Nat)}
    (hd : dagK M MI nb N ws = true) (z : Nat) :
    ∀ (S : List Nat) (dec : List (List Nat)), decK M MI N z S dec = true →
      decOK (rowsOf M N) (unpack 24 24 z) (S.map (unpack 24 24)) dec = true := by
  intro S
  induction S with
  | nil =>
    intro dec h
    cases dec with
    | nil => rfl
    | cons ps dec => simp [decK] at h
  | cons s S ih =>
    intro dec h
    cases dec with
    | nil => simp [decK] at h
    | cons ps dec =>
      simp only [decK, Bool.and_eq_true, List.all_eq_true] at h
      obtain ⟨⟨hps, he⟩, hrest⟩ := h
      have hok : ∀ k ∈ ps, okK N k = true := fun k hk => (hps k hk).1
      simp only [List.map_cons, decOK, Bool.and_eq_true]
      refine ⟨⟨?_, ?_⟩, ih dec hrest⟩
      · unfold invsOK
        rw [List.all_eq_true]
        intro k hk
        have hk' : k - 1 < N := by
          have := okK_iff.1 (hok k hk)
          omega
        rw [entryR_rows (hok k hk), inv_of_dagK hd hk', ← MatL.unpack_mulK, ← MatL.unpack_idM,
          beq_unpack]
        exact (hps k hk).2
      · rw [conjProdR_eq hd z hok, beq_unpack]
        exact he

theorem pwCoreOK_of {M MI : Nat → Nat} {nb N : Nat} {ws : List (List Nat)}
    (hd : dagK M MI nb N ws = true) {S : List Nat} {iz ih R : Nat} {dec : List (List Nat)}
    (h : pwCoreK M MI N S iz ih dec R = true) :
    pwCoreOK (rowsOf M N) (S.map (unpack 24 24)) iz ih dec (unpack 24 24 R) = true := by
  unfold pwCoreK at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hz, hh⟩, h4⟩, hc⟩, hS⟩, hdec⟩ := h
  unfold pwCoreOK
  rw [entryR_rows hz, entryR_rows hh, List.all_map]
  simp only [← MatL.unpack_mulK, ← MatL.unpack_idM, beq_unpack, Function.comp_def, commR_unpack,
    Bool.and_eq_true, List.all_eq_true]
  exact ⟨⟨⟨h4, hc⟩, hS⟩, decOK_eq hd _ S dec hdec⟩

theorem entriesR_of {M MI : Nat → Nat} {N : Nat} {base : List Rows} {ws : List (List Int)}
    (hdag : dag base ws = (rowsOf M N, rowsOf MI N, true)) {idx : List Nat}
    (hidx : idx.all (okK N) = true) :
    entriesR base ws idx = idx.map fun k => unpack 24 24 (M (k - 1)) := by
  unfold entriesR
  rw [hdag]
  apply List.map_congr_left
  intro k hk
  exact entryR_rows (List.all_eq_true.1 hidx k hk)

end CFSG.KC.Co1PW

end
