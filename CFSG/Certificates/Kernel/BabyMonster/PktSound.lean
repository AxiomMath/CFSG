module

public import CFSG.Certificates.Kernel.BabyMonster.PktDecode

public section

namespace CFSG.KC.BM.Pkt

open CFSG.KC.BM CFSG.KC.BM.B64 CFSG.KC.BM.Lat CFSG.KC.YModel CFSG.KC.BM.Dy

@[expose] def numerOf (rows : Array (Array (Array (Nat × Int)))) (j t u : Nat) : Int :=
  ((rows[j]!)[t]!).foldl (fun s e => if e.1 = u then s + e.2 else s) 0

@[expose] noncomputable def kNumMono (T t u : Nat) : Int :=
  (fun f : Nat => if u = f % 8192 then (if f / 8192 = 1 then (-8 : Int) else 8) else 0)
    (T / 2 ^ (16 * t) % 65536)

@[expose] noncomputable def kNumSparse (SG : List (List Nat)) (t u : Nat) : Int :=
  (fun x : Nat => if 1024 ≤ x then (x : Int) - 2048 else (x : Int))
    (recOf SG t / 2 ^ (16 * u) % 65536)

theorem decodeRows_text {CH : List (Nat × Nat)} {S : List Nat} (hc : piecesOK CH = true)
    (hS : linesAt CH S = true) (hn : Nat.beq (lenL S) (nat_lit 49) = true)
    (hl : ∀ i < 48, lineOK (lineOf CH S i) = true) :
    CFSG.Monster.B.Native.decodeRows (String.ofList (charsOf CH)) =
      ((List.range 48).map (fun i => lineRows (lineOf CH S i))).toArray := by
  rw [decodeRows_eq]
  exact decode_text hc hS (Nat.eq_of_beq_eq_true hn) hl

theorem numerOf_mono {CH : List (Nat × Nat)} {S : List Nat} {T j : Nat}
    (hS : linesAt CH S = true) (hn : Nat.beq (lenL S) (nat_lit 49) = true)
    (hl : ∀ i < 48, lineOK (lineOf CH S i) = true) (hj : j < 48)
    (h : monoOK (lineOf CH S j) T = true) (hc : piecesOK CH = true) (hT : tabOK T = true) :
    ∀ t u : Nat, t < 4371 →
      numerOf (CFSG.Monster.B.Native.decodeRows (String.ofList (charsOf CH))) j t u =
        kNumMono T t u := by
  intro t u ht
  unfold numerOf
  rw [decodeRows_text hc hS hn hl,
    List.getElem!_toArray (xs := (List.range 48).map fun i => lineRows (lineOf CH S i)),
    getElem!_map_range _ hj, mono_rows h ht,
    ← Array.foldl_toList]
  obtain ⟨-, hT2⟩ := tab_facts hT t ht
  have hk : kNumMono T t u =
      if u = fld T t % 8192 then (if fld T t / 8192 = 1 then (-8 : ℤ) else 8) else 0 := rfl
  rw [hk]
  change (if fld T t % 8192 = u then 0 + CFSG.Monster.B.Native.numOfCode (fld T t / 8192)
    else 0) = _
  have hu' : (fld T t % 8192 = u) ↔ (u = fld T t % 8192) := eq_comm
  rcases (show fld T t / 8192 = 0 ∨ fld T t / 8192 = 1 by omega) with h0 | h0 <;> rw [h0] <;>
    by_cases hu : u = fld T t % 8192 <;> simp [hu, hu'] <;> rfl

theorem numerOf_sparse {CH : List (Nat × Nat)} {S : List Nat} {SG : List (List Nat)} {j : Nat}
    (hS : linesAt CH S = true) (hn : Nat.beq (lenL S) (nat_lit 49) = true)
    (hl : ∀ i < 48, lineOK (lineOf CH S i) = true) (hj : j < 48)
    (h : sparseOK (lineOf CH S j) SG = true) (hc : piecesOK CH = true) :
    ∀ t u : Nat, t < 4371 → u < 4371 →
      numerOf (CFSG.Monster.B.Native.decodeRows (String.ofList (charsOf CH))) j t u =
        kNumSparse SG t u := by
  intro t u ht _
  unfold numerOf
  rw [decodeRows_text hc hS hn hl,
    List.getElem!_toArray (xs := (List.range 48).map fun i => lineRows (lineOf CH S i)),
    getElem!_map_range _ hj]
  change sumAt ((lineRows (lineOf CH S j))[t]!) u = gF (fld (recOf SG t) u)
  generalize lineOf CH S j = p at h ⊢
  unfold sparseOK at h
  generalize hPs : splitN (nat_lit 192) (nat_lit 12) p.1 = Ps at h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨hle, h⟩ := andB_true h
  obtain ⟨hfin, -⟩ := andB_true h
  have hfin' := Nat.eq_of_beq_eq_true hfin
  change (chunkR SG Ps (Nat.div p.2 (nat_lit 3)) (nat_lit 0, nat_lit 0)).1 = nat_lit 4371 at hfin'
  rw [show Nat.div p.2 (nat_lit 3) = p.2 / 3 from rfl] at hfin'
  have hle' : p.2 ≤ 786432 := Nat.le_of_ble_eq_true hle
  have hlen := (splitN_chars 192 12 p.1).1
  have hent := split_entV p.1
  rw [hPs] at hlen hent
  have hlen' : Ps.length = 4096 := hlen
  rw [chunkR_eq SG _ (entV p.1) _ _ hent (by rw [hlen']; omega)] at hfin'
  exact sparse_rows _ 0 0 #[] #[] rfl (fun u => by simp [sumAt, gF, fld])
    (fun t ht => absurd ht (Nat.not_lt_zero t)) hfin' t ht u

end CFSG.KC.BM.Pkt

end
