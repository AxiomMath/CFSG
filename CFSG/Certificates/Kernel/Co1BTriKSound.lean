module

public import Certificates.Data.Kernel.Co1BTri
public import CFSG.Certificates.Kernel.PackSetSound
public import CFSG.Certificates.Kernel.Co1BTrSound
public import CFSG.Certificates.Kernel.SporSch.Co1MatSound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Sporadic.Co1Block.CentCheck
public import CFSG.Sporadic.Co1Block.TwoBCheckDefs

public section

namespace CFSG.KC.Co1T

open CFSG.KC.Enum CFSG.KS CFSG.KC.Pack CFSG.Sporadic.Co1Block.Native

theorem bif_true {e t c : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true) :
    (c = true ∧ t = true) ∨ (c = false ∧ e = true) := by
  cases c
  · exact Or.inr ⟨rfl, h⟩
  · exact Or.inl ⟨rfl, h⟩

theorem beq_of_true {a b : Nat} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem lt_of_blt {a b : Nat} (h : Nat.blt a b = true) : a < b := Eq.mp Nat.blt_eq h

theorem blt_of_lt {a b : Nat} (h : a < b) : Nat.blt a b = true := Eq.mpr Nat.blt_eq h

theorem unpack_eq_unpackR (P : Nat) :
    CFSG.KS.Raw.unpack 24 24 P = CFSG.KC.Co1F2.unpackR 24 P := by
  unfold CFSG.KS.Raw.unpack CFSG.KC.Co1F2.unpackR
  congr 1
  funext i
  rw [mask_eq, pg_eq]

theorem act_unpack {P T : Nat} (hT : CFSG.KC.Co1F2.trK 24 P = T) (v : Nat) :
    CFSG.Sporadic.Co1Schreier.Native.act (CFSG.KS.Raw.unpack 24 24 P) v =
      CFSG.KC.M1F2.vmF 24 T v := by
  rw [unpack_eq_unpackR]
  exact CFSG.KC.F2W.act_unpackR hT v

theorem pg_lt' (w p j : Nat) : pg w (mask w) p j < 2 ^ w := by
  rw [mask_eq, pg_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem tu_lt (PT k : Nat) : tu PT k < 2 ^ 24 := pg_lt' 24 PT _

theorem tv_lt (PT k : Nat) : tv PT k < 2 ^ 24 := pg_lt' 24 PT _

theorem xor_lt (PT k : Nat) : tu PT k ^^^ tv PT k < 2 ^ 24 :=
  Nat.xor_lt_two_pow (tu_lt PT k) (tv_lt PT k)

theorem trisPK_sound {PT : Nat} : ∀ {L : List (Nat × Nat)} {k : Nat}, trisPK PT L k = true →
    ∀ i (hi : i < L.length), L[i] = (tu PT (k + i), tv PT (k + i))
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | p :: L, k, h, i, hi => by
    have h' : strictB k (fun k => bAnd(Nat.beq (tu PT k) p.1,
        bAnd(Nat.beq (tv PT k) p.2, trisPK PT L (Nat.succ k)))) = true := h
    rw [strictB_eq] at h'
    obtain ⟨h1, h'⟩ := band_iff.1 h'
    obtain ⟨h2, h3⟩ := band_iff.1 h'
    rcases i with _ | i
    · simp only [List.getElem_cons_zero, Nat.add_zero]
      rw [beq_of_true h1, beq_of_true h2]
    · simp only [List.getElem_cons_succ]
      rw [trisPK_sound h3 i (by simpa using hi), Nat.succ_add, Nat.add_succ]

theorem inTK_sound {PT j a : Nat} (h : inTK PT j a = true) :
    a ∈ [tu PT j, tv PT j, tu PT j ^^^ tv PT j] := by
  have h' : bIf(Nat.beq a (tu PT j), true, bIf(Nat.beq a (tv PT j), true,
      Nat.beq a (Nat.xor (tu PT j) (tv PT j)))) = true := by
    have := h
    unfold inTK at this
    rwa [strictB_eq, strictB_eq] at this
  rcases bif_true h' with ⟨h1, -⟩ | ⟨-, h'⟩
  · simp [beq_of_true h1]
  · rcases bif_true h' with ⟨h2, -⟩ | ⟨-, h3⟩
    · simp [beq_of_true h2]
    · have : a = tu PT j ^^^ tv PT j := beq_of_true h3
      simp [this]

theorem triOneK_sound {T PT P k : Nat} (h : triOneK T PT P k = true) (hk : k < 1365) :
    pg 11 (mask 11) P k < 1365 ∧ ∀ x ∈ [tu PT k, tv PT k, tu PT k ^^^ tv PT k],
      CFSG.KC.M1F2.vmF 24 T x ∈ [tu PT (pg 11 (mask 11) P k), tv PT (pg 11 (mask 11) P k),
        tu PT (pg 11 (mask 11) P k) ^^^ tv PT (pg 11 (mask 11) P k)] := by
  have hb : Nat.blt k 1365 = true := blt_of_lt hk
  have h' : bIf(Nat.blt k 1365, bAnd(Nat.blt (pg 11 (mask 11) P k) 1365,
      bAnd(inTK PT (pg 11 (mask 11) P k) (CFSG.KC.M1F2.vmF 24 T (tu PT k)),
        bAnd(inTK PT (pg 11 (mask 11) P k) (CFSG.KC.M1F2.vmF 24 T (tv PT k)),
          inTK PT (pg 11 (mask 11) P k)
            (CFSG.KC.M1F2.vmF 24 T (Nat.xor (tu PT k) (tv PT k)))))), true) = true := by
    have := h
    unfold triOneK at this
    rwa [strictB_eq, strictB_eq, strictB_eq] at this
  rw [hb] at h'
  obtain ⟨h1, h'⟩ := band_iff.1 h'
  obtain ⟨h2, h'⟩ := band_iff.1 h'
  obtain ⟨h3, h4⟩ := band_iff.1 h'
  refine ⟨lt_of_blt h1, fun x hx => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  exacts [inTK_sound h2, inTK_sound h3, inTK_sound h4]

theorem slices_all {f : Nat → Bool} {L NS n : Nat} (h : ∀ s < NS, allBlk (s * L) f L = true)
    (hn : n ≤ NS * L) : ∀ k < n, f k = true := by
  intro k hk
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · subst h0
      omega
    · exact h0
  have hs : k / L < NS := (Nat.div_lt_iff_lt_mul hL).2 (by omega)
  have := CFSG.KS.allBlk_spec (h (k / L) hs) (k % L) (Nat.mod_lt _ hL)
  rwa [Nat.add_eq, Nat.div_add_mod'] at this

@[expose] noncomputable def vecT (PT i : Nat) : Nat :=
  if i % 3 = 0 then tu PT (i / 3) else if i % 3 = 1 then tv PT (i / 3)
  else tu PT (i / 3) ^^^ tv PT (i / 3)

theorem flatMap_range (PT : Nat) : ∀ m, (List.range m).flatMap
    (fun k => [tu PT k, tv PT k, tu PT k ^^^ tv PT k]) = (List.range (3 * m)).map (vecT PT)
  | 0 => rfl
  | m + 1 => by
    have e : 3 * (m + 1) = 3 * m + 1 + 1 + 1 := by ring
    rw [List.range_succ, List.flatMap_append, flatMap_range PT m, e, List.range_succ,
      List.range_succ, List.range_succ]
    have e0 : (3 * m) % 3 = 0 := by omega
    have d0 : 3 * m / 3 = m := by omega
    have e1 : (3 * m + 1) % 3 = 1 := by omega
    have d1 : (3 * m + 1) / 3 = m := by omega
    have e2 : (3 * m + 1 + 1) % 3 = 2 := by omega
    have d2 : (3 * m + 1 + 1) / 3 = m := by omega
    simp [vecT, e0, d0, e1, d1, e2, d2]

theorem vecOK_sound {TA SV SG ST i x : Nat} (h : vecOK TA SV SG ST i x = true) :
    0 < x ∧ CFSG.KC.M1F2.vmF 24 TA x = x ∧ pg 12 (mask 12) SG i < 4095 ∧
      pg 24 (mask 24) SV (pg 12 (mask 12) SG i) = x ∧
      pg 12 (mask 12) ST (pg 12 (mask 12) SG i) = i := by
  unfold vecOK rkOK at h
  rw [strictB_eq] at h
  obtain ⟨h1, h⟩ := band_iff.1 h
  obtain ⟨h2, h⟩ := band_iff.1 h
  obtain ⟨h3, h⟩ := band_iff.1 h
  obtain ⟨h4, h5⟩ := band_iff.1 h
  exact ⟨lt_of_blt h1, beq_of_true h2, lt_of_blt h3, beq_of_true h4, beq_of_true h5⟩

theorem baseOneK_vec {TA PT SV SG ST k : Nat} (h : baseOneK TA PT SV SG ST k = true)
    (hk : k < 1365) : ∀ e < 3, vecOK TA SV SG ST (3 * k + e) (vecT PT (3 * k + e)) = true := by
  have hb : Nat.blt k 1365 = true := blt_of_lt hk
  have h' : bIf(Nat.blt k 1365, bAnd(vecOK TA SV SG ST (3 * k) (tu PT k),
      bAnd(vecOK TA SV SG ST (3 * k + 1) (tv PT k),
        vecOK TA SV SG ST (3 * k + 2) (Nat.xor (tu PT k) (tv PT k)))), true) = true := by
    have := h
    unfold baseOneK at this
    rwa [strictB_eq, strictB_eq] at this
  rw [hb] at h'
  obtain ⟨h1, h'⟩ := band_iff.1 h'
  obtain ⟨h2, h3⟩ := band_iff.1 h'
  intro e he
  have d : (3 * k + e) / 3 = k := by omega
  interval_cases e
  · have e0 : (3 * k + 0) % 3 = 0 := by omega
    simpa [vecT, e0, d] using h1
  · have e1 : (3 * k + 1) % 3 = 1 := by omega
    simpa [vecT, e1, d] using h2
  · have e2 : (3 * k + 2) % 3 = 2 := by omega
    simpa [vecT, e2, d] using h3

theorem sortK_lt {SV n : Nat} (h : sortK SV n = true) :
    ∀ p q, p < q → q ≤ n → pg 24 (mask 24) SV p < pg 24 (mask 24) SV q := by
  have hs := CFSG.KS.allN_spec h
  intro p q hpq hq
  induction q with
  | zero => omega
  | succ q ih =>
    have h1 := lt_of_blt (hs q (by omega))
    rcases Nat.lt_or_ge p q with hp | hp
    · exact lt_trans (ih hp (by omega)) h1
    · obtain rfl : p = q := by omega
      exact h1

theorem vecs_facts {PT TA SV SG ST : Nat} {L : List (Nat × Nat)} (hlen : L.length = 1365)
    (hL : trisPK PT L 0 = true) (hb : ∀ k < 1365, baseOneK TA PT SV SG ST k = true)
    (hs : sortK SV 4094 = true) :
    L = (List.range 1365).map (fun k => (tu PT k, tv PT k)) ∧ (triVecs L).Nodup ∧
      ∀ y ∈ triVecs L, y < 2 ^ 24 ∧ y ≠ 0 ∧ CFSG.KC.M1F2.vmF 24 TA y = y := by
  have hLe : L = (List.range 1365).map (fun k => (tu PT k, tv PT k)) := by
    apply List.ext_getElem (by simp [hlen])
    intro i h1 h2
    rw [trisPK_sound hL i h1]
    simp
  have hV : triVecs L = (List.range 4095).map (vecT PT) := by
    rw [triVecs, hLe, List.flatMap_map]
    exact flatMap_range PT 1365
  have hok : ∀ i < 4095, vecOK TA SV SG ST i (vecT PT i) = true := by
    intro i hi
    have := baseOneK_vec (hb (i / 3) (by omega)) (by omega) (i % 3) (Nat.mod_lt _ (by norm_num))
    rwa [Nat.div_add_mod] at this
  have hlt : ∀ i, vecT PT i < 2 ^ 24 := by
    intro i
    unfold vecT
    split_ifs
    exacts [tu_lt _ _, tv_lt _ _, xor_lt _ _]
  refine ⟨hLe, ?_, ?_⟩
  · rw [hV]
    refine List.Nodup.map_on (fun i hi j hj e => ?_) List.nodup_range
    have hi' := List.mem_range.1 hi
    have hj' := List.mem_range.1 hj
    obtain ⟨-, -, ri, si, ti⟩ := vecOK_sound (hok i hi')
    obtain ⟨-, -, rj, sj, tj⟩ := vecOK_sound (hok j hj')
    have hr : pg 12 (mask 12) SG i = pg 12 (mask 12) SG j := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hl | hl
      · have := sortK_lt hs _ _ hl (by omega)
        rw [si, sj, e] at this
        exact lt_irrefl _ this
      · have := sortK_lt hs _ _ hl (by omega)
        rw [si, sj, e] at this
        exact lt_irrefl _ this
    rw [← ti, ← tj, hr]
  · intro y hy
    rw [hV, List.mem_map] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    obtain ⟨h0, hf, -⟩ := vecOK_sound (hok i (List.mem_range.1 hi))
    exact ⟨hlt i, Nat.pos_iff_ne_zero.1 h0, hf⟩

theorem mpowK_unpack (X : Nat) : ∀ e, CFSG.Sporadic.Co1Schreier.Native.mul
    (CFSG.KS.Raw.unpack 24 24 (mpowK X e)) (CFSG.KS.Raw.unpack 24 24 X) =
      CFSG.KS.Raw.unpack 24 24 (mpowK X (e + 1)) := by
  intro e
  have : mpowK X (e + 1) = strictN (mpowK X e) (fun q => CFSG.KS.SporSch.M24.mulK q X) := rfl
  rw [this, strictN_eq]
  exact CFSG.KS.SporSch.M24.mulEqK_sound (Nat.beq_refl _)

theorem ne1K_sound {T v : Nat} (h : ne1K T v = true) : CFSG.KC.M1F2.vmF 24 T v ≠ v := by
  intro e
  unfold ne1K at h
  rw [e, Nat.beq_refl] at h
  exact Bool.false_ne_true h

theorem neK2_sound {T T' v : Nat} (h : neK2 T T' v = true) :
    CFSG.KC.M1F2.vmF 24 T v ≠ CFSG.KC.M1F2.vmF 24 T' v := by
  intro e
  unfold neK2 at h
  rw [e, Nat.beq_refl] at h
  exact Bool.false_ne_true h

theorem ne1K2_sound {T T' v : Nat} (h : ne1K2 T T' v = true) :
    CFSG.KC.M1F2.vmF 24 T (CFSG.KC.M1F2.vmF 24 T' v) ≠ v := by
  intro e
  unfold ne1K2 at h
  rw [e, Nat.beq_refl] at h
  exact Bool.false_ne_true h

end CFSG.KC.Co1T

end
