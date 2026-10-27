module

public import Certificates.Data.Kernel.SporSch.TitsEnum5
public import CFSG.Certificates.Kernel.Spor.RawSlSound
public import CFSG.Sporadic.Schreier.TitsEnum
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.RawSiftK
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.Sporadic.Schreier.TitsBasic
public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Sporadic.Schreier.Tits
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

theorem canonK_facts {n w nw p : Nat} (hp : canonK n w (mask w) nw p = true) :
    n < 16777216 ∧ n + 1 < 2 ^ w ∧ p >>> nw = 0 ∧ ∀ i < n, pg w (mask w) p i < n := by
  unfold canonK szOK at hp
  simp only [bAnd_iff] at hp
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
  refine ⟨by simpa [Nat.blt_eq] using h1, ?_, by simpa using h3, fun i hi => ?_⟩
  · simpa [Nat.blt_eq, Nat.shiftLeft_eq] using h2
  · simpa [Nat.blt_eq] using allN_spec h4 i hi

theorem unpack_getT {n w P i : Nat} (hi : i < n) : (unpack n w P)[i]! = pg w (mask w) P i := by
  rw [unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem allN_eq_eqA {n : Nat} {f : Nat → Bool} {a b : Array Nat}
    (h : ∀ i < n, (f i = true ↔ a[i]! = b[i]!)) : allN n f = eqA n a b := by
  rw [Bool.eq_iff_iff, eqA, CFSG.Monster.B.Co2.allLt_iff]
  refine ⟨fun H i hi => ?_, fun H => allN_of_forall fun i hi => (h i hi).2 ?_⟩
  · rw [beq_iff_eq]
    exact (h i hi).1 (allN_spec H i hi)
  · exact beq_iff_eq.1 (H i hi)

theorem pg_prod5K {n w t0 t1 t2 t3 t4 i : Nat} (hn : n < 2 ^ 32)
    (h2 : ∀ j < n, pg w (mask w) t2 j < n) (h3 : ∀ j < n, pg w (mask w) t3 j < n)
    (h4 : ∀ j < n, pg w (mask w) t4 j < n) (hi : i < n) :
    pg w (mask w) (prod5K n w (mask w) t0 t1 t2 t3 t4) i = gpt w (mask w) t0 t1 t2 t3 t4 i := by
  unfold prod5K gpt
  rw [PackFld.pg_pcomp hn hi, PackFld.pg_pcomp hn (h4 i hi), PackFld.pg_pcomp hn (h3 _ (h4 i hi)),
    PackFld.pg_pcomp hn (h2 _ (h3 _ (h4 i hi)))]

theorem gpt_facts {n w t0 t1 t2 t3 t4 : Nat}
    (h0 : canonK n w (mask w) (n * w) t0 = true) (h1 : canonK n w (mask w) (n * w) t1 = true)
    (h2 : canonK n w (mask w) (n * w) t2 = true) (h3 : canonK n w (mask w) (n * w) t3 = true)
    (h4 : canonK n w (mask w) (n * w) t4 = true) :
    n < 16777216 ∧ ∀ i < n, (unpack n w (prod5K n w (mask w) t0 t1 t2 t3 t4))[i]! =
      gpt w (mask w) t0 t1 t2 t3 t4 i ∧ gpt w (mask w) t0 t1 t2 t3 t4 i < n := by
  obtain ⟨hn, -, -, r0⟩ := canonK_facts h0
  obtain ⟨-, -, -, r1⟩ := canonK_facts h1
  obtain ⟨-, -, -, r2⟩ := canonK_facts h2
  obtain ⟨-, -, -, r3⟩ := canonK_facts h3
  obtain ⟨-, -, -, r4⟩ := canonK_facts h4
  refine ⟨hn, fun i hi => ⟨?_, r0 _ (r1 _ (r2 _ (r3 _ (r4 i hi))))⟩⟩
  rw [unpack_getT hi, pg_prod5K (by omega) r2 r3 r4 hi]

section Chain

variable {n w kS BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
  {base : Array Nat}

theorem lev_trAt {nb : Nat} (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) {i : Nat} (hi : i < nb) :
    (rawLevels n S base)[i]!.pts.size = rcnt (LR i) ∧ ∀ k < rcnt (LR i),
      canonK n w (mask w) (n * w) (trAt n (n * w) LR TR i k) = true ∧
      (∀ x < n, ((rawLevels n S base)[i]!.tr[k]!)[x]! = pg w (mask w) (trAt n (n * w) LR TR i k) x) ∧
      ∃ σ, CFSG.Monster.B.Co2.Rep n (rawLevels n S base)[i]!.tr[k]! σ := by
  have hbl := Raw.Orb.base_lt_of_levels hb hl
  obtain ⟨A, P⟩ := Raw.Orb.agree_levelK hb hp hbl (R := LR) (TRI := TRI) hi (hl i hi)
  obtain ⟨hsz, -, -, -, -, hperm⟩ := Raw.Orb.levelK_facts (hl i hi)
  refine ⟨A.cnt.symm, fun k hk => ⟨?_, fun x hx => ?_, ⟨_, (A.tr k (by rw [← A.cnt]; exact hk)).1⟩⟩⟩
  · obtain ⟨h1, -, h3⟩ := Raw.Orb.permOK_facts (hperm k hk)
    change canonK n w (mask w) (n * w) (TR (roff n (n * w) (LR i) + k)) = true
    unfold canonK
    refine (bAnd_iff _ _).2 ⟨hsz, (bAnd_iff _ _).2 ⟨?_, allN_of_forall fun x hx => ?_⟩⟩
    · rw [h1]
      rfl
    · exact Nat.blt_eq.mpr (h3 x hx).1
  · have R := (A.tr k (by rw [← A.cnt]; exact hk)).1 ⟨x, hx⟩
    change _ = pg w (mask w) (TR (roff n (n * w) (LR i) + k)) x
    rw [(P k hk).1 ⟨x, hx⟩]
    exact R

theorem prod5_facts (hb : Binds n w PS kS 5 BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS 5 BP) {a b c d e : Nat} (ha : a < rcnt (LR 0))
    (hb1 : b < rcnt (LR 1)) (hc : c < rcnt (LR 2)) (hd : d < rcnt (LR 3)) (he : e < rcnt (LR 4)) :
    (canonK n w (mask w) (n * w) (trAt n (n * w) LR TR 0 a) = true ∧
      canonK n w (mask w) (n * w) (trAt n (n * w) LR TR 1 b) = true ∧
      canonK n w (mask w) (n * w) (trAt n (n * w) LR TR 2 c) = true ∧
      canonK n w (mask w) (n * w) (trAt n (n * w) LR TR 3 d) = true ∧
      canonK n w (mask w) (n * w) (trAt n (n * w) LR TR 4 e) = true) ∧
    prod5 n (rawLevels n S base) a b c d e = unpack n w (prod5K n w (mask w)
      (trAt n (n * w) LR TR 0 a) (trAt n (n * w) LR TR 1 b) (trAt n (n * w) LR TR 2 c)
      (trAt n (n * w) LR TR 3 d) (trAt n (n * w) LR TR 4 e)) ∧
    ∃ σ, CFSG.Monster.B.Co2.Rep n (prod5 n (rawLevels n S base) a b c d e) σ := by
  obtain ⟨k0, E0, σ0, R0⟩ := (lev_trAt hb hp hl (i := 0) (by omega)).2 a ha
  obtain ⟨k1, E1, σ1, R1⟩ := (lev_trAt hb hp hl (i := 1) (by omega)).2 b hb1
  obtain ⟨k2, E2, σ2, R2⟩ := (lev_trAt hb hp hl (i := 2) (by omega)).2 c hc
  obtain ⟨k3, E3, σ3, R3⟩ := (lev_trAt hb hp hl (i := 3) (by omega)).2 d hd
  obtain ⟨k4, E4, σ4, R4⟩ := (lev_trAt hb hp hl (i := 4) (by omega)).2 e he
  obtain ⟨-, hP⟩ := gpt_facts k0 k1 k2 k3 k4
  obtain ⟨-, -, -, r1⟩ := canonK_facts k1
  obtain ⟨-, -, -, r2⟩ := canonK_facts k2
  obtain ⟨-, -, -, r3⟩ := canonK_facts k3
  obtain ⟨-, -, -, r4⟩ := canonK_facts k4
  refine ⟨⟨k0, k1, k2, k3, k4⟩, ?_, ⟨_, CFSG.Monster.B.Co2.rep_compA
    (CFSG.Monster.B.Co2.rep_compA (CFSG.Monster.B.Co2.rep_compA
      (CFSG.Monster.B.Co2.rep_compA R0 R1) R2) R3) R4⟩⟩
  apply Array.ext
  · simp [prod5, compA, unpack]
  · intro i h1 _
    have hi : i < n := by simpa [prod5, compA] using h1
    rw [← getElem!_pos _ i h1, ← getElem!_pos _ i (by simpa [unpack] using hi), (hP i hi).1]
    unfold prod5 gpt
    rw [CFSG.Monster.B.Co2.compA_get hi, E4 i hi, CFSG.Monster.B.Co2.compA_get (r4 i hi),
      E3 _ (r4 i hi), CFSG.Monster.B.Co2.compA_get (r3 _ (r4 i hi)), E2 _ (r3 _ (r4 i hi)),
      CFSG.Monster.B.Co2.compA_get (r2 _ (r3 _ (r4 i hi))), E1 _ (r2 _ (r3 _ (r4 i hi))),
      E0 _ (r1 _ (r2 _ (r3 _ (r4 i hi))))]

end Chain

theorem all5K_at {n nw : Nat} {LR TR : Nat → Nat} {Q : Nat → Nat → Nat → Nat → Nat → Nat → Bool}
    (h : all5K n nw LR TR Q = true) {a b c d e : Nat} (ha : a < rcnt (LR 0))
    (hb : b < rcnt (LR 1)) (hc : c < rcnt (LR 2)) (hd : d < rcnt (LR 3)) (he : e < rcnt (LR 4)) :
    Q ((((a * rcnt (LR 1) + b) * rcnt (LR 2) + c) * rcnt (LR 3) + d) * rcnt (LR 4) + e)
      (trAt n nw LR TR 0 a) (trAt n nw LR TR 1 b) (trAt n nw LR TR 2 c) (trAt n nw LR TR 3 d)
      (trAt n nw LR TR 4 e) = true := by
  have h1 := allN_spec (allN_spec h a ha) b hb
  unfold e5ab at h1
  simp only [strictB_eq] at h1
  exact allN_spec (allN_spec (allN_spec h1 c hc) d hd) e he

theorem flatMap_range_mul {α : Type} (A B : Nat) (g : Nat → Nat → List α) :
    (List.range A).flatMap (fun x => (List.range B).flatMap (fun y => g x y)) =
      (List.range (A * B)).flatMap (fun k => g (k / B) (k % B)) := by
  induction A with
  | zero => simp
  | succ A ih =>
    rw [List.range_succ, List.flatMap_append, ih, Nat.succ_mul, List.range_add, List.flatMap_append,
      List.flatMap_map]
    congr 1
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro y hy
    have hy' := List.mem_range.1 hy
    have hB : 0 < B := by omega
    have e1 : (A * B + y) / B = A := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hy', Nat.zero_add]
    have e2 : (A * B + y) % B = y := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy']
    simp only [e1, e2]

theorem filter_map_flatMap {α β : Type} (f : α → β) (p : β → Bool) :
    ∀ l : List α, (l.map f).filter p = l.flatMap (fun x => if p (f x) then [f x] else [])
  | [] => rfl
  | x :: l => by
    rw [List.map_cons, List.filter_cons, List.flatMap_cons, filter_map_flatMap f p l]
    split <;> rfl

theorem flatMap_ite {α β : Type} (f : α → β) (q : α → Bool) :
    ∀ l : List α, l.flatMap (fun x => if q x then [f x] else []) = (l.filter q).map f
  | [] => rfl
  | x :: l => by
    rw [List.flatMap_cons, List.filter_cons, flatMap_ite f q l]
    split <;> rfl

theorem hasBit_maskOf (C : List Nat) (k : Nat) : hasBit (maskOf C) k = decide (k ∈ C) := by
  rw [Raw.Orb.hasBit_eq]
  induction C with
  | nil => simp [maskOf]
  | cons c C ih =>
    change ((maskOf C) ||| (1 <<< c)).testBit k = _
    rw [Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases h : k = c
    · subst h
      simp
    · simp [h, Ne.symm h]

theorem ascK_spec {T : Nat} : ∀ {C : List Nat} {lo : Nat}, ascK T C lo = true →
    C.Pairwise (· < ·) ∧ ∀ c ∈ C, lo ≤ c ∧ c < T
  | [], _, _ => ⟨List.Pairwise.nil, fun _ h => absurd h List.not_mem_nil⟩
  | c :: C, lo, h => by
    have h' : bAnd(Nat.ble lo c, bAnd(Nat.blt c T, ascK T C (Nat.succ c))) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h2
    obtain ⟨ih1, ih2⟩ := ascK_spec h3
    have h1' := Nat.ble_eq.mp h1
    have h2' := Nat.blt_eq.mp h2
    refine ⟨List.pairwise_cons.2 ⟨fun c' hc' => ?_, ih1⟩, fun c' hc' => ?_⟩
    · have := (ih2 c' hc').1
      omega
    · rcases List.mem_cons.1 hc' with rfl | hc'
      · exact ⟨h1', h2'⟩
      · have := ih2 c' hc'
        omega

theorem zipK_beq_map {f : Nat → Nat} : ∀ {C L : List Nat},
    zipK (fun c l => Nat.beq (f c) l) C L = true → L = C.map f
  | [], [], _ => rfl
  | [], _ :: _, h => (Bool.false_ne_true h).elim
  | _ :: _, [], h => (Bool.false_ne_true h).elim
  | c :: C, l :: L, h => by
    have h' : bAnd(Nat.beq (f c) l, zipK (fun c l => Nat.beq (f c) l) C L) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    rw [List.map_cons, Nat.eq_of_beq_eq_true h1, zipK_beq_map h2]

theorem prodCode_eq (n w m nw : Nat) (LR TR : Nat → Nat) (k : Nat) :
    prodCode n w m nw LR TR k = prod5K n w m
      (trAt n nw LR TR 0 (k / rcnt (LR 4) / rcnt (LR 3) / rcnt (LR 2) / rcnt (LR 1)))
      (trAt n nw LR TR 1 (k / rcnt (LR 4) / rcnt (LR 3) / rcnt (LR 2) % rcnt (LR 1)))
      (trAt n nw LR TR 2 (k / rcnt (LR 4) / rcnt (LR 3) % rcnt (LR 2)))
      (trAt n nw LR TR 3 (k / rcnt (LR 4) % rcnt (LR 3))) (trAt n nw LR TR 4 (k % rcnt (LR 4))) := by
  unfold prodCode
  simp only [PackFld.strictN_eqP]
  rfl

theorem code_facts {LR : Nat → Nat} {k : Nat} (hk : k < tot5 LR) :
    k / rcnt (LR 4) / rcnt (LR 3) / rcnt (LR 2) / rcnt (LR 1) < rcnt (LR 0) ∧
    k / rcnt (LR 4) / rcnt (LR 3) / rcnt (LR 2) % rcnt (LR 1) < rcnt (LR 1) ∧
    k / rcnt (LR 4) / rcnt (LR 3) % rcnt (LR 2) < rcnt (LR 2) ∧
    k / rcnt (LR 4) % rcnt (LR 3) < rcnt (LR 3) ∧ k % rcnt (LR 4) < rcnt (LR 4) ∧
    ((((k / rcnt (LR 4) / rcnt (LR 3) / rcnt (LR 2) / rcnt (LR 1) * rcnt (LR 1) +
      k / rcnt (LR 4) / rcnt (LR 3) / rcnt (LR 2) % rcnt (LR 1)) * rcnt (LR 2) +
      k / rcnt (LR 4) / rcnt (LR 3) % rcnt (LR 2)) * rcnt (LR 3) +
      k / rcnt (LR 4) % rcnt (LR 3)) * rcnt (LR 4) + k % rcnt (LR 4)) = k := by
  have hk' : k < rcnt (LR 0) * rcnt (LR 1) * rcnt (LR 2) * rcnt (LR 3) * rcnt (LR 4) := hk
  have p4 : 0 < rcnt (LR 4) := Nat.pos_of_ne_zero fun h => by rw [h, Nat.mul_zero] at hk'; omega
  have p3 : 0 < rcnt (LR 3) := Nat.pos_of_ne_zero fun h => by
    rw [h, Nat.mul_zero, Nat.zero_mul] at hk'; omega
  have p2 : 0 < rcnt (LR 2) := Nat.pos_of_ne_zero fun h => by
    rw [h, Nat.mul_zero, Nat.zero_mul, Nat.zero_mul] at hk'; omega
  have p1 : 0 < rcnt (LR 1) := Nat.pos_of_ne_zero fun h => by
    rw [h, Nat.mul_zero, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul] at hk'; omega
  refine ⟨?_, Nat.mod_lt _ p1, Nat.mod_lt _ p2, Nat.mod_lt _ p3, Nat.mod_lt _ p4, ?_⟩
  · rw [Nat.div_lt_iff_lt_mul p1, Nat.div_lt_iff_lt_mul p2, Nat.div_lt_iff_lt_mul p3,
      Nat.div_lt_iff_lt_mul p4]
    exact hk'
  · rw [Nat.div_add_mod', Nat.div_add_mod', Nat.div_add_mod', Nat.div_add_mod']

section Survivors

variable {n w kS BP M : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
  {base : Array Nat} {p : Array Nat → Bool} {P : Nat → Nat → Nat → Nat → Nat → Bool} {C : List Nat}

theorem survivors5_codes (hb : Binds n w PS kS 5 BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS 5 BP)
    (hP : ∀ t0 t1 t2 t3 t4, canonK n w (mask w) (n * w) t0 = true →
      canonK n w (mask w) (n * w) t1 = true → canonK n w (mask w) (n * w) t2 = true →
      canonK n w (mask w) (n * w) t3 = true → canonK n w (mask w) (n * w) t4 = true →
      P t0 t1 t2 t3 t4 = p (unpack n w (prod5K n w (mask w) t0 t1 t2 t3 t4)))
    (hM : Nat.beq (maskOf C) M = true)
    (hA : ascK (tot5 LR) C 0 = true)
    (h : all5K n (n * w) LR TR (survQ P M) = true) :
    survivors5 n (rawLevels n S base) p =
      C.map (fun k => unpack n w (prodCode n w (mask w) (n * w) LR TR k)) := by
  have c0 := (lev_trAt hb hp hl (i := 0) (by omega)).1
  have c1 := (lev_trAt hb hp hl (i := 1) (by omega)).1
  have c2 := (lev_trAt hb hp hl (i := 2) (by omega)).1
  have c3 := (lev_trAt hb hp hl (i := 3) (by omega)).1
  have c4 := (lev_trAt hb hp hl (i := 4) (by omega)).1
  have hF : ∀ k < tot5 LR, prod5 n (rawLevels n S base)
      (k / rcnt (LR 4) / rcnt (LR 3) / rcnt (LR 2) / rcnt (LR 1))
      (k / rcnt (LR 4) / rcnt (LR 3) / rcnt (LR 2) % rcnt (LR 1))
      (k / rcnt (LR 4) / rcnt (LR 3) % rcnt (LR 2)) (k / rcnt (LR 4) % rcnt (LR 3))
      (k % rcnt (LR 4)) = unpack n w (prodCode n w (mask w) (n * w) LR TR k) ∧
      (p (unpack n w (prodCode n w (mask w) (n * w) LR TR k)) = decide (k ∈ C)) := by
    intro k hk
    obtain ⟨d0, d1, d2, d3, d4, dk⟩ := code_facts hk
    obtain ⟨⟨k0, k1, k2, k3, k4⟩, e, -⟩ := prod5_facts hb hp hl d0 d1 d2 d3 d4
    rw [prodCode_eq]
    refine ⟨e, ?_⟩
    have hq := all5K_at h d0 d1 d2 d3 d4
    rw [dk] at hq
    unfold survQ at hq
    rw [hP _ _ _ _ _ k0 k1 k2 k3 k4, ← Nat.eq_of_beq_eq_true hM, hasBit_maskOf] at hq
    cases hp' : p (unpack n w (prod5K n w (mask w) _ _ _ _ _)) <;>
      cases hd : decide (k ∈ C) <;> simp_all
  unfold survivors5
  rw [c0, c1, c2, c3, c4]
  simp only [filter_map_flatMap]
  rw [flatMap_range_mul, flatMap_range_mul, flatMap_range_mul, flatMap_range_mul, flatMap_ite]
  obtain ⟨hC1, hC2⟩ := ascK_spec hA
  have hT : rcnt (LR 0) * rcnt (LR 1) * rcnt (LR 2) * rcnt (LR 3) * rcnt (LR 4) = tot5 LR := rfl
  rw [hT]
  have hfil : (List.range (tot5 LR)).filter (fun k => p (prod5 n (rawLevels n S base)
      (k / rcnt (LR 4) / rcnt (LR 3) / rcnt (LR 2) / rcnt (LR 1))
      (k / rcnt (LR 4) / rcnt (LR 3) / rcnt (LR 2) % rcnt (LR 1))
      (k / rcnt (LR 4) / rcnt (LR 3) % rcnt (LR 2)) (k / rcnt (LR 4) % rcnt (LR 3))
      (k % rcnt (LR 4)))) = C := by
    refine List.Pairwise.eq_of_mem_iff (r := (· < ·)) (List.pairwise_lt_range.filter _) hC1
      fun k => ?_
    rw [List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨hk, hpk⟩
      rw [(hF k hk).1, (hF k hk).2] at hpk
      exact of_decide_eq_true hpk
    · intro hk
      have hk' := (hC2 k hk).2
      refine ⟨hk', ?_⟩
      rw [(hF k hk').1, (hF k hk').2]
      exact decide_eq_true hk
  rw [hfil]
  exact List.map_congr_left fun k hk => (hF k (hC2 k hk).2).1

end Survivors

theorem all5K_sound {n w kS BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
    {base : Array Nat} {p : Array Nat → Bool} {P : Nat → Nat → Nat → Nat → Nat → Bool}
    (hb : Binds n w PS kS 5 BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS 5 BP)
    (hP : ∀ t0 t1 t2 t3 t4, canonK n w (mask w) (n * w) t0 = true →
      canonK n w (mask w) (n * w) t1 = true → canonK n w (mask w) (n * w) t2 = true →
      canonK n w (mask w) (n * w) t3 = true → canonK n w (mask w) (n * w) t4 = true →
      isInvA n (unpack n w (prod5K n w (mask w) t0 t1 t2 t3 t4))
        (invCand n (unpack n w (prod5K n w (mask w) t0 t1 t2 t3 t4))) = true →
      P t0 t1 t2 t3 t4 = true → p (unpack n w (prod5K n w (mask w) t0 t1 t2 t3 t4)) = true)
    (h : all5K n (n * w) LR TR (fun _ => P) = true) :
    all5 n (rawLevels n S base) p = true := by
  have c0 := (lev_trAt hb hp hl (i := 0) (by omega)).1
  have c1 := (lev_trAt hb hp hl (i := 1) (by omega)).1
  have c2 := (lev_trAt hb hp hl (i := 2) (by omega)).1
  have c3 := (lev_trAt hb hp hl (i := 3) (by omega)).1
  have c4 := (lev_trAt hb hp hl (i := 4) (by omega)).1
  unfold all5
  rw [c0, c1, c2, c3, c4]
  refine CFSG.Monster.B.Co2.allLt_iff.2 fun a ha => CFSG.Monster.B.Co2.allLt_iff.2 fun b hb' =>
    CFSG.Monster.B.Co2.allLt_iff.2 fun c hc => CFSG.Monster.B.Co2.allLt_iff.2 fun d hd =>
    CFSG.Monster.B.Co2.allLt_iff.2 fun e he => ?_
  obtain ⟨⟨k0, k1, k2, k3, k4⟩, eg, σ, hσ⟩ := prod5_facts hb hp hl ha hb' hc hd he
  have hinv : isInvA n (unpack n w (prod5K n w (mask w) (trAt n (n * w) LR TR 0 a)
      (trAt n (n * w) LR TR 1 b) (trAt n (n * w) LR TR 2 c) (trAt n (n * w) LR TR 3 d)
      (trAt n (n * w) LR TR 4 e))) (invCand n (unpack n w (prod5K n w (mask w)
      (trAt n (n * w) LR TR 0 a) (trAt n (n * w) LR TR 1 b) (trAt n (n * w) LR TR 2 c)
      (trAt n (n * w) LR TR 3 d) (trAt n (n * w) LR TR 4 e)))) = true := by
    rw [← eg]
    exact isInvA_of_rep hσ (rep_invCand hσ)
  rw [eg]
  exact hP _ _ _ _ _ k0 k1 k2 k3 k4 hinv (all5K_at h ha hb' hc hd he)

theorem surv5K_sound {n w kS BP M : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {p : Array Nat → Bool}
    {P : Nat → Nat → Nat → Nat → Nat → Bool} {C L : List Nat}
    (hb : Binds n w PS kS 5 BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS 5 BP)
    (hP : ∀ t0 t1 t2 t3 t4, canonK n w (mask w) (n * w) t0 = true →
      canonK n w (mask w) (n * w) t1 = true → canonK n w (mask w) (n * w) t2 = true →
      canonK n w (mask w) (n * w) t3 = true → canonK n w (mask w) (n * w) t4 = true →
      P t0 t1 t2 t3 t4 = p (unpack n w (prod5K n w (mask w) t0 t1 t2 t3 t4)))
    (hM : Nat.beq (maskOf C) M = true)
    (hA : ascK (tot5 LR) C 0 = true)
    (hZ : zipK (fun c l => Nat.beq (prodCode n w (mask w) (n * w) LR TR c) l) C L = true)
    (h : all5K n (n * w) LR TR (survQ P M) = true) :
    survivors5 n (rawLevels n S base) p = L.map (unpack n w) := by
  rw [survivors5_codes hb hp hl hP hM hA h, zipK_beq_map hZ, List.map_map]
  rfl

theorem commPts_sound {n w G t0 t1 t2 t3 t4 : Nat}
    (h0 : canonK n w (mask w) (n * w) t0 = true) (h1 : canonK n w (mask w) (n * w) t1 = true)
    (h2 : canonK n w (mask w) (n * w) t2 = true) (h3 : canonK n w (mask w) (n * w) t3 = true)
    (h4 : canonK n w (mask w) (n * w) t4 = true) (hG : canonK n w (mask w) (n * w) G = true) :
    commPts n w (mask w) G t0 t1 t2 t3 t4 =
      eqA n (compA n (unpack n w (prod5K n w (mask w) t0 t1 t2 t3 t4)) (unpack n w G))
        (compA n (unpack n w G) (unpack n w (prod5K n w (mask w) t0 t1 t2 t3 t4))) := by
  obtain ⟨-, hP⟩ := gpt_facts h0 h1 h2 h3 h4
  obtain ⟨-, -, -, rG⟩ := canonK_facts hG
  unfold commPts
  refine allN_eq_eqA fun i hi => ?_
  have eG : (unpack n w G)[i]! = pg w (mask w) G i := unpack_getT hi
  have eG' : (unpack n w G)[gpt w (mask w) t0 t1 t2 t3 t4 i]! =
      pg w (mask w) G (gpt w (mask w) t0 t1 t2 t3 t4 i) := unpack_getT (hP i hi).2
  rw [CFSG.Monster.B.Co2.compA_get hi, CFSG.Monster.B.Co2.compA_get hi, eG, (hP i hi).1,
    (hP _ (rG i hi)).1, eG', Nat.beq_eq]

theorem eqPts_sound {n w Z t0 t1 t2 t3 t4 : Nat}
    (h0 : canonK n w (mask w) (n * w) t0 = true) (h1 : canonK n w (mask w) (n * w) t1 = true)
    (h2 : canonK n w (mask w) (n * w) t2 = true) (h3 : canonK n w (mask w) (n * w) t3 = true)
    (h4 : canonK n w (mask w) (n * w) t4 = true) (_hZ : canonK n w (mask w) (n * w) Z = true) :
    eqPts n w (mask w) Z t0 t1 t2 t3 t4 =
      eqA n (unpack n w (prod5K n w (mask w) t0 t1 t2 t3 t4)) (unpack n w Z) := by
  obtain ⟨-, hP⟩ := gpt_facts h0 h1 h2 h3 h4
  unfold eqPts
  refine allN_eq_eqA fun i hi => ?_
  rw [(hP i hi).1, unpack_getT hi, Nat.beq_eq]

theorem sqPts_sound {n w t0 t1 t2 t3 t4 : Nat}
    (h0 : canonK n w (mask w) (n * w) t0 = true) (h1 : canonK n w (mask w) (n * w) t1 = true)
    (h2 : canonK n w (mask w) (n * w) t2 = true) (h3 : canonK n w (mask w) (n * w) t3 = true)
    (h4 : canonK n w (mask w) (n * w) t4 = true) :
    sqPts n w (mask w) t0 t1 t2 t3 t4 =
      eqA n (compA n (unpack n w (prod5K n w (mask w) t0 t1 t2 t3 t4))
        (unpack n w (prod5K n w (mask w) t0 t1 t2 t3 t4))) (idA n) := by
  obtain ⟨-, hP⟩ := gpt_facts h0 h1 h2 h3 h4
  unfold sqPts
  refine allN_eq_eqA fun i hi => ?_
  rw [CFSG.Monster.B.Co2.compA_get hi, CFSG.Monster.B.Co2.idA_get hi, (hP i hi).1,
    (hP _ (hP i hi).2).1, Nat.beq_eq]

theorem sqGPts_sound {n w G t0 t1 t2 t3 t4 : Nat}
    (h0 : canonK n w (mask w) (n * w) t0 = true) (h1 : canonK n w (mask w) (n * w) t1 = true)
    (h2 : canonK n w (mask w) (n * w) t2 = true) (h3 : canonK n w (mask w) (n * w) t3 = true)
    (h4 : canonK n w (mask w) (n * w) t4 = true) (hG : canonK n w (mask w) (n * w) G = true) :
    sqGPts n w (mask w) G t0 t1 t2 t3 t4 =
      eqA n (compA n (compA n (unpack n w (prod5K n w (mask w) t0 t1 t2 t3 t4)) (unpack n w G))
        (compA n (unpack n w (prod5K n w (mask w) t0 t1 t2 t3 t4)) (unpack n w G))) (idA n) := by
  obtain ⟨-, hP⟩ := gpt_facts h0 h1 h2 h3 h4
  obtain ⟨-, -, -, rG⟩ := canonK_facts hG
  have eC : ∀ j < n, (compA n (unpack n w (prod5K n w (mask w) t0 t1 t2 t3 t4))
      (unpack n w G))[j]! = gpt w (mask w) t0 t1 t2 t3 t4 (pg w (mask w) G j) := fun j hj => by
    rw [CFSG.Monster.B.Co2.compA_get hj, unpack_getT hj, (hP _ (rG j hj)).1]
  unfold sqGPts
  refine allN_eq_eqA fun i hi => ?_
  rw [CFSG.Monster.B.Co2.compA_get hi, eC i hi, eC _ (hP _ (rG i hi)).2,
    CFSG.Monster.B.Co2.idA_get hi, strictB_eq, Nat.beq_eq]

theorem conjPts_sound {n w T y t0 t1 t2 t3 t4 : Nat}
    (h0 : canonK n w (mask w) (n * w) t0 = true) (h1 : canonK n w (mask w) (n * w) t1 = true)
    (h2 : canonK n w (mask w) (n * w) t2 = true) (h3 : canonK n w (mask w) (n * w) t3 = true)
    (h4 : canonK n w (mask w) (n * w) t4 = true) (hT : canonK n w (mask w) (n * w) T = true)
    (_hy : canonK n w (mask w) (n * w) y = true)
    (hg : isInvA n (unpack n w (prod5K n w (mask w) t0 t1 t2 t3 t4))
      (invCand n (unpack n w (prod5K n w (mask w) t0 t1 t2 t3 t4))) = true) :
    conjPts n w (mask w) T y t0 t1 t2 t3 t4 =
      eqA n (compA n (compA n (unpack n w (prod5K n w (mask w) t0 t1 t2 t3 t4)) (unpack n w T))
        (invCand n (unpack n w (prod5K n w (mask w) t0 t1 t2 t3 t4)))) (unpack n w y) := by
  obtain ⟨-, hP⟩ := gpt_facts h0 h1 h2 h3 h4
  obtain ⟨-, -, -, rT⟩ := canonK_facts hT
  obtain ⟨hR, hRi⟩ := CFSG.Monster.B.Co2.rep_permOfArr hg
  have hr : ∀ i < n, (invCand n (unpack n w (prod5K n w (mask w) t0 t1 t2 t3 t4)))[i]! < n ∧
      (unpack n w (prod5K n w (mask w) t0 t1 t2 t3 t4))[(invCand n
        (unpack n w (prod5K n w (mask w) t0 t1 t2 t3 t4)))[i]!]! = i := by
    intro i hi
    rw [hRi.apply hi, hR]
    simp
  unfold conjPts
  rw [Bool.eq_iff_iff, eqA, CFSG.Monster.B.Co2.allLt_iff]
  constructor
  · intro H i hi
    obtain ⟨hri, hPr⟩ := hr i hi
    have e := allN_spec H _ hri
    rw [Nat.beq_eq, ← (hP _ hri).1, hPr] at e
    rw [beq_iff_eq, CFSG.Monster.B.Co2.compA_get hi, CFSG.Monster.B.Co2.compA_get hri,
      unpack_getT hri, (hP _ (rT _ hri)).1, unpack_getT hi]
    exact e
  · intro H
    refine allN_of_forall fun j hj => ?_
    have hj' := CFSG.Monster.B.Co2.isInvA_spec hg hj
    rw [(hP j hj).1] at hj'
    have e := H _ hj'.1
    rw [beq_iff_eq, CFSG.Monster.B.Co2.compA_get hj'.1, hj'.2, CFSG.Monster.B.Co2.compA_get hj,
      unpack_getT hj, (hP _ (rT j hj)).1, unpack_getT hj'.1] at e
    rw [Nat.beq_eq]
    exact e

theorem all5K_of {n nw c0 c1 : Nat} {LR TR : Nat → Nat}
    {Q : Nat → Nat → Nat → Nat → Nat → Nat → Bool} (h0 : rcnt (LR 0) = c0) (h1 : rcnt (LR 1) = c1)
    (h : ∀ a < c0, ∀ b < c1, e5ab n nw LR TR Q a b = true) : all5K n nw LR TR Q = true := by
  unfold all5K
  rw [h0, h1]
  exact allN_of_forall fun a ha => allN_of_forall fun b hb => h a ha b hb

theorem eq22_sound {n w x g : Nat} (hx : canonK n w (mask w) (n * w) x = true)
    (hg : canonK n w (mask w) (n * w) g = true) :
    eq22 n w (mask w) x g g x = eqA n (compA n (unpack n w x) (unpack n w g))
      (compA n (unpack n w g) (unpack n w x)) := by
  obtain ⟨-, -, -, rx⟩ := canonK_facts hx
  obtain ⟨-, -, -, rg⟩ := canonK_facts hg
  unfold eq22
  refine allN_eq_eqA fun i hi => ?_
  have ex : (unpack n w x)[i]! = pg w (mask w) x i := unpack_getT hi
  have eg : (unpack n w g)[i]! = pg w (mask w) g i := unpack_getT hi
  rw [CFSG.Monster.B.Co2.compA_get hi, CFSG.Monster.B.Co2.compA_get hi, ex, eg,
    unpack_getT (rg i hi), unpack_getT (rx i hi), Nat.beq_eq]

end CFSG.KS.SporSch

end
