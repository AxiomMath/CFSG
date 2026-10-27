module

public import Certificates.Data.Kernel.Co2SmithS.Class
public import CFSG.Certificates.Kernel.Co2SmithS.BfsSound
public import CFSG.Certificates.Kernel.Co2SmithS.RowsSound

set_option exponentiation.threshold 600

public section

namespace CFSG.KC.Co2SmithS

open CFSG.KC.Co2InvS CFSG.KC.Co1F2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co2Smith.Native

@[expose] def fields22 : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, P => P % 2 ^ 22 :: fields22 n (P / 2 ^ 22)

theorem foldr_fields22 : ∀ (n P : Nat),
    (fields22 n P).foldr (fun r acc => acc * 4194304 + r) 0 = P % 2 ^ (22 * n)
  | 0, P => by simp [fields22, Nat.mod_one]
  | n + 1, P => by
    rw [fields22, List.foldr_cons, foldr_fields22 n (P / 2 ^ 22)]
    rw [show 22 * (n + 1) = 22 + 22 * n by ring, Nat.pow_add, Nat.mod_mul]
    have e : (2 : Nat) ^ 22 = 4194304 := by norm_num
    rw [e]
    ring

theorem unpack_toList : ∀ (n P : Nat),
    (List.ofFn fun i : Fin n => P / 2 ^ (22 * i.val) % 2 ^ 22) = fields22 n P
  | 0, P => rfl
  | n + 1, P => by
    rw [List.ofFn_succ, fields22, ← unpack_toList n (P / 2 ^ 22)]
    simp only [Fin.val_zero, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Fin.val_succ]
    refine congrArg _ (congrArg List.ofFn (funext fun i => ?_))
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, show 22 * (i.val + 1) = 22 + 22 * i.val by ring]

theorem encM_unpack {P : Nat} (hP : P < 2 ^ 484) : encM (unpackR 22 P) = P := by
  unfold encM unpackR
  rw [← Array.foldr_toList, Array.toList_ofFn, unpack_toList, foldr_fields22]
  exact Nat.mod_eq_of_lt hP

theorem cFld_lt (r o w : Nat) : cFld r o w < 2 ^ w := by
  unfold cFld
  rw [Nat.sub_eq, Nat.pow_eq, Nat.land_eq, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem cE_lt (CF : Nat → Nat) (k : Nat) : cE CF k < 2 ^ 484 := cFld_lt _ _ _

theorem cL_lt (CF : Nat → Nat) (k : Nat) : cL CF k < 2 := by
  unfold cL
  exact cFld_lt (cRec CF k) 569 1

structure RecFacts (CF : Nat → Nat) (A B B4 N : Nat) (k : Nat) : Prop where
  t0 : cT CF k 0 < N
  t1 : cT CF k 1 < N
  e0 : cE CF (cT CF k 0) = conjK A B B4 0 (cE CF k)
  e1 : cE CF (cT CF k 1) = conjK A B B4 1 (cE CF k)
  cnt : cM CF N (k + 1) =
    if k < cM CF N k then rowC (cP CF) (cL CF) (cT CF) 2 k (cM CF N k) else 0
  s : cS CF k < N
  sort : k + 1 < N → cE CF (cS CF k) < cE CF (cS CF (k + 1))
  root : k = 0 → cE CF 0 = A ∧ cP CF 0 = 0 ∧ cL CF 0 = 0 ∧ cM CF N 0 = 1
  tree : 0 < k → cP CF k < k ∧ cE CF k = conjK A B B4 (cL CF k) (cE CF (cP CF k))

theorem recFacts {CF : Nat → Nat} {A B B4 N k : Nat} (h : classRecK CF A B B4 N k = true) :
    RecFacts CF A B B4 N k := by
  unfold classRecK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨of_decide_eq_true h1, of_decide_eq_true h2, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5, of_decide_eq_true h6, fun hk => ?_,
    fun hk => ?_, fun hk => ?_⟩
  · rw [Bool.or_eq_true] at h7
    rcases h7 with h7 | h7
    · rw [Bool.not_eq_true'] at h7
      exact absurd hk (of_decide_eq_false h7)
    · exact of_decide_eq_true h7
  · subst hk
    rw [if_pos rfl] at h8
    simp only [Bool.and_eq_true] at h8
    obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h8
    exact ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b, Nat.eq_of_beq_eq_true c,
      Nat.eq_of_beq_eq_true d⟩
  · rw [if_neg (by omega)] at h8
    simp only [Bool.and_eq_true] at h8
    exact ⟨of_decide_eq_true h8.1, Nat.eq_of_beq_eq_true h8.2⟩

theorem cE_inj {CF : Nat → Nat} {A B B4 N : Nat} (hrec : ∀ k < N, RecFacts CF A B B4 N k) :
    ∀ i < N, ∀ j < N, cE CF i = cE CF j → i = j := by
  have hmono : ∀ a b, a < b → b < N → cE CF (cS CF a) < cE CF (cS CF b) := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | h
      · exact Nat.lt_trans (ih h (by omega)) ((hrec b (by omega)).sort hb)
      · subst h
        exact (hrec a (by omega)).sort hb
  let f : Fin N → Fin N := fun t => ⟨cS CF t.val, (hrec t.val t.isLt).s⟩
  have hf : Function.Injective f := by
    intro a b hab
    have e : cS CF a.val = cS CF b.val := congrArg Fin.val hab
    rcases Nat.lt_trichotomy a.val b.val with h | h | h
    · have := hmono _ _ h b.isLt
      rw [e] at this
      exact absurd this (Nat.lt_irrefl _)
    · exact Fin.ext h
    · have := hmono _ _ h a.isLt
      rw [e] at this
      exact absurd this (Nat.lt_irrefl _)
  have hs : Function.Surjective f := Finite.injective_iff_surjective.1 hf
  intro i hi j hj e
  obtain ⟨a, ha⟩ := hs ⟨i, hi⟩
  obtain ⟨b, hb⟩ := hs ⟨j, hj⟩
  have ea : cS CF a.val = i := congrArg Fin.val ha
  have eb : cS CF b.val = j := congrArg Fin.val hb
  rcases Nat.lt_trichotomy a.val b.val with h | h | h
  · have := hmono _ _ h b.isLt
    rw [ea, eb, e] at this
    exact absurd this (Nat.lt_irrefl _)
  · rw [← ea, ← eb, h]
  · have := hmono _ _ h a.isLt
    rw [ea, eb, e] at this
    exact absurd this (Nat.lt_irrefl _)

theorem powRows22_eq (M : Nat) : ∀ e, powRows 22 (unpackR 22 M) e = unpackR 22 (powV M e)
  | 0 => idRows_eq
  | e + 1 => by
    have h : powRows 22 (unpackR 22 M) (e + 1) =
        mulRows 22 (powRows 22 (unpackR 22 M) e) (unpackR 22 M) := rfl
    rw [h, powRows22_eq M e, mulRows_unpack]
    rfl

private theorem conjSeed_zero (S : Array (Array Nat)) (X : Array Nat) :
    conjSeed S 0 X = mulRows 22 (mulRows 22 S[0]! X) S[0]! := rfl

private theorem conjSeed_ne (S : Array (Array Nat)) (X : Array Nat) {l : Nat}
    (hl : (l == 0) = false) :
    conjSeed S l X = mulRows 22 (mulRows 22 S[1]! X) (powRows 22 S[1]! 4) := by
  unfold conjSeed
  rw [hl]
  rfl

private theorem get2_zero (a b : Array Nat) : (#[a, b] : Array (Array Nat))[0]! = a := rfl

private theorem get2_one (a b : Array Nat) : (#[a, b] : Array (Array Nat))[1]! = b := rfl

private theorem conjK_of_eq {A B B4 l P : Nat} (hl : l = 0) :
    conjK A B B4 l P = mulV (mulV A P) A := by
  unfold conjK
  rw [if_pos hl]

theorem conjSeed_unpack (A B P l : Nat) :
    conjSeed #[unpackR 22 A, unpackR 22 B] l (unpackR 22 P) =
      unpackR 22 (conjK A B (powV B 4) l P) := by
  by_cases hl : l = 0
  · have e' := conjK_of_eq (A := A) (B := B) (B4 := powV B 4) (P := P) hl
    subst hl
    rw [conjSeed_zero, get2_zero, e', mulRows_unpack, mulRows_unpack]
  · have hb : (l == 0) = false := by simp [hl]
    have e' : conjK A B (powV B 4) l P = mulV (mulV B P) (powV B 4) := by
      unfold conjK
      rw [if_neg hl]
    rw [conjSeed_ne _ _ hb, get2_one, e', powRows22_eq, mulRows_unpack, mulRows_unpack]

theorem classBFS_rec {CF : Nat → Nat} {A B N cap : Nat} (hN : 0 < N) (hcap : N ≤ cap)
    (hrec : ∀ k < N, RecFacts CF A B (powV B 4) N k) :
    classBFS #[unpackR 22 A, unpackR 22 B] (unpackR 22 A) cap =
      (Array.ofFn (n := N) fun i => unpackR 22 (cE CF i.val),
        Array.ofFn (n := N) fun i => cP CF i.val, Array.ofFn (n := N) fun i => cL CF i.val) := by
  obtain ⟨hA, hp0, hl0, hm0⟩ := (hrec 0 hN).root rfl
  have e1 : classBFS #[unpackR 22 A, unpackR 22 B] (unpackR 22 A) cap =
      gbfs encM (conjSeed #[unpackR 22 A, unpackR 22 B]) 2 (unpackR 22 (cE CF 0)) cap := by
    rw [classBFS_eq]
    exact congrArg (fun X => gbfs encM (conjSeed #[unpackR 22 A, unpackR 22 B]) 2 X cap)
      (by rw [hA])
  rw [e1]
  have hlast : cM CF N N = N := by simp [cM]
  refine gbfs_of (T := fun i => unpackR 22 (cE CF i)) (TB := cT CF) (M := cM CF N) hcap
    (fun i hi j hj e => ?_) (fun i hi l hl => ?_) ⟨hN, hm0, fun h hh => (hrec h hh).cnt, hlast⟩
    hp0 hl0
  · rw [encM_unpack (cE_lt _ _), encM_unpack (cE_lt _ _)] at e
    exact cE_inj hrec i hi j hj e
  · rw [conjSeed_unpack]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · exact ⟨(hrec i hi).t0, by rw [(hrec i hi).e0]⟩
    · exact ⟨(hrec i hi).t1, by rw [(hrec i hi).e1]⟩

theorem posMap_eq (els : Array (Array Nat)) :
    posMap els = (List.range els.size).foldl (fun m i => m.insert (encM els[i]!) i) ∅ := by
  unfold posMap
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl, List.range_eq_range']
  rfl

theorem classOK_of {CF : Nat → Nat} {A B : Nat}
    (hrec : ∀ k < 56925, classRecK CF A B (powV B 4) 56925 k = true) :
    classOK #[unpackR 22 A, unpackR 22 B] = true := by
  have hF : ∀ k < 56925, RecFacts CF A B (powV B 4) 56925 k := fun k hk => recFacts (hrec k hk)
  have hT : (#[unpackR 22 A, unpackR 22 B] : Array (Array Nat))[0]! = unpackR 22 A := rfl
  unfold classOK
  rw [hT, classBFS_rec (by norm_num) (by norm_num) hF]
  unfold classCertOK
  dsimp only
  have hinj := cE_inj hF
  have hkey : ∀ i < 56925, ∀ j < 56925,
      encM (unpackR 22 (cE CF i)) = encM (unpackR 22 (cE CF j)) → i = j := by
    intro i hi j hj e
    rw [encM_unpack (cE_lt _ _), encM_unpack (cE_lt _ _)] at e
    exact hinj i hi j hj e
  have hget : ∀ i < 56925, (Array.ofFn (n := 56925) fun i => unpackR 22 (cE CF i.val))[i]! =
      unpackR 22 (cE CF i) := fun i hi => by
    rw [getElem!_pos _ i (by simpa using hi)]
    simp
  have hgetN : ∀ (f : Nat → Nat) i, i < 56925 → (Array.ofFn (n := 56925) fun i => f i.val)[i]! = f i :=
    fun f i hi => by
      rw [getElem!_pos _ i (by simpa using hi)]
      simp
  have hpos : ∀ i < 56925, (posMap (Array.ofFn (n := 56925) fun i => unpackR 22 (cE CF i.val))).getD
      (encM (unpackR 22 (cE CF i))) 56925 = i := by
    intro i hi
    rw [posMap_eq]
    have := CFSG.KS.VOR.vindex_get (pts := Array.ofFn (n := 56925) fun i => unpackR 22 (cE CF i.val))
      (k := encM) (fun a ha b hb e => by
        simp only [Array.size_ofFn] at ha hb
        rw [hget a ha, hget b hb] at e
        exact hkey a ha b hb e) i (by simpa using hi)
    rw [hget i hi] at this
    simp only [Array.size_ofFn] at this
    rw [Std.HashMap.getD_eq_getD_getElem?, Array.size_ofFn, this]
    rfl
  simp only [Array.size_ofFn, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, List.all_eq_true,
    List.mem_range]
  have himg : ∀ x < 56925, ∀ l < 2, conjSeed #[unpackR 22 A, unpackR 22 B] l (unpackR 22 (cE CF x)) =
      unpackR 22 (cE CF (cT CF x l)) ∧ cT CF x l < 56925 := by
    intro x hx l hl
    rw [conjSeed_unpack]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · exact ⟨by rw [(hF x hx).e0], (hF x hx).t0⟩
    · exact ⟨by rw [(hF x hx).e1], (hF x hx).t1⟩
  refine ⟨?_, fun x hx => ⟨⟨⟨?_, ?_⟩, ?_⟩, fun l hl => ?_⟩⟩
  · rw [hget 0 (by norm_num), ((hF 0 (by norm_num)).root rfl).1]
    exact beq_self_eq_true _
  · rw [hget x hx]
    exact validM_unpack _
  · rw [hget x hx, hpos x hx]
    exact beq_self_eq_true _
  · by_cases h0 : x = 0
    · subst h0
      rfl
    · obtain ⟨hp, he⟩ := (hF x hx).tree (by omega)
      rw [hgetN _ x hx, hgetN _ x hx, hget x hx, hget _ (by omega), conjSeed_unpack, ← he]
      simp only [h0, decide_true, hp, cL_lt, beq_self_eq_true, Bool.and_self, Bool.or_true,
        beq_iff_eq]
  · obtain ⟨e, ht⟩ := himg x hx l hl
    rw [hget x hx, e, hpos _ ht, hget _ ht]
    simp [ht]

end CFSG.KC.Co2SmithS

end
