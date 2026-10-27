module

public import Certificates.Data.Kernel.Spor.Co1Row26683Z
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.PackSetSound

public section

namespace CFSG.KS.Co1Row26683

open CFSG.KC.Enum CFSG.KC.Pack CFSG.KS.Raw.Orb

theorem mask11 : CFSG.KS.mask 11 = 2047 := rfl

@[expose] def lpP (x y : Equiv.Perm (Fin 1365)) (c : Nat) : Equiv.Perm (Fin 1365) :=
  Bool.rec (motive := fun _ => Equiv.Perm (Fin 1365))
    (Bool.rec (motive := fun _ => Equiv.Perm (Fin 1365))
      (Bool.rec (motive := fun _ => Equiv.Perm (Fin 1365)) y⁻¹ x⁻¹ (Nat.beq c (nat_lit 3)))
      y (Nat.beq c (nat_lit 2)))
    x (Nat.beq c (nat_lit 1))

@[expose] def wP (x y : Equiv.Perm (Fin 1365)) (w : List Nat) : Equiv.Perm (Fin 1365) :=
  w.foldr (fun c g => lpP x y c * g) 1

theorem ap_prep {P : Nat} {g : Equiv.Perm (Fin 1365)} (h : PRep 1365 11 P g) (q : Fin 1365) :
    ap P q = g q := by
  have h' := h q
  rw [mask11] at h'
  exact h'

variable {X Y Xi Yi : Nat} {x y : Equiv.Perm (Fin 1365)}

theorem lp_prep (hX : PRep 1365 11 X x) (hY : PRep 1365 11 Y y) (hXi : PRep 1365 11 Xi x⁻¹)
    (hYi : PRep 1365 11 Yi y⁻¹) (c : Nat) : PRep 1365 11 (lp X Y Xi Yi c) (lpP x y c) := by
  unfold lp lpP
  cases Nat.beq c (nat_lit 1) <;> cases Nat.beq c (nat_lit 2) <;>
    cases Nat.beq c (nat_lit 3) <;> assumption

theorem lpP_mem {K : Subgroup (Equiv.Perm (Fin 1365))} (hx : x ∈ K) (hy : y ∈ K) (c : Nat) :
    lpP x y c ∈ K := by
  unfold lpP
  cases Nat.beq c (nat_lit 1) <;> cases Nat.beq c (nat_lit 2) <;>
    cases Nat.beq c (nat_lit 3) <;>
    first | exact hx | exact hy | exact K.inv_mem hx | exact K.inv_mem hy

theorem wP_mem {K : Subgroup (Equiv.Perm (Fin 1365))} (hx : x ∈ K) (hy : y ∈ K) :
    ∀ w : List Nat, wP x y w ∈ K
  | [] => K.one_mem
  | c :: t => K.mul_mem (lpP_mem hx hy c) (wP_mem hx hy t)

theorem wv_eq (hX : PRep 1365 11 X x) (hY : PRep 1365 11 Y y) (hXi : PRep 1365 11 Xi x⁻¹)
    (hYi : PRep 1365 11 Yi y⁻¹) : ∀ (w : List Nat) (q : Fin 1365),
    wv X Y Xi Yi w q = (wP x y w q : Nat)
  | [], _ => rfl
  | c :: t, q => by
    change strictN (wv X Y Xi Yi t q) (fun r => ap (lp X Y Xi Yi c) r) = _
    rw [CFSG.KC.Pack.strictN_eq, wv_eq hX hY hXi hYi t q, ap_prep (lp_prep hX hY hXi hYi c)]
    rfl

theorem fixL_sound {w : List Nat} : ∀ {F : List Nat},
    List.rec (motive := fun _ => Bool) true
      (fun f _ ih2 => bAnd(Nat.beq (wv X Y Xi Yi w f) f, ih2)) F = true →
    ∀ f ∈ F, wv X Y Xi Yi w f = f
  | [], _, f, hf => by simp at hf
  | f0 :: F, h, f, hf => by
    obtain ⟨g1, g2⟩ := band_iff.1 h
    rcases List.mem_cons.1 hf with rfl | hf
    · exact Nat.eq_of_beq_eq_true g1
    · exact fixL_sound g2 f hf

theorem fixK_sound {H : List (List Nat)} {F : List Nat} (h : fixK X Y Xi Yi H F = true) :
    ∀ w ∈ H, ∀ f ∈ F, wv X Y Xi Yi w f = f := by
  induction H with
  | nil => intro w hw; simp at hw
  | cons w0 H ih =>
    obtain ⟨h1, h2⟩ := band_iff.1 h
    intro w hw f hf
    rcases List.mem_cons.1 hw with rfl | hw
    · exact fixL_sound h1 f hf
    · exact ih h2 w hw f hf

theorem nthW_mem : ∀ {H : List (List Nat)} {g : Nat}, g < lenW H → nthW H g ∈ H
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | w :: _, 0, _ => List.mem_cons_self
  | _ :: H, g + 1, h => List.mem_cons_of_mem _ (nthW_mem (H := H) (Nat.lt_of_succ_lt_succ h))

theorem land_fld (R o : Nat) :
    Nat.land (Nat.land (Nat.shiftRight R o) (nat_lit 4294967295)) (nat_lit 2047) =
      Nat.land (Nat.shiftRight R o) (nat_lit 2047) := by
  change (R >>> o &&& 4294967295) &&& 2047 = R >>> o &&& 2047
  rw [Nat.and_assoc]
  rfl

theorem lt_of_blt' {a b : Nat} (h : Nat.blt a b = true) : a < b := by simpa using h

theorem trOK_sound (hX : PRep 1365 11 X x) (hY : PRep 1365 11 Y y) (hXi : PRep 1365 11 Xi x⁻¹)
    (hYi : PRep 1365 11 Yi y⁻¹) {H : List (List Nat)} {R n : Nat} {root : Fin 1365}
    (h : trOK X Y Xi Yi H R n root = true) :
    ∀ k < n, ∃ g ∈ Subgroup.closure {g | ∃ w ∈ H, wP x y w = g}, (g root : Nat) = tpt R k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    have hk' := allN_spec h k hk
    simp only [CFSG.KC.Pack.strictB_eq] at hk'
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · have hp : Nat.beq (Nat.land (Nat.land (Nat.shiftRight R (Nat.mul (nat_lit 32) 0))
          (nat_lit 4294967295)) (nat_lit 2047)) root = true := hk'
      refine ⟨1, Subgroup.one_mem _, ?_⟩
      have e := Nat.eq_of_beq_eq_true hp
      rw [land_fld] at e
      exact e.symm
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hkb : Nat.beq (k' + 1) (nat_lit 0) = false := rfl
      rw [hkb] at hk'
      obtain ⟨hpar, hk2⟩ := band_iff.1 hk'
      obtain ⟨hg, hp⟩ := band_iff.1 hk2
      have hpar' := lt_of_blt' hpar
      have hg' := lt_of_blt' hg
      obtain ⟨g', hg'm, e'⟩ := ih _ hpar' (by omega)
      have hw := nthW_mem hg'
      refine ⟨wP x y (nthW H _) * g', Subgroup.mul_mem _ (Subgroup.subset_closure ⟨_, hw, rfl⟩)
        hg'm, ?_⟩
      have e := Nat.eq_of_beq_eq_true hp
      rw [land_fld] at e
      rw [Equiv.Perm.mul_apply, ← wv_eq hX hY hXi hYi, e']
      exact e.symm

theorem bitN_eq (s p : Nat) : bitN s p = if s.testBit p then 1 else 0 := by
  change (s >>> p) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (s / 2 ^ p) with h | h <;> simp [h]

theorem fold_bits {f : Nat → Nat → Nat} {t : Nat → Nat}
    (hf : ∀ k s, f k s ≠ 0 →
      s ≠ 0 ∧ t k < 1365 ∧ s.testBit (t k) = false ∧ f k s = s ||| 2 ^ t k) (s0 : Nat) :
    ∀ L : List Nat, L.foldr f s0 ≠ 0 →
      (∀ k ∈ L, t k < 1365 ∧ (L.foldr f s0).testBit (t k) = true) ∧ (L.map t).Nodup
  | [], _ => ⟨by simp, List.nodup_nil⟩
  | k :: L, h => by
    rw [List.foldr_cons] at h ⊢
    obtain ⟨hs, hk, hb, he⟩ := hf k _ h
    obtain ⟨ih1, ih2⟩ := fold_bits hf s0 L hs
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [he, Nat.testBit_or, Nat.testBit_two_pow]
      rcases List.mem_cons.1 hj with rfl | hj
      · exact ⟨hk, by simp⟩
      · exact ⟨(ih1 j hj).1, by simp [(ih1 j hj).2]⟩
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, ih2⟩
      obtain ⟨j, hj, e⟩ := List.mem_map.1 hm
      have h2 := (ih1 j hj).2
      rw [e, hb] at h2
      exact Bool.false_ne_true h2

theorem trMask_sound {R n : Nat} (h : trMask R n ≠ 0) :
    (∀ k < n, tpt R k < 1365 ∧ bitN (trMask R n) (tpt R k) = 1) ∧
      ∀ k < n, ∀ k' < n, tpt R k = tpt R k' → k = k' := by
  unfold trMask at h ⊢
  rw [CFSG.KC.Pack.foldN_eq] at h ⊢
  have key := fold_bits (t := tpt R) ?_ _ (List.range n) h
  · obtain ⟨h1, h2⟩ := key
    refine ⟨fun k hk => ?_, fun k hk k' hk' e => ?_⟩
    · obtain ⟨a, b⟩ := h1 k (List.mem_range.2 hk)
      refine ⟨a, ?_⟩
      rw [bitN_eq, b]
      rfl
    · exact List.inj_on_of_nodup_map h2 (List.mem_range.2 hk) (List.mem_range.2 hk') e
  · intro k s hne
    cases h1 : Nat.beq s (nat_lit 0) <;> cases h2 : Nat.blt (tpt R k) (nat_lit 1365) <;>
      cases h3 : Nat.beq (bitN s (tpt R k)) (nat_lit 0) <;>
      simp only [h1, h2, h3, CFSG.KC.Pack.strictN_eq] at hne ⊢ <;>
      try exact absurd rfl hne
    have h4 := Nat.eq_of_beq_eq_true h3
    rw [bitN_eq] at h4
    refine ⟨Nat.ne_of_beq_eq_false h1, lt_of_blt' h2, ?_, ?_⟩
    · cases hb : s.testBit (tpt R k)
      · rfl
      · rw [hb] at h4
        exact absurd h4 (by decide)
    · change s ||| 1 <<< tpt R k = _
      rw [Nat.one_shiftLeft]

theorem witK_sound {F A2 : Nat} {U0 U1 : List Nat} (h : witK X Y Xi Yi F U0 U1 A2 = true) :
    wv X Y Xi Yi U0 0 = ap F 0 ∧ wv X Y Xi Yi U1 0 = 0 ∧
      wv X Y Xi Yi U0 (wv X Y Xi Yi U1 1) = ap F 1 ∧ A2 < 1365 ∧
      wv X Y Xi Yi U0 (wv X Y Xi Yi U1 A2) = ap F 2 := by
  obtain ⟨h1, h⟩ := band_iff.1 h
  obtain ⟨h2, h⟩ := band_iff.1 h
  obtain ⟨h3, h⟩ := band_iff.1 h
  obtain ⟨h4, h5⟩ := band_iff.1 h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    lt_of_blt' h4, Nat.eq_of_beq_eq_true h5⟩

theorem tree2K_sound {F A2 T2R : Nat} {H2 : List (List Nat)} {U0 U1 : List Nat}
    (h : tree2K X Y Xi Yi F H2 T2R U0 U1 A2 = true) :
    fixK X Y Xi Yi H2 [0, 1] = true ∧ trOK X Y Xi Yi H2 T2R 180 2 = true ∧
      witK X Y Xi Yi F U0 U1 A2 = true ∧ trMask T2R 180 ≠ 0 ∧ bitN (trMask T2R 180) A2 = 0 := by
  obtain ⟨h1, h⟩ := band_iff.1 h
  obtain ⟨h2, h⟩ := band_iff.1 h
  obtain ⟨h3, h⟩ := band_iff.1 h
  rw [CFSG.KC.Pack.strictB_eq] at h
  obtain ⟨h4, h5⟩ := band_iff.1 h
  refine ⟨h1, h2, h3, fun e => ?_, Nat.eq_of_beq_eq_true h5⟩
  have e' : trMask T2R (nat_lit 180) = nat_lit 0 := e
  rw [e'] at h4
  exact Bool.false_ne_true h4

theorem allBlk0 {f : Nat → Bool} {len : Nat} (h : allBlk 0 f len = true) :
    ∀ l < len, f l = true := fun l hl => by
  have := allBlk_spec h l hl
  rwa [Nat.add_eq, Nat.zero_add] at this

theorem allBlk0_of {f : Nat → Bool} : ∀ {len : Nat}, (∀ l < len, f l = true) → allBlk 0 f len = true
  | 0, _ => rfl
  | len + 1, h => by
    change Bool.rec (motive := fun _ => Bool) false (allBlk 0 f len) (f (Nat.add 0 len)) = true
    rw [Nat.add_eq, Nat.zero_add, h len (by omega)]
    exact allBlk0_of fun l hl => h l (by omega)

theorem genSl_sound {G : Nat → Nat} {WS : List (List Nat)} {j s : Nat}
    (h : genSl X Y Xi Yi G WS j s = true) : ∀ k < 342, Nat.add (Nat.mul 342 s) k < 1365 →
      ap (G j) (Nat.add (Nat.mul 342 s) k) = wv X Y Xi Yi (nthW WS j) (Nat.add (Nat.mul 342 s) k) := by
  intro k hk hp
  have h1 := allN_spec h k hk
  rw [CFSG.KC.Pack.strictB_eq] at h1
  have hb : Nat.blt (Nat.add (Nat.mul 342 s) k) 1365 = true := Eq.mpr Nat.blt_eq hp
  rw [hb] at h1
  exact Nat.eq_of_beq_eq_true h1

theorem beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem lane_land (r : Nat) {i : Nat} (hi : i < 13) :
    lane (Nat.land r (nat_lit 11150372599265311570767859136324180752990207)) i = lane r i := by
  have e : (11150372599265311570767859136324180752990207 : Nat) = 2 ^ 143 - 1 := by norm_num
  change (r &&& 11150372599265311570767859136324180752990207) >>> (11 * i) &&& 2047 =
    r >>> (11 * i) &&& 2047
  rw [e]
  apply Nat.eq_of_testBit_eq
  intro t
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  have e2 : (2047 : Nat) = 2 ^ 11 - 1 := by norm_num
  rw [e2, Nat.testBit_two_pow_sub_one]
  by_cases ht : t < 11
  · have : 11 * i + t < 143 := by omega
    simp [this]
  · simp [ht]

theorem treeK_sound {G : Nat → Nat} {RP QP n r : Nat} (h : treeK G RP QP n r = true) :
    (n = 0 → ∀ i < 13, lane r i = lane QP i) ∧
      (n ≠ 0 → ∃ p g, p < n ∧ g < 4 ∧ ∀ i < 13, lane r i = ap (G g) (lane (nrec RP p) i)) := by
  unfold treeK at h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨fun _ i hi => ?_, fun h0 => absurd rfl h0⟩
    have e := Nat.eq_of_beq_eq_true h
    rw [← lane_land r hi, e]
  · have hb : Nat.beq n 0 = false := beq_false_of_ne (by omega)
    rw [hb, CFSG.KC.Pack.strictB_eq, CFSG.KC.Pack.strictB_eq] at h
    obtain ⟨h1, h2⟩ := band_iff.1 h
    rw [CFSG.KC.Pack.strictB_eq] at h2
    refine ⟨fun e => absurd e (by omega), fun _ => ⟨_, Nat.land (Nat.shiftRight r (nat_lit 204))
      (nat_lit 3), lt_of_blt' h1, Nat.lt_of_le_of_lt Nat.and_le_right (by decide), fun i hi => ?_⟩⟩
    exact Nat.eq_of_beq_eq_true (allBlk0 h2 i hi)

theorem closK_sound {G : Nat → Nat} {RP r : Nat} (h : closK G RP r = true) :
    ∀ j < 4, ∃ m < 4096, ∀ b < 3, lane (nrec RP m) b = ap (G j) (lane r b) := by
  intro j hj
  have h1 := allBlk0 h j hj
  rw [CFSG.KC.Pack.strictB_eq] at h1
  obtain ⟨h2, h3⟩ := band_iff.1 h1
  rw [CFSG.KC.Pack.strictB_eq] at h3
  exact ⟨_, lt_of_blt' h2, fun b hb => Nat.eq_of_beq_eq_true (allBlk0 h3 b hb)⟩

@[expose] def qi (QIP j b : Nat) : Nat :=
  fld(QIP, Nat.mul (nat_lit 4) (Nat.add (Nat.mul (nat_lit 3) j) b), nat_lit 15)

theorem commK_iff {G : Nat → Nat} {QIP r : Nat} :
    commK G QIP r = true ↔ ∀ j < 4, ∀ b < 3, ap (G j) (lane r b) = lane r (qi QIP j b) := by
  constructor
  · intro h j hj b hb
    exact Nat.eq_of_beq_eq_true (allBlk0 (allBlk0 h j hj) b hb)
  · intro h
    refine allBlk0_of fun j hj => allBlk0_of fun b hb => ?_
    change Nat.beq (ap (G j) (lane r b)) (lane r (qi QIP j b)) = true
    rw [h j hj b hb]
    exact Nat.beq_refl _

theorem nodeK_sound {G : Nat → Nat} {RP QP QIP : Nat} {NC : List Nat} {n : Nat}
    (h : nodeK G RP QP QIP NC n = true) :
    treeK G RP QP n (nrec RP n) = true ∧ closK G RP (nrec RP n) = true ∧
      (commK G QIP (nrec RP n) = true ↔ inL NC n = true) := by
  unfold nodeK at h
  rw [CFSG.KC.Pack.strictB_eq] at h
  obtain ⟨h1, h⟩ := band_iff.1 h
  obtain ⟨h2, h3⟩ := band_iff.1 h
  refine ⟨h1, h2, ?_⟩
  revert h3
  cases commK G QIP (nrec RP n) <;> cases inL NC n <;> simp

theorem inL_iff {n : Nat} : ∀ {L : List Nat}, inL L n = true ↔ n ∈ L
  | [] => by simp [inL]
  | c :: L => by
    change bIf(Nat.beq c n, true, inL L n) = true ↔ _
    rw [List.mem_cons, ← inL_iff (L := L)]
    cases h : Nat.beq c n
    · have : c ≠ n := Nat.ne_of_beq_eq_false h
      change inL L n = true ↔ n = c ∨ inL L n = true
      constructor
      · exact Or.inr
      · rintro (e | e)
        · exact absurd e.symm this
        · exact e
    · change true = true ↔ n = c ∨ inL L n = true
      exact ⟨fun _ => Or.inl (Nat.eq_of_beq_eq_true h).symm, fun _ => rfl⟩

@[expose] def noA (NOP i : Nat) : Nat := fld(NOP, Nat.mul (nat_lit 12) i, nat_lit 4095)

theorem ordK_sound {RP NOP i : Nat} (h : ordK RP NOP i = true) :
    noA NOP i < 4096 ∧ (i ≠ 0 → key (nrec RP (noA NOP (i - 1))) < key (nrec RP (noA NOP i))) := by
  unfold ordK at h
  rw [CFSG.KC.Pack.strictB_eq] at h
  obtain ⟨h1, h2⟩ := band_iff.1 h
  refine ⟨lt_of_blt' h1, fun hi => ?_⟩
  have hb : Nat.beq i 0 = false := beq_false_of_ne hi
  rw [hb, CFSG.KC.Pack.strictB_eq] at h2
  exact lt_of_blt' h2

theorem sSl_sound {G : Nat → Nat} {RP NOP QP QIP : Nat} {NC : List Nat} {s : Nat}
    (h : sSl G RP NOP QP QIP NC s = true) : ∀ k < 256,
      nodeK G RP QP QIP NC (Nat.add (Nat.mul 256 s) k) = true ∧
        ordK RP NOP (Nat.add (Nat.mul 256 s) k) = true := by
  intro k hk
  have h1 := allN_spec h k hk
  rw [CFSG.KC.Pack.strictB_eq] at h1
  exact band_iff.1 h1

theorem ncOne_sound {RP : Nat} {ZQ : List (List Nat)} {c w : Nat} (h : ncOne RP ZQ c w = true) :
    c < 4096 ∧ ∀ b < 3, lane (nrec RP c) b =
      nIf(Nat.beq w (nat_lit 0), b, nthN (nthW ZQ (Nat.sub w (nat_lit 1))) b) := by
  unfold ncOne at h
  obtain ⟨h1, h2⟩ := band_iff.1 h
  rw [CFSG.KC.Pack.strictB_eq] at h2
  exact ⟨lt_of_blt' h1, fun b hb => Nat.eq_of_beq_eq_true (allBlk0 h2 b hb)⟩

theorem baseK_sound {G : Nat → Nat} {RP QP QIP : Nat} {NC NCW : List Nat} {ZQ : List (List Nat)}
    (h : baseK G RP QP QIP NC NCW ZQ = true) :
    (∀ b < 3, lane QP b = b) ∧
      (∀ j < 4, ∀ b < 3, qi QIP j b < 13 ∧ lane QP (qi QIP j b) = ap (G j) b) ∧
      ∀ k < 4, ncOne RP ZQ (nthN NC k) (nthN NCW k) = true := by
  unfold baseK at h
  obtain ⟨-, h⟩ := band_iff.1 h
  obtain ⟨h1, h⟩ := band_iff.1 h
  obtain ⟨h2, h3⟩ := band_iff.1 h
  refine ⟨fun b hb => Nat.eq_of_beq_eq_true (allBlk0 h1 b hb), fun j hj b hb => ?_,
    fun k hk => allBlk0 h3 k hk⟩
  have h4 := allBlk0 (allBlk0 h2 j hj) b hb
  rw [CFSG.KC.Pack.strictB_eq] at h4
  obtain ⟨h5, h6⟩ := band_iff.1 h4
  exact ⟨lt_of_blt' h5, Nat.eq_of_beq_eq_true h6⟩

end CFSG.KS.Co1Row26683

namespace CFSG.KS.Co1Row26683Z

open CFSG.KC.Enum CFSG.KC.Pack

theorem allBlk_of {b : Nat} {f : Nat → Bool} :
    ∀ {len : Nat}, (∀ l < len, f (Nat.add b l) = true) → allBlk b f len = true
  | 0, _ => rfl
  | len + 1, h => by
    change Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) = true
    rw [h len (by omega)]
    exact allBlk_of fun l hl => h l (by omega)

theorem movedK_sound {S : Nat → Nat} {r : Nat} (h : movedK S r = true) :
    ∃ i, 2 ≤ i ∧ i < 6 ∧ pg 11 2047 (S i) r ≠ r := by
  by_contra hne'
  have hne : ∀ i, 2 ≤ i → i < 6 → pg 11 2047 (S i) r = r := fun i h1 h2 => by
    by_contra e
    exact hne' ⟨i, h1, h2, e⟩
  have ha : allBlk 2 (fun i => Nat.beq (pg 11 2047 (S i) r) r) 4 = true :=
    allBlk_of fun l hl => by
      have e := hne (2 + l) (by omega) (by omega)
      change Nat.beq (pg 11 2047 (S (2 + l)) r) r = true
      rw [e]
      exact Nat.beq_refl r
  have hb : movedK S r = false := congrArg Bool.not ha
  rw [hb] at h
  exact Bool.false_ne_true h

theorem primK_sound {S : Nat → Nat} : ∀ {reps : List Nat}, primK S reps = true →
    ∀ r ∈ reps, movedK S r = true
  | [], _, r, hr => by simp at hr
  | r0 :: reps, h, r, hr => by
    obtain ⟨h1, h2⟩ := band_iff.1 h
    rcases List.mem_cons.1 hr with rfl | hr
    · exact h1
    · exact primK_sound h2 r hr

open CFSG.KS.Raw.Orb

open CFSG.KS.Co1Row26683 in
theorem lpP_inv (x y : Equiv.Perm (Fin 1365)) (c : Nat) : lpP x⁻¹ y⁻¹ c = (lpP x y c)⁻¹ := by
  unfold lpP
  cases Nat.beq c (nat_lit 1) <;> cases Nat.beq c (nat_lit 2) <;>
    cases Nat.beq c (nat_lit 3) <;> simp

open CFSG.KS.Co1Row26683 in
theorem wvI_eq {X Y Xi Yi : Nat} {x y : Equiv.Perm (Fin 1365)} (hX : PRep 1365 11 X x)
    (hY : PRep 1365 11 Y y) (hXi : PRep 1365 11 Xi x⁻¹) (hYi : PRep 1365 11 Yi y⁻¹) :
    ∀ (w : List Nat) (q : Fin 1365), wvI X Y Xi Yi w q = ((wP x y w)⁻¹ q : Nat)
  | [], _ => rfl
  | c :: t, q => by
    have hX' : PRep 1365 11 X x⁻¹⁻¹ := by rwa [inv_inv]
    have hY' : PRep 1365 11 Y y⁻¹⁻¹ := by rwa [inv_inv]
    change strictN (ap (lp Xi Yi X Y c) q) (wvI X Y Xi Yi t) = _
    rw [CFSG.KC.Pack.strictN_eq, ap_prep (lp_prep hXi hYi hX' hY' c), wvI_eq hX hY hXi hYi t,
      lpP_inv]
    change _ = (((lpP x y c * wP x y t)⁻¹ q : Fin 1365) : Nat)
    rw [mul_inv_rev, Equiv.Perm.mul_apply]

open CFSG.KS.Co1Row26683 in
theorem zqK_sound {X Y Xi Yi P : Nat} {WC ZQ : List (List Nat)} (h : zqK X Y Xi Yi P WC ZQ = true) :
    (∀ b < 3, nthN (nthW ZQ 0) b = ap P b) ∧ ∀ i < 2, ∀ b < 3,
      nthN (nthW ZQ (i + 1)) b = wv X Y Xi Yi (nthW WC i) (ap P (wvI X Y Xi Yi (nthW WC i) b)) := by
  unfold zqK at h
  obtain ⟨h1, h2⟩ := band_iff.1 h
  exact ⟨fun b hb => Nat.eq_of_beq_eq_true (allBlk0 h1 b hb),
    fun i hi b hb => Nat.eq_of_beq_eq_true (allBlk0 (allBlk0 h2 i hi) b hb)⟩

end CFSG.KS.Co1Row26683Z

end
