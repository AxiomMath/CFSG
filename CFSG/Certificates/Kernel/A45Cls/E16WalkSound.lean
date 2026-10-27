module

public import Certificates.Data.Kernel.A45Cls.E16Walk
public import CFSG.Certificates.Kernel.A45Cls.DefsSound
public import CFSG.Certificates.Kernel.A45Cls.PockSound
public import CFSG.Certificates.Kernel.OrbFindSound
public import CFSG.Certificates.Kernel.PermCent.OrbGroup
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KC.E16Walk

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.KC.BfsPin
  CFSG.KC.EnumSound

local notation "Pm" => Equiv.Perm (Fin 45)

theorem bA {a b : Bool} : Bool.rec (motive := fun _ => Bool) false b a = true ↔
    a = true ∧ b = true := by
  cases a <;> cases b <;> simp

theorem bEqK_iff {a b : Bool} : bEqK a b = true ↔ a = b := by
  cases a <;> cases b <;> decide

theorem bitK_iff (m i : ℕ) : bitK m i = true ↔ m.testBit i = true := by
  change Nat.blt 0 (m &&& 1 <<< i) = true ↔ _
  rw [Nat.blt_eq, Nat.one_shiftLeft]
  constructor
  · intro h
    by_contra hb
    have h0 : m &&& 2 ^ i = 0 := Nat.eq_of_testBit_eq fun j => by
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hj : i = j
      · subst hj
        simp_all
      · simp [hj]
    omega
  · intro h
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have := congrArg (Nat.testBit · i) h0
    simp [Nat.testBit_and, Nat.testBit_two_pow_self, h] at this

theorem bitK_false {m i : ℕ} (h : m.testBit i = false) : bitK m i = false := by
  cases e : bitK m i
  · rfl
  · rw [(bitK_iff _ _).1 e] at h
    exact absurd h (by decide)

theorem subK_iff {c u : ℕ} : subK c u = true ↔ ∀ i, c.testBit i = true → u.testBit i = true := by
  change Nat.beq (c &&& u) c = true ↔ _
  rw [Nat.beq_eq]
  constructor
  · intro h i hi
    rw [← h, Nat.testBit_and, Bool.and_eq_true] at hi
    exact hi.2
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hc : c.testBit i
    · rfl
    · rw [h i hc]
      rfl

theorem lt43 {m i : ℕ} (hm : m < 2 ^ 43) (h : m.testBit i = true) : i < 43 := by
  by_contra hc
  rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) (by omega)))]
    at h
  exact absurd h (by decide)

theorem lt_of_bits {a b : ℕ} (hb : b < 2 ^ 43) (h : ∀ i, a.testBit i = true → b.testBit i = true) :
    a < 2 ^ 43 :=
  Nat.lt_pow_two_of_testBit a fun i hi => by
    cases e : a.testBit i
    · rfl
    · exact absurd (lt43 hb (h i e)) (by omega)

theorem w_add_eq_or {a b : ℕ} (h : a &&& b = 0) : a + b = a ||| b := by
  have hab : a + b < 2 ^ (a + b) := Nat.lt_two_pow_self
  have ha : a < 2 ^ (a + b) := lt_of_le_of_lt (by omega) hab
  have hb : b < 2 ^ (a + b) := lt_of_le_of_lt (by omega) hab
  have h0 : BitVec.ofNat (a + b) a &&& BitVec.ofNat (a + b) b = 0#(a + b) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb, h, BitVec.toNat_zero]
  have key := congrArg BitVec.toNat (BitVec.add_eq_or_of_and_eq_zero _ _ h0)
  rw [BitVec.toNat_add, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hab] at key
  exact key

theorem w_sub_land (y K p : ℕ) :
    (y - (y &&& K)).testBit p = (y.testBit p && !K.testBit p) := by
  have h1 : (y &&& K) &&& (y ^^^ (y &&& K)) = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
    cases y.testBit i <;> cases K.testBit i <;> decide
  have h2 : (y &&& K) ||| (y ^^^ (y &&& K)) = y := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
    cases y.testBit i <;> cases K.testBit i <;> decide
  have h3 := w_add_eq_or h1
  have e : y - (y &&& K) = y ^^^ (y &&& K) := by omega
  rw [e, Nat.testBit_xor, Nat.testBit_and]
  cases y.testBit p <;> cases K.testBit p <;> decide

theorem lrec_all {f : ℕ → Bool} : ∀ {E : List ℕ},
    List.rec (motive := fun _ => Bool) true
      (fun e _ ih => Bool.rec (motive := fun _ => Bool) false ih (f e)) E = true →
    ∀ e ∈ E, f e = true
  | [], _ => by simp
  | e :: E, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false (List.rec (motive := fun _ => Bool) true
        (fun e _ ih => Bool.rec (motive := fun _ => Bool) false ih (f e)) E) (f e) = true := h
    rw [bA] at h'
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h'.1
    · exact lrec_all h'.2 x hx

theorem lrec_all2 {f g : ℕ → Bool} : ∀ {E : List ℕ},
    List.rec (motive := fun _ => Bool) true
      (fun e _ ih => Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false ih (g e)) (f e)) E = true →
    ∀ e ∈ E, f e = true ∧ g e = true
  | [], _ => by simp
  | e :: E, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
        (List.rec (motive := fun _ => Bool) true (fun e _ ih => Bool.rec (motive := fun _ => Bool)
          false (Bool.rec (motive := fun _ => Bool) false ih (g e)) (f e)) E) (g e)) (f e) = true :=
      h
    rw [bA, bA] at h'
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨h'.1, h'.2.1⟩
    · exact lrec_all2 h'.2.2 x hx

theorem orBits_testBit (f : ℕ → ℕ) : ∀ (E : List ℕ) (i : ℕ),
    (orBits f E).testBit i = true ↔ ∃ e ∈ E, f e = i
  | [], i => by
    change (0 : ℕ).testBit i = true ↔ _
    simp
  | e :: E, i => by
    change (1 <<< f e ||| orBits f E).testBit i = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, orBits_testBit f E i, Nat.one_shiftLeft,
      Nat.testBit_two_pow]
    constructor
    · rintro (h | ⟨x, hx, h⟩)
      · exact ⟨e, List.mem_cons_self, of_decide_eq_true h⟩
      · exact ⟨x, List.mem_cons_of_mem _ hx, h⟩
    · rintro ⟨x, hx, h⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Or.inl (decide_eq_true h)
      · exact Or.inr ⟨x, hx, h⟩

theorem inMasks_spec {x : ℕ} : ∀ {P : List ℕ}, inMasks P x = true → ∃ p ∈ P, mK p = x
  | [], h => by
    change false = true at h
    exact absurd h (by decide)
  | p :: P, h => by
    change Bool.rec (motive := fun _ => Bool) (inMasks P x) true (Nat.beq (mK p) x) = true at h
    cases hb : Nat.beq (mK p) x
    · rw [hb] at h
      obtain ⟨p', hp', e⟩ := inMasks_spec (P := P) h
      exact ⟨p', List.mem_cons_of_mem _ hp', e⟩
    · exact ⟨p, List.mem_cons_self, Nat.eq_of_beq_eq_true hb⟩

theorem unionK_testBit {p i : ℕ} : ∀ {L : List ℕ}, (unionK L p).testBit i = true →
    ∃ q ∈ L, Nat.land (mK q) p = p ∧ (mK q).testBit i = true
  | [], h => by
    change (0 : ℕ).testBit i = true at h
    simp at h
  | q :: L, h => by
    change (Bool.rec (motive := fun _ => ℕ) (unionK L p) (Nat.lor (mK q) (unionK L p))
      (Nat.beq (Nat.land (mK q) p) p)).testBit i = true at h
    cases hb : Nat.beq (Nat.land (mK q) p) p
    · rw [hb] at h
      obtain ⟨q', hq', h'⟩ := unionK_testBit (L := L) h
      exact ⟨q', List.mem_cons_of_mem _ hq', h'⟩
    · rw [hb] at h
      change (mK q ||| unionK L p).testBit i = true at h
      rw [Nat.testBit_or, Bool.or_eq_true] at h
      rcases h with h | h
      · exact ⟨q, List.mem_cons_self, Nat.eq_of_beq_eq_true hb, h⟩
      · obtain ⟨q', hq', h'⟩ := unionK_testBit (L := L) h
        exact ⟨q', List.mem_cons_of_mem _ hq', h'⟩

noncomputable def crow (full : ℕ) (E : List ℕ) (p : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) full
    (fun e _ ih => nIf(bitK p (posK e), Nat.land (rowK e) ih, ih)) E

theorem crow_testBit (full p i : ℕ) : ∀ E : List ℕ, (crow full E p).testBit i = true ↔
    full.testBit i = true ∧ ∀ e ∈ E, p.testBit (posK e) = true → (rowK e).testBit i = true
  | [] => by
    change full.testBit i = true ↔ _
    simp
  | e :: E => by
    have ih := crow_testBit full p i E
    change (Bool.rec (motive := fun _ => ℕ) (crow full E p) (Nat.land (rowK e) (crow full E p))
      (bitK p (posK e))).testBit i = true ↔ _
    rw [List.forall_mem_cons]
    cases hb : bitK p (posK e)
    · have hb' : p.testBit (posK e) = false := by
        cases e' : p.testBit (posK e)
        · rfl
        · rw [(bitK_iff _ _).2 e'] at hb
          exact absurd hb (by decide)
      change (crow full E p).testBit i = true ↔ _
      rw [ih]
      constructor
      · rintro ⟨hf, hall⟩
        exact ⟨hf, fun h => by rw [hb'] at h; exact absurd h (by decide), hall⟩
      · rintro ⟨hf, -, hall⟩
        exact ⟨hf, hall⟩
    · have hb' := (bitK_iff _ _).1 hb
      change (rowK e &&& crow full E p).testBit i = true ↔ _
      rw [Nat.testBit_and, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨hr, hf, hall⟩
        exact ⟨hf, fun _ => hr, hall⟩
      · rintro ⟨hf, hr, hall⟩
        exact ⟨hr hb', hf, hall⟩

theorem candK_testBit {full p i : ℕ} {E : List ℕ} :
    (candK full E p).testBit i = ((crow full E p).testBit i && !p.testBit i) := by
  change (crow full E p - (crow full E p &&& p)).testBit i = _
  exact w_sub_land _ _ _

theorem comm_of_sq {a b : Pm} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b * (a * b) = 1) :
    a * b = b * a := by
  have h1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have h2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  rw [eq_inv_of_mul_eq_one_left hab, mul_inv_rev, h1, h2]

theorem eq22_of_comm {P Q : ℕ} {g h : Pm} (hP : PRep 45 6 P g) (hQ : PRep 45 6 Q h)
    (hc : g * h = h * g) : eq22 45 6 (mask 6) P Q Q P = true := by
  unfold eq22
  refine Raw.Orb.allN_iff.2 fun i hi => ?_
  have e : g (h ⟨i, hi⟩) = h (g ⟨i, hi⟩) := by
    rw [← Equiv.Perm.mul_apply, hc, Equiv.Perm.mul_apply]
  rw [prep_at hQ hi, prep_at hP hi, hP (h ⟨i, hi⟩), hQ (g ⟨i, hi⟩), e]
  exact Nat.beq_refl _

theorem exists_t {G : Subgroup Pm} {N : ℕ} {T : ℕ → ℕ} (hG : Nat.card G = N)
    (hT : ∀ y ∈ G, ∃ i < N, PRep 45 6 (T i) y) :
    ∃ t : ℕ → Pm, (∀ i < N, PRep 45 6 (T i) (t i) ∧ t i ∈ G) ∧
      ∀ i < N, ∀ j < N, t i = t j → i = j := by
  classical
  let f : G → Fin N := fun y => ⟨(hT y y.2).choose, (hT y y.2).choose_spec.1⟩
  have hf : Function.Injective f := by
    intro y z e
    have e' : (hT y y.2).choose = (hT z z.2).choose := congrArg Fin.val e
    have h1 := (hT y y.2).choose_spec.2
    have h2 := (hT z z.2).choose_spec.2
    rw [e'] at h1
    exact Subtype.ext (prep_unique h1 h2)
  have hb : Function.Bijective f :=
    hf.bijective_of_nat_card_le (le_of_eq (by rw [Nat.card_fin, hG]))
  let g := Function.surjInv hb.2
  refine ⟨fun i => if h : i < N then (g ⟨i, h⟩ : Pm) else 1, fun i hi => ?_, ?_⟩
  · simp only [dif_pos hi]
    refine ⟨?_, (g ⟨i, hi⟩).2⟩
    have e := Function.surjInv_eq hb.2 ⟨i, hi⟩
    have h1 := (hT _ (g ⟨i, hi⟩).2).choose_spec.2
    have e' : (hT _ (g ⟨i, hi⟩).2).choose = i := congrArg Fin.val e
    rw [e'] at h1
    exact h1
  · intro i hi j hj e
    simp only [dif_pos hi, dif_pos hj] at e
    have := congrArg f (Subtype.ext e : g ⟨i, hi⟩ = g ⟨j, hj⟩)
    have e1 := Function.surjInv_eq hb.2 ⟨i, hi⟩
    have e2 := Function.surjInv_eq hb.2 ⟨j, hj⟩
    exact congrArg Fin.val (e1.symm.trans (this.trans e2))

abbrev pT (posT j : ℕ) : ℕ := fld(posT, Nat.mul (nat_lit 6) j, nat_lit 63)

abbrev jJ (jT k : ℕ) : ℕ := fld(jT, Nat.mul (nat_lit 8) k, nat_lit 255)

structure Tab (T : ℕ → ℕ) (N im posT jT : ℕ) (E : List ℕ) (t : ℕ → Pm) : Prop where
  prep : ∀ i < N, PRep 45 6 (T i) (t i)
  inj : ∀ i < N, ∀ j < N, t i = t j → i = j
  imN : im < 2 ^ N
  inv : invOK T N im = true
  tab : tabOK im 43 posT jT E = true
  pos : posOK N im posT jT = true

variable {T : ℕ → ℕ} {N im posT jT : ℕ} {E : List ℕ} {t : ℕ → Pm}

theorem Tab.tab3 (W : Tab T N im posT jT E t) :
    orBits jK E = im ∧ orBits posK E = 2 ^ 43 - 1 ∧
      ∀ e ∈ E, pT posT (jK e) = posK e ∧ jJ jT (posK e) = jK e := by
  have h := W.tab
  unfold tabOK at h
  rw [bA, bA] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h1, (Nat.eq_of_beq_eq_true h2).trans (by decide), fun e he => ?_⟩
  have := lrec_all2 h3 e he
  exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩

theorem Tab.bitN (W : Tab T N im posT jT E t) {j : ℕ} (hb : im.testBit j = true) : j < N := by
  by_contra hc
  rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le W.imN (Nat.pow_le_pow_right (by decide) (by omega)))]
    at hb
  exact absurd hb (by decide)

theorem Tab.pos_lt (W : Tab T N im posT jT E t) {e : ℕ} (he : e ∈ E) : posK e < 43 := by
  have hk : (orBits posK E).testBit (posK e) = true := (orBits_testBit posK E _).2 ⟨e, he, rfl⟩
  rw [W.tab3.2.1, Nat.testBit_two_pow_sub_one] at hk
  exact of_decide_eq_true hk

theorem Tab.entry (W : Tab T N im posT jT E t) {k : ℕ} (hk : k < 43) :
    ∃ e ∈ E, posK e = k ∧ jK e = jJ jT k := by
  obtain ⟨-, h2, h3⟩ := W.tab3
  have : (orBits posK E).testBit k = true := by
    rw [h2, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hk
  obtain ⟨e, he, rfl⟩ := (orBits_testBit posK E k).1 this
  exact ⟨e, he, rfl, ((h3 e he).2).symm⟩

theorem Tab.posn (W : Tab T N im posT jT E t) {k : ℕ} (hk : k < 43) :
    jJ jT k < N ∧ im.testBit (jJ jT k) = true ∧ pT posT (jJ jT k) = k := by
  obtain ⟨e, he, rfl, hj⟩ := W.entry hk
  obtain ⟨h1, -, h3⟩ := W.tab3
  have hb : im.testBit (jK e) = true := by
    rw [← h1]
    exact (orBits_testBit jK E _).2 ⟨e, he, rfl⟩
  rw [← hj]
  exact ⟨W.bitN hb, hb, (h3 e he).1⟩

theorem Tab.idx (W : Tab T N im posT jT E t) {j : ℕ} (hb : im.testBit j = true) :
    pT posT j < 43 ∧ jJ jT (pT posT j) = j := by
  obtain ⟨h1, -, h3⟩ := W.tab3
  rw [← h1] at hb
  obtain ⟨e, he, rfl⟩ := (orBits_testBit jK E j).1 hb
  rw [(h3 e he).1]
  exact ⟨W.pos_lt he, (h3 e he).2⟩

theorem Tab.inv_iff (W : Tab T N im posT jT E t) {j : ℕ} (hj : j < N) :
    orderOf (t j) = 2 ↔ im.testBit j = true := by
  have h := Raw.Orb.allN_iff.1 W.inv j hj
  rw [← isInvK_iff (by norm_num) (W.prep j hj), bEqK_iff.1 h, bitK_iff]

theorem Tab.x_inv (W : Tab T N im posT jT E t) {k : ℕ} (hk : k < 43) :
    t (jJ jT k) * t (jJ jT k) = 1 ∧ t (jJ jT k) ≠ 1 := by
  obtain ⟨hN, hb, -⟩ := W.posn hk
  have := orderOf_eq_prime_iff.1 ((W.inv_iff hN).2 hb)
  exact ⟨by rw [← sq]; exact this.1, this.2⟩

theorem Tab.inv_bit (W : Tab T N im posT jT E t) {j : ℕ} (hj : j < N) (h2 : t j * t j = 1)
    (h1 : t j ≠ 1) : im.testBit j = true :=
  (W.inv_iff hj).1 (orderOf_eq_prime_iff.2 ⟨by rw [sq]; exact h2, h1⟩)

theorem Tab.x_inj (W : Tab T N im posT jT E t) {k k' : ℕ} (hk : k < 43) (hk' : k' < 43)
    (e : t (jJ jT k) = t (jJ jT k')) : k = k' := by
  obtain ⟨hN, -, hp⟩ := W.posn hk
  obtain ⟨hN', -, hp'⟩ := W.posn hk'
  calc k = pT posT (jJ jT k) := hp.symm
    _ = pT posT (jJ jT k') := by rw [W.inj _ hN _ hN' e]
    _ = k' := hp'

theorem posOK_spec (h : posOK N im posT jT = true) {j : ℕ} (hj : j < N)
    (hb : im.testBit j = false) : pT posT j = 63 := by
  have := Raw.Orb.allN_iff.1 h j hj
  rw [bitK_false hb] at this
  exact Nat.eq_of_beq_eq_true this

def pos43 (m : ℕ) : Finset ℕ := (Finset.range 43).filter fun k => m.testBit k = true

def Qs (jT : ℕ) (t : ℕ → Pm) (m : ℕ) : Finset Pm :=
  insert 1 ((pos43 m).image fun k => t (jJ jT k))

def Cl (X : Finset Pm) : Prop := ∀ a ∈ X, ∀ b ∈ X, a * b ∈ X

theorem mem_pos43 {m k : ℕ} : k ∈ pos43 m ↔ k < 43 ∧ m.testBit k = true := by
  unfold pos43
  rw [Finset.mem_filter, Finset.mem_range]

theorem mem_Qs {m : ℕ} {y : Pm} :
    y ∈ Qs jT t m ↔ y = 1 ∨ ∃ k < 43, m.testBit k = true ∧ t (jJ jT k) = y := by
  unfold Qs
  rw [Finset.mem_insert, Finset.mem_image]
  simp only [mem_pos43, and_assoc]

theorem one_mem_Qs {m : ℕ} : (1 : Pm) ∈ Qs jT t m := mem_Qs.2 (Or.inl rfl)

theorem x_mem {m k : ℕ} (hk : k < 43) (hm : m.testBit k = true) : t (jJ jT k) ∈ Qs jT t m :=
  mem_Qs.2 (Or.inr ⟨k, hk, hm, rfl⟩)

theorem qs_mono {a b : ℕ} (h : ∀ i, a.testBit i = true → b.testBit i = true) :
    Qs jT t a ⊆ Qs jT t b := fun y hy => by
  rcases mem_Qs.1 hy with rfl | ⟨k, hk, hb, rfl⟩
  · exact one_mem_Qs
  · exact x_mem hk (h k hb)

theorem popK_eq {m : ℕ} (hm : m < 2 ^ 43) : popK m = (pos43 m).card := by
  rw [popK, cntN_eq]
  congr 1
  ext i
  rw [Finset.mem_filter, Finset.mem_range, bitK_iff, mem_pos43]
  constructor
  · rintro ⟨-, h⟩
    exact ⟨lt43 hm h, h⟩
  · rintro ⟨h1, h2⟩
    exact ⟨lt_trans h1 (by decide), h2⟩

theorem Tab.qs_sq (W : Tab T N im posT jT E t) {m : ℕ} {y : Pm} (hy : y ∈ Qs jT t m) :
    y * y = 1 := by
  rcases mem_Qs.1 hy with rfl | ⟨k, hk, -, rfl⟩
  · exact mul_one 1
  · exact (W.x_inv hk).1

theorem Tab.qs_card (W : Tab T N im posT jT E t) (m : ℕ) :
    (Qs jT t m).card = (pos43 m).card + 1 := by
  have hinj : Set.InjOn (fun k => t (jJ jT k)) (pos43 m) := fun a ha b hb e =>
    W.x_inj (mem_pos43.1 (Finset.mem_coe.1 ha)).1 (mem_pos43.1 (Finset.mem_coe.1 hb)).1 e
  have hn : (1 : Pm) ∉ (pos43 m).image fun k => t (jJ jT k) := fun h => by
    obtain ⟨k, hk, e⟩ := Finset.mem_image.1 h
    exact (W.x_inv (mem_pos43.1 hk).1).2 e
  rw [Qs, Finset.card_insert_of_notMem hn, Finset.card_image_of_injOn hinj]

theorem coset_card {X : Finset Pm} (hX : Cl X) (hsq : ∀ y ∈ X, y * y = 1) {b : Pm} (hb : b ∉ X) :
    (X ∪ X.image (b * ·)).card = 2 * X.card := by
  have hdisj : Disjoint X (X.image (b * ·)) := by
    rw [Finset.disjoint_left]
    intro a ha hab
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hab
    apply hb
    have e : b * y * y = b := by rw [mul_assoc, hsq y hy, mul_one]
    rw [← e]
    exact hX _ ha _ hy
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ (mul_right_injective b)]
  ring

theorem Tab.qs_one (W : Tab T N im posT jT E t) {p k : ℕ} (hk : k < 43) (hp : pos43 p = {k}) :
    Cl (Qs jT t p) ∧ (Qs jT t p).card = 2 := by
  have hmem : ∀ y ∈ Qs jT t p, y = 1 ∨ y = t (jJ jT k) := by
    intro y hy
    rcases mem_Qs.1 hy with h | ⟨k', hk', hb, rfl⟩
    · exact Or.inl h
    · have : k' ∈ pos43 p := mem_pos43.2 ⟨hk', hb⟩
      rw [hp, Finset.mem_singleton] at this
      rw [this]
      exact Or.inr rfl
  have hkm : k ∈ pos43 p := by
    rw [hp]
    exact Finset.mem_singleton_self k
  have hx : t (jJ jT k) ∈ Qs jT t p := x_mem hk (mem_pos43.1 hkm).2
  refine ⟨fun a ha b hb => ?_, by rw [W.qs_card, hp, Finset.card_singleton]⟩
  rcases hmem a ha with rfl | rfl <;> rcases hmem b hb with rfl | rfl
  · rw [mul_one]
    exact one_mem_Qs
  · rw [one_mul]
    exact hx
  · rw [mul_one]
    exact hx
  · rw [(W.x_inv hk).1]
    exact one_mem_Qs

theorem prodIn_spec {ps : List ℕ} {S : ℕ → ℕ} {m a b : ℕ} (h : prodIn ps T S N posT m a b = true) :
    ∃ j < N, T j = pcomp 45 6 (mask 6) (T a) (T b) ∧ m.testBit (pT posT j) = true := by
  unfold prodIn at h
  rw [strictB_eq', bA, bA] at h
  exact ⟨_, Nat.blt_eq.mp h.1, Nat.eq_of_beq_eq_true h.2.1, (bitK_iff _ _).1 h.2.2⟩

theorem node_basic {ps : List ℕ} {S : ℕ → ℕ} {q : ℕ} (hq : nodeOK ps T S N posT jT E q = true) :
    popK (mK q) = 2 * popK (pmK q) + 1 ∧ (mK q).testBit (dK q) = true ∧
      (pmK q).testBit (dK q) = false ∧
      (∀ i, (pmK q).testBit i = true → (mK q).testBit i = true) ∧
      ∀ f ∈ E, (pmK q).testBit (posK f) = true →
        prodIn ps T S N posT (mK q) (jJ jT (dK q)) (jK f) = true := by
  unfold nodeOK at hq
  rw [bA, bA, bA, bA] at hq
  obtain ⟨h1, h2, h3, h4, h5⟩ := hq
  refine ⟨Nat.eq_of_beq_eq_true h1, (bitK_iff _ _).1 h2, ?_, subK_iff.1 h4, fun f hf hb => ?_⟩
  · cases e : (pmK q).testBit (dK q)
    · rfl
    · rw [(bitK_iff _ _).2 e] at h3
      exact absurd h3 (by decide)
  · have := lrec_all h5 f hf
    rw [(bitK_iff _ _).2 hb] at this
    exact this

theorem Tab.node_core (W : Tab T N im posT jT E t) {ps : List ℕ} {S : ℕ → ℕ} {m pm d : ℕ}
    (hm : m < 2 ^ 43) (hpop : popK m = 2 * popK pm + 1) (hd : m.testBit d = true)
    (hnd : pm.testBit d = false) (hsub : ∀ i, pm.testBit i = true → m.testBit i = true)
    (hrow : ∀ f ∈ E, pm.testBit (posK f) = true → prodIn ps T S N posT m (jJ jT d) (jK f) = true)
    (hF : Cl (Qs jT t pm)) :
    Cl (Qs jT t m) ∧ (Qs jT t m).card = 2 * (Qs jT t pm).card := by
  have hpm : pm < 2 ^ 43 := lt_of_bits hm hsub
  have hd43 : d < 43 := lt43 hm hd
  have hδm : t (jJ jT d) ∈ Qs jT t m := x_mem hd43 hd
  have hprod : ∀ y ∈ Qs jT t pm, t (jJ jT d) * y ∈ Qs jT t m := by
    intro y hy
    rcases mem_Qs.1 hy with rfl | ⟨k, hk, hb, rfl⟩
    · rw [mul_one]
      exact hδm
    · obtain ⟨e, he, rfl, hje⟩ := W.entry hk
      obtain ⟨j, hj, hT, hjm⟩ := prodIn_spec (hrow e he hb)
      have hdN : jJ jT d < N := (W.posn hd43).1
      have hkN : jK e < N := by
        rw [hje]
        exact (W.posn hk).1
      have e1 : t j = t (jJ jT d) * t (jK e) := prep_unique (W.prep j hj) (by
        rw [hT]
        exact prep_pcomp (by norm_num) (W.prep _ hdN) (W.prep _ hkN))
      have hjim : im.testBit j = true := by
        cases e2 : im.testBit j
        · rw [posOK_spec W.pos hj e2] at hjm
          have h63 : m.testBit 63 = false := Nat.testBit_lt_two_pow
            (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) (by decide)))
          rw [h63] at hjm
          exact absurd hjm (by decide)
        · rfl
      obtain ⟨hk', hjj⟩ := W.idx hjim
      rw [← hje, ← e1, ← hjj]
      exact x_mem hk' hjm
  have hδn : t (jJ jT d) ∉ Qs jT t pm := by
    intro h
    rcases mem_Qs.1 h with h1 | ⟨k, hk, hb, e⟩
    · exact (W.x_inv hd43).2 h1
    · rw [W.x_inj hk hd43 e, hnd] at hb
      exact absurd hb (by decide)
  have hU : Qs jT t pm ∪ (Qs jT t pm).image (t (jJ jT d) * ·) ⊆ Qs jT t m :=
    Finset.union_subset (qs_mono hsub) fun z hz => by
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
      exact hprod y hy
  have hcardM : (Qs jT t m).card = 2 * (Qs jT t pm).card := by
    rw [W.qs_card, W.qs_card, ← popK_eq hm, ← popK_eq hpm, hpop]
    ring
  have heq : Qs jT t pm ∪ (Qs jT t pm).image (t (jJ jT d) * ·) = Qs jT t m :=
    Finset.eq_of_subset_of_card_le hU (by rw [coset_card hF (fun y hy => W.qs_sq hy) hδn, hcardM])
  refine ⟨?_, hcardM⟩
  have hcomm : ∀ y ∈ Qs jT t pm, t (jJ jT d) * y = y * t (jJ jT d) := fun y hy =>
    comm_of_sq (W.qs_sq hδm) (W.qs_sq hy) (W.qs_sq (hprod y hy))
  intro a ha b hb
  rw [← heq] at ha hb ⊢
  rcases Finset.mem_union.1 ha with ha | ha <;> rcases Finset.mem_union.1 hb with hb | hb
  · exact Finset.mem_union_left _ (hF a ha b hb)
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hb
    refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨a * y, hF a ha y hy, ?_⟩)
    change t (jJ jT d) * (a * y) = a * (t (jJ jT d) * y)
    rw [← mul_assoc, ← mul_assoc, hcomm a ha]
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 ha
    refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨y * b, hF y hy b hb, ?_⟩)
    change t (jJ jT d) * (y * b) = t (jJ jT d) * y * b
    rw [mul_assoc]
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hb
    refine Finset.mem_union_left _ ?_
    have e : t (jJ jT d) * y * (t (jJ jT d) * z) = y * z := by
      rw [hcomm y hy, mul_assoc, ← mul_assoc (t (jJ jT d)) (t (jJ jT d)) z, W.qs_sq hδm, one_mul]
    rw [e]
    exact hF y hy z hz

theorem mK_lt {full q : ℕ} (hfull : full = 2 ^ 43 - 1) (h : subK (mK q) full = true) :
    mK q < 2 ^ 43 :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    cases e : (mK q).testBit i
    · rfl
    · have := subK_iff.1 h i e
      rw [hfull, Nat.testBit_two_pow_sub_one] at this
      exact absurd (of_decide_eq_true this) (by omega)

theorem Tab.node_spec (W : Tab T N im posT jT E t) {ps : List ℕ} {S : ℕ → ℕ} {q : ℕ}
    (hq : nodeOK ps T S N posT jT E q = true) (hm : mK q < 2 ^ 43) (hF : Cl (Qs jT t (pmK q))) :
    Cl (Qs jT t (mK q)) ∧ (Qs jT t (mK q)).card = 2 * (Qs jT t (pmK q)).card := by
  obtain ⟨hpop, hd, hnd, hsub, hrow⟩ := node_basic hq
  exact W.node_core hm hpop hd hnd hsub hrow hF

theorem Tab.level2 (W : Tab T N im posT jT E t) {ps : List ℕ} {S : ℕ → ℕ} {full : ℕ}
    {L : List ℕ} (hfull : full = 2 ^ 43 - 1) (hn : nodesOK ps T S N posT jT E L = true)
    (hp : par1OK full L = true) :
    ∀ q ∈ L, Cl (Qs jT t (mK q)) ∧ (Qs jT t (mK q)).card = 2 * 2 ∧ mK q < 2 ^ 43 := by
  intro q hq
  have hnq := lrec_all hn q hq
  obtain ⟨hs, h1⟩ := lrec_all2 hp q hq
  have hm := mK_lt hfull hs
  obtain ⟨-, -, -, hsub, -⟩ := node_basic hnq
  have hpm := lt_of_bits hm hsub
  have hc : (pos43 (pmK q)).card = 1 := by
    rw [← popK_eq hpm]
    exact Nat.eq_of_beq_eq_true h1
  obtain ⟨k, hk⟩ := Finset.card_eq_one.1 hc
  have hkm : k ∈ pos43 (pmK q) := by
    rw [hk]
    exact Finset.mem_singleton_self k
  obtain ⟨hcl, hc2⟩ := W.qs_one (mem_pos43.1 hkm).1 hk
  obtain ⟨hcl', hc'⟩ := W.node_spec hnq hm hcl
  exact ⟨hcl', by rw [hc', hc2], hm⟩

theorem Tab.level_next (W : Tab T N im posT jT E t) {ps : List ℕ} {S : ℕ → ℕ} {full c : ℕ}
    {P L : List ℕ} (hfull : full = 2 ^ 43 - 1) (hn : nodesOK ps T S N posT jT E L = true)
    (hp : parOK full P L = true)
    (hP : ∀ p ∈ P, Cl (Qs jT t (mK p)) ∧ (Qs jT t (mK p)).card = c ∧ mK p < 2 ^ 43) :
    ∀ q ∈ L, Cl (Qs jT t (mK q)) ∧ (Qs jT t (mK q)).card = 2 * c ∧ mK q < 2 ^ 43 := by
  intro q hq
  have hnq := lrec_all hn q hq
  obtain ⟨hs, h1⟩ := lrec_all2 hp q hq
  have hm := mK_lt hfull hs
  obtain ⟨p, hpP, hpe⟩ := inMasks_spec h1
  obtain ⟨hcl, hc, -⟩ := hP p hpP
  rw [hpe] at hcl hc
  obtain ⟨hcl', hc'⟩ := W.node_spec hnq hm hcl
  exact ⟨hcl', by rw [hc', hc], hm⟩

theorem adj_spec (h : adjOK T E = true) {e f : ℕ} (he : e ∈ E) (hf : f ∈ E)
    (hb : (rowK e).testBit (posK f) = false) :
    eq22 45 6 (mask 6) (T (jK e)) (T (jK f)) (T (jK f)) (T (jK e)) = false := by
  have h1 := lrec_all (lrec_all h e he) f hf
  rw [bitK_false hb] at h1
  have h2 : notK (eq22 45 6 (mask 6) (T (jK e)) (T (jK f)) (T (jK f)) (T (jK e))) = true := h1
  cases hx : eq22 45 6 (mask 6) (T (jK e)) (T (jK f)) (T (jK f)) (T (jK e))
  · rfl
  · rw [hx] at h2
    exact absurd h2 (by decide)

theorem Tab.step (W : Tab T N im posT jT E t) (hadj : adjOK T E = true) {full p c : ℕ}
    {L : List ℕ} (hfull : full = 2 ^ 43 - 1) (hc : subK (candK full E p) (unionK L p) = true)
    (hL : ∀ q ∈ L, Cl (Qs jT t (mK q)) ∧ (Qs jT t (mK q)).card = 2 * c ∧ mK q < 2 ^ 43)
    (hpc : (Qs jT t p).card = c) (hpcl : Cl (Qs jT t p)) {V : Subgroup Pm}
    (hV : ∀ x ∈ V, x * x = 1) (hsub : ∀ y ∈ Qs jT t p, y ∈ V) {j : ℕ} (hj : j < N)
    (hbV : t j ∈ V) (hbn : t j ∉ Qs jT t p) :
    ∃ q ∈ L, ∀ y ∈ Qs jT t (mK q), y ∈ V := by
  have hb1 : t j ≠ 1 := fun h => hbn (by rw [h]; exact one_mem_Qs)
  have hjim := W.inv_bit hj (hV _ hbV) hb1
  obtain ⟨hk, hjj⟩ := W.idx hjim
  have hkp : p.testBit (pT posT j) = false := by
    cases e : p.testBit (pT posT j)
    · rfl
    · exact absurd (by rw [← hjj]; exact x_mem hk e) hbn
  have hcand : (candK full E p).testBit (pT posT j) = true := by
    rw [candK_testBit, hkp, Bool.not_false, Bool.and_true, crow_testBit]
    refine ⟨by rw [hfull, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hk, fun e he hpe => ?_⟩
    obtain ⟨f, hf, hfk, hfj⟩ := W.entry hk
    by_contra hr
    have hr' : (rowK e).testBit (posK f) = false := by
      rw [hfk]
      simpa using hr
    have hx := adj_spec hadj he hf hr'
    have hek : posK e < 43 := W.pos_lt he
    have hje : jJ jT (posK e) = jK e := (W.tab3.2.2 e he).2
    have hmemV : t (jK e) ∈ V := hsub _ (by rw [← hje]; exact x_mem hek hpe)
    have hcomm : t (jK e) * t j = t j * t (jK e) :=
      comm_of_sq (hV _ hmemV) (hV _ hbV) (hV _ (V.mul_mem hmemV hbV))
    have hNe : jK e < N := by
      rw [← hje]
      exact (W.posn hek).1
    rw [hfj.trans hjj, eq22_of_comm (W.prep _ hNe) (W.prep _ hj) hcomm] at hx
    exact absurd hx (by decide)
  obtain ⟨q, hqL, hqp, hqk⟩ := unionK_testBit (subK_iff.1 hc _ hcand)
  obtain ⟨hcl, hcard, -⟩ := hL q hqL
  have hpq : ∀ i, p.testBit i = true → (mK q).testBit i = true := fun i hi => by
    rw [← hqp, Nat.land_eq, Nat.testBit_and, Bool.and_eq_true] at hi
    exact hi.1
  have hbq : t j ∈ Qs jT t (mK q) := by
    rw [← hjj]
    exact x_mem hk hqk
  have hU : Qs jT t p ∪ (Qs jT t p).image (t j * ·) ⊆ Qs jT t (mK q) :=
    Finset.union_subset (qs_mono hpq) fun z hz => by
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
      exact hcl _ hbq _ (qs_mono hpq hy)
  have heq : Qs jT t p ∪ (Qs jT t p).image (t j * ·) = Qs jT t (mK q) :=
    Finset.eq_of_subset_of_card_le hU
      (by rw [coset_card hpcl (fun y hy => W.qs_sq hy) hbn, hcard, hpc])
  refine ⟨q, hqL, fun y hy => ?_⟩
  rw [← heq] at hy
  rcases Finset.mem_union.1 hy with hy | hy
  · exact hsub y hy
  · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
    exact V.mul_mem hbV (hsub z hz)

theorem fixC_one : fixC (1 : Pm) = 45 := by
  unfold fixC
  simp

theorem e16_sound {ps : List ℕ} {S : ℕ → ℕ} {full F15 FP : ℕ} {L2 L3 L4 : List ℕ}
    {G : Subgroup Pm} (hG : Nat.card G = N) (hT : ∀ y ∈ G, ∃ i < N, PRep 45 6 (T i) y)
    (him : im < 2 ^ N) (hinv : invOK T N im = true) (htab : tabOK im 43 posT jT E = true)
    (hfull : Nat.beq full (Nat.sub (Nat.shiftLeft 1 43) 1) = true)
    (hpos : posOK N im posT jT = true) (hadj : adjOK T E = true)
    (hn2 : nodesOK ps T S N posT jT E L2 = true) (hn3 : nodesOK ps T S N posT jT E L3 = true)
    (hn4 : nodesOK ps T S N posT jT E L4 = true) (hp2 : par1OK full L2 = true)
    (hp3 : parOK full L2 L3 = true) (hp4 : parOK full L3 L4 = true)
    (hc1 : compl1K full E L2 = true) (hc2 : complK full E L2 L3 = true)
    (hc3 : complK full E L3 L4 = true) (hfix : fixOK T F15 FP E = true)
    (hgood : goodK F15 FP L4 = true) {V : Subgroup Pm} (hVG : V ≤ G) (hV16 : Nat.card V = 16)
    (hV : ∀ x ∈ V, x * x = 1) :
    ((∀ x ∈ V, fixC x = 45 ∨ fixC x = 13 ∨ fixC x = 5) ∨ ∃ x ∈ V, fixC x = 15) ∧
      ∀ F : Finset Pm, (∀ x ∈ F, x ∈ V ∧ fixC x = 15) → F.card ≤ 4 := by
  classical
  obtain ⟨t, ht, hinj⟩ := exists_t hG hT
  have W : Tab T N im posT jT E t := ⟨fun i hi => (ht i hi).1, hinj, him, hinv, htab, hpos⟩
  have hfull' : full = 2 ^ 43 - 1 := (Nat.eq_of_beq_eq_true hfull).trans (by decide)
  have hVt : ∀ y ∈ V, ∃ i < N, t i = y := fun y hy => by
    obtain ⟨i, hi, hp⟩ := hT y (hVG hy)
    exact ⟨i, hi, prep_unique (ht i hi).1 hp⟩
  obtain ⟨SV, hSVm⟩ : ∃ SV : Finset Pm, ∀ x, x ∈ SV ↔ x ∈ V :=
    ⟨Finset.univ.filter (· ∈ V), fun x => by simp⟩
  have hSV : SV.card = 16 := by
    rw [← hV16, ← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight hSVm)
  have hlt : ∀ X : Finset Pm, X.card < 16 → ∃ b ∈ V, b ∉ X := fun X hX => by
    obtain ⟨b, hb, hbX⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := X) (t := SV)
      (by rw [hSV]; exact hX)
    exact ⟨b, (hSVm b).1 hb, hbX⟩
  obtain ⟨a, haV, ha1⟩ := hlt {1} (by rw [Finset.card_singleton]; decide)
  obtain ⟨ia, hia, rfl⟩ := hVt a haV
  have hima := W.inv_bit hia (hV _ haV) fun h => ha1 (by rw [h]; exact Finset.mem_singleton_self 1)
  obtain ⟨hka, hjja⟩ := W.idx hima
  obtain ⟨ea, hea, hpa, -⟩ := W.entry hka
  have hka' : posK ea < 43 := by
    rw [hpa]
    exact hka
  have hp0 : pos43 (Nat.shiftLeft (nat_lit 1) (posK ea)) = {posK ea} := by
    ext k
    rw [mem_pos43, Finset.mem_singleton]
    change k < 43 ∧ (1 <<< posK ea).testBit k = true ↔ _
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
    constructor
    · rintro ⟨-, h⟩
      exact (of_decide_eq_true h).symm
    · rintro rfl
      exact ⟨hka', decide_eq_true rfl⟩
  obtain ⟨hcl1, hcard1⟩ := W.qs_one hka' hp0
  have hsub1 : ∀ y ∈ Qs jT t (Nat.shiftLeft (nat_lit 1) (posK ea)), y ∈ V := by
    intro y hy
    rcases mem_Qs.1 hy with rfl | ⟨k, hk, hb, rfl⟩
    · exact V.one_mem
    · have : k ∈ pos43 (Nat.shiftLeft (nat_lit 1) (posK ea)) := mem_pos43.2 ⟨hk, hb⟩
      rw [hp0, Finset.mem_singleton] at this
      rw [this, hpa, hjja]
      exact haV
  have H2 := W.level2 hfull' hn2 hp2
  have H3 := W.level_next hfull' hn3 hp3 H2
  have H4 := W.level_next hfull' hn4 hp4 H3
  obtain ⟨b1, hb1V, hb1n⟩ := hlt _ (by rw [hcard1]; decide)
  obtain ⟨j1, hj1, rfl⟩ := hVt b1 hb1V
  obtain ⟨q2, hq2, hs2⟩ := W.step hadj hfull' (lrec_all hc1 ea hea) H2 hcard1 hcl1 hV hsub1 hj1
    hb1V hb1n
  obtain ⟨hcl2, hcard2, -⟩ := H2 q2 hq2
  obtain ⟨b2, hb2V, hb2n⟩ := hlt _ (by rw [hcard2]; decide)
  obtain ⟨j2, hj2, rfl⟩ := hVt b2 hb2V
  obtain ⟨q3, hq3, hs3⟩ := W.step hadj hfull' (lrec_all hc2 q2 hq2) H3 hcard2 hcl2 hV hs2 hj2
    hb2V hb2n
  obtain ⟨hcl3, hcard3, -⟩ := H3 q3 hq3
  obtain ⟨b3, hb3V, hb3n⟩ := hlt _ (by rw [hcard3]; decide)
  obtain ⟨j3, hj3, rfl⟩ := hVt b3 hb3V
  obtain ⟨q4, hq4, hs4⟩ := W.step hadj hfull' (lrec_all hc3 q3 hq3) H4 hcard3 hcl3 hV hs3 hj3
    hb3V hb3n
  obtain ⟨-, hcard4, hm4⟩ := H4 q4 hq4
  have hall : ∀ x ∈ V, x ∈ Qs jT t (mK q4) := by
    have e := Finset.eq_of_subset_of_card_le (s := Qs jT t (mK q4)) (t := SV)
      (fun y hy => (hSVm y).2 (hs4 y hy)) (le_of_eq (by rw [hSV, hcard4]))
    intro x hx
    rw [e]
    exact (hSVm x).2 hx
  have hfx : ∀ k < 43, (F15.testBit k = true ↔ fixC (t (jJ jT k)) = 15) ∧
      (FP.testBit k = true ↔ fixC (t (jJ jT k)) = 13 ∨ fixC (t (jJ jT k)) = 5) := by
    intro k hk
    obtain ⟨e, he, rfl, hje⟩ := W.entry hk
    have h := lrec_all hfix e he
    rw [bA, bEqK_iff, bEqK_iff] at h
    have hN : jK e < N := by
      rw [hje]
      exact (W.posn hk).1
    have hfk : fixK 45 6 (T (jK e)) = fixC (t (jK e)) := fixK_eq (W.prep _ hN)
    rw [← hje]
    constructor
    · rw [← bitK_iff, h.1, hfk, Nat.beq_eq]
    · rw [← bitK_iff, h.2, hfk]
      cases h13 : Nat.beq (fixC (t (jK e))) (nat_lit 13)
      · have hne : fixC (t (jK e)) ≠ 13 := Nat.ne_of_beq_eq_false h13
        change Nat.beq (fixC (t (jK e))) (nat_lit 5) = true ↔ _
        rw [Nat.beq_eq]
        constructor
        · exact Or.inr
        · rintro (h' | h')
          · exact absurd h' hne
          · exact h'
      · exact ⟨fun _ => Or.inl (Nat.eq_of_beq_eq_true h13), fun _ => rfl⟩
  have hgq := lrec_all hgood q4 hq4
  rw [bA] at hgq
  obtain ⟨hg1, hg2⟩ := hgq
  have hland : ∀ i, (Nat.land (mK q4) F15).testBit i = true →
      (mK q4).testBit i = true ∧ F15.testBit i = true := fun i hi => by
    rw [Nat.land_eq, Nat.testBit_and, Bool.and_eq_true] at hi
    exact hi
  refine ⟨?_, fun F hF => ?_⟩
  · cases hs : subK (mK q4) FP
    · rw [hs] at hg1
      have hne : Nat.land (mK q4) F15 ≠ 0 := by
        intro h0
        change notK (Nat.beq (Nat.land (mK q4) F15) (nat_lit 0)) = true at hg1
        rw [h0] at hg1
        exact absurd hg1 (by decide)
      obtain ⟨k, hk⟩ := Nat.exists_testBit_of_ne_zero hne
      obtain ⟨hk1, hk2⟩ := hland k hk
      have hk43 := lt43 hm4 hk1
      exact Or.inr ⟨t (jJ jT k), hs4 _ (x_mem hk43 hk1), (hfx k hk43).1.1 hk2⟩
    · refine Or.inl fun x hx => ?_
      rcases mem_Qs.1 (hall x hx) with rfl | ⟨k, hk, hb, rfl⟩
      · exact Or.inl fixC_one
      · exact Or.inr ((hfx k hk).2.1 (subK_iff.1 hs k hb))
  · have hsubF : F ⊆ (pos43 (Nat.land (mK q4) F15)).image fun k => t (jJ jT k) := by
      intro x hx
      obtain ⟨hxV, hx15⟩ := hF x hx
      rcases mem_Qs.1 (hall x hxV) with rfl | ⟨k, hk, hb, rfl⟩
      · rw [fixC_one] at hx15
        exact absurd hx15 (by decide)
      · refine Finset.mem_image.2 ⟨k, mem_pos43.2 ⟨hk, ?_⟩, rfl⟩
        rw [Nat.land_eq, Nat.testBit_and, hb, (hfx k hk).1.2 hx15]
        rfl
    have hlt' : Nat.land (mK q4) F15 < 2 ^ 43 := lt_of_bits hm4 fun i hi => (hland i hi).1
    calc F.card ≤ _ := Finset.card_le_card hsubF
      _ ≤ (pos43 (Nat.land (mK q4) F15)).card := Finset.card_image_le
      _ = popK (Nat.land (mK q4) F15) := (popK_eq hlt').symm
      _ ≤ 4 := Nat.le_of_ble_eq_true hg2

end CFSG.KC.E16Walk
