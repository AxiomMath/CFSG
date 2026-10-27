module

public import Certificates.Data.Kernel.AE6Tri.DefsC
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.YoshQ.TabNSound

public section

namespace CFSG.KC.AE6Tri

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KC.AE6F CFSG.KS.Raw Pointwise

@[expose] def GRep (G : List Nat) (g : Nat → Equiv.Perm (Fin 360)) : Prop :=
  ∀ c, Orb.PRep 360 9 (gl G c) (g c)

@[expose] def wv (g : Nat → Equiv.Perm (Fin 360)) (w : List Nat) : Equiv.Perm (Fin 360) :=
  (w.map g).prod

@[expose] def lsub (g : Nat → Equiv.Perm (Fin 360)) (L : Nat) : Subgroup (Equiv.Perm (Fin 360)) :=
  Subgroup.closure {x | ∃ c < 8, bit L c = true ∧ g c = x}

@[expose] def finOfL (B : List Nat) : Set (Fin 360) := {x | x.val ∈ B}

@[expose] def setStab (S : Set (Fin 360)) : Subgroup (Equiv.Perm (Fin 360)) :=
  MulAction.stabilizer (Equiv.Perm (Fin 360)) S

variable {G : List Nat} {g : Nat → Equiv.Perm (Fin 360)}

theorem wv_nil (g : Nat → Equiv.Perm (Fin 360)) : wv g [] = 1 := rfl

theorem wv_cons (g : Nat → Equiv.Perm (Fin 360)) (c : Nat) (w : List Nat) :
    wv g (c :: w) = g c * wv g w := by
  simp [wv]

theorem ptW_eq (hG : GRep G g) : ∀ (w : List Nat) (x : Fin 360), ptW G w x = (wv g w x : Nat)
  | [], _ => rfl
  | c :: w, x => by
    have ih := ptW_eq hG w x
    change pg 9 (mask 9) (gl G c) (ptW G w x) = _
    rw [ih, wv_cons, Equiv.Perm.mul_apply]
    exact hG c (wv g w x)

theorem prep_mod {P : Nat} {x : Equiv.Perm (Fin 360)} (h : Orb.PRep 360 9 P x) :
    Orb.PRep 360 9 (P % 2 ^ (360 * 9)) x := fun i => by
  rw [pg_mod i.2]
  exact h i

theorem prep_pmN {P Q : Nat} {x y : Equiv.Perm (Fin 360)} (hP : Orb.PRep 360 9 P x)
    (hQ : Orb.PRep 360 9 Q y) : Orb.PRep 360 9 (pmN 360 9 P Q) (x * y) := by
  unfold pmN
  exact Orb.prep_pcomp (by norm_num) (prep_mod hP) hQ

theorem prep_pidn' : Orb.PRep 360 9 (pidn 360 9) 1 := Orb.prep_pidn (by norm_num) (by norm_num)

theorem eqN_iff {P Q : Nat} {x y : Equiv.Perm (Fin 360)} (hP : Orb.PRep 360 9 P x)
    (hQ : Orb.PRep 360 9 Q y) : eqN 360 9 P Q = true ↔ x = y := by
  unfold eqN
  rw [Nat.beq_eq]
  constructor
  · intro h
    exact Equiv.ext fun i => Fin.ext (by rw [← prep_mod hP i, h, prep_mod hQ i])
  · rintro rfl
    exact PF.eq_of_fields (by norm_num) (mod_shr _) (mod_shr _) fun i hi => by
      rw [prep_mod hP ⟨i, hi⟩, prep_mod hQ ⟨i, hi⟩]

theorem prep_awN {L : List Nat} {f : Nat → Equiv.Perm (Fin 360)}
    (hL : ∀ c, Orb.PRep 360 9 (L.getD c (pidn 360 9)) (f c)) :
    ∀ w : List Nat, Orb.PRep 360 9 (awN L w) ((w.map f).prod)
  | [] => prep_pidn'
  | c :: w => by
    have e : awN L (c :: w) = pmN 360 9 (L.getD c (pidn 360 9)) (awN L w) := rfl
    rw [e, List.map_cons, List.prod_cons]
    exact prep_pmN (hL c) (prep_awN hL w)

theorem prep_wv (hG : GRep G g) (w : List Nat) : Orb.PRep 360 9 (awN G w) (wv g w) :=
  prep_awN hG w

theorem allIx_iff {α : Type} (L : List α) (f : Nat → α → Bool) (i₀ : Nat) :
    allIx L f i₀ = true ↔ ∀ i (hi : i < L.length), f (i₀ + i) L[i] = true := by
  induction L generalizing i₀ with
  | nil => simp [allIx]
  | cons a L ih =>
    have e : allIx (a :: L) f i₀ = (f i₀ a && allIx L f (i₀ + 1)) := by
      change bAnd(f i₀ a, allIx L f (Nat.succ i₀)) = _
      rw [Orb.bAnd_eq]
    rw [e, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h0, h1⟩ i hi
      cases i with
      | zero => simpa using h0
      | succ i =>
        have e2 : i₀ + (i + 1) = i₀ + 1 + i := by omega
        rw [e2]
        exact h1 i (by simpa using hi)
    · intro h
      have h0 := h 0 (by simp)
      rw [Nat.add_zero] at h0
      refine ⟨h0, fun i hi => ?_⟩
      have e2 : i₀ + 1 + i = i₀ + (i + 1) := by omega
      rw [e2]
      exact h (i + 1) (by simpa using hi)

theorem allIx_getD {α : Type} {L : List α} {f : Nat → α → Bool} (d : α)
    (h : allIx L f 0 = true) : ∀ i < L.length, f i (L.getD i d) = true := fun i hi => by
  have := (allIx_iff L f 0).1 h i hi
  rwa [Nat.zero_add, ← List.getD_eq_getElem _ d hi] at this

theorem allIx_mem {α : Type} {L : List α} {f : Nat → α → Bool} (h : allIx L f 0 = true) :
    ∀ a ∈ L, ∃ i, f i a = true := fun a ha => by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ha
  exact ⟨0 + i, (allIx_iff L f 0).1 h i hi⟩

theorem forceMap_eq {α : Type} (L : List α) (f : α → Nat) (k : List Nat → Bool) :
    forceMap L f k = k (L.map f) := by
  induction L generalizing k with
  | nil => rfl
  | cons a L ih =>
    change strictB (f a) (fun v => forceMap L f (fun t => k (v :: t))) = _
    rw [Orb.strictB_eq, ih]
    rfl

theorem distinctL_iff (L : List Nat) : distinctL L = true ↔ L.Pairwise (· ≠ ·) := by
  induction L with
  | nil => simp [distinctL]
  | cons a t ih =>
    have hin : ∀ s : List Nat, List.rec (motive := fun _ => Bool) true
        (fun b _ ih2 => bAnd(Bool.rec (motive := fun _ => Bool) true false (Nat.beq a b), ih2)) s
        = true ↔ ∀ b ∈ s, a ≠ b := by
      intro s
      induction s with
      | nil => simp
      | cons b s ih2 =>
        change bAnd(Bool.rec (motive := fun _ => Bool) true false (Nat.beq a b), _) = true ↔ _
        rw [Orb.bAnd_eq, Bool.and_eq_true, ih2, List.forall_mem_cons]
        cases hab : Nat.beq a b
        · simp only [true_and]
          exact ⟨fun h => ⟨Nat.ne_of_beq_eq_false hab, h⟩, fun h => h.2⟩
        · simp only [Bool.false_eq_true, false_and, false_iff, not_and]
          intro h
          exact absurd (Nat.eq_of_beq_eq_true hab) h
    change bAnd(List.rec (motive := fun _ => Bool) true
      (fun b _ ih2 => bAnd(Bool.rec (motive := fun _ => Bool) true false (Nat.beq a b), ih2)) t,
      distinctL t) = true ↔ _
    rw [Orb.bAnd_eq, Bool.and_eq_true, hin, ih, List.pairwise_cons]

theorem bit_eq' (s b : Nat) : bit s b = s.testBit b := by
  unfold bit
  change Nat.blt 0 (s &&& 1 <<< b) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow, Orb.blt_dec]
  cases s.testBit b <;> simp

theorem testBit_maskL (B : List Nat) (x : Nat) : (maskL B).testBit x = decide (x ∈ B) := by
  induction B with
  | nil => simp [maskL]
  | cons a B ih =>
    change (1 <<< a ||| maskL B).testBit x = _
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, ih]
    by_cases h : x = a <;> simp [h, eq_comm]

theorem bit_maskL (B : List Nat) (x : Nat) : bit (maskL B) x = true ↔ x ∈ B := by
  rw [bit_eq', testBit_maskL, decide_eq_true_iff]

theorem notB_eq (b : Bool) : notB b = !b := by cases b <;> rfl

theorem lenL_eq {α : Type} (L : List α) : lenL L = L.length := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    change Nat.succ (lenL L) = _
    rw [ih, List.length_cons]

theorem prep_of_eqN {P Q : Nat} {x : Equiv.Perm (Fin 360)} (h : eqN 360 9 P Q = true)
    (hP : Orb.PRep 360 9 P x) : Orb.PRep 360 9 Q x := fun i => by
  unfold eqN at h
  rw [← pg_mod i.2, ← Nat.eq_of_beq_eq_true h, pg_mod i.2]
  exact hP i

theorem prep_at2 {QG : List (List Nat)} {q : Nat → Nat → Equiv.Perm (Fin 360)}
    (hQ : ∀ x j, Orb.PRep 360 9 ((QG.getD x []).getD j (pidn 360 9)) (q x j)) {x j : Nat}
    (hj : j < (QG.getD x []).length) : Orb.PRep 360 9 (at2 QG 0 x j) (q x j) := by
  unfold at2
  rw [List.getD_eq_getElem _ 0 hj, ← List.getD_eq_getElem _ (pidn 360 9) hj]
  exact hQ x j

theorem testBit_foldImg (P s y : Nat) : ∀ l : List Nat,
    (l.foldr (fun z acc => if bit s z = true then Nat.lor acc (Nat.shiftLeft 1 (pg 9 (mask 9) P z))
      else acc) 0).testBit y = true ↔ ∃ z ∈ l, bit s z = true ∧ pg 9 (mask 9) P z = y
  | [] => by simp
  | z :: l => by
    simp only [List.foldr_cons]
    simp only [List.mem_cons, or_and_right, exists_or, exists_eq_left]
    by_cases hb : bit s z = true
    · rw [if_pos hb]
      change ((_ ||| 1 <<< _)).testBit y = true ↔ _
      rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
        testBit_foldImg P s y l, decide_eq_true_iff]
      simp only [hb, true_and]
      exact or_comm
    · rw [if_neg hb, testBit_foldImg P s y l]
      simp [hb]

theorem testBit_imgM {P : Nat} {x : Equiv.Perm (Fin 360)} (hP : Orb.PRep 360 9 P x) (s y : Nat) :
    (imgM P s).testBit y = true ↔ ∃ z : Fin 360, s.testBit z = true ∧ (x z).val = y := by
  unfold imgM
  rw [Orb.foldN_eq]
  simp only [Orb.nIf_eq]
  rw [testBit_foldImg]
  constructor
  · rintro ⟨z, hz, hb, he⟩
    have hz' := List.mem_range.1 hz
    refine ⟨⟨z, hz'⟩, ?_, ?_⟩
    · rw [← bit_eq']
      exact hb
    · rw [← hP ⟨z, hz'⟩]
      exact he
  · rintro ⟨z, hb, he⟩
    refine ⟨z, List.mem_range.2 z.2, ?_, ?_⟩
    · rw [bit_eq']
      exact hb
    · rw [hP z]
      exact he

theorem testBit_imgW (hG : GRep G g) {B : List Nat} (hB : ∀ x ∈ B, x < 360) :
    ∀ (w : List Nat) (y : Nat), (imgW G w (maskL B)).testBit y = true ↔
      ∃ z : Fin 360, z.val ∈ B ∧ (wv g w z).val = y
  | [], y => by
    change (maskL B).testBit y = true ↔ _
    rw [testBit_maskL, decide_eq_true_iff]
    constructor
    · intro hy
      exact ⟨⟨y, hB y hy⟩, hy, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact hz
  | c :: w, y => by
    change (strictN (imgW G w (maskL B)) (fun t => imgM (gl G c) t)).testBit y = true ↔ _
    rw [Orb.strictN_eq, testBit_imgM (hG c)]
    constructor
    · rintro ⟨z, hz, hzy⟩
      obtain ⟨u, hu, huz⟩ := (testBit_imgW hG hB w z).1 hz
      refine ⟨u, hu, ?_⟩
      have e : wv g w u = z := Fin.ext huz
      rw [wv_cons, Equiv.Perm.mul_apply, e]
      exact hzy
    · rintro ⟨u, hu, huy⟩
      refine ⟨wv g w u, (testBit_imgW hG hB w _).2 ⟨u, hu, rfl⟩, ?_⟩
      rw [wv_cons, Equiv.Perm.mul_apply] at huy
      exact huy

theorem exists_smul_iff (x : Equiv.Perm (Fin 360)) (B : List Nat) (y : Nat) :
    (∃ z : Fin 360, z.val ∈ B ∧ (x z).val = y) ↔ ∃ t ∈ x • finOfL B, t.val = y := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨x z, Set.mem_smul_set.2 ⟨z, hz, rfl⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨z, hz, rfl⟩ := Set.mem_smul_set.1 ht
    exact ⟨z, hz, rfl⟩

theorem bit_lt8 {L c : Nat} (hL : L < 256) (h : bit L c = true) : c < 8 := by
  by_contra hc
  rw [bit_eq', Nat.testBit_eq_false_of_lt] at h
  · exact Bool.false_ne_true h
  · calc L < 256 := hL
      _ = 2 ^ 8 := by norm_num
      _ ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem lsub_mono {L L' : Nat} (h : L &&& L' = L) : lsub g L ≤ lsub g L' := by
  apply Subgroup.closure_mono
  rintro x ⟨c, hc, hb, rfl⟩
  refine ⟨c, hc, ?_, rfl⟩
  rw [bit_eq'] at hb ⊢
  rw [← h, Nat.testBit_and, Bool.and_eq_true] at hb
  exact hb.2

theorem lsub_le_stab {L : Nat} {q : Fin 360} (h : ∀ c < 8, bit L c = true → g c q = q) :
    lsub g L ≤ MulAction.stabilizer (Equiv.Perm (Fin 360)) q := by
  rw [lsub, Subgroup.closure_le]
  rintro x ⟨c, hc, hb, rfl⟩
  exact MulAction.mem_stabilizer_iff.2 (h c hc hb)

theorem fixL_sound (hG : GRep G g) {L q : Nat} (h : fixL G L q = true) (hq : q < 360) :
    ∀ c < 8, bit L c = true → g c ⟨q, hq⟩ = ⟨q, hq⟩ := by
  intro c hc hb
  unfold fixL at h
  have e := Orb.allN_iff.1 h c hc
  rw [Orb.bIf_eq, if_pos hb] at e
  exact Fin.ext ((hG c ⟨q, hq⟩).symm.trans (Nat.eq_of_beq_eq_true e))

theorem treeOK_sound (hG : GRep G g) {L : Nat} (hL : L < 256) (p : Fin 360) :
    ∀ (T : List Nat) (vis : Nat) (V : Finset (Fin 360)),
      (∀ y, vis.testBit y = true ↔ ∃ v ∈ V, v.val = y) →
      (∀ v ∈ V, ∃ x ∈ lsub g L, x p = v) → treeOK G L T vis = true →
      ∃ S : Finset (Fin 360), S.card = V.card + T.length ∧ ∀ v ∈ S, ∃ x ∈ lsub g L, x p = v
  | [], _, V, _, hV, _ => ⟨V, rfl, hV⟩
  | e :: T, vis, V, hvis, hV, h => by
    have e1 : treeOK G L (e :: T) vis =
        bAnd(bit L (Nat.shiftRight e 18), bAnd(bit vis (Nat.land (Nat.shiftRight e 9) 511),
          bAnd(Nat.blt (Nat.land e 511) 360,
          bAnd(Nat.beq (Nat.land vis (Nat.shiftLeft 1 (Nat.land e 511))) 0,
          bAnd(Nat.beq (pg 9 (mask 9) (gl G (Nat.shiftRight e 18)) (Nat.land (Nat.shiftRight e 9) 511))
            (Nat.land e 511),
          strictB (Nat.lor vis (Nat.shiftLeft 1 (Nat.land e 511))) (treeOK G L T)))))) := rfl
    rw [e1] at h
    simp only [Orb.bAnd_eq, Orb.strictB_eq, Bool.and_eq_true] at h
    obtain ⟨hc, hx, hy, hfr, hgy, hT⟩ := h
    generalize Nat.land e 511 = y at hy hfr hgy hT
    generalize Nat.land (Nat.shiftRight e 9) 511 = x at hx hgy
    generalize Nat.shiftRight e 18 = c at hc hgy
    have hy' : y < 360 := by simpa [Nat.blt_eq] using hy
    have hc8 := bit_lt8 hL hc
    rw [bit_eq'] at hx
    obtain ⟨v, hv, hvx⟩ := (hvis x).1 hx
    obtain ⟨h0, h0K, h0p⟩ := hV v hv
    have hgv : (g c v).val = y := by
      rw [← hG c v, hvx]
      exact Nat.eq_of_beq_eq_true hgy
    have hnot : ∀ u ∈ V, u.val ≠ y := by
      intro u hu hu'
      have hb : bit vis y = true := by
        rw [bit_eq']
        exact (hvis y).2 ⟨u, hu, hu'⟩
      unfold bit at hb
      rw [Nat.eq_of_beq_eq_true hfr] at hb
      exact absurd hb (by decide)
    have hyV : (⟨y, hy'⟩ : Fin 360) ∉ V := fun hm => hnot _ hm rfl
    have hvis' : ∀ z, (Nat.lor vis (Nat.shiftLeft 1 y)).testBit z = true ↔
        ∃ v ∈ insert (⟨y, hy'⟩ : Fin 360) V, v.val = z := by
      intro z
      change (vis ||| 1 <<< y).testBit z = true ↔ _
      rw [Nat.testBit_or, Bool.or_eq_true, hvis z, Nat.one_shiftLeft, Nat.testBit_two_pow,
        decide_eq_true_iff, Finset.exists_mem_insert]
      exact or_comm
    have hV' : ∀ u ∈ insert (⟨y, hy'⟩ : Fin 360) V, ∃ x ∈ lsub g L, x p = u := by
      intro u hu
      rcases Finset.mem_insert.1 hu with rfl | hu
      · refine ⟨g c * h0, Subgroup.mul_mem _ (Subgroup.subset_closure ⟨c, hc8, hc, rfl⟩) h0K, ?_⟩
        rw [Equiv.Perm.mul_apply, h0p]
        exact Fin.ext hgv
      · exact hV u hu
    obtain ⟨S, hS, hSo⟩ := treeOK_sound hG hL p T _ _ hvis' hV' hT
    refine ⟨S, ?_, hSo⟩
    rw [hS, Finset.card_insert_of_notMem hyV, List.length_cons]
    omega

theorem card_mul_stab_le (K : Subgroup (Equiv.Perm (Fin 360))) (b : Fin 360) (S : Finset (Fin 360))
    (hS : ∀ p ∈ S, ∃ x ∈ K, x b = p) :
    S.card * Nat.card ↥(K ⊓ MulAction.stabilizer (Equiv.Perm (Fin 360)) b) ≤ Nat.card K := by
  rw [← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K b), Nat.card_prod]
  apply Nat.mul_le_mul
  · have hsub : (S : Set (Fin 360)) ⊆ MulAction.orbit K b := by
      intro p hp
      obtain ⟨x, hx, rfl⟩ := hS p hp
      exact ⟨⟨x, hx⟩, rfl⟩
    calc S.card = Nat.card (S : Set (Fin 360)) := (Nat.card_coe_set_eq _).symm ▸ by simp
      _ ≤ Nat.card (MulAction.orbit K b) := Nat.card_mono (Set.toFinite _) hsub
  · apply le_of_eq
    refine Nat.card_congr
      { toFun := fun g => ⟨⟨g.1, g.2.1⟩, g.2.2⟩
        invFun := fun g => ⟨g.1.1, g.1.2, g.2⟩
        left_inv := fun g => rfl
        right_inv := fun g => rfl }

theorem rowsOK_aux (hG : GRep G g) : ∀ (R : List (List Nat)) (Lp q : Nat) (fst : Bool)
    (H : Subgroup (Equiv.Perm (Fin 360))), rowsOK G R Lp q fst = true →
    (fst = true → lsub g Lp ≤ H) →
    (fst = false → ∃ hq : q < 360,
      lsub g Lp ⊓ MulAction.stabilizer (Equiv.Perm (Fin 360)) (⟨q, hq⟩ : Fin 360) ≤ H) →
    chainCnt R ≤ Nat.card H
  | [], _, _, _, H, _, _, _ => Nat.card_pos
  | [] :: R, _, _, _, _, h, _, _ => by
    change false = true at h
    cases h
  | (hd :: T) :: R, Lp, q, fst, H, h, h1, h2 => by
    have e1 : rowsOK G ((hd :: T) :: R) Lp q fst =
        bAnd(Nat.blt (Nat.land hd 511) 360, bAnd(Nat.blt (Nat.shiftRight hd 9) 256,
          bAnd(Nat.beq (Nat.land (Nat.shiftRight hd 9) Lp) (Nat.shiftRight hd 9),
          bAnd(bIf(fst, Nat.beq (Nat.shiftRight hd 9) Lp, fixL G (Nat.shiftRight hd 9) q),
          bAnd(treeOK G (Nat.shiftRight hd 9) T (Nat.shiftLeft 1 (Nat.land hd 511)),
            rowsOK G R (Nat.shiftRight hd 9) (Nat.land hd 511) false))))) := rfl
    rw [e1] at h
    simp only [Orb.bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨hp, hL, hsub, hfst, htree, hrest⟩ := h
    generalize Nat.land hd 511 = p at hp htree hrest
    generalize Nat.shiftRight hd 9 = L at hL hsub hfst htree hrest
    have hp' : p < 360 := by simpa [Nat.blt_eq] using hp
    have hL : L < 256 := by simpa [Nat.blt_eq] using hL
    have hsub' : L &&& Lp = L := Nat.eq_of_beq_eq_true hsub
    have hKH : lsub g L ≤ H := by
      cases fst with
      | true =>
        change Nat.beq L Lp = true at hfst
        rw [Nat.eq_of_beq_eq_true hfst]
        exact h1 rfl
      | false =>
        change fixL G L q = true at hfst
        obtain ⟨hq, hle⟩ := h2 rfl
        exact le_trans (le_inf (lsub_mono hsub') (lsub_le_stab (fixL_sound hG hfst hq))) hle
    have hv1 : ∀ y, (Nat.shiftLeft 1 p).testBit y = true ↔
        ∃ v ∈ ({⟨p, hp'⟩} : Finset (Fin 360)), v.val = y := by
      intro y
      change (1 <<< p).testBit y = true ↔ _
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_iff]
      simp
    have hv2 : ∀ v ∈ ({⟨p, hp'⟩} : Finset (Fin 360)), ∃ x ∈ lsub g L, x ⟨p, hp'⟩ = v := by
      intro v hv
      rw [Finset.mem_singleton.1 hv]
      exact ⟨1, Subgroup.one_mem _, rfl⟩
    obtain ⟨S, hS, hSo⟩ := treeOK_sound hG hL ⟨p, hp'⟩ T _ _ hv1 hv2 htree
    · have hIH := rowsOK_aux hG R L p false
        (lsub g L ⊓ MulAction.stabilizer (Equiv.Perm (Fin 360)) (⟨p, hp'⟩ : Fin 360)) hrest
        (fun h => by cases h) (fun _ => ⟨hp', le_rfl⟩)
      have hst := card_mul_stab_le (lsub g L) ⟨p, hp'⟩ S hSo
      have hcc : chainCnt ((hd :: T) :: R) = (T.length + 1) * chainCnt R := by
        change lenL (hd :: T) * chainCnt R = _
        rw [lenL_eq, List.length_cons]
      rw [hcc]
      calc (T.length + 1) * chainCnt R
          ≤ S.card * Nat.card ↥(lsub g L ⊓
            MulAction.stabilizer (Equiv.Perm (Fin 360)) (⟨p, hp'⟩ : Fin 360)) := by
            rw [hS, Finset.card_singleton, Nat.add_comm 1]
            exact Nat.mul_le_mul_left _ hIH
        _ ≤ Nat.card (lsub g L) := hst
        _ ≤ Nat.card H := Subgroup.card_le_of_le hKH

theorem prep_mapAw (hG : GRep G g) (TW : List (List Nat)) (i : Nat) :
    Orb.PRep 360 9 ((TW.map fun w => awN G w).getD i (pidn 360 9)) (wv g (TW.getD i [])) := by
  by_cases hi : i < TW.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
      List.getD_eq_getElem _ _ hi]
    exact prep_wv hG _
  · rw [List.getD_eq_default _ _ (by simpa using hi), List.getD_eq_default _ _ (by simpa using hi)]
    exact prep_pidn'

theorem gamOK_sound (hG : GRep G g) {d : List Nat} {X XI : Nat}
    (h : gamOK G d X XI = true) :
    ∃ x : Equiv.Perm (Fin 360), Orb.PRep 360 9 X x ∧
      ∀ i < d.length, x * g i * x⁻¹ = g (d.getD i 0) := by
  unfold gamOK at h
  rw [Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hp, hd⟩ := h
  obtain ⟨-, -, hX⟩ := Orb.permOK_facts (n := 360) (w := 9) hp
  let f : Fin 360 → Fin 360 := fun i => ⟨pg 9 (mask 9) X i, (hX i i.2).1⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have ha := (hX a a.2).2
    have hb := (hX b b.2).2
    have e : pg 9 (mask 9) X a = pg 9 (mask 9) X b := congrArg Fin.val hab
    rw [e] at ha
    exact Fin.ext (ha.symm.trans hb)
  let x : Equiv.Perm (Fin 360) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj)
  have hxr : Orb.PRep 360 9 X x := fun i => rfl
  refine ⟨x, hxr, fun i hi => ?_⟩
  have e := allIx_getD 0 hd i hi
  have e2 := (eqN_iff (prep_pmN hxr (hG i)) (prep_pmN (hG _) hxr)).1 e
  rw [mul_inv_eq_iff_eq_mul, e2]

theorem rowsOK_sound (hG : GRep G g) {R : List (List Nat)} {L : Nat}
    (h : rowsOK G R L 0 true = true) : chainCnt R ≤ Nat.card (lsub g L) := by
  exact rowsOK_aux hG R L 0 true (lsub g L) h (fun _ => le_rfl) (fun h => by cases h)

theorem invB_sound (hG : GRep G g) {L B : List Nat} (h : invB G L B = true) :
    ∀ c ∈ L, g c ∈ setStab (finOfL B) := by
  unfold invB at h
  rw [Orb.strictB_eq] at h
  intro c hc
  obtain ⟨_, hc'⟩ := allIx_mem h c hc
  have key := testBit_imgM (hG c) (maskL B)
  rw [Nat.eq_of_beq_eq_true hc'] at key
  rw [setStab, MulAction.mem_stabilizer_iff]
  ext y
  simp only [Set.mem_smul_set, finOfL, Set.mem_setOf_eq, Equiv.Perm.smul_def]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have e := (key _).2 ⟨z, by rw [testBit_maskL, decide_eq_true_iff]; exact hz, rfl⟩
    rw [testBit_maskL, decide_eq_true_iff] at e
    exact e
  · intro hy
    obtain ⟨z, hz, hzy⟩ := (key y).1 (by rw [testBit_maskL, decide_eq_true_iff]; exact hy)
    rw [testBit_maskL, decide_eq_true_iff] at hz
    exact ⟨z, hz, Fin.ext hzy⟩

theorem distB_sound (hG : GRep G g) {ws : List (List Nat)} {B : List Nat}
    (hB : ∀ x ∈ B, x < 360) (h : distB G ws B = true) :
    ws.Pairwise fun u v => wv g u • finOfL B ≠ wv g v • finOfL B := by
  unfold distB at h
  rw [Orb.strictB_eq, forceMap_eq, distinctL_iff, List.pairwise_map] at h
  refine h.imp fun {u v} huv hs => huv ?_
  apply Nat.eq_of_testBit_eq
  intro y
  apply Bool.eq_iff_iff.2
  rw [testBit_imgW hG hB, testBit_imgW hG hB, exists_smul_iff, exists_smul_iff, hs]

theorem pinOK_sound (hG : GRep G g) {WS : List (List (List Nat))} {V : List (List Nat)}
    (h : pinOK G WS V = true) :
    ∀ i < WS.length, ∀ j < (WS.getD i []).length,
      Orb.PRep 360 9 ((V.getD i []).getD j (pidn 360 9)) (wv g ((WS.getD i []).getD j [])) := by
  unfold pinOK at h
  rw [Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  intro i hi j hj
  have e := allIx_getD [] h i hi
  rw [Orb.bAnd_eq, Bool.and_eq_true, lenL_eq, lenL_eq] at e
  obtain ⟨hl, e⟩ := e
  have hj' : j < (V.getD i []).length := by
    rw [Nat.eq_of_beq_eq_true hl]
    exact hj
  have e2 := allIx_getD [] e j hj
  dsimp only [at2] at e2
  rw [List.getD_eq_getElem _ 0 hj'] at e2
  rw [List.getD_eq_getElem _ (pidn 360 9) hj']
  exact prep_of_eqN e2 (prep_wv hG _)

theorem qnOK_sound (hG : GRep G g) {ML : List Nat} {QW : List (List (List Nat))}
    {QG : List (List Nat)} {W : List (List (List (List Nat)))} {q : Nat → Nat → Equiv.Perm (Fin 360)}
    (hQ : ∀ x j, Orb.PRep 360 9 ((QG.getD x []).getD j (pidn 360 9)) (q x j))
    (h : qnOK G ML QW QG W = true) :
    ∀ x < QW.length, ∀ j < (QW.getD x []).length, ∀ t < ML.length,
      j < (QG.getD x []).length →
      g (ML.getD t 0) * q x j * g (ML.getD t 0) = (((at2 W [] x j).getD t []).map (q x)).prod := by
  intro x hx j hj t ht hjQ
  unfold qnOK at h
  have e1 := allIx_getD [] h x hx
  have e2 := allIx_getD [] e1 j hj
  have e3 := allIx_getD 0 e2 t ht
  exact (eqN_iff (prep_pmN (prep_pmN (hG _) (prep_at2 hQ hjQ)) (hG _))
    (prep_awN (hQ x) _)).1 e3

theorem qdOK_sound {DG QG : List (List Nat)} {QW : List (List (List Nat))} {dq : List (List Nat)}
    {W : List (List (List (List Nat)))} {dl : Nat → Nat → Equiv.Perm (Fin 360)}
    {q : Nat → Nat → Equiv.Perm (Fin 360)}
    (hD : ∀ k c, Orb.PRep 360 9 ((DG.getD k []).getD c (pidn 360 9)) (dl k c))
    (hQ : ∀ x j, Orb.PRep 360 9 ((QG.getD x []).getD j (pidn 360 9)) (q x j))
    (h : qdOK DG QG QW dq W = true) :
    ∀ k < dq.length, ∀ x < QW.length, ∀ j < (QW.getD x []).length,
      (((QW.getD x []).getD j []).map (dl k)).prod =
        ((at2 (W.getD k []) [] x j).map (q ((dq.getD k []).getD x 0))).prod := by
  intro k hk x hx j hj
  unfold qdOK at h
  have e1 := allIx_getD [] h k hk
  have e2 := allIx_getD [] e1 x hx
  have e3 := allIx_getD [] e2 j hj
  exact (eqN_iff (prep_awN (hD k) _) (prep_awN (hQ _) _)).1 e3

theorem qzOK_sound (hG : GRep G g) {QW : List (List (List Nat))} {QG : List (List Nat)}
    {ZW : List (List (List Nat))} {ZJ : List (List Nat)} {q : Nat → Nat → Equiv.Perm (Fin 360)}
    (hQ : ∀ x j, Orb.PRep 360 9 ((QG.getD x []).getD j (pidn 360 9)) (q x j))
    (hJ : ∀ x < QW.length, ∀ y < QW.length, at2 ZJ 0 y x < (QG.getD x []).length)
    (h : qzOK G QW QG ZW ZJ = true) :
    ∀ x < QW.length, ∀ y < QW.length, x ≠ y →
      (∀ j < (QG.getD y []).length, wv g (at2 ZW [] y x) * q y j = q y j * wv g (at2 ZW [] y x)) ∧
      wv g (at2 ZW [] y x) * q x (at2 ZJ 0 y x) ≠ q x (at2 ZJ 0 y x) * wv g (at2 ZW [] y x) := by
  intro x hx y hy hxy
  unfold qzOK at h
  have e1 := allIx_getD [] h y hy
  have e2 := allIx_getD [] e1 x hx
  have hne : ¬ Nat.beq x y = true := by
    rw [Nat.beq_eq]
    exact hxy
  rw [Orb.bIf_eq, if_neg hne] at e2
  beta_reduce at e2
  rw [Orb.bAnd_eq, Bool.and_eq_true] at e2
  obtain ⟨e3, e4⟩ := e2
  have hz := prep_wv hG (at2 ZW [] y x)
  refine ⟨fun j hj => ?_, fun hc => ?_⟩
  · have e5 := allIx_getD (pidn 360 9) e3 j hj
    dsimp only [commN] at e5
    exact (eqN_iff (prep_pmN hz (hQ y j)) (prep_pmN (hQ y j) hz)).1 e5
  · have hq := prep_at2 hQ (hJ x hx y hy)
    have hcn : commN (awN G (at2 ZW [] y x)) (at2 QG 0 x (at2 ZJ 0 y x)) = true :=
      (eqN_iff (prep_pmN hz hq) (prep_pmN hq hz)).2 hc
    rw [hcn] at e4
    exact Bool.false_ne_true e4

theorem grOK_sound (hG : GRep G g) {S : Nat → Nat} {D VL : List Nat}
    {d : Nat → Equiv.Perm (Fin 360)} (hD : GRep D d) {s : Nat → Equiv.Perm (Fin 720)}
    (hS : ∀ j < VL.length, Orb.PRep 720 10 (S j) (s j)) (h : grOK S G D VL = true) :
    ∀ j < VL.length, s j = finSumFinEquiv.permCongr
      (Equiv.sumCongr (g (VL.getD j 0)) (d (VL.getD j 0))) := by
  intro j hj
  unfold grOK at h
  have e := allIx_getD 0 h j hj
  rw [Orb.allN_iff] at e
  refine Equiv.ext fun z => Fin.ext ?_
  obtain ⟨u, rfl⟩ := (finSumFinEquiv (m := 360) (n := 360)).surjective z
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, ← hS j hj]
  cases u with
  | inl a =>
    have e3 := e a a.2
    rw [Orb.bAnd_eq, Bool.and_eq_true] at e3
    simp only [Equiv.sumCongr_apply, Sum.map_inl]
    change pg 10 (mask 10) (S j) a = (g (VL.getD j 0) a : Nat)
    rw [← hG _ a]
    exact Nat.eq_of_beq_eq_true e3.1
  | inr b =>
    have e3 := e b b.2
    rw [Orb.bAnd_eq, Bool.and_eq_true] at e3
    simp only [Equiv.sumCongr_apply, Sum.map_inr]
    change pg 10 (mask 10) (S j) (360 + b) = 360 + (d (VL.getD j 0) b : Nat)
    rw [← hD _ b]
    exact Nat.eq_of_beq_eq_true e3.2

theorem mgOK_sound (hG : GRep G g) {S : Nat → Nat} {ML : List Nat}
    {s : Nat → Equiv.Perm (Fin 360)} (hS : ∀ j < ML.length, Orb.PRep 360 9 (S j) (s j))
    (h : mgOK S G ML = true) : ∀ j < ML.length, s j = g (ML.getD j 0) := by
  unfold mgOK at h
  intro j hj
  exact (eqN_iff (hS j hj) (hG _)).1 (allIx_getD 0 h j hj)

theorem invDOK_sound (hG : GRep G g) {D VL : List Nat} {W : List (List Nat)}
    {d : Nat → Equiv.Perm (Fin 360)} (hD : GRep D d) (h : invDOK G D VL W = true) :
    ∀ i ∈ VL, wv d (W.getD i []) = g i := by
  unfold invDOK at h
  intro i hi
  obtain ⟨_, e⟩ := allIx_mem h i hi
  exact (eqN_iff (prep_wv hD _) (hG i)).1 e

theorem tgOK_sound (hG : GRep G g) {TW : List (List Nat)} {EL : List Nat} {U : List (List Nat)}
    (h : tgOK G TW EL U = true) :
    ∀ t < EL.length, ((U.getD t []).map fun i => wv g (TW.getD i [])).prod = g (EL.getD t 0) := by
  unfold tgOK at h
  rw [forceMap_eq] at h
  intro t ht
  exact (eqN_iff (prep_awN (prep_mapAw hG TW) _) (hG _)).1 (allIx_getD 0 h t ht)

theorem kcOK_sound (hG : GRep G g) {DG : List (List Nat)} {KW KG CW : List (List Nat)}
    {U : List (List (List Nat))} {dl : Nat → Nat → Equiv.Perm (Fin 360)}
    (hD : ∀ k c, Orb.PRep 360 9 ((DG.getD k []).getD c (pidn 360 9)) (dl k c))
    (h : kcOK G DG KW KG CW U = true) :
    ∀ k < U.length, ∀ s < KW.length,
      ((KW.getD s []).map (dl k)).prod * wv g (CW.getD k []) =
        wv g (CW.getD k []) * (((U.getD k []).getD s []).map fun i => wv g (KG.getD i [])).prod := by
  unfold kcOK at h
  rw [forceMap_eq] at h
  intro k hk s hs
  have h1 := allIx_getD [] h k hk
  rw [Orb.strictB_eq] at h1
  have hC := prep_wv hG (CW.getD k [])
  exact (eqN_iff (prep_pmN (prep_awN (hD k) _) hC)
    (prep_pmN hC (prep_awN (prep_mapAw hG KG) _))).1 (allIx_getD [] h1 s hs)

theorem sepOK_sound (hG : GRep G g) {L p : Nat} {hw : List Nat} {b : Nat} {O : List Nat}
    (h : sepOK G L p hw b O = true) :
    ∃ (hp : p < 360) (hb : b < 360),
      (∀ c < 8, bit L c = true → ∀ q : Fin 360, q.val ∈ O → (g c q).val ∈ O) ∧ p ∈ O ∧
      (∀ q : Fin 360, q.val ∈ O → q.val ≠ p →
        ∃ c < 8, bit L c = true ∧ g c ⟨p, hp⟩ = ⟨p, hp⟩ ∧ g c q ≠ q) ∧
      lettersIn L hw = true ∧ wv g hw ⟨p, hp⟩ = ⟨b, hb⟩ := by
  unfold sepOK at h
  rw [Orb.bAnd_eq, Bool.and_eq_true, Orb.bAnd_eq, Bool.and_eq_true, Orb.bAnd_eq, Bool.and_eq_true,
    Orb.bAnd_eq, Bool.and_eq_true, Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hp : p < 360 := by simpa [Nat.blt_eq] using h3
  have hpt : ptW G hw p = (wv g hw ⟨p, hp⟩).val := ptW_eq hG hw ⟨p, hp⟩
  have hb' : b = (wv g hw ⟨p, hp⟩).val := by
    rw [← hpt]
    exact (Nat.eq_of_beq_eq_true h6).symm
  have hb : b < 360 := by
    rw [hb']
    exact (wv g hw ⟨p, hp⟩).2
  refine ⟨hp, hb, ?_, (bit_maskL _ _).1 h2, ?_, h5, Fin.ext hb'.symm⟩
  · intro c hc hLc q hq
    have e := Orb.allN_iff.1 h1 c hc
    rw [Orb.bIf_eq, if_pos hLc] at e
    obtain ⟨_, e⟩ := allIx_mem e q hq
    rw [bit_maskL, hG c q] at e
    exact e
  · intro q hq hqp
    obtain ⟨_, e⟩ := allIx_mem h4 q hq
    rw [Orb.bAnd_eq, Bool.and_eq_true, Orb.bIf_eq,
      if_neg (fun e => hqp (Nat.eq_of_beq_eq_true e)), notB_eq, Bool.not_eq_true'] at e
    obtain ⟨c, hc, hfc⟩ : ∃ c < 8, ¬ notB (bAnd(bit L c, bAnd(Nat.beq (pg 9 (mask 9) (gl G c) p) p,
        notB (Nat.beq (pg 9 (mask 9) (gl G c) q) q)))) = true := by
      by_contra hne
      push_neg at hne
      rw [Orb.allN_iff.2 hne] at e
      exact Bool.noConfusion e.2
    rw [notB_eq, Bool.not_eq_true, Bool.not_eq_false', Orb.bAnd_eq, Bool.and_eq_true, Orb.bAnd_eq,
      Bool.and_eq_true, notB_eq, Bool.not_eq_true'] at hfc
    obtain ⟨hLc, hpp, hqq⟩ := hfc
    refine ⟨c, hc, hLc, Fin.ext ?_, fun hcq => ?_⟩
    · rw [← hG c ⟨p, hp⟩]
      exact Nat.eq_of_beq_eq_true hpp
    · have e2 : pg 9 (mask 9) (gl G c) q = q := by rw [hG c q, hcq]
      rw [e2, Nat.beq_refl] at hqq
      exact Bool.noConfusion hqq

theorem levOK_sound (hG : GRep G g) {L : Nat} {F : List Nat} {b : Nat} {ws : List (List Nat)}
    (hb : b < 360) (h : levOK G L F b ws = true) :
    (∀ w ∈ ws, lettersIn L w = true ∧ ∀ c : Fin 360, c.val ∈ F → wv g w c = c) ∧
      ws.Pairwise fun u v => wv g u ⟨b, hb⟩ ≠ wv g v ⟨b, hb⟩ := by
  unfold levOK at h
  rw [Orb.bAnd_eq, Bool.and_eq_true, forceMap_eq, distinctL_iff, List.pairwise_map] at h
  refine ⟨fun w hw => ?_, h.2.imp fun {u v} huv e => huv ?_⟩
  · obtain ⟨_, e⟩ := allIx_mem h.1 w hw
    rw [Orb.bAnd_eq, Bool.and_eq_true] at e
    refine ⟨e.1, fun c hc => Fin.ext ?_⟩
    obtain ⟨_, e2⟩ := allIx_mem e.2 c hc
    rw [← ptW_eq hG w c]
    exact Nat.eq_of_beq_eq_true e2
  · exact (ptW_eq hG u ⟨b, hb⟩).trans ((congrArg Fin.val e).trans (ptW_eq hG v ⟨b, hb⟩).symm)

theorem wv_mem {L : Nat} : ∀ w : List Nat, (∀ c ∈ w, c < 8 ∧ bit L c = true) → wv g w ∈ lsub g L
  | [], _ => Subgroup.one_mem _
  | c :: w, h => by
    rw [wv_cons]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨c, (h c (by simp)).1, (h c (by simp)).2, rfl⟩)
      (wv_mem w fun d hd => h d (by simp [hd]))

theorem comm_of_closure {z : Equiv.Perm (Fin 360)} {s : Set (Equiv.Perm (Fin 360))}
    (hs : ∀ x ∈ s, z * x = x * z) : ∀ x ∈ Subgroup.closure s, z * x = x * z := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hs y hy
  | one => exact Commute.one_right z
  | mul a b _ _ ha hb => exact Commute.mul_right ha hb
  | inv a _ ha => exact Commute.inv_right ha

theorem inv_maps {x : Equiv.Perm (Fin 360)} {O : Finset (Fin 360)} (h : ∀ q ∈ O, x q ∈ O) :
    ∀ q ∈ O, x⁻¹ q ∈ O := by
  have hs : O.map x.toEmbedding ⊆ O := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.1 hy
    exact h q hq
  have he := Finset.eq_of_subset_of_card_le hs (by simp)
  intro q hq
  rw [← he] at hq
  obtain ⟨q', hq', hx⟩ := Finset.mem_map.1 hq
  rw [Equiv.toEmbedding_apply] at hx
  rw [← hx]
  simpa using hq'

theorem maps_of_closure {O : Finset (Fin 360)} {s : Set (Equiv.Perm (Fin 360))}
    (hs : ∀ x ∈ s, ∀ q ∈ O, x q ∈ O) : ∀ x ∈ Subgroup.closure s, ∀ q ∈ O, x q ∈ O := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hs y hy
  | one => exact fun q hq => hq
  | mul a b _ _ ha hb => exact fun q hq => ha _ (hb q hq)
  | inv a _ ha => exact inv_maps ha

theorem fix_of_sep {K : Subgroup (Equiv.Perm (Fin 360))} {z : Equiv.Perm (Fin 360)}
    (hc : ∀ x ∈ K, z * x = x * z) (hz : z ∈ K) {O : Finset (Fin 360)}
    (hO : ∀ x ∈ K, ∀ q ∈ O, x q ∈ O) {p : Fin 360} (hp : p ∈ O)
    (hsep : ∀ q ∈ O, q ≠ p → ∃ x ∈ K, x p = p ∧ x q ≠ q) {h : Equiv.Perm (Fin 360)}
    (hh : h ∈ K) : z (h p) = h p := by
  have hzp : z p = p := by
    by_contra hne
    obtain ⟨x, hx, hxp, hxq⟩ := hsep (z p) (hO z hz p hp) hne
    apply hxq
    have e := congrArg (fun f : Equiv.Perm (Fin 360) => f p) (hc x hx)
    simp only [Equiv.Perm.mul_apply, hxp] at e
    exact e.symm
  have e := congrArg (fun f : Equiv.Perm (Fin 360) => f p) (hc h hh)
  simp only [Equiv.Perm.mul_apply, hzp] at e
  exact e

theorem eq_one_of_base {K : Subgroup (Equiv.Perm (Fin 360))} {z : Equiv.Perm (Fin 360)}
    (b0 b1 b2 : Fin 360) (S0 S1 S2 : Finset (Fin 360))
    (h0 : ∀ p ∈ S0, ∃ x ∈ K, x b0 = p)
    (h1 : ∀ p ∈ S1, ∃ x ∈ K, x b0 = b0 ∧ x b1 = p)
    (h2 : ∀ p ∈ S2, ∃ x ∈ K, x b0 = b0 ∧ x b1 = b1 ∧ x b2 = p)
    (hK : Nat.card K ≤ S0.card * S1.card * S2.card) (hpos : 0 < S0.card * S1.card * S2.card)
    (hz : z ∈ K) (hb0 : z b0 = b0) (hb1 : z b1 = b1) (hb2 : z b2 = b2) : z = 1 := by
  have e0 := card_mul_stab_le K b0 S0 h0
  have e1 := card_mul_stab_le (K ⊓ MulAction.stabilizer (Equiv.Perm (Fin 360)) b0) b1 S1
    fun p hp => by
      obtain ⟨x, hx, hx0, hx1⟩ := h1 p hp
      exact ⟨x, ⟨hx, hx0⟩, hx1⟩
  have e2 := card_mul_stab_le (K ⊓ MulAction.stabilizer (Equiv.Perm (Fin 360)) b0 ⊓
    MulAction.stabilizer (Equiv.Perm (Fin 360)) b1) b2 S2 fun p hp => by
      obtain ⟨x, hx, hx0, hx1, hx2⟩ := h2 p hp
      exact ⟨x, ⟨⟨hx, hx0⟩, hx1⟩, hx2⟩
  have hc : Nat.card ↥(K ⊓ MulAction.stabilizer (Equiv.Perm (Fin 360)) b0 ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 360)) b1 ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 360)) b2) ≤ 1 := by
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc _ = S0.card * (S1.card * (S2.card * _)) := by ring
      _ ≤ S0.card * (S1.card * _) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ e2)
      _ ≤ S0.card * _ := Nat.mul_le_mul_left _ e1
      _ ≤ Nat.card K := e0
      _ ≤ _ := by rw [mul_one]; exact hK
  have hs := Finite.card_le_one_iff_subsingleton.1 hc
  exact congrArg Subtype.val (Subsingleton.elim (⟨z, ⟨⟨⟨hz, hb0⟩, hb1⟩, hb2⟩⟩ :
    ↥(K ⊓ MulAction.stabilizer (Equiv.Perm (Fin 360)) b0 ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 360)) b1 ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 360)) b2)) ⟨1, Subgroup.one_mem _⟩)

end CFSG.KC.AE6Tri

end
