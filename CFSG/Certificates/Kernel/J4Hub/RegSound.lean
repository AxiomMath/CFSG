module

public import CFSG.Certificates.Kernel.J4Hub.Defs
import all CFSG.Certificates.Kernel.Spor.OrdSound
import CFSG.Certificates.Kernel.Spor.OrdCanon
public import CFSG.Certificates.Kernel.Fam.Lin

public section

namespace CFSG.KS.J4Hub

open CFSG.KC.Ord CFSG.KS.Ord Matrix

variable {p d w S T L H CM RM ONE LV HV nb : Nat}

private theorem andT {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

private theorem strictN_eqR (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

private theorem rec_andR {f : Nat → Bool} : ∀ m,
    Nat.rec (motive := fun _ => Bool) true (fun g ih => andB ih (f g)) m = true →
      ∀ g < m, f g = true
  | 0, _, g, hg => absurd hg (Nat.not_lt_zero g)
  | m + 1, h, g, hg => by
    have h' : andB (Nat.rec (motive := fun _ => Bool) true (fun g ih => andB ih (f g)) m)
        (f m) = true := h
    obtain ⟨h1, h2⟩ := andT h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hg with hg | rfl
    · exact rec_andR m h1 g hg
    · exact h2

private theorem cv (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {X : Nat} (h : validM p nb L H X = true) : Canon p d w X := by
  subst hnb
  exact validM_canon hc h

private theorem vc (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {X : Nat} (h : Canon p d w X) : validM p nb L H X = true := by
  subst hnb
  exact CFSG.KS.OrdCanon.validM_of_canon hc h

private theorem canon_inj (hc : constsOK p w S d T L H CM RM ONE LV HV = true) {A B : Nat}
    (hA : Canon p d w A) (hB : Canon p d w B) (h : ordMat p d w S A = ordMat p d w S B) :
    A = B := by
  obtain ⟨-, hS, hw, -⟩ := consts_facts hc
  subst hS
  rw [pk_lane hw hA.1, pk_lane hw hB.1]
  refine pk_congr fun t ht => ?_
  have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at ht)
  have hi : t / d < d := (Nat.div_lt_iff_lt_mul hd).2 ht
  have hj : t % d < d := Nat.mod_lt _ hd
  have e := congrFun (congrFun h ⟨t / d, hi⟩) ⟨t % d, hj⟩
  have et : d * w * (t / d) + w * (t % d) = w * t := by
    rw [Nat.mul_comm d w, Nat.mul_assoc, ← Nat.mul_add, Nat.div_add_mod]
  simp only [ordMat] at e
  rw [et] at e
  have ha := hA.2 t ht
  have hb := hB.2 t ht
  unfold lane at ha hb ⊢
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at e
  exact e

private theorem rec_inv {s : Nat → Nat → Nat} {x : Nat} {Q : Nat → Nat → Prop} (h0 : Q 0 x)
    (hs : ∀ i a, Q i a → Q (i + 1) (s i a)) : ∀ m, Q m (Nat.rec (motive := fun _ => Nat) x s m)
  | 0 => h0
  | m + 1 => hs m _ (rec_inv h0 hs m)

private theorem shr_split (e n : Nat) : e >>> n = 2 * (e >>> (n + 1)) + (e >>> n) % 2 := by
  have h : e >>> (n + 1) = (e >>> n) / 2 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.pow_succ, Nat.div_div_eq_div_mul]
  rw [h]
  exact (Nat.div_add_mod _ 2).symm

private noncomputable def powStep (mul : Nat → Nat → Nat) (ONE M e : Nat) (i acc : Nat) : Nat :=
  CFSG.KC.Loop.strictN acc (fun a =>
      (fun sq => Bool.rec (motive := fun _ => Nat) sq
          (Bool.rec (motive := fun _ => Nat) (mul sq M) M (Nat.beq sq ONE))
          (Nat.beq (Nat.land (Nat.shiftRight e (Nat.sub (nat_lit 15) i)) (nat_lit 1)) (nat_lit 1)))
        (Bool.rec (motive := fun _ => Nat) (mul a a) a (Nat.beq a ONE)))

private theorem powR_eq (mul : Nat → Nat → Nat) (ONE M e : Nat) :
    powR mul ONE M e = Nat.rec (motive := fun _ => Nat) ONE (powStep mul ONE M e) 16 :=
  rfl

private theorem powR_sem {R : Type} [Monoid R] {mul : Nat → Nat → Nat} {ONE X e : Nat}
    {P : Nat → Prop} {M : Nat → R}
    (hmul : ∀ A B, P A → P B → P (mul A B) ∧ M (mul A B) = M A * M B) (h1 : P ONE)
    (h1' : M ONE = 1) (hX : P X) (he : e < 2 ^ 16) :
    P (powR mul ONE X e) ∧ M (powR mul ONE X e) = M X ^ e := by
  have hfin : ∀ a, (16 ≤ 16 → P a ∧ M a = M X ^ (e >>> (16 - 16))) → P a ∧ M a = M X ^ e := by
    intro a h
    simpa using h le_rfl
  rw [powR_eq]
  apply hfin
  refine rec_inv (s := powStep mul ONE X e) (x := ONE)
    (Q := fun i a => i ≤ 16 → P a ∧ M a = M X ^ (e >>> (16 - i))) ?_ ?_ 16
  · intro _
    have e16 : e >>> (16 - 0) = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt he
    rw [e16, pow_zero]
    exact ⟨h1, h1'⟩
  · intro i a ih hi
    obtain ⟨hPa, hMa⟩ := ih (by omega)
    unfold powStep
    rw [strictN_eqR]
    dsimp only
    obtain ⟨sq, hsq, hPs, hMs⟩ : ∃ sq, Bool.rec (motive := fun _ => Nat) (mul a a) a
        (Nat.beq a ONE) = sq ∧ P sq ∧ M sq = M X ^ (2 * (e >>> (16 - i))) := by
      cases hq : Nat.beq a ONE
      · obtain ⟨h2, h3⟩ := hmul a a hPa hPa
        exact ⟨_, rfl, h2, by rw [h3, hMa, ← pow_add, two_mul]⟩
      · have ha : a = ONE := Nat.eq_of_beq_eq_true hq
        refine ⟨_, rfl, hPa, ?_⟩
        rw [two_mul, pow_add, ← hMa, ha, h1', one_mul]
    rw [hsq]
    have hsplit := shr_split e (15 - i)
    have e1 : 15 - i + 1 = 16 - i := by omega
    have e2 : 16 - (i + 1) = 15 - i := by omega
    rw [e1] at hsplit
    rw [e2]
    have hy : Nat.land (Nat.shiftRight e (Nat.sub (nat_lit 15) i)) (nat_lit 1) = (e >>> (15 - i)) % 2 :=
      Nat.and_one_is_mod _
    rw [hy]
    rcases Nat.mod_two_eq_zero_or_one (e >>> (15 - i)) with hb | hb
    · rw [hb]
      refine ⟨hPs, ?_⟩
      change M sq = M X ^ (e >>> (15 - i))
      rw [hsplit, hb, Nat.add_zero, hMs]
    · rw [hb]
      change P (Bool.rec (motive := fun _ => Nat) (mul sq X) X (Nat.beq sq ONE)) ∧
        M (Bool.rec (motive := fun _ => Nat) (mul sq X) X (Nat.beq sq ONE)) = M X ^ (e >>> (15 - i))
      rw [hsplit, hb, pow_succ, ← hMs]
      cases hq : Nat.beq sq ONE
      · exact hmul sq X hPs hX
      · have hs1 : sq = ONE := Nat.eq_of_beq_eq_true hq
        refine ⟨hX, ?_⟩
        rw [hs1, h1', one_mul]

private theorem powR_mat (hc : constsOK p w S d T L H CM RM ONE LV HV = true) {X e : Nat}
    (hX : Canon p d w X) (he : e < 65536) :
    Canon p d w (powR (mulR p w S d T L H CM RM) ONE X e) ∧
      ordMat p d w S (powR (mulR p w S d T L H CM RM) ONE X e) = ordMat p d w S X ^ e :=
  powR_sem (fun _ _ hA hB => mulR_sound hc hA hB) (CFSG.KS.Ord.one_sound hc).1
    (CFSG.KS.Ord.one_sound hc).2 hX (by norm_num; exact he)

theorem one_sound' (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S) :
    validM p nb L H ONE = true ∧ ordMat p d w S ONE = 1 :=
  ⟨vc hc hnb (CFSG.KS.Ord.one_sound hc).1, (CFSG.KS.Ord.one_sound hc).2⟩

theorem mul_sound' (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {A B : Nat} (hA : validM p nb L H A = true) (hB : validM p nb L H B = true) :
    validM p nb L H (mulR p w S d T L H CM RM A B) = true ∧
      ordMat p d w S (mulR p w S d T L H CM RM A B) = ordMat p d w S A * ordMat p d w S B := by
  obtain ⟨h1, h2⟩ := mulR_sound hc (cv hc hnb hA) (cv hc hnb hB)
  exact ⟨vc hc hnb h1, h2⟩

theorem ordMat_inj' (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {A B : Nat} (hA : validM p nb L H A = true) (hB : validM p nb L H B = true)
    (h : ordMat p d w S A = ordMat p d w S B) : A = B :=
  canon_inj hc (cv hc hnb hA) (cv hc hnb hB) h

theorem ordExact_sound' (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {RB : Nat → Nat} {nreg r q : Nat} {ps : List Nat} (hq : q < 65536)
    (hr : validM p nb L H (RB r) = true)
    (h : CFSG.KC.Fam.ordExact RB (mulR p w S d T L H CM RM) ONE nreg r q ps = true) :
    0 < r ∧ r < nreg ∧ ordMat p d w S (RB r) ^ q = 1 ∧ ∀ l ∈ ps, ordMat p d w S (RB r) ^ (q / l) ≠ 1 := by
  have hX := cv hc hnb hr
  obtain ⟨hO1, hO2⟩ := CFSG.KS.Ord.one_sound hc
  obtain ⟨h1, h⟩ := andT h
  obtain ⟨h2, h3⟩ := andT h
  obtain ⟨h1a, h1b⟩ := andT h1
  refine ⟨Nat.blt_eq.mp h1a, Nat.blt_eq.mp h1b, ?_, ?_⟩
  · rw [← (powR_mat hc hX hq).2, Nat.eq_of_beq_eq_true h2, hO2]
  · have key : ∀ ps : List Nat,
        CFSG.KC.Fam.properOK (mulR p w S d T L H CM RM) ONE (RB r) q ps = true →
          ∀ l ∈ ps, ordMat p d w S (RB r) ^ (q / l) ≠ 1 := by
      intro ps
      induction ps with
      | nil => intro _ l hl; simp at hl
      | cons l ps ih =>
        intro hp l' hl'
        have hp' : andB (notB (Nat.beq (powR (mulR p w S d T L H CM RM) ONE (RB r) (Nat.div q l))
            ONE)) (CFSG.KC.Fam.properOK (mulR p w S d T L H CM RM) ONE (RB r) q ps) = true := hp
        obtain ⟨ha, hb⟩ := andT hp'
        rcases List.mem_cons.1 hl' with rfl | hl'
        · intro he
          have hP := powR_mat hc hX (e := Nat.div q l') (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hq)
          have e1 : powR (mulR p w S d T L H CM RM) ONE (RB r) (Nat.div q l') = ONE :=
            canon_inj hc hP.1 hO1 (hP.2.trans (he.trans hO2.symm))
          rw [e1, Nat.beq_refl] at ha
          exact absurd ha (by decide)
        · exact ih hb l' hl'
    exact key ps h3

theorem prime_sound' (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {RB : Nat → Nat} {nreg r q : Nat} (hq : q < 65536) (hr : validM p nb L H (RB r) = true)
    (h : primeOK RB (mulR p w S d T L H CM RM) ONE nreg r q = true) :
    ordMat p d w S (RB r) ^ q = 1 ∧ ordMat p d w S (RB r) ≠ 1 := by
  have hX := cv hc hnb hr
  obtain ⟨hO1, hO2⟩ := CFSG.KS.Ord.one_sound hc
  obtain ⟨-, h⟩ := andT h
  obtain ⟨h2, h3⟩ := andT h
  refine ⟨?_, fun he => ?_⟩
  · rw [← (powR_mat hc hX hq).2, Nat.eq_of_beq_eq_true h2, hO2]
  · rw [canon_inj hc hX hO1 (by rw [he, hO2]), Nat.beq_refl] at h3
    exact absurd h3 (by decide)

theorem invPairs_sound' (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {RB : Nat → Nat} {nreg GR IR Lg : Nat}
    (h : CFSG.KC.Fam.invPairs RB (mulR p w S d T L H CM RM) ONE nreg GR IR Lg = true) :
    ∀ g < Lg, 0 < at16 GR g ∧ at16 GR g < nreg ∧ 0 < at16 IR g ∧ at16 IR g < nreg ∧
      (validM p nb L H (RB (at16 GR g)) = true → validM p nb L H (RB (at16 IR g)) = true →
        ordMat p d w S (RB (at16 GR g)) * ordMat p d w S (RB (at16 IR g)) = 1) := by
  obtain ⟨h1, h⟩ := andT h
  obtain ⟨h2, h3⟩ := andT h
  intro g hg
  obtain ⟨a1, a2⟩ := andT (rec_andR (f := fun k => regBelow (at16 GR k) nreg) Lg h1 g hg)
  obtain ⟨b1, b2⟩ := andT (rec_andR (f := fun k => regBelow (at16 IR k) nreg) Lg h2 g hg)
  refine ⟨Nat.blt_eq.mp a1, Nat.blt_eq.mp a2, Nat.blt_eq.mp b1, Nat.blt_eq.mp b2, fun hA hB => ?_⟩
  have e := Nat.eq_of_beq_eq_true (rec_andR (f := fun k =>
    Nat.beq (mulR p w S d T L H CM RM (RB (at16 GR k)) (RB (at16 IR k))) ONE) Lg h3 g hg)
  rw [← (mulR_sound hc (cv hc hnb hA) (cv hc hnb hB)).2, e, (CFSG.KS.Ord.one_sound hc).2]

private theorem wordProd_sem (hc : constsOK p w S d T L H CM RM ONE LV HV = true)
    {RB : Nat → Nat} {GR IR : Nat} : ∀ (l : List (Nat × Bool)) (acc : Nat), Canon p d w acc →
    (∀ x ∈ l, Canon p d w (CFSG.KC.Fam.letL RB GR IR x)) →
    Canon p d w (CFSG.KC.Fam.wordProd RB (mulR p w S d T L H CM RM) ONE GR IR l acc) ∧
      ordMat p d w S (CFSG.KC.Fam.wordProd RB (mulR p w S d T L H CM RM) ONE GR IR l acc) =
        ordMat p d w S acc * (l.map fun x => ordMat p d w S (CFSG.KC.Fam.letL RB GR IR x)).prod
  | [], _, hacc, _ => ⟨hacc, by rw [List.map_nil, List.prod_nil, mul_one]; rfl⟩
  | x :: l, acc, hacc, hl => by
    have e : CFSG.KC.Fam.wordProd RB (mulR p w S d T L H CM RM) ONE GR IR (x :: l) acc =
        CFSG.KC.Fam.wordProd RB (mulR p w S d T L H CM RM) ONE GR IR l
          (Bool.rec (motive := fun _ => Nat) (mulR p w S d T L H CM RM acc
            (CFSG.KC.Fam.letL RB GR IR x)) (CFSG.KC.Fam.letL RB GR IR x) (Nat.beq acc ONE)) :=
      strictN_eqR _ _
    have hx := hl x (by simp)
    obtain ⟨hONE1, hONE2⟩ := CFSG.KS.Ord.one_sound hc
    obtain ⟨acc', hacc', hP', hM'⟩ : ∃ acc', Bool.rec (motive := fun _ => Nat)
        (mulR p w S d T L H CM RM acc (CFSG.KC.Fam.letL RB GR IR x)) (CFSG.KC.Fam.letL RB GR IR x)
        (Nat.beq acc ONE) = acc' ∧ Canon p d w acc' ∧
          ordMat p d w S acc' = ordMat p d w S acc * ordMat p d w S (CFSG.KC.Fam.letL RB GR IR x) := by
      cases hq : Nat.beq acc ONE
      · exact ⟨_, rfl, mulR_sound hc hacc hx⟩
      · have hq' : acc = ONE := Nat.eq_of_beq_eq_true hq
        exact ⟨_, rfl, hx, by rw [hq', hONE2, one_mul]⟩
    rw [e, hacc']
    obtain ⟨h1, h2⟩ := wordProd_sem hc l acc' hP' fun y hy => hl y (List.mem_cons_of_mem _ hy)
    exact ⟨h1, by rw [h2, hM', List.map_cons, List.prod_cons, mul_assoc]⟩

theorem wordProd_sound' (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {RB : Nat → Nat} {GR IR : Nat} {l : List (Nat × Bool)}
    (hv : ∀ x ∈ l, validM p nb L H (CFSG.KC.Fam.letL RB GR IR x) = true) :
    validM p nb L H (CFSG.KC.Fam.wordProd RB (mulR p w S d T L H CM RM) ONE GR IR l ONE) = true ∧
      ordMat p d w S (CFSG.KC.Fam.wordProd RB (mulR p w S d T L H CM RM) ONE GR IR l ONE) =
        (l.map fun x => ordMat p d w S (CFSG.KC.Fam.letL RB GR IR x)).prod := by
  obtain ⟨hO1, hO2⟩ := CFSG.KS.Ord.one_sound hc
  obtain ⟨h1, h2⟩ := wordProd_sem hc l ONE hO1 fun x hx => cv hc hnb (hv x hx)
  exact ⟨vc hc hnb h1, by rw [h2, hO2, one_mul]⟩

theorem conj_sound' (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {C Ci X Y : Nat} (hX : validM p nb L H X = true) (hY : validM p nb L H Y = true)
    (h : CFSG.KC.Fam.conjOK (mulR p w S d T L H CM RM) (validM p nb L H) ONE C Ci X Y = true) :
    ordMat p d w S C * ordMat p d w S Ci = 1 ∧
      ordMat p d w S X * ordMat p d w S C = ordMat p d w S C * ordMat p d w S Y := by
  obtain ⟨hC, h⟩ := andT h
  obtain ⟨hCi, h⟩ := andT h
  obtain ⟨h1, h2⟩ := andT h
  have cC := cv hc hnb hC
  have cCi := cv hc hnb hCi
  have cX := cv hc hnb hX
  have cY := cv hc hnb hY
  refine ⟨?_, ?_⟩
  · rw [← (mulR_sound hc cC cCi).2, Nat.eq_of_beq_eq_true h1, (CFSG.KS.Ord.one_sound hc).2]
  · rw [← (mulR_sound hc cX cC).2, ← (mulR_sound hc cC cY).2, Nat.eq_of_beq_eq_true h2]

private noncomputable def chunkRunR (RB : Nat → Nat) (mul : Nat → Nat → Nat) (vld : Nat → Bool)
    (ONE : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih2 J S => CFSG.KC.Loop.strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
        (andB (Nat.blt (nat_lit 0) S) (insOK RB mul vld ONE S (bitsN J (nat_lit 0) (nat_lit 50)))))
      (ih2 (Nat.shiftRight J (nat_lit 50))))

private theorem chunkRunR_succ (RB : Nat → Nat) (mul : Nat → Nat → Nat) (vld : Nat → Bool)
    (ONE m J S : Nat) :
    chunkRunR RB mul vld ONE (m + 1) J S =
      CFSG.KC.Loop.strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
          (andB (Nat.blt (nat_lit 0) S) (insOK RB mul vld ONE S (bitsN J (nat_lit 0) (nat_lit 50)))))
        (chunkRunR RB mul vld ONE m (Nat.shiftRight J (nat_lit 50))) :=
  rfl

private theorem runSlp_consR (RB : Nat → Nat) (mul : Nat → Nat → Nat) (vld : Nat → Bool)
    (ONE C : Nat) (Cs : List Nat) (s : Nat) :
    runSlp RB mul vld ONE (C :: Cs) s =
      runSlp RB mul vld ONE Cs (chunkRunR RB mul vld ONE (Nat.land C (nat_lit 255))
        (Nat.shiftRight C (nat_lit 8)) s) :=
  strictN_eqR _ _

private theorem brec_presR {Q : Nat → Prop} {x y : Nat} (c : Bool) (hx : Q x) (hy : Q y) :
    Q (Bool.rec (motive := fun _ => Nat) x y c) := by
  cases c
  · exact hx
  · exact hy

private theorem nrec_presR {Q : Nat → Prop} {x : Nat} {s : Nat → Nat → Nat} (hx : Q x)
    (hs : ∀ i a, Q a → Q (s i a)) : ∀ m, Q (Nat.rec (motive := fun _ => Nat) x s m)
  | 0 => hx
  | m + 1 => hs m _ (nrec_presR hx hs m)

private theorem powR_presR {Q : Nat → Prop} {mul : Nat → Nat → Nat} {ONE M : Nat} (e : Nat)
    (hmul : ∀ A B, Q A → Q B → Q (mul A B)) (hone : Q ONE) (hM : Q M) :
    Q (powR mul ONE M e) := by
  unfold powR
  generalize (nat_lit 16) = m
  apply nrec_presR hone
  intro i a ha
  rw [strictN_eqR]
  have hsq := brec_presR (Q := Q) (Nat.beq a ONE) (hmul a a ha ha) ha
  exact brec_presR _ hsq (brec_presR _ (hmul _ _ hsq hM) hM)

theorem slp_sound' (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {G : Subgroup (GL (Fin d) (ZMod p))} {RB : Nat → Nat} {Cs : List Nat} {s s' : Nat}
    (hin : RegsIn p d w S nb L H G RB s)
    (h : Nat.beq (runSlp RB (mulR p w S d T L H CM RM) (validM p nb L H) ONE Cs s) s' = true)
    (_hs' : 0 < s') : RegsIn p d w S nb L H G RB s' := by
  subst hnb
  obtain ⟨hONEc, hONE⟩ := CFSG.KS.Ord.one_sound hc
  let Q : Nat → Prop := fun X => Canon p d w X ∧
    ∃ g ∈ G, ((g : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)) = ordMat p d w S X
  have hmulQ : ∀ A B, Q A → Q B → Q (mulR p w S d T L H CM RM A B) := by
    rintro A B ⟨cA, gA, hgA, eA⟩ ⟨cB, gB, hgB, eB⟩
    obtain ⟨h1, h2⟩ := mulR_sound hc cA cB
    exact ⟨h1, gA * gB, G.mul_mem hgA hgB, by rw [h2, Units.val_mul, eA, eB]⟩
  have hQ : ∀ r, 0 < r → ∀ s, RegsIn p d w S (d * S) L H G RB s → r < s → Q (RB r) := by
    intro r hr s hs hrs
    obtain ⟨h1, h2⟩ := hs r hr hrs
    exact ⟨validM_canon hc h1, h2⟩
  have hins : ∀ s ins, RegsIn p d w S (d * S) L H G RB s → 0 < s →
      insOK RB (mulR p w S d T L H CM RM) (validM p (d * S) L H) ONE s ins = true →
      RegsIn p d w S (d * S) L H G RB (s + 1) := by
    intro s ins hs hs0 h
    have hnew : validM p (d * S) L H (RB s) = true ∧
        ∃ g ∈ G, ((g : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)) =
          ordMat p d w S (RB s) := by
      unfold insOK at h
      generalize Nat.land ins (nat_lit 3) = k at h
      generalize bitsN ins (nat_lit 2) (nat_lit 16) = a at h
      generalize bitsN ins (nat_lit 18) (nat_lit 16) = b at h
      generalize bitsN ins (nat_lit 34) (nat_lit 16) = e at h
      dsimp only at h
      revert h
      cases Nat.beq k (nat_lit 0)
      · cases Nat.beq k (nat_lit 1)
        · cases Nat.beq k (nat_lit 2)
          · intro h
            exact absurd h Bool.false_ne_true
          · intro h
            obtain ⟨ha, h⟩ := andT h
            obtain ⟨hv, h⟩ := andT h
            obtain ⟨ha0, has⟩ := andT ha
            obtain ⟨-, ga, hga, ea⟩ := hQ a (Nat.blt_eq.mp ha0) s hs (Nat.blt_eq.mp has)
            have hcs := validM_canon hc hv
            have hm := (mulR_sound hc (hQ a (Nat.blt_eq.mp ha0) s hs (Nat.blt_eq.mp has)).1 hcs).2
            rw [Nat.eq_of_beq_eq_true h, hONE] at hm
            refine ⟨hv, ga⁻¹, G.inv_mem hga, ?_⟩
            calc ((ga⁻¹ : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p))
                = ((ga⁻¹ : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)) *
                    (ordMat p d w S (RB a) * ordMat p d w S (RB s)) := by rw [← hm, mul_one]
              _ = ordMat p d w S (RB s) := by
                rw [← ea, ← mul_assoc, Units.inv_mul, one_mul]
        · intro h
          obtain ⟨ha, h⟩ := andT h
          obtain ⟨-, h⟩ := andT h
          obtain ⟨ha0, has⟩ := andT ha
          have hQa := hQ a (Nat.blt_eq.mp ha0) s hs (Nat.blt_eq.mp has)
          have hp := powR_presR (Q := Q) e hmulQ
            ⟨hONEc, 1, G.one_mem, by rw [hONE, Units.val_one]⟩ hQa
          rw [← Nat.eq_of_beq_eq_true h] at hp
          exact ⟨CFSG.KS.OrdCanon.validM_of_canon hc hp.1, hp.2⟩
      · intro h
        obtain ⟨ha, h⟩ := andT h
        obtain ⟨hb, h⟩ := andT h
        obtain ⟨ha0, has⟩ := andT ha
        obtain ⟨hb0, hbs⟩ := andT hb
        have hQa := hQ a (Nat.blt_eq.mp ha0) s hs (Nat.blt_eq.mp has)
        have hQb := hQ b (Nat.blt_eq.mp hb0) s hs (Nat.blt_eq.mp hbs)
        have hp := hmulQ _ _ hQa hQb
        rw [← Nat.eq_of_beq_eq_true h] at hp
        exact ⟨CFSG.KS.OrdCanon.validM_of_canon hc hp.1, hp.2⟩
    intro r hr hrs
    rcases Nat.lt_succ_iff_lt_or_eq.1 hrs with hrs | rfl
    · exact hs r hr hrs
    · exact hnew
  have hzero : RegsIn p d w S (d * S) L H G RB 0 := fun r _ hr => absurd hr (Nat.not_lt_zero r)
  have hchunk : ∀ m J s, RegsIn p d w S (d * S) L H G RB s →
      RegsIn p d w S (d * S) L H G RB
        (chunkRunR RB (mulR p w S d T L H CM RM) (validM p (d * S) L H) ONE m J s) := by
    intro m
    induction m with
    | zero => intro J s hs; exact hs
    | succ m ih =>
      intro J s hs
      rw [chunkRunR_succ, strictN_eqR]
      refine ih (Nat.shiftRight J (nat_lit 50)) _ ?_
      cases hb : andB (Nat.blt (nat_lit 0) s)
          (insOK RB (mulR p w S d T L H CM RM) (validM p (d * S) L H) ONE s
            (bitsN J (nat_lit 0) (nat_lit 50)))
      · exact hzero
      · obtain ⟨h1, h2⟩ := andT hb
        exact hins s _ hs (Nat.blt_eq.mp h1) h2
  have hrun : ∀ (Cs : List Nat) s, RegsIn p d w S (d * S) L H G RB s →
      RegsIn p d w S (d * S) L H G RB
        (runSlp RB (mulR p w S d T L H CM RM) (validM p (d * S) L H) ONE Cs s) := by
    intro Cs
    induction Cs with
    | nil => intro s hs; exact hs
    | cons C Cs ih =>
      intro s hs
      rw [runSlp_consR]
      exact ih _ (hchunk _ _ _ hs)
  rw [← Nat.eq_of_beq_eq_true h]
  exact hrun Cs s hin

end CFSG.KS.J4Hub

end
