module

public import CFSG.Certificates.Kernel.GMS78RuWSound
import all CFSG.Certificates.Kernel.Spor.OrdSound
public import CFSG.Certificates.Kernel.Spor.OrdSound

public section

namespace CFSG.KC.GMSW

open CFSG.KC.Ord

open CFSG.KS.Ord in
private theorem canon_eq {p w S d T L H CM RM ONE LV HV A B : Nat}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true)
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

theorem relNe_sound {p d w S T L H CM RM ONE LV HV nb Lg : Nat} {RB : Nat → Nat}
    {rels : List (List (Nat × Bool))}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    (hroot : rootsOK RB (validM p nb L H) 1 (Lg + 1) = true)
    (hinv : invsOK RB (mulR p w S d T L H CM RM) (validM p nb L H) Lg ONE = true)
    (hb : relsBounded rels Lg = true) {r : Nat}
    (h : relNeOK RB (mulR p w S d T L H CM RM) rels Lg ONE r = true) :
    ((nthRel rels r).map fun x => CFSG.KS.Ord.ordMat p d w S (letM RB Lg x)).prod ≠ 1 := by
  open CFSG.KS.Ord in
  subst hnb
  have hmul : ∀ A B, Canon p d w A → Canon p d w B →
      Canon p d w (mulR p w S d T L H CM RM A B) ∧
        ordMat p d w S (mulR p w S d T L H CM RM A B) = ordMat p d w S A * ordMat p d w S B :=
    fun A B hA hB => mulR_sound hc hA hB
  obtain ⟨hONEc, hONE⟩ := one_sound hc
  have hR0 := rec_and (f := fun i => Bool.rec (motive := fun _ => Bool) true
    (validM p (d * S) L H (RB i)) (Nat.ble 1 i)) (Lg + 1) hroot
  have hR : ∀ g < Lg, Canon p d w (RB (g + 1)) := by
    intro g hg
    have h := hR0 (g + 1) (by omega)
    have hb1 : Nat.ble 1 (g + 1) = true := Nat.ble_eq.mpr (by omega)
    rw [hb1] at h
    exact validM_canon hc h
  have hI0 := rec_and (f := fun g => andB (validM p (d * S) L H (RB (Nat.add (Nat.succ Lg) g)))
    (Nat.beq (mulR p w S d T L H CM RM (RB (Nat.succ g)) (RB (Nat.add (Nat.succ Lg) g))) ONE))
    Lg hinv
  have hlet : ∀ x : Nat × Bool, x.1 < Lg → Canon p d w (letM RB Lg x) := by
    rintro ⟨g, s⟩ hg
    cases s
    · exact validM_canon hc (CFSG.KS.Ord.andB_true (hI0 g hg)).1
    · exact hR g hg
  have h' : andB (Nat.blt r (lenL rels))
      (notB (Nat.beq (segProd RB (mulR p w S d T L H CM RM) ONE Lg 0 (lenL (nthRel rels r))
        (nthRel rels r) 0 ONE) ONE)) = true := h
  obtain ⟨hr, hne⟩ := CFSG.KS.Ord.andB_true h'
  have hr' : r < rels.length := by
    rw [← CFSG.KS.Ord.lenL_eq]
    exact Nat.blt_eq.mp hr
  have hmem : nthRel rels r ∈ rels := by
    rw [nthRel_eq rels r hr']
    exact List.getElem_mem hr'
  have hbd := relsBounded_spec rels hb
  obtain ⟨hsc, hs⟩ := segProd_sem (P := Canon p d w) (M := ordMat p d w S) (lo := 0)
    (hi := lenL (nthRel rels r)) hmul hONE (nthRel rels r) 0 ONE (Nat.le_refl 0)
    (by rw [CFSG.KS.Ord.lenL_eq]; omega) hONEc (fun x hx => hlet x (hbd _ hmem x hx))
  intro hprod
  rw [hONE, one_mul, hprod, ← hONE] at hs
  rw [canon_eq hc hsc hONEc hs, Nat.beq_refl] at hne
  exact Bool.false_ne_true hne

private noncomputable def packV : List Nat → Nat
  | [] => 0
  | x :: R => x + 64 * packV R

private theorem packK_eq : ∀ R : List Nat, (∀ x ∈ R, x < 64) → ∀ i,
    packK R i = packV R <<< (6 * i)
  | [], _, i => by
    change 0 = 0 <<< (6 * i)
    rw [Nat.zero_shiftLeft]
  | x :: R, hR, i => by
    change Nat.lor (Nat.shiftLeft x (Nat.mul 6 i)) (packK R (Nat.succ i)) = _
    rw [packK_eq R (fun y hy => hR y (List.mem_cons_of_mem _ hy)) (Nat.succ i)]
    have hx : x < 2 ^ 6 := hR x List.mem_cons_self
    change x <<< (6 * i) ||| packV R <<< (6 * (i + 1)) = (x + 64 * packV R) <<< (6 * i)
    rw [show 6 * (i + 1) = 6 + 6 * i by ring, Nat.shiftLeft_add, ← Nat.shiftLeft_or_distrib,
      Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx]
    congr 1
    rw [Nat.shiftLeft_eq]
    ring

private theorem packV_field : ∀ R : List Nat, (∀ x ∈ R, x < 64) → ∀ i,
    packV R / 2 ^ (6 * i) % 2 ^ 6 = R.getD i 0
  | [], _, i => by simp [packV]
  | x :: R, hR, 0 => by
    have hx := hR x List.mem_cons_self
    simp only [packV, Nat.mul_zero, Nat.pow_zero, Nat.div_one, List.getD_cons_zero]
    omega
  | x :: R, hR, i + 1 => by
    have hx := hR x List.mem_cons_self
    rw [List.getD_cons_succ, ← packV_field R (fun y hy => hR y (List.mem_cons_of_mem _ hy)) i,
      show 6 * (i + 1) = 6 + 6 * i by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul]
    congr 2
    simp only [packV]
    omega

private theorem bitsN_eq (x o m : Nat) : bitsN x o m = x / 2 ^ o % 2 ^ m := by
  unfold bitsN
  change (x >>> o) &&& ((1 <<< m) - 1) = _
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

private theorem bit_cond (i j : Nat) :
    Nat.beq (Nat.land (Nat.shiftRight i j) 1) 1 = i.testBit j := by
  change ((i >>> j) &&& 1 == 1) = _
  unfold Nat.testBit
  rw [Nat.and_comm 1, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (i >>> j) with h | h <;> simp [h]

private theorem allLtK_spec : ∀ R : List Nat, allLtK R 64 = true → ∀ x ∈ R, x < 64
  | [], _ => by simp
  | x :: R, h => by
    obtain ⟨h1, h2⟩ := andB_eq_true.1 (h : andB (Nat.blt x 64) (allLtK R 64) = true)
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact Nat.blt_eq.mp h1
    · exact allLtK_spec R h2 y hy

private theorem xorRec_eq (i : Nat) (F : Nat → Nat) : ∀ n,
    Nat.rec (motive := fun _ => Nat) 0
      (fun j acc => Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (F j))
        (Nat.beq (Nat.land (Nat.shiftRight i j) 1) 1)) n =
      ((List.range n).filter fun j => i.testBit j).foldl (fun a j => a ^^^ F j) 0
  | 0 => rfl
  | n + 1 => by
    change Bool.rec (motive := fun _ => Nat) _ (Nat.xor _ (F n))
      (Nat.beq (Nat.land (Nat.shiftRight i n) 1) 1) = _
    rw [xorRec_eq i F n, bit_cond, List.range_succ, List.filter_append, List.foldl_append]
    cases h : i.testBit n <;> simp [h] <;> rfl


theorem linTab_sound {T : List (List Nat)} (h : linTabK T = true) :
    ∀ k < 6, ∀ i < 64, (T.getD k []).getD i 0 =
      ((List.range 6).filter fun j => i.testBit j).foldl
        (fun a j => a ^^^ (T.getD k []).getD (2 ^ j) 0) 0 := by
  intro k hk i hi
  have h' : andB (Nat.beq (lenL T) 6) (List.rec (motive := fun _ => Bool) true
      (fun R _ ih => andB (rowLinK R) ih) T) = true := h
  obtain ⟨hlen, hrows⟩ := andB_eq_true.1 h'
  have hrow : ∀ R ∈ T, rowLinK R = true := by
    clear hlen h h' hk
    induction T with
    | nil => simp
    | cons R T ih =>
      obtain ⟨h1, h2⟩ := andB_eq_true.1 hrows
      intro R' hR'
      rcases List.mem_cons.1 hR' with rfl | hR'
      · exact h1
      · exact ih h2 R' hR'
  have hkT : k < T.length := by
    rw [← lenL_eq, Nat.eq_of_beq_eq_true hlen]
    exact hk
  have hmem : T.getD k [] ∈ T := by
    rw [List.getD_eq_getElem _ _ hkT]
    exact List.getElem_mem hkT
  generalize T.getD k [] = R at hmem ⊢
  have hR := hrow R hmem
  have hR' : andB (Nat.beq (lenL R) 64) (andB (allLtK R 64)
      (Nat.rec (motive := fun _ => Bool) true
        (fun i ih => andB ih (Nat.beq (bitsN (packK R 0) (Nat.mul 6 i) 6) (xorBitsK (packK R 0) i)))
        64)) = true := hR
  obtain ⟨-, hR'⟩ := andB_eq_true.1 hR'
  obtain ⟨hlt, hlin⟩ := andB_eq_true.1 hR'
  have hb := allLtK_spec R hlt
  have hP : packK R 0 = packV R := by rw [packK_eq R hb 0, Nat.mul_zero, Nat.shiftLeft_zero]
  have hfld : ∀ t, bitsN (packK R 0) (6 * t) 6 = R.getD t 0 := fun t => by
    rw [bitsN_eq, hP, packV_field R hb t]
  have e := Nat.eq_of_beq_eq_true (CFSG.KS.Ord.rec_and
    (f := fun i => Nat.beq (bitsN (packK R 0) (Nat.mul 6 i) 6) (xorBitsK (packK R 0) i)) 64 hlin i hi)
  change bitsN (packK R 0) (6 * i) 6 = xorBitsK (packK R 0) i at e
  rw [hfld] at e
  rw [e]
  refine (xorRec_eq i (fun j => bitsN (packK R 0) (Nat.mul 6 (Nat.shiftLeft 1 j)) 6) 6).trans ?_
  congr 1
  funext a j
  rw [show Nat.shiftLeft 1 j = 2 ^ j from (Nat.shiftLeft_eq 1 j).trans (Nat.one_mul _)]
  exact congrArg (a ^^^ ·) (hfld _)

end CFSG.KC.GMSW

end
