module

public import CFSG.Certificates.Kernel.Q47KOSound
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.PackSetSound

public section

namespace CFSG.KC.Q47K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK

@[expose] def mB47 (v j : Nat) : Nat := Nat.mod (Nat.div v (Nat.pow 2 j)) 2

@[expose] def xs47 (g : Nat → Nat) (v : Nat) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun j acc => Nat.xor acc (Nat.mul (mB47 v j) (g j))) k

theorem add_two_pow_xor47 {b k : Nat} (hb : b < 2 ^ k) : b + 2 ^ k = b ^^^ 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  have e : b + 2 ^ k = 2 ^ k * 1 + b := by omega
  rw [e, Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases h : i < k
  · have : k ≠ i := by omega
    simp [h, this]
  · have hb' : b.testBit i = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb
      (Nat.pow_le_pow_right (by omega) (by omega)))
    by_cases hk : i = k
    · subst hk
      simp [hb']
    · have hik : k ≠ i := fun h' => hk h'.symm
      have : 0 < i - k := by omega
      have h1 : Nat.testBit 1 (i - k) = false :=
        Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega))
      simp [h, hb', hik, h1]

theorem mB47_mod {a j k : Nat} (hj : j < k) : mB47 (a % 2 ^ k) j = mB47 a j := by
  unfold mB47
  change a % 2 ^ k / 2 ^ j % 2 = a / 2 ^ j % 2
  have e : 2 ^ k = 2 ^ j * 2 ^ (k - j) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [e, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  exact Nat.dvd_of_mod_eq_zero (by
    have : k - j = (k - j - 1) + 1 := by omega
    rw [this, Nat.pow_succ, Nat.mul_mod_left])

theorem xs47_mod (g : Nat → Nat) (a : Nat) {k : Nat} :
    ∀ m ≤ k, xs47 g (a % 2 ^ k) m = xs47 g a m
  | 0, _ => rfl
  | m + 1, h => by
    change Nat.xor (xs47 g (a % 2 ^ k) m) (Nat.mul (mB47 (a % 2 ^ k) m) (g m)) =
      Nat.xor (xs47 g a m) (Nat.mul (mB47 a m) (g m))
    rw [xs47_mod g a m (by omega), mB47_mod (by omega)]

theorem lin_xs47 {f : Nat → Nat} {n : Nat}
    (hl : ∀ u v, u < 2 ^ n → v < 2 ^ n → f (u ^^^ v) = f u ^^^ f v) :
    ∀ k ≤ n, ∀ a < 2 ^ k, f a = xs47 (fun j => f (2 ^ j)) a k
  | 0, _, a, ha => by
    have a0 : a = 0 := by simpa using ha
    subst a0
    have h := hl 0 0 (Nat.two_pow_pos n) (Nat.two_pow_pos n)
    rw [Nat.xor_self] at h
    change f 0 = 0
    rw [h, Nat.xor_self]
  | k + 1, hk, a, ha => by
    have hpk : 2 ^ k < 2 ^ n := Nat.pow_lt_pow_right (by omega) (by omega)
    have hb : a % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
    have hdm := Nat.div_add_mod a (2 ^ k)
    have hq : a / 2 ^ k < 2 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)]
      rw [Nat.pow_succ] at ha
      omega
    have hB : mB47 a k = a / 2 ^ k := Nat.mod_eq_of_lt hq
    change f a = Nat.xor (xs47 (fun j => f (2 ^ j)) a k) (Nat.mul (mB47 a k) (f (2 ^ k)))
    rw [← xs47_mod _ a k (Nat.le_refl k), ← lin_xs47 hl k (by omega) _ hb, hB]
    rcases (by omega : a / 2 ^ k = 0 ∨ a / 2 ^ k = 1) with h0 | h1
    · rw [h0]
      change f a = f (a % 2 ^ k) ^^^ 0 * f (2 ^ k)
      rw [Nat.zero_mul, Nat.xor_zero]
      congr 1
      rw [h0, Nat.mul_zero, Nat.zero_add] at hdm
      exact hdm.symm
    · rw [h1]
      change f a = f (a % 2 ^ k) ^^^ 1 * f (2 ^ k)
      rw [Nat.one_mul]
      have ea : a = a % 2 ^ k ^^^ 2 ^ k := by
        rw [← add_two_pow_xor47 hb]
        rw [h1, Nat.mul_one] at hdm
        omega
      rw [← hl _ _ (Nat.lt_trans hb hpk) hpk, ← ea]

theorem xs47_congr {g g' : Nat → Nat} (v : Nat) : ∀ k, (∀ j < k, g j = g' j) →
    xs47 g v k = xs47 g' v k
  | 0, _ => rfl
  | k + 1, h => by
    change Nat.xor (xs47 g v k) (Nat.mul (mB47 v k) (g k)) =
      Nat.xor (xs47 g' v k) (Nat.mul (mB47 v k) (g' k))
    rw [xs47_congr v k fun j hj => h j (by omega), h k (by omega)]

@[expose] def mC47 (a j : Nat) : Nat := Nat.mod (Nat.div a (Nat.pow 256 j)) 256

@[expose] def mPk47 (g : Nat → Nat) : Nat :=
  g 0 + 256 * (g 1 + 256 * (g 2 + 256 * (g 3 + 256 * (g 4 + 256 * g 5))))

@[expose] def mAp47 (a v : Nat) : Nat := xs47 (mC47 a) v 6

@[expose] def mMul47 (a b : Nat) : Nat := mPk47 fun j => mAp47 a (mC47 b j)

@[expose] noncomputable def mOf47 (t : Nat) : Nat := mPk47 fun j => pg 7 (mask 7) t (2 ^ j)

theorem mPk47_congr {g g' : Nat → Nat} (h : ∀ j < 6, g j = g' j) : mPk47 g = mPk47 g' := by
  unfold mPk47
  rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega),
    h 5 (by omega)]

theorem mC47_mPk47 {g : Nat → Nat} (hg : ∀ j < 6, g j < 256) : ∀ j < 6, mC47 (mPk47 g) j = g j := by
  have h0 := hg 0 (by omega)
  have h1 := hg 1 (by omega)
  have h2 := hg 2 (by omega)
  have h3 := hg 3 (by omega)
  have h4 := hg 4 (by omega)
  have h5 := hg 5 (by omega)
  intro j hj
  unfold mC47 mPk47
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl
  · change (_ + _) / 1 % 256 = _
    omega
  · change (_ + _) / 256 % 256 = _
    omega
  · change (_ + _) / 65536 % 256 = _
    omega
  · change (_ + _) / 16777216 % 256 = _
    omega
  · change (_ + _) / 4294967296 % 256 = _
    omega
  · change (_ + _) / 1099511627776 % 256 = _
    omega

theorem lin_of_addK {t : Nat} (ha : addK t = true) :
    ∀ u v, u < 2 ^ 6 → v < 2 ^ 6 →
      pg 7 (mask 7) t (u ^^^ v) = pg 7 (mask 7) t u ^^^ pg 7 (mask 7) t v := by
  intro u v hu hv
  unfold addK at ha
  exact Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec (CFSG.KC.Pack.allN_spec ha u hu) v hv)

theorem pg_lt64K {t : Nat} (ht : PP 64 7 t) {x : Nat} (hx : x < 64) : pg 7 (mask 7) t x < 64 :=
  (PF.canon_facts ht.1).2.2.2 x hx

theorem mC47_mOf47 {t : Nat} (ht : PP 64 7 t) : ∀ j < 6, mC47 (mOf47 t) j = pg 7 (mask 7) t (2 ^ j) :=
  mC47_mPk47 fun j hj => Nat.lt_trans (pg_lt64K ht (Nat.pow_lt_pow_right (by omega) hj)) (by omega)

theorem pg_mAp47 {t : Nat} (ht : PP 64 7 t) (ha : addK t = true) {a : Nat} (hx : a < 64) :
    pg 7 (mask 7) t a = mAp47 (mOf47 t) a := by
  rw [lin_xs47 (lin_of_addK ha) 6 (Nat.le_refl 6) a hx]
  exact xs47_congr a 6 fun j hj => (mC47_mOf47 ht j hj).symm

theorem mOf47_mul {p q : Nat} (hp : PP 64 7 p) (ap : addK p = true) (hq : PP 64 7 q) :
    mOf47 (HexaK.mul 64 7 p q) = mMul47 (mOf47 p) (mOf47 q) := by
  rw [mOf47, mMul47]
  refine mPk47_congr fun j hj => ?_
  have h2 : 2 ^ j < 64 := Nat.pow_lt_pow_right (by omega) hj
  change pg 7 (mask 7) (pcomp 64 7 (mask 7) p q) (2 ^ j) = _
  rw [PF.pg_pcomp (by omega) h2, mC47_mOf47 hq j hj, pg_mAp47 hp ap (pg_lt64K hq h2)]

theorem addK_mul47 {p q : Nat} (hp : PP 64 7 p) (ap : addK p = true) (hq : PP 64 7 q)
    (aq : addK q = true) : addK (HexaK.mul 64 7 p q) = true := by
  unfold addK
  rw [allN_eq', List.all_eq_true]
  intro u hu
  rw [allN_eq', List.all_eq_true]
  intro v hv
  have hu' := List.mem_range.1 hu
  have hv' := List.mem_range.1 hv
  have huv : Nat.xor u v < 64 := Nat.xor_lt_two_pow (n := 6) hu' hv'
  change Nat.beq (pg 7 (mask 7) (pcomp 64 7 (mask 7) p q) (Nat.xor u v))
    (Nat.xor (pg 7 (mask 7) (pcomp 64 7 (mask 7) p q) u)
      (pg 7 (mask 7) (pcomp 64 7 (mask 7) p q) v)) = true
  rw [PF.pg_pcomp (by omega) huv, PF.pg_pcomp (by omega) hu', PF.pg_pcomp (by omega) hv']
  have e1 := lin_of_addK aq u v hu' hv'
  have e2 := lin_of_addK ap _ _ (pg_lt64K hq hu') (pg_lt64K hq hv')
  change Nat.beq (pg 7 (mask 7) p (pg 7 (mask 7) q (u ^^^ v)))
    (pg 7 (mask 7) p (pg 7 (mask 7) q u) ^^^ pg 7 (mask 7) p (pg 7 (mask 7) q v)) = true
  rw [e1, e2, Nat.beq_refl]

@[expose] noncomputable def cubeM47 (M : Nat) : Bool :=
  allN 6 fun j => Nat.beq (mAp47 M (mAp47 M (mAp47 M (2 ^ j)))) (2 ^ j)

theorem cube_basis47 {t : Nat} (ht : PP 64 7 t) (ha : addK t = true) :
    (allN 64 fun x => Nat.beq (pg 7 (mask 7) t (pg 7 (mask 7) t (pg 7 (mask 7) t x))) x) =
      cubeM47 (mOf47 t) := by
  have hl := lin_of_addK ha
  have b1 : ∀ x < 64, pg 7 (mask 7) t x < 64 := fun x hx => pg_lt64K ht hx
  have e3 : ∀ x < 64, pg 7 (mask 7) t (pg 7 (mask 7) t (pg 7 (mask 7) t x)) =
      mAp47 (mOf47 t) (mAp47 (mOf47 t) (mAp47 (mOf47 t) x)) := fun x hx => by
    rw [pg_mAp47 ht ha (b1 _ (b1 x hx)), pg_mAp47 ht ha (b1 x hx), pg_mAp47 ht ha hx]
  unfold cubeM47
  apply Bool.eq_iff_iff.2
  rw [allN_eq', allN_eq', List.all_eq_true, List.all_eq_true]
  constructor
  · intro h j hj
    have hj' := List.mem_range.1 hj
    have h2 : 2 ^ j < 64 := Nat.pow_lt_pow_right (by omega) hj'
    have := h (2 ^ j) (List.mem_range.2 h2)
    rwa [e3 _ h2] at this
  · intro h x hx
    have hx' := List.mem_range.1 hx
    have lf : ∀ u v, u < 2 ^ 6 → v < 2 ^ 6 →
        (fun x => pg 7 (mask 7) t (pg 7 (mask 7) t (pg 7 (mask 7) t x))) (u ^^^ v) =
          (fun x => pg 7 (mask 7) t (pg 7 (mask 7) t (pg 7 (mask 7) t x))) u ^^^
          (fun x => pg 7 (mask 7) t (pg 7 (mask 7) t (pg 7 (mask 7) t x))) v := by
      intro u v hu hv
      simp only []
      rw [hl u v hu hv, hl _ _ (b1 u hu) (b1 v hv), hl _ _ (b1 _ (b1 u hu)) (b1 _ (b1 v hv))]
    have li : ∀ u v, u < 2 ^ 6 → v < 2 ^ 6 → (fun x : Nat => x) (u ^^^ v) =
        (fun x : Nat => x) u ^^^ (fun x : Nat => x) v := fun _ _ _ _ => rfl
    have r1 := lin_xs47 (f := fun x => pg 7 (mask 7) t (pg 7 (mask 7) t (pg 7 (mask 7) t x))) lf 6
      (Nat.le_refl 6) x hx'
    have r2 := lin_xs47 (f := fun x : Nat => x) li 6 (Nat.le_refl 6) x hx'
    rw [Nat.beq_eq, r1]
    refine Eq.trans (xs47_congr (g' := fun j => 2 ^ j) x 6 fun j hj => ?_) r2.symm
    have h2 : 2 ^ j < 64 := Nat.pow_lt_pow_right (by omega) hj
    have := Nat.eq_of_beq_eq_true (h j (List.mem_range.2 hj))
    rw [e3 _ h2, this]

theorem xs47_id {x : Nat} (hx : x < 64) : xs47 (fun j => 2 ^ j) x 6 = x :=
  (lin_xs47 (f := fun x : Nat => x) (n := 6) (fun _ _ _ _ => rfl) 6 (Nat.le_refl 6) x hx).symm

theorem beq_pidn_mat {t : Nat} (ht : PP 64 7 t) (ha : addK t = true) :
    Nat.beq t (pidn 64 7) = Nat.beq (mOf47 t) (mOf47 (pidn 64 7)) := by
  have hsz : szOK 64 7 = true := by decide
  have pI := PP.id hsz
  obtain ⟨hn, hw, ht0, -⟩ := PF.canon_facts ht.1
  apply Bool.eq_iff_iff.2
  rw [Nat.beq_eq, Nat.beq_eq]
  constructor
  · intro h
    rw [h]
  · intro h
    refine PF.eq_of_fields (by omega) ht0 (PF.pidn_shr hn hw) fun i hi => ?_
    rw [PF.pg_pidn hn hw hi, pg_mAp47 ht ha hi, h]
    unfold mAp47
    rw [xs47_congr (g' := fun j => 2 ^ j) i 6 fun j hj => ?_, xs47_id hi]
    rw [mC47_mOf47 pI j hj, PF.pg_pidn hn hw (Nat.pow_lt_pow_right (by omega) hj)]

@[expose] noncomputable def ord3M47 (M : Nat) : Bool :=
  CFSG.KLie.CT.andB (cubeM47 M) (CFSG.KLie.CT.notB (Nat.beq M (mOf47 (pidn 64 7))))

theorem ord3F47_mat {t : Nat} (ht : PP 64 7 t) (ha : addK t = true) :
    ord3F47 t = ord3M47 (mOf47 t) := by
  unfold ord3F47 ord3M47
  rw [cube_basis47 ht ha, beq_pidn_mat ht ha]

@[expose] noncomputable def mExp47 (M : Nat) : Nat := pmkT 64 7 (fun x => mAp47 M x) 6 0

theorem mExp47_mOf47 {t : Nat} (ht : PP 64 7 t) (ha : addK t = true) : mExp47 (mOf47 t) = t := by
  obtain ⟨hn, hw, ht0, -⟩ := PF.canon_facts ht.1
  have hf : ∀ x < 64, mAp47 (mOf47 t) x < 2 ^ 7 := fun x hx => by
    rw [← pg_mAp47 ht ha hx]
    exact Nat.lt_trans (pg_lt64K ht hx) (by omega)
  have hF := PF.fld_pmkT 64 7 (fun x => mAp47 (mOf47 t) x) hf 6 0
  have hg : ∀ i < 64, (if i < 2 ^ 6 then (if 0 + i < 64 then mAp47 (mOf47 t) (0 + i) else 0)
      else 0) = pg 7 (mask 7) t i := fun i hi => by
    have h1 : i < 2 ^ 6 := hi
    simp only [h1, Nat.zero_add, hi, ↓reduceIte]
    exact (pg_mAp47 ht ha hi).symm
  unfold mExp47
  refine PF.eq_of_fields (n := 64) (by omega) (PF.shr_zero_of_fld (by omega) hF fun i hi => ?_) ht0
    fun i hi => ?_
  · have h1 : ¬ i < 2 ^ 6 := by omega
    simp only [h1, ↓reduceIte]
  · rw [PF.pg_of_fld hF (by rw [hg i hi]; exact PF.pg_lt _ _ _), hg i hi]

@[expose] noncomputable def imgMM47 (M : Nat) (A : Array Nat) : Nat :=
  A.toList.foldr (fun a acc => Nat.lor acc (Nat.shiftLeft 1 (mAp47 M a))) 0

theorem imgM47_mat {t : Nat} (ht : PP 64 7 t) (ha : addK t = true) {A : Array Nat}
    (hA : ∀ a ∈ A.toList, a < 64) : imgM47 t A = imgMM47 (mOf47 t) A := by
  unfold imgM47 imgMM47
  suffices h : ∀ L : List Nat, (∀ a ∈ L, a < 64) →
      L.foldr (fun a acc => Nat.lor acc (Nat.shiftLeft 1 (pg 7 (mask 7) t a))) 0 =
        L.foldr (fun a acc => Nat.lor acc (Nat.shiftLeft 1 (mAp47 (mOf47 t) a))) 0 from h _ hA
  intro L
  induction L with
  | nil => intro _; rfl
  | cons a L ih =>
    intro hL
    rw [List.foldr_cons, List.foldr_cons, ih fun b hb => hL b (List.mem_cons_of_mem a hb),
      pg_mAp47 ht ha (hL a List.mem_cons_self)]

@[expose] noncomputable def okM47 (LM : List Nat) (cs : List Cls) (M i1 i2 : Nat) : Bool :=
  CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (LM.any fun m => subK47 i1 m) (LM.any fun m => subK47 i2 m))
    (CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (ord3M47 M)) (cs.all fun c => clsC c (mExp47 M)))

@[expose] noncomputable def oStepM47 (m1 m2 : Nat) (W1 W2 : Array Nat) (LM : List Nat) (cs : List Cls)
    (M st : Nat) : Nat :=
  strictN M fun M => strictN (imgMM47 M W1) fun i1 => strictN (imgMM47 M W2) fun i2 =>
    Nat.add st (Nat.add (bn (subK47 i1 m1)) (Nat.add (Nat.mul 65536 (bn (subK47 i2 m2)))
      (Nat.add (Nat.mul 4294967296 (bn (CFSG.KLie.CT.orB
          (CFSG.KLie.CT.andB (subK47 i1 m1) (subK47 i2 m2)) (CFSG.KLie.CT.andB (subK47 i1 m2) (subK47 i2 m1)))))
        (Nat.mul 281474976710656 (bn (CFSG.KLie.CT.notB (okM47 LM cs M i1 i2)))))))

theorem oStepF_mat {m1 m2 : Nat} {W1 W2 : Array Nat} (h1 : ∀ a ∈ W1.toList, a < 64)
    (h2 : ∀ a ∈ W2.toList, a < 64) (LM : List Nat) (cs : List Cls) {t : Nat} (st : Nat)
    (ht : PP 64 7 t) (ha : addK t = true) :
    oStepF m1 m2 W1 W2 LM cs t st = oStepM47 m1 m2 W1 W2 LM cs (mOf47 t) st := by
  have hs : ∀ y (c : Nat → Nat), strictN y c = c y := fun y c => by cases y <;> rfl
  have ho : okF47 LM cs t = okM47 LM cs (mOf47 t) := by
    funext i1 i2
    unfold okF47 okM47
    rw [ord3F47_mat ht ha, mExp47_mOf47 ht ha]
  unfold oStepF oStepM47
  rw [hs, hs, hs, hs, hs, hs, imgM47_mat ht ha h1, imgM47_mat ht ha h2, ho]

@[expose] noncomputable def mFold47 (SZ : Nat → Nat) (TM : Nat → Nat → Nat) (F : Nat → Nat → Nat) :
    Nat → Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ p st => F p st)
    (fun _ ih k p st => foldN (SZ k) (fun j st' => strictN (mMul47 p (TM k j)) fun q =>
      ih (Nat.succ k) q st') st)

theorem foldr_congr_mem47 {f g : Nat → Nat → Nat} : ∀ {L : List Nat}, (∀ j ∈ L, ∀ s, f j s = g j s) →
    ∀ s, L.foldr f s = L.foldr g s
  | [], _, _ => rfl
  | j :: L, h, s => by
    rw [List.foldr_cons, List.foldr_cons, foldr_congr_mem47 (fun i hi => h i (List.mem_cons_of_mem j hi)),
      h j List.mem_cons_self]

theorem oFold_mFold47 {SZ : Nat → Nat} {TR TM : Nat → Nat → Nat} {F F' : Nat → Nat → Nat}
    (hT : ∀ k < 6, ∀ j < SZ k, PP 64 7 (TR k j) ∧ addK (TR k j) = true)
    (hM : ∀ k < 6, ∀ j < SZ k, TM k j = mOf47 (TR k j))
    (hF : ∀ p st, PP 64 7 p → addK p = true → F p st = F' (mOf47 p) st) :
    ∀ r k p st, k + r ≤ 6 → PP 64 7 p → addK p = true →
      oFold SZ TR F r k p st = mFold47 SZ TM F' r k (mOf47 p) st
  | 0, _, p, st, _, hp, ap => hF p st hp ap
  | r + 1, k, p, st, hk, hp, ap => by
    have hs : ∀ y (c : Nat → Nat), strictN y c = c y := fun y c => by cases y <;> rfl
    change foldN (SZ k) (fun j st' => strictN (HexaK.mul 64 7 p (TR k j)) fun q =>
        oFold SZ TR F r (k + 1) q st') st =
      foldN (SZ k) (fun j st' => strictN (mMul47 (mOf47 p) (TM k j)) fun q =>
        mFold47 SZ TM F' r (k + 1) q st') st
    rw [CFSG.KC.Pack.foldN_eq, CFSG.KC.Pack.foldN_eq]
    refine foldr_congr_mem47 (fun j hj s => ?_) st
    have hj' := List.mem_range.1 hj
    obtain ⟨pj, aj⟩ := hT k (by omega) j hj'
    rw [hs, hs, hM k (by omega) j hj', ← mOf47_mul hp ap pj]
    exact oFold_mFold47 hT hM hF r (k + 1) _ s (by omega) (hp.mul pj) (addK_mul47 hp ap pj aj)

theorem oBlockF_mat {SZ : Nat → Nat} {TR TM : Nat → Nat → Nat} {m1 m2 : Nat} {W1 W2 : Array Nat}
    (h1 : ∀ a ∈ W1.toList, a < 64) (h2 : ∀ a ∈ W2.toList, a < 64) (LM : List Nat) (cs : List Cls)
    (hT : ∀ k < 6, ∀ j < SZ k, PP 64 7 (TR k j) ∧ addK (TR k j) = true)
    (hM : ∀ k < 6, ∀ j < SZ k, TM k j = mOf47 (TR k j)) {s : Nat} (hs : s < SZ 0) :
    oBlockF SZ TR m1 m2 W1 W2 LM cs s =
      mFold47 SZ TM (oStepM47 m1 m2 W1 W2 LM cs) 5 1 (TM 0 s) 0 := by
  unfold oBlockF
  rw [hM 0 (by omega) s hs]
  exact oFold_mFold47 hT hM (fun p st hp ap => oStepF_mat h1 h2 LM cs st hp ap) 5 1 _ 0 (by omega)
    (hT 0 (by omega) s hs).1 (hT 0 (by omega) s hs).2

end CFSG.KC.Q47K

end
