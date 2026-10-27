module

public import CFSG.Certificates.Kernel.O8S0Proved
public import Certificates.Data.Kernel.O8.T0

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KC.F4M CFSG.EvenSmallLie.OmegaEight.Chain

@[expose] noncomputable def dec4M (A : Nat) : Array (Array ℕ) :=
  Array.ofFn (n := 6) fun i => Array.ofFn (n := 6) fun j => ent4 A i.val j.val

@[expose] def encV (v : Array ℕ) : ℕ :=
  CFSG.EvenSmallLie.UnitarySix.YamadaPar.bitsOf 12 fun p =>
    if p < 6 then (v.getD p 0).testBit 0 else (v.getD (p - 6) 0).testBit 1

end CFSG.KC.O8

namespace CFSG.KC.O8.Z4Pf

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M CFSG.KC.O8 CFSG.KC.O8.OrthPf CFSG.KC.O8.WordPf
  CFSG.KC.O8.S0Pf CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight
  CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Chain

theorem getD_ofFn6 {α : Type} (f : Fin 6 → α) (d : α) {i : ℕ} (hi : i < 6) :
    (Array.ofFn f).getD i d = f ⟨i, hi⟩ := by
  simp [Array.getD_eq_getD_getElem?, hi]

theorem m4Get_dec4M (A : ℕ) {i j : ℕ} (hi : i < 6) (hj : j < 6) :
    m4Get (dec4M A) i j = ent4 A i j := by
  unfold m4Get dec4M
  rw [getD_ofFn6 _ _ hi, getD_ofFn6 _ _ hj]

theorem ent4_lt (A i j : ℕ) : ent4 A i j < 4 := fget_lt _ _ 2

theorem ent4_mk (f : ℕ → ℕ → ℕ) {i j : ℕ} (hi : i < 6) (hj : j < 6) :
    ent4 (mk f) i j = f i j % 4 := by
  change fget (orN 36 fun t => Nat.shiftLeft (Nat.land (f (t / 6) (t % 6)) 3) (Nat.mul 2 t))
    (6 * i + j) 2 = _
  rw [fget_orN (fun t _ => by
      change Nat.land _ 3 < 4
      exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)) (by omega)]
  rw [show (6 * i + j) / 6 = i by omega, show (6 * i + j) % 6 = j by omega]
  exact Nat.and_two_pow_sub_one_eq_mod _ 2

theorem sumN_eq (n : ℕ) (f : ℕ → ℕ) : sumN n f = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change f n + sumN n f = _
    rw [ih, Finset.sum_range_succ, Nat.add_comm]

theorem ofFn66_congr {f g : Fin 6 → Fin 6 → ℕ} (h : ∀ i j, f i j = g i j) :
    (Array.ofFn fun i => Array.ofFn fun j => f i j) = Array.ofFn fun i => Array.ofFn fun j => g i j := by
  have : f = g := funext fun i => funext fun j => h i j
  rw [this]

theorem dec4M_mul4K (A B : ℕ) : dec4M (mul4K A B) = mul4 (dec4M A) (dec4M B) := by
  unfold mul4
  conv_lhs => unfold dec4M
  apply ofFn66_congr
  intro i j
  change ent4 (strictN A fun A => strictN B fun B =>
    mk fun i j => sumN 6 fun k => Nat.mul (ent4 A i k) (ent4 B k j)) i j = _
  rw [strictN_eq, strictN_eq, ent4_mk _ i.2 j.2, sumN_eq, ← Fin.sum_univ_eq_sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [m4Get_dec4M A i.2 k.2, m4Get_dec4M B k.2 j.2]
  rfl

theorem dec4M_add4K (A B : ℕ) : dec4M (add4K A B) = add4 (dec4M A) (dec4M B) := by
  unfold add4
  conv_lhs => unfold dec4M
  apply ofFn66_congr
  intro i j
  change ent4 (strictN A fun A => strictN B fun B => mk fun i j => Nat.add (ent4 A i j) (ent4 B i j))
    i j = _
  rw [strictN_eq, strictN_eq, ent4_mk _ i.2 j.2, m4Get_dec4M A i.2 j.2, m4Get_dec4M B i.2 j.2]
  rfl

theorem dec4M_lift2K (M : ℕ) : dec4M (lift2K M) = lift2 (decR M) := by
  unfold lift2
  conv_lhs => unfold dec4M
  apply ofFn66_congr
  intro i j
  change ent4 (strictN M fun M => mk fun i j => bitN (frow M i) j) i j = _
  rw [strictN_eq, ent4_mk _ i.2 j.2, decR_getD M i.2, bitN_eq]
  cases (frow M i).testBit j <;> rfl

theorem dec4M_ONE : dec4M ONE = one4 := by decide +kernel

theorem prod4K_eq {GP CP : ℕ} {G C : ℕ → Array ℕ} (hG : ∀ s < 6, G s = decR (mat GP s))
    (hC : ∀ s < 6, C s = decR (mat CP s)) :
    ∀ (w : List ℕ), (∀ s ∈ w, s < 6) → dec4M (prod4K GP CP w) = prod4G G C w
  | [], _ => dec4M_ONE
  | s :: w, hw => by
    change dec4M (mul4K (ptilK GP CP s) (prod4K GP CP w)) = mul4 (ptil4G G C s) (prod4G G C w)
    have hs := hw s (by simp)
    rw [dec4M_mul4K, prod4K_eq hG hC w (fun t ht => hw t (by simp [ht]))]
    congr 1
    change dec4M (add4K (lift2K (mat GP s)) (add4K (lift2K (mat CP s)) (lift2K (mat CP s)))) =
      add4 (lift2 (G s)) (add4 (lift2 (C s)) (lift2 (C s)))
    rw [dec4M_add4K, dec4M_add4K, dec4M_lift2K, dec4M_lift2K, hG s hs, hC s hs]

@[expose] def SlOK (A : Array (Array ℕ)) (X : ℕ) : Prop :=
  ∀ i < 6, ∀ k < 6, ∀ b < 2, X.testBit (12 * i + 6 * b + k) = (m4Get A i k).testBit b

theorem orN6_lt {f : ℕ → ℕ} (hf : ∀ k < 6, f k < 2) :
    (orN 6 fun k => Nat.shiftLeft (f k) k) < 64 := by
  have : (orN 6 fun k => Nat.shiftLeft (f k) k) < 2 ^ 6 := by
    apply Nat.lt_pow_two_of_testBit
    intro p hp
    rw [Bool.eq_false_iff]
    intro h
    obtain ⟨k, hk, h⟩ := (testBit_orN_iff _ p 6).1 h
    change (f k <<< k).testBit p = true at h
    rw [Nat.testBit_shiftLeft, Bool.and_eq_true] at h
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hf k hk)
      (by simpa using Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : 1 ≤ p - k)))] at h
    exact absurd h.2 (by decide)
  simpa using this

theorem testBit_orN6 {f : ℕ → ℕ} (hf : ∀ k < 6, f k < 2) {k : ℕ} (hk : k < 6) :
    (orN 6 fun k => Nat.shiftLeft (f k) k).testBit k = (f k).testBit 0 := by
  have := testBit_orN_shl (w := 1) (n := 6) (g := f) (fun k hk => hf k hk) hk (p := 0) (by omega)
  simpa using this

theorem bitN_lt2 (x i : ℕ) : bitN x i < 2 := by
  rw [bitN_eq]
  cases x.testBit i <;> decide

theorem sliceK_testBit (A : ℕ) {i k b : ℕ} (hi : i < 6) (hk : k < 6) (hb : b < 2) :
    (sliceK A).testBit (12 * i + 6 * b + k) = (ent4 A i k).testBit b := by
  change (strictN A fun A => orN 6 fun i => Nat.shiftLeft
    (Nat.add (orN 6 fun k => Nat.shiftLeft (bitN (ent4 A i k) 0) k)
      (Nat.shiftLeft (orN 6 fun k => Nat.shiftLeft (bitN (ent4 A i k) 1) k) 6))
    (Nat.mul 12 i)).testBit _ = _
  rw [strictN_eq]
  have hlo : ∀ i, (orN 6 fun k => Nat.shiftLeft (bitN (ent4 A i k) 0) k) < 64 :=
    fun i => orN6_lt (fun k _ => bitN_lt2 _ _)
  have hhi : ∀ i, (orN 6 fun k => Nat.shiftLeft (bitN (ent4 A i k) 1) k) < 64 :=
    fun i => orN6_lt (fun k _ => bitN_lt2 _ _)
  have hrow : ∀ i, Nat.add (orN 6 fun k => Nat.shiftLeft (bitN (ent4 A i k) 0) k)
      (Nat.shiftLeft (orN 6 fun k => Nat.shiftLeft (bitN (ent4 A i k) 1) k) 6) < 2 ^ 12 := by
    intro i
    change _ + _ <<< 6 < _
    rw [Nat.shiftLeft_eq]
    have := hlo i
    have := hhi i
    omega
  rw [Nat.add_assoc, testBit_orN_shl (w := 12) (fun i _ => hrow i) hi (by omega)]
  have e : ∀ x y : ℕ, Nat.add x (Nat.shiftLeft y 6) = 2 ^ 6 * y + x := by
    intro x y
    change x + y <<< 6 = _
    rw [Nat.shiftLeft_eq]
    ring
  rw [e, Nat.testBit_two_pow_mul_add _ (hlo i)]
  have hb' : ∀ x, (bitN x b).testBit 0 = x.testBit b := fun x => by
    rw [bitN_eq]
    cases x.testBit b <;> rfl
  interval_cases b
  · rw [if_pos (by omega), show 6 * 0 + k = k by omega, testBit_orN6 (fun k _ => bitN_lt2 _ _) hk, hb']
  · rw [if_neg (by omega), show 6 * 1 + k - 6 = k by omega, testBit_orN6 (fun k _ => bitN_lt2 _ _) hk,
      hb']

theorem slOK_slice (A : ℕ) : SlOK (dec4M A) (sliceK A) := fun i hi k hk b hb => by
  rw [sliceK_testBit A hi hk hb, m4Get_dec4M A hi hk]

theorem testBit_encV (v : Array ℕ) (p : ℕ) : (encV v).testBit p =
    (decide (p < 12) && if p < 6 then (v.getD p 0).testBit 0 else (v.getD (p - 6) 0).testBit 1) := by
  rw [encV, testBit_bitsOf]

theorem encV_lt (v : Array ℕ) : encV v < 4096 := by
  have : encV v < 2 ^ 12 := by
    apply Nat.lt_pow_two_of_testBit
    intro p hp
    rw [testBit_encV, decide_eq_false (by omega), Bool.false_and]
  simpa using this

theorem tb (x i : ℕ) : x.testBit i = decide (x / 2 ^ i % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq

theorem digit_eq {x y : ℕ} (hx : x < 4) (hy : y < 4) (h0 : x.testBit 0 = y.testBit 0)
    (h1 : x.testBit 1 = y.testBit 1) : x = y := by
  rw [tb, tb] at h0 h1
  simp only [pow_zero, Nat.div_one, pow_one, decide_eq_decide] at h0 h1
  omega

theorem encV_inj {v w : Array ℕ} (hv : v.size = 6) (hw : w.size = 6) (hv4 : ∀ k < 6, v.getD k 0 < 4)
    (hw4 : ∀ k < 6, w.getD k 0 < 4) (h : encV v = encV w) : v = w := by
  apply Array.ext (by rw [hv, hw])
  intro k h1 h2
  have hk : k < 6 := by omega
  have e : ∀ u : Array ℕ, (hu : k < u.size) → u[k]'hu = u.getD k 0 := fun u hu => by
    simp [Array.getD_eq_getD_getElem?, hu]
  rw [e v h1, e w h2]
  apply digit_eq (hv4 k hk) (hw4 k hk)
  · have := congrArg (fun x => Nat.testBit x k) h
    simpa [testBit_encV, hk, show k < 12 by omega] using this
  · have := congrArg (fun x => Nat.testBit x (k + 6)) h
    simpa [testBit_encV, hk, show k + 6 < 12 by omega] using this

theorem testBit_land63 (x k : ℕ) : (Nat.land x 63).testBit k = (decide (k < 6) && x.testBit k) := by
  rw [testBit_land, show (63 : ℕ) = 2 ^ 6 - 1 by norm_num, Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem testBit_shr6 (x k : ℕ) : (Nat.shiftRight x 6).testBit k = x.testBit (6 + k) := by
  change (x >>> 6).testBit k = _
  rw [Nat.testBit_shiftRight]

theorem toNat_testBit_lt (x : ℕ) : (Nat.land x 1) < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem testBit_orN_pair {a b : ℕ → ℕ} (ha : ∀ i < 6, a i < 2) (hb : ∀ i < 6, b i < 2) (p : ℕ) :
    (orN 6 fun i => Nat.lor (Nat.shiftLeft (a i) i) (Nat.shiftLeft (b i) (Nat.add 6 i))).testBit p =
      (decide (p < 12) && if p < 6 then (a p).testBit 0 else (b (p - 6)).testBit 0) := by
  have h2 : ∀ x : ℕ, x < 2 → ∀ q, x.testBit q = (decide (q = 0) && x.testBit 0) := by
    intro x hx q
    rcases q with _ | q
    · simp
    · have h4 : 2 ^ 1 ≤ 2 ^ (q + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (by simpa using h4))]
      simp
  rw [Bool.eq_iff_iff, testBit_orN_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    change (a i <<< i ||| b i <<< (6 + i)).testBit p = true at h
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Bool.or_eq_true,
      Bool.and_eq_true, Bool.and_eq_true, h2 _ (ha i hi), h2 _ (hb i hi)] at h
    simp only [decide_eq_true_eq, Bool.and_eq_true] at h
    rcases h with ⟨h1, h3, h4⟩ | ⟨h1, h3, h4⟩
    · have : p = i := by omega
      subst this
      simp [show p < 12 by omega, hi, h4]
    · have : p = 6 + i := by omega
      subst this
      simp [show 6 + i < 12 by omega, show ¬ 6 + i < 6 by omega, h4]
  · intro h
    rw [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hp, h⟩ := h
    by_cases hp6 : p < 6
    · rw [if_pos hp6] at h
      refine ⟨p, hp6, ?_⟩
      change (a p <<< p ||| b p <<< (6 + p)).testBit p = true
      rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.sub_self, h]
      simp
    · rw [if_neg hp6] at h
      refine ⟨p - 6, by omega, ?_⟩
      change (a (p - 6) <<< (p - 6) ||| b (p - 6) <<< (6 + (p - 6))).testBit p = true
      rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
        show p - (6 + (p - 6)) = 0 by omega, h]
      simp [show 6 + (p - 6) ≤ p by omega]

theorem popc6_eq (x : ℕ) : popc 6 x = ∑ k ∈ Finset.range 6, (x.testBit k).toNat := by
  rw [show popc 6 x = sumN 6 fun i => bitN x i from rfl, sumN_eq]
  exact Finset.sum_congr rfl fun k _ => bitN_eq x k

theorem POPT_get : ∀ x < 64, fget POPT x 3 = popc 6 x := by decide +kernel

theorem toNat_and (a b : Bool) : (a && b).toNat = a.toNat * b.toNat := by
  cases a <;> cases b <;> rfl

theorem toNat_testBit0 (x : ℕ) : (x.testBit 0).toNat = x % 2 := by
  rw [tb]
  simp only [pow_zero, Nat.div_one]
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]

theorem toNat_testBit1 (x : ℕ) : (x.testBit 1).toNat = x / 2 % 2 := by
  rw [tb]
  simp only [pow_one]
  rcases Nat.mod_two_eq_zero_or_one (x / 2) with h | h <;> simp [h]

theorem sum_mod4 (a v : ℕ → ℕ) :
    let c := ∑ k ∈ Finset.range 6, a k % 2 * (v k % 2)
    let d := ∑ k ∈ Finset.range 6, (a k / 2 % 2 * (v k % 2) + a k % 2 * (v k / 2 % 2))
    let z := ∑ k ∈ Finset.range 6, a k / 2 % 2 * (v k / 2 % 2)
    (∀ k < 6, a k < 4) → (∀ k < 6, v k < 4) →
      ∑ k ∈ Finset.range 6, a k * v k = c + 2 * d + 4 * z := by
  intro c d z ha hv
  simp only [c, d, z, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.1 hk
  have e1 : a k = a k % 2 + 2 * (a k / 2 % 2) := by have := ha k hk'; omega
  have e2 : v k = v k % 2 + 2 * (v k / 2 % 2) := by have := hv k hk'; omega
  conv_lhs => rw [e1, e2]
  ring

theorem xor_toNat_mod (a b : ℕ) : (Nat.xor a b).testBit 0 = decide ((a + b) % 2 = 1) := by
  rw [testBit_nxor, tb, tb]
  simp only [pow_zero, Nat.div_one]
  rcases Nat.mod_two_eq_zero_or_one a with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one b with h' | h' <;> simp [h, h', Nat.add_mod]

theorem bitN1_t0 (x : ℕ) : (bitN x 1).testBit 0 = decide (x / 2 % 2 = 1) := by
  rw [bitN_eq, tb (x := x), pow_one]
  cases decide (x / 2 % 2 = 1) <;> rfl

theorem xor_mod2 (a b : ℕ) : Nat.xor a b % 2 = (a + b) % 2 := by
  have h := xor_toNat_mod a b
  rw [tb] at h
  simp only [pow_zero, Nat.div_one, decide_eq_decide] at h
  omega

theorem land1_testBit0 (x : ℕ) : (Nat.land x 1).testBit 0 = decide (x % 2 = 1) := by
  rw [testBit_land, tb, tb]
  simp

theorem pc_land (P x y : ℕ) (hP : P = POPT) (hx : x < 64) :
    pc6 P (Nat.land x y) = ∑ k ∈ Finset.range 6, (x.testBit k && y.testBit k).toNat := by
  subst hP
  have hl : Nat.land x y < 64 := Nat.lt_of_le_of_lt Nat.and_le_left hx
  rw [pc6, POPT_get _ hl, popc6_eq]
  exact Finset.sum_congr rfl fun k _ => by rw [testBit_land]

theorem mvB_eq {A : Array (Array ℕ)} {X : ℕ} (hA : SlOK A X) (hA4 : ∀ i < 6, ∀ k < 6, m4Get A i k < 4)
    {v : Array ℕ} (hv : ∀ k < 6, v.getD k 0 < 4) : mvB POPT X (encV v) = encV (mv4 A v) := by
  apply Nat.eq_of_testBit_eq
  intro p
  have hlo : ∀ i < 6, fget X (Nat.mul 2 i) 6 < 64 := fun i _ => fget_lt _ _ 6
  have hhi : ∀ i < 6, fget X (Nat.succ (Nat.mul 2 i)) 6 < 64 := fun i _ => fget_lt _ _ 6
  have bl : ∀ i < 6, ∀ k < 6, (fget X (Nat.mul 2 i) 6).testBit k = (m4Get A i k).testBit 0 := by
    intro i hi k hk
    rw [testBit_fget, decide_eq_true hk, Bool.true_and, ← hA i hi k hk 0 (by norm_num)]
    congr 1
    change 2 * i * 6 + k = _
    ring
  have bh : ∀ i < 6, ∀ k < 6, (fget X (Nat.succ (Nat.mul 2 i)) 6).testBit k =
      (m4Get A i k).testBit 1 := by
    intro i hi k hk
    rw [testBit_fget, decide_eq_true hk, Bool.true_and, ← hA i hi k hk 1 (by norm_num)]
    congr 1
    change (2 * i + 1) * 6 + k = _
    ring
  have b0 : ∀ k < 6, (Nat.land (encV v) 63).testBit k = (v.getD k 0).testBit 0 := by
    intro k hk
    rw [testBit_land63, testBit_encV]
    simp [hk, show k < 12 by omega]
  have b1 : ∀ k < 6, (Nat.shiftRight (encV v) 6).testBit k = (v.getD k 0).testBit 1 := by
    intro k hk
    rw [testBit_shr6, testBit_encV]
    simp [show 6 + k < 12 by omega, show ¬ 6 + k < 6 by omega]
  have sc : ∀ i < 6, pc6 POPT (Nat.land (fget X (Nat.mul 2 i) 6) (Nat.land (encV v) 63)) =
      ∑ k ∈ Finset.range 6, m4Get A i k % 2 * (v.getD k 0 % 2) := by
    intro i hi
    rw [pc_land _ _ _ rfl (hlo i hi)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    rw [bl i hi k hk', b0 k hk', toNat_and, toNat_testBit0, toNat_testBit0]
  have sh : ∀ i < 6, pc6 POPT (Nat.land (fget X (Nat.succ (Nat.mul 2 i)) 6) (Nat.land (encV v) 63)) =
      ∑ k ∈ Finset.range 6, m4Get A i k / 2 % 2 * (v.getD k 0 % 2) := by
    intro i hi
    rw [pc_land _ _ _ rfl (hhi i hi)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    rw [bh i hi k hk', b0 k hk', toNat_and, toNat_testBit1, toNat_testBit0]
  have sl : ∀ i < 6, pc6 POPT (Nat.land (fget X (Nat.mul 2 i) 6) (Nat.shiftRight (encV v) 6)) =
      ∑ k ∈ Finset.range 6, m4Get A i k % 2 * (v.getD k 0 / 2 % 2) := by
    intro i hi
    rw [pc_land _ _ _ rfl (hlo i hi)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    rw [bl i hi k hk', b1 k hk', toNat_and, toNat_testBit0, toNat_testBit1]
  have hmv : ∀ i < 6, (mv4 A v).getD i 0 =
      (∑ k ∈ Finset.range 6, m4Get A i k * v.getD k 0) % 4 := by
    intro i hi
    unfold mv4
    rw [getD_ofFn6 _ _ hi]
    congr 1
  have hb2 : ∀ i < 6, Nat.xor (bitN (pc6 POPT (Nat.land (fget X (Nat.mul 2 i) 6) (Nat.land (encV v) 63))) 1)
      (Nat.land (Nat.xor (pc6 POPT (Nat.land (fget X (Nat.succ (Nat.mul 2 i)) 6) (Nat.land (encV v) 63)))
        (pc6 POPT (Nat.land (fget X (Nat.mul 2 i) 6) (Nat.shiftRight (encV v) 6)))) 1) < 2 := by
    intro i _
    exact Nat.xor_lt_two_pow (n := 1) (bitN_lt2 _ _) (toNat_testBit_lt _)
  unfold mvB
  beta_reduce
  rw [testBit_orN_pair (fun i _ => toNat_testBit_lt _) hb2, testBit_encV]
  by_cases hp : p < 12
  · rw [decide_eq_true hp, Bool.true_and, Bool.true_and]
    have key := fun i (hi : i < 6) => sum_mod4 (fun k => m4Get A i k) (fun k => v.getD k 0)
      (fun k hk => hA4 i hi k hk) (fun k hk => hv k hk)
    by_cases hp6 : p < 6
    · rw [if_pos hp6, if_pos hp6, sc p hp6, land1_testBit0, hmv p hp6, key p hp6, tb]
      simp only [pow_zero, Nat.div_one, decide_eq_decide]
      omega
    · have hi : p - 6 < 6 := by omega
      rw [if_neg hp6, if_neg hp6, sc _ hi, sh _ hi, sl _ hi, testBit_nxor, land1_testBit0,
        hmv _ hi, key _ hi, Finset.sum_add_distrib, bitN1_t0, xor_mod2, tb, pow_one]
      generalize (∑ k ∈ Finset.range 6, m4Get A (p - 6) k % 2 * (v.getD k 0 % 2)) = c
      generalize (∑ k ∈ Finset.range 6, m4Get A (p - 6) k / 2 % 2 * (v.getD k 0 % 2)) = x
      generalize (∑ k ∈ Finset.range 6, m4Get A (p - 6) k % 2 * (v.getD k 0 / 2 % 2)) = y
      generalize (∑ k ∈ Finset.range 6, m4Get A (p - 6) k / 2 % 2 * (v.getD k 0 / 2 % 2)) = z
      have e : (c + 2 * (x + y) + 4 * z) % 4 / 2 % 2 = (c / 2 % 2 + (x + y) % 2) % 2 := by omega
      rw [e]
      rcases Nat.mod_two_eq_zero_or_one (c / 2) with h1 | h1 <;>
        rcases Nat.mod_two_eq_zero_or_one (x + y) with h2 | h2 <;> rw [h1, h2] <;> rfl
  · rw [decide_eq_false hp, Bool.false_and, Bool.false_and]

end CFSG.KC.O8.Z4Pf

end
