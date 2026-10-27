module

public import Certificates.Data.Kernel.SporSch.HNF5Kron
public import CFSG.Certificates.Kernel.SporSch.HNF5Sound
public import CFSG.Certificates.Kernel.SporSch.HNF5Lane
import CFSG.Certificates.Kernel.PackSetSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.SporSch.F5Kron

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.KS.SporSch.F5Lane Finset

attribute [local irreducible] krConst

set_option exponentiation.threshold 2200

theorem lane5_land (a b t : Nat) : lane5 (Nat.land a b) t = Nat.land (lane5 a t) (lane5 b t) := by
  unfold lane5
  change (a &&& b) >>> (16 * t) &&& 65535 = ((a >>> (16 * t)) &&& 65535) &&& ((b >>> (16 * t)) &&& 65535)
  apply Nat.eq_of_testBit_eq
  intro r
  simp only [Nat.testBit_land, Nat.testBit_shiftRight]
  cases a.testBit (16 * t + r) <;> cases b.testBit (16 * t + r) <;> cases (65535 : Nat).testBit r <;> rfl

theorem land_zero' (a : Nat) : Nat.land a 0 = 0 := Nat.and_zero a

theorem land_le (a b : Nat) : Nat.land a b ≤ b := Nat.and_le_right

theorem land_low {v : Nat} (hv : v < 2 ^ 16) : Nat.land v 65535 = v := by
  change v &&& (2 ^ 16 - 1) = v
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hv]

theorem sum_fiber {ι : Type*} (I : Finset ι) (v p : ι → Nat) (n : Nat) (hp : ∀ i ∈ I, p i < n) :
    ∑ i ∈ I, v i * 2 ^ (16 * p i) =
      ∑ t ∈ range n, (∑ i ∈ I with p i = t, v i) * 2 ^ (16 * t) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := p) (t := range n) fun i hi => mem_range.2 (hp i hi)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.1 hi).2]

theorem lane_fiber {ι : Type*} (I : Finset ι) (v p : ι → Nat) (n : Nat) (hp : ∀ i ∈ I, p i < n)
    (hb : ∀ t < n, ∑ i ∈ I with p i = t, v i < 2 ^ 16) {t : Nat} (ht : t < n) :
    lane5 (∑ i ∈ I, v i * 2 ^ (16 * p i)) t = ∑ i ∈ I with p i = t, v i := by
  rw [sum_fiber I v p n hp, lane5_eq]
  exact lane_sum _ n hb t ht

theorem lt_fiber {ι : Type*} (I : Finset ι) (v p : ι → Nat) (n : Nat) (hp : ∀ i ∈ I, p i < n)
    (hb : ∀ t < n, ∑ i ∈ I with p i = t, v i < 2 ^ 16) :
    ∑ i ∈ I, v i * 2 ^ (16 * p i) < 2 ^ (16 * n) := by
  rw [sum_fiber I v p n hp]
  exact sum_lt _ n hb

theorem lane_high {x n t : Nat} (hx : x < 2 ^ (16 * n)) (ht : n ≤ t) : lane5 x t = 0 := by
  rw [lane5_eq, Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num)
    (by omega))), Nat.zero_mod]

theorem eq_of_lanes_n {x y n : Nat} (hx : x < 2 ^ (16 * n)) (hy : y < 2 ^ (16 * n))
    (h : ∀ t < n, lane5 x t = lane5 y t) : x = y := by
  rw [← Nat.mod_eq_of_lt hx, ← Nat.mod_eq_of_lt hy, mod_expand x n, mod_expand y n]
  exact Finset.sum_congr rfl fun t ht => by rw [h t (mem_range.1 ht)]

theorem expand_n {x n : Nat} (hx : x < 2 ^ (16 * n)) :
    x = ∑ t ∈ range n, lane5 x t * 2 ^ (16 * t) := by
  rw [← mod_expand x n, Nat.mod_eq_of_lt hx]

theorem lane5_shr (x m t : Nat) : lane5 (Nat.shiftRight x (16 * m)) t = lane5 x (t + m) := by
  rw [lane5_eq, lane5_eq]
  change x >>> (16 * m) / _ % _ = _
  rw [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 3
  ring

theorem fiber_le {ι : Type*} (I : Finset ι) (v : ι → Nat) (P : ι → Prop) {_ : DecidablePred P}
    {w c : Nat} (hv : ∀ i ∈ I, v i ≤ w) (hc : (I.filter P).card ≤ c) :
    ∑ i ∈ I with P i, v i ≤ c * w :=
  calc ∑ i ∈ I with P i, v i ≤ (I.filter P).card • w :=
        Finset.sum_le_card_nsmul _ _ _ fun i hi => hv i (Finset.mem_filter.1 hi).1
    _ ≤ c * w := by rw [smul_eq_mul]; exact Nat.mul_le_mul_right _ hc

theorem fib1 {ι : Type*} (I : Finset ι) (v : ι → Nat) (P : ι → Prop) {_ : DecidablePred P}
    {w : Nat} (hv : ∀ i ∈ I, v i ≤ w) (hw : w < 2 ^ 16) (hc : (I.filter P).card ≤ 1) :
    ∑ i ∈ I with P i, v i < 2 ^ 16 := by
  have := fiber_le I v P hv hc
  omega

theorem krConst_eq (v s : Nat) : krConst v s = ∑ d ∈ range 133, v * 2 ^ (16 * (s * d)) := by
  unfold krConst
  rw [CFSG.KC.Pack.foldN_eq, foldr_range_add (fun d => v * 2 ^ (16 * (s * d))), Nat.zero_add]
  intro j acc
  change acc + v <<< (16 * s * j) = _
  rw [Nat.shiftLeft_eq, Nat.mul_assoc]

theorem card_le_one_265 {s t : Nat} (hs : 1 ≤ s) :
    ((range 133).filter fun d => s * d = t).card ≤ 1 :=
  Finset.card_le_one.2 fun a ha b hb => by
    simp only [Finset.mem_filter] at ha hb
    have := ha.2.trans hb.2.symm
    exact Nat.eq_of_mul_eq_mul_left hs this

theorem krConst_lt {v s : Nat} (hv : v < 2 ^ 16) (hs : 1 ≤ s) :
    krConst v s < 2 ^ (16 * (s * 133)) := by
  rw [krConst_eq]
  refine lt_fiber _ (fun _ => v) (fun d => s * d) _ (fun d hd => ?_) fun t _ => ?_
  · have := mem_range.1 hd
    nlinarith
  · exact fib1 _ _ _ (fun _ _ => le_rfl) hv (card_le_one_265 hs)

theorem lane_krConst {v s : Nat} (hv : v < 2 ^ 16) (hs : 1 ≤ s) (t : Nat) :
    lane5 (krConst v s) t = if t % s = 0 ∧ t / s < 133 then v else 0 := by
  rcases Nat.lt_or_ge t (s * 133) with ht | ht
  · have hp : ∀ d ∈ range 133, s * d < s * 133 := fun d hd =>
      Nat.mul_lt_mul_of_pos_left (mem_range.1 hd) hs
    rw [krConst_eq, lane_fiber _ (fun _ => v) (fun d => s * d) (s * 133) hp
      (fun t _ => fib1 _ _ _ (fun _ _ => le_rfl) hv (card_le_one_265 hs)) ht]
    split_ifs with h
    · have e : ((range 133).filter fun d => s * d = t) = {t / s} := by
        ext d
        simp only [Finset.mem_filter, mem_range, Finset.mem_singleton]
        constructor
        · rintro ⟨-, rfl⟩
          rw [Nat.mul_div_cancel_left _ hs]
        · rintro rfl
          exact ⟨h.2, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h.1)⟩
      rw [e, Finset.sum_singleton]
    · refine Finset.sum_eq_zero fun d hd => absurd ?_ h
      obtain ⟨hd1, rfl⟩ := Finset.mem_filter.1 hd
      exact ⟨Nat.mul_mod_right _ _, by rw [Nat.mul_div_cancel_left _ hs]; exact mem_range.1 hd1⟩
  · rw [lane_high (krConst_lt hv hs) (by omega), if_neg]
    rintro ⟨h1, h2⟩
    have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h1)
    nlinarith

@[irreducible] def krP2 : Finset (Nat × Nat) := range 133 ×ˢ range 133

theorem mem_krP2 {i : Nat × Nat} : i ∈ krP2 ↔ i.1 < 133 ∧ i.2 < 133 := by
  unfold krP2
  rw [Finset.mem_product, mem_range, mem_range]

theorem krSpr_eq {r : Nat} (hr : canon5 r = true) :
    krSpr (krConst 1 264) (krConst 65535 265) r =
      ∑ c ∈ range 133, lane5 r c * 2 ^ (16 * (265 * c)) := by
  have hl : ∀ c, lane5 r c < 5 := fun c => by
    rcases Nat.lt_or_ge c 133 with hc | hc
    · exact canon5_lane hr hc
    · have h16 : r < 2 ^ (16 * 133) := canon5_lt hr
      rw [lane_high h16 hc]
      norm_num
  have hRS : Nat.mul r (krConst 1 264) = ∑ i ∈ krP2,
      lane5 r i.1 * 2 ^ (16 * (i.1 + 264 * i.2)) := by
    change r * krConst 1 264 = _
    conv_lhs => rw [row_expand (canon5_lt hr), krConst_eq, Finset.sum_mul_sum]
    unfold krP2
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [Nat.mul_add 16, Nat.pow_add]
    ring
  have hpos : ∀ i ∈ krP2, i.1 + 264 * i.2 < 265 * 133 := fun i hi => by
    rw [mem_krP2] at hi
    omega
  have hcard : ∀ t, (krP2.filter fun i => i.1 + 264 * i.2 = t).card ≤ 1 :=
    fun t => Finset.card_le_one.2 fun a ha b hb => by
      rw [Finset.mem_filter, mem_krP2] at ha hb
      ext <;> omega
  have hfb : ∀ t < 265 * 133, ∑ i ∈ krP2 with i.1 + 264 * i.2 = t,
      lane5 r i.1 < 2 ^ 16 := by
    intro t _
    have h1 := fiber_le krP2 (fun i => lane5 r i.1)
      (fun i => i.1 + 264 * i.2 = t) (fun i _ => (hl i.1).le) (hcard t)
    exact Nat.lt_of_le_of_lt h1 (by norm_num)
  have hpos2 : ∀ c ∈ range 133, 265 * c < 265 * 133 := fun c hc => by
    have := mem_range.1 hc
    omega
  have hcard2 : ∀ t, ((range 133).filter fun c => 265 * c = t).card ≤ 1 :=
    fun t => card_le_one_265 (by norm_num)
  have hfb2 : ∀ t < 265 * 133, ∑ c ∈ range 133 with 265 * c = t, lane5 r c < 2 ^ 16 :=
    fun t _ => fib1 _ (fun c => lane5 r c) _ (fun c _ => (hl c).le) (by norm_num) (hcard2 t)
  refine eq_of_lanes_n (n := 265 * 133) ?_ (lt_fiber _ _ (fun c => 265 * c) _ hpos2 hfb2)
    fun t ht => ?_
  · unfold krSpr
    exact Nat.lt_of_le_of_lt (land_le _ _) (krConst_lt (by norm_num) (by norm_num))
  · have A : lane5 (Nat.mul r (krConst 1 264)) t =
        ∑ i ∈ krP2 with i.1 + 264 * i.2 = t, lane5 r i.1 := by
      rw [hRS]
      exact lane_fiber krP2 (fun i => lane5 r i.1) (fun i => i.1 + 264 * i.2) _ hpos hfb ht
    have B := lane_krConst (v := 65535) (s := 265) (by norm_num) (by norm_num) t
    have C : lane5 (∑ c ∈ range 133, lane5 r c * 2 ^ (16 * (265 * c))) t =
        ∑ c ∈ range 133 with 265 * c = t, lane5 r c :=
      lane_fiber _ _ (fun c => 265 * c) _ hpos2 hfb2 ht
    refine (lane5_land _ _ _).trans (Eq.trans ?_ C.symm)
    rw [A, B]
    split_ifs with h
    · obtain ⟨c0, rfl⟩ : ∃ c0, t = 265 * c0 :=
        ⟨t / 265, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h.1)).symm⟩
      have hc0 : c0 < 133 := by omega
      have e1 : (krP2.filter fun i => i.1 + 264 * i.2 = 265 * c0) = {(c0, c0)} := by
        ext ⟨c, d⟩
        rw [Finset.mem_filter, mem_krP2, Finset.mem_singleton, Prod.mk.injEq]
        omega
      have e2 : ((range 133).filter fun c => 265 * c = 265 * c0) = {c0} := by
        ext c
        simp only [Finset.mem_filter, mem_range, Finset.mem_singleton]
        omega
      simp only [e1, e2, Finset.sum_singleton]
      exact land_low (Nat.lt_trans (hl c0) (by norm_num))
    · rw [land_zero']
      symm
      refine Finset.sum_eq_zero fun c hc => absurd ?_ h
      obtain ⟨hc1, rfl⟩ := Finset.mem_filter.1 hc
      have := mem_range.1 hc1
      omega

theorem krCol_eq {Y : Nat → Nat} (hY : ∀ j < 133, canon5 (Y j) = true) :
    krCol (krConst 1 264) (krConst 65535 265) Y = ∑ i ∈ range 133 ×ˢ range 133,
      lane5 (Y i.1) i.2 * 2 ^ (16 * (265 * i.2 + (132 - i.1))) := by
  unfold krCol
  rw [CFSG.KC.Pack.foldN_eq, foldr_range_add (fun j => krSpr (krConst 1 264) (krConst 65535 265) (Y j)
    * 2 ^ (16 * (132 - j))), Nat.zero_add, Finset.sum_product]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [krSpr_eq (hY j (mem_range.1 hj)), Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Nat.mul_add 16, Nat.pow_add]
    ring
  · intro j acc
    change acc + _ <<< (16 * (132 - j)) = _
    rw [Nat.shiftLeft_eq]

theorem lane_prod {Y : Nat → Nat} (hY : ∀ j < 133, canon5 (Y j) = true) {x : Nat}
    (hx : canon5 x = true) :
    (∀ t, lane5 (x * krCol (krConst 1 264) (krConst 65535 265) Y) t ≤ 2128) ∧
    ∀ c < 133, lane5 (x * krCol (krConst 1 264) (krConst 65535 265) Y) (265 * c + 132) =
      ∑ j ∈ range 133, lane5 x j * lane5 (Y j) c := by
  set I := range 133 ×ˢ (range 133 ×ˢ range 133)
  have hP : x * krCol (krConst 1 264) (krConst 65535 265) Y = ∑ i ∈ I,
      lane5 x i.1 * lane5 (Y i.2.1) i.2.2 * 2 ^ (16 * (i.1 + (265 * i.2.2 + (132 - i.2.1)))) := by
    rw [krCol_eq hY]
    conv_lhs => rw [row_expand (canon5_lt hx), Finset.sum_mul_sum]
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun j' _ => Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.mul_add 16, Nat.pow_add]
    ring
  have hpos : ∀ i ∈ I, i.1 + (265 * i.2.2 + (132 - i.2.1)) < 265 * 133 := fun i hi => by
    simp only [I, Finset.mem_product, mem_range] at hi
    omega
  have hv : ∀ i ∈ I, lane5 x i.1 * lane5 (Y i.2.1) i.2.2 ≤ 16 := fun i hi => by
    simp only [I, Finset.mem_product, mem_range] at hi
    have h1 := canon5_lane hx hi.1
    have h2 := canon5_lane (hY _ hi.2.1) hi.2.2
    have h3 : lane5 x i.1 ≤ 4 := by omega
    have h4 : lane5 (Y i.2.1) i.2.2 ≤ 4 := by omega
    exact Nat.mul_le_mul h3 h4
  have hcard : ∀ t, (I.filter fun i => i.1 + (265 * i.2.2 + (132 - i.2.1)) = t).card ≤ 133 := by
    intro t
    rw [← Finset.card_range 133]
    apply Finset.card_le_card_of_injOn (fun i => i.1)
    · intro i hi
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hi
      rw [Finset.mem_coe]
      exact hi.1.1
    · intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_product, mem_range,
        mem_range, mem_range] at ha hb
      obtain ⟨a1, a2, a3⟩ := a
      obtain ⟨b1, b2, b3⟩ := b
      simp only at ha hb hab
      subst hab
      have e3 : a3 = b3 := by omega
      have e2 : a2 = b2 := by omega
      rw [e2, e3]
  have hb : ∀ t, ∑ i ∈ I with i.1 + (265 * i.2.2 + (132 - i.2.1)) = t,
      lane5 x i.1 * lane5 (Y i.2.1) i.2.2 ≤ 2128 := fun t =>
    (fiber_le _ _ _ hv (hcard t)).trans (by norm_num)
  have hb' : ∀ t < 265 * 133, ∑ i ∈ I with i.1 + (265 * i.2.2 + (132 - i.2.1)) = t,
      lane5 x i.1 * lane5 (Y i.2.1) i.2.2 < 2 ^ 16 := fun t _ =>
    Nat.lt_of_le_of_lt (hb t) (by norm_num)
  refine ⟨fun t => ?_, fun c hc => ?_⟩
  · rcases Nat.lt_or_ge t (265 * 133) with ht | ht
    · rw [hP, lane_fiber _ _ _ _ hpos hb' ht]
      exact hb t
    · rw [lane_high (by rw [hP]; exact lt_fiber _ _ _ _ hpos hb') ht]
      norm_num
  · rw [hP, lane_fiber _ _ _ _ hpos hb' (by omega)]
    have e : (I.filter fun i => i.1 + (265 * i.2.2 + (132 - i.2.1)) = 265 * c + 132) =
        (range 133).image fun j => (j, j, c) := by
      ext ⟨a1, a2, a3⟩
      simp only [I, Finset.mem_filter, Finset.mem_product, mem_range, Finset.mem_image,
        Prod.mk.injEq]
      constructor
      · rintro ⟨⟨h1, h2, h3⟩, h4⟩
        exact ⟨a1, h1, rfl, by omega, by omega⟩
      · rintro ⟨j, hj, rfl, rfl, rfl⟩
        exact ⟨⟨hj, hj, hc⟩, by omega⟩
    rw [e, Finset.sum_image fun a _ b _ h => by simpa using congrArg Prod.fst h]

theorem vm5_lt (Y : Nat → Nat) (x : Nat) : vm5 Y x < 2 ^ 2128 := by
  rw [vm5_eq]
  unfold red5
  rw [CFSG.KC.Pack.foldN_eq]
  have key : ∀ l : List Nat, (∀ j ∈ l, j < 133) → l.foldr (fun j acc => Nat.lor acc
      (Nat.shiftLeft (Nat.mod (lane5 (∑ j ∈ range 133, lane5 x j * Y j) j) 5)
        (Nat.mul 16 j))) 0 < 2 ^ 2128 := by
    intro l
    induction l with
    | nil => intro _; exact Nat.two_pow_pos _
    | cons j l ih =>
      intro hl
      rw [List.foldr_cons]
      refine Nat.or_lt_two_pow (ih fun i hi => hl i (List.mem_cons_of_mem _ hi)) ?_
      change _ <<< (16 * j) < _
      rw [Nat.shiftLeft_eq]
      have hj := hl j List.mem_cons_self
      have h5 := Nat.mod_lt (lane5 (∑ j ∈ range 133, lane5 x j * Y j) j) (show 0 < 5 by norm_num)
      calc _ < 5 * 2 ^ (16 * j) := Nat.mul_lt_mul_of_pos_right h5 (Nat.two_pow_pos _)
        _ ≤ 2 ^ 16 * 2 ^ (16 * j) := Nat.mul_le_mul_right _ (by norm_num)
        _ = 2 ^ (16 * (j + 1)) := by rw [← Nat.pow_add]; ring_nf
        _ ≤ 2 ^ 2128 := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact key _ fun j hj => List.mem_range.1 hj

theorem krRow_spec {S M F Q cs x c : Nat} (h : krRow S M F Q cs x c = true) :
    ∃ u sc D q : Nat, u = Nat.land (Nat.shiftRight (x * cs) 2112) M ∧ sc = krSpr S M c ∧
      D = u + F - sc ∧ q = D / 5 ∧ sc ≤ u + F ∧ q * 5 = D ∧ Nat.land q Q = q := by
  unfold krRow at h
  simp only [CFSG.KC.Pack.strictB_eq, CFSG.KC.Pack.band_iff, Nat.ble_eq, Nat.beq_eq] at h
  exact ⟨_, _, _, _, rfl, rfl, rfl, rfl, h.1, h.2.1, h.2.2⟩

theorem krRow_sound {Y : Nat → Nat} (hY : ∀ j < 133, canon5 (Y j) = true) {x c : Nat}
    (hx : canon5 x = true) (hc : canon5 c = true)
    (h : krRow (krConst 1 264) (krConst 65535 265) (krConst 5 265) (krConst 4095 265)
      (krCol (krConst 1 264) (krConst 65535 265) Y) x c = true) :
    vm5 Y x = c := by
  obtain ⟨hall, hdot⟩ := lane_prod hY hx
  obtain ⟨u, sc, D, q, hu, hsc, hD, hq, hle, hq5, hqQ⟩ := krRow_spec h
  clear h hq
  generalize hS : krConst 1 264 = S at hall hdot hu hsc
  generalize hM0 : krConst 65535 265 = M at hall hdot hu hsc
  generalize hF0 : krConst 5 265 = F at hD hle
  generalize hQ0 : krConst 4095 265 = Q at hqQ
  generalize hcs : krCol S M Y = cs at hall hdot hu
  have hM : ∀ t, lane5 M t = if t % 265 = 0 ∧ t / 265 < 133 then 65535 else 0 := by
    rw [← hM0]
    exact lane_krConst (by norm_num) (by norm_num)
  have hul : ∀ t, lane5 u t = if t % 265 = 0 ∧ t / 265 < 133 then
      lane5 (x * cs) (t + 132) else 0 := fun t => by
    have e : (2112 : Nat) = 16 * 132 := by norm_num
    rw [hu, lane5_land, e, lane5_shr, hM]
    split_ifs
    · exact land_low (Nat.lt_of_le_of_lt (hall _) (by norm_num))
    · exact land_zero' _
  have hub : ∀ t, lane5 u t ≤ 2128 := fun t => by
    rw [hul]
    split_ifs
    · exact hall _
    · exact Nat.zero_le _
  have hscl : ∀ t, lane5 sc t = if t % 265 = 0 ∧ t / 265 < 133 then lane5 c (t / 265) else 0 :=
    fun t => by
      rw [hsc, ← hS, ← hM0, krSpr_eq hc]
      have hp : ∀ c' ∈ range 133, 265 * c' < 265 * 133 := fun c' hc' => by
        have := mem_range.1 hc'
        omega
      have hfb : ∀ t < 265 * 133, ∑ c' ∈ range 133 with 265 * c' = t, lane5 c c' < 2 ^ 16 :=
        fun t _ => fib1 _ (fun c' => lane5 c c') _
          (fun c' hc' => (canon5_lane hc (mem_range.1 hc')).le) (by norm_num)
          (card_le_one_265 (by norm_num))
      rcases Nat.lt_or_ge t (265 * 133) with ht | ht
      · refine (lane_fiber _ _ (fun c => 265 * c) (265 * 133) hp hfb ht).trans ?_
        split_ifs with h1
        · have e : ((range 133).filter fun c => 265 * c = t) = {t / 265} := by
            ext d
            simp only [Finset.mem_filter, mem_range, Finset.mem_singleton]
            omega
          simp only [e, Finset.sum_singleton]
        · refine Finset.sum_eq_zero fun d hd => absurd ?_ h1
          obtain ⟨hd1, rfl⟩ := Finset.mem_filter.1 hd
          have := mem_range.1 hd1
          omega
      · have hn : ¬(t % 265 = 0 ∧ t / 265 < 133) := by omega
        refine (lane_high (n := 265 * 133) (lt_fiber _ _ (fun c => 265 * c) _ hp hfb) ht).trans ?_
        rw [if_neg hn]
  have hscb : ∀ t, lane5 sc t ≤ 4 := fun t => by
    rw [hscl]
    split_ifs with h1
    · exact Nat.le_of_lt_succ (canon5_lane hc h1.2)
    · exact Nat.zero_le _
  have hFl : ∀ t, lane5 F t = if t % 265 = 0 ∧ t / 265 < 133 then 5 else 0 := by
    rw [← hF0]
    exact lane_krConst (by norm_num) (by norm_num)
  have hQl : ∀ t, lane5 Q t = if t % 265 = 0 ∧ t / 265 < 133 then 4095 else 0 := by
    rw [← hQ0]
    exact lane_krConst (by norm_num) (by norm_num)
  have hql : ∀ t, lane5 q t ≤ 4095 := fun t => by
    rw [← hqQ, lane5_land, hQl]
    split_ifs
    · exact land_le _ _
    · rw [land_zero']
      exact Nat.zero_le _
  have hMlt : M < 2 ^ (16 * (265 * 133)) := by
    rw [← hM0]
    exact krConst_lt (v := 65535) (s := 265) (by norm_num) (by norm_num)
  have e1 : u + F = ∑ t ∈ range (265 * 133), (lane5 u t + lane5 F t) * 2 ^ (16 * t) := by
    have hult : u < 2 ^ (16 * (265 * 133)) := by
      rw [hu]
      exact Nat.lt_of_le_of_lt (land_le _ _) hMlt
    have hFlt : F < 2 ^ (16 * (265 * 133)) := by
      rw [← hF0]
      exact krConst_lt (v := 5) (s := 265) (by norm_num) (by norm_num)
    conv_lhs => rw [expand_n hult, expand_n hFlt]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  have e2 : u + F = ∑ t ∈ range (265 * 133), (5 * lane5 q t + lane5 sc t) * 2 ^ (16 * t) := by
    have hsclt : sc < 2 ^ (16 * (265 * 133)) := by
      rw [hsc]
      exact Nat.lt_of_le_of_lt (land_le _ _) hMlt
    have hQlt : Q < 2 ^ (16 * (265 * 133)) := by
      rw [← hQ0]
      exact krConst_lt (v := 4095) (s := 265) (by norm_num) (by norm_num)
    have hqlt : q < 2 ^ (16 * (265 * 133)) := by
      rw [← hqQ]
      exact Nat.lt_of_le_of_lt (land_le _ _) hQlt
    have e : u + F = q * 5 + sc := by rw [hq5, hD, Nat.sub_add_cancel hle]
    rw [e]
    conv_lhs => rw [expand_n hqlt, expand_n hsclt]
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  clear hMlt
  set n := 265 * 133
  have hb1 : ∀ t < n, lane5 u t + lane5 F t < 2 ^ 16 := fun t _ => by
    have h1 := hub t
    have h2 := hFl t
    split_ifs at h2 <;> omega
  have hb2 : ∀ t < n, 5 * lane5 q t + lane5 sc t < 2 ^ 16 := fun t _ => by
    have h1 := hql t
    have h2 := hscb t
    omega
  have hlanes : ∀ t < n, lane5 u t + lane5 F t = 5 * lane5 q t + lane5 sc t := fun t ht => by
    have a1 : lane5 (u + F) t = lane5 u t + lane5 F t := by
      rw [e1, lane5_eq]
      exact lane_sum (fun t => lane5 u t + lane5 F t) n hb1 t ht
    have a2 : lane5 (u + F) t = 5 * lane5 q t + lane5 sc t := by
      rw [e2, lane5_eq]
      exact lane_sum (fun t => 5 * lane5 q t + lane5 sc t) n hb2 t ht
    exact a1.symm.trans a2
  refine eq_of_lanes (vm5_lt Y x) (canon5_lt hc) fun k hk => ?_
  rw [vm5_lane hY hx hk]
  have h1 := hlanes (265 * k) (by omega)
  have c1 : 265 * k % 265 = 0 ∧ 265 * k / 265 < 133 := by omega
  have c2 : 265 * k / 265 = k := by omega
  rw [hul, hFl, hscl, if_pos c1, if_pos c1, if_pos c1, c2, hdot k hk] at h1
  have h2 := canon5_lane hc hk
  omega

theorem krProd_sound {Y X C : Nat → Nat} (hY : Canon5 Y) (hX : Canon5 X) (hC : Canon5 C)
    (h : krProd (krConst 1 264) (krConst 65535 265) (krConst 5 265) (krConst 4095 265) Y X C = true) :
    ∀ i < 133, vm5 Y (X i) = C i := by
  unfold krProd at h
  rw [CFSG.KC.Pack.strictB_eq] at h
  intro i hi
  exact krRow_sound hY (hX i hi) (hC i hi) (CFSG.KC.Pack.allN_spec h i hi)

theorem lt8_of_land {v : Nat} (hv : v < 2 ^ 16) (h : Nat.land v 65528 = 0) : v < 8 := by
  have e : v = Nat.land v 7 := by
    calc v = Nat.land v 65535 := (land_low hv).symm
      _ = Nat.lor (Nat.land v 65528) (Nat.land v 7) := by
        have e : (65535 : Nat) = Nat.lor 65528 7 := rfl
        rw [e]
        exact Nat.and_or_distrib_left v 65528 7
      _ = Nat.land v 7 := by rw [h]; exact Nat.zero_or _
  rw [e]
  change v &&& (2 ^ 3 - 1) < 8
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by norm_num)

theorem krCanon_sound {x : Nat} (h : krCanon (krConst 65528 1) (krConst 3 1) x = true) :
    canon5 x = true := by
  unfold krCanon at h
  generalize hM80 : krConst 65528 1 = M8 at h
  generalize hK30 : krConst 3 1 = K3 at h
  simp only [CFSG.KC.Pack.band_iff, Nat.beq_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  change x >>> 2128 = 0 at h1
  rw [Nat.shiftRight_eq_div_pow] at h1
  have hx : x < 2 ^ 2128 := by
    by_contra hc
    have hp := Nat.div_pos (Nat.le_of_not_lt hc) (Nat.two_pow_pos 2128)
    rw [h1] at hp
    exact absurd hp (Nat.lt_irrefl 0)
  have hM8 : ∀ t < 133, lane5 M8 t = 65528 := fun t ht => by
    have c : t % 1 = 0 ∧ t / 1 < 133 := ⟨Nat.mod_one t, by rw [Nat.div_one]; exact ht⟩
    rw [← hM80, lane_krConst (v := 65528) (s := 1) (by norm_num) (by norm_num), if_pos c]
  have h8 : ∀ t < 133, lane5 x t < 8 := fun t ht => by
    have := congrArg (lane5 · t) h2
    simp only [lane5_land, lane5_zero, hM8 t ht] at this
    exact lt8_of_land (lane5_lt _ _) this
  have h11 : ∀ t < 133, lane5 x t + 3 < 2 ^ 16 := fun t ht =>
    Nat.lt_of_lt_of_le (Nat.add_lt_add_right (h8 t ht) 3) (by norm_num)
  have hK : ∀ t < 133, lane5 (Nat.add x K3) t = lane5 x t + 3 := fun t ht => by
    have e : Nat.add x K3 = ∑ s ∈ range 133, (lane5 x s + 3) * 2 ^ (16 * s) := by
      change x + K3 = _
      rw [← hK30, krConst_eq]
      conv_lhs => rw [row_expand hx]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [e, lane5_eq]
    exact lane_sum (fun s => lane5 x s + 3) 133 h11 t ht
  have h5 : ∀ t < 133, lane5 x t < 5 := fun t ht => by
    have h3t := congrArg (lane5 · t) h3
    simp only [lane5_land, lane5_zero, hM8 t ht, hK t ht] at h3t
    exact Nat.lt_of_add_lt_add_right (lt8_of_land (h11 t ht) h3t)
  have hs : Nat.beq (x >>> 2128) 0 = true := by
    rw [Nat.beq_eq, Nat.shiftRight_eq_div_pow, h1]
  unfold canon5
  rw [CFSG.KC.Pack.band_iff]
  refine ⟨hs, CFSG.KS.Raw.Orb.allN_iff.2 fun j hj => ?_⟩
  rw [Nat.blt_eq]
  exact h5 j hj

theorem krBlk_sound {MT OP L R : Nat → Nat} {a n : Nat} (h : krBlk MT OP L R a n = true) {k : Nat}
    (hk1 : a ≤ k) (hk2 : k < a + n) :
    Canon5 (slice5 MT k) ∧
    (OP k = 0 → Canon5 (slice5 MT (L k)) → Canon5 (slice5 MT (R k)) →
      ∀ i < 133, vm5 (slice5 MT (R k)) (slice5 MT (L k) i) = slice5 MT k i) ∧
    (OP k = 1 → ∀ i < 133, slice5 MT (L k) i = slice5 MT k i) := by
  unfold krBlk at h
  simp only [CFSG.KC.Pack.strictB_eq] at h
  have hk := CFSG.KC.Pack.allBlk_spec h (k - a) (by omega)
  have e : Nat.add a (k - a) = k := by
    change a + (k - a) = k
    omega
  rw [e] at hk
  unfold krEnt at hk
  simp only [CFSG.KC.Pack.strictB_eq, CFSG.KC.Pack.band_iff] at hk
  obtain ⟨hcan, hrest⟩ := hk
  have hC : Canon5 (slice5 MT k) := fun i hi => krCanon_sound (CFSG.KC.Pack.allN_spec hcan i hi)
  refine ⟨hC, fun ho hl hr => ?_, fun ho => ?_⟩
  · have e0 : Nat.beq 0 0 = true := rfl
    rw [ho, e0] at hrest
    exact krProd_sound hr hl hC hrest
  · have e1 : Nat.beq 1 0 = false := rfl
    have e2 : Nat.beq 1 1 = true := rfl
    rw [ho, e1, e2] at hrest
    intro i hi
    exact Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec hrest i hi)

end CFSG.KS.SporSch.F5Kron

end
