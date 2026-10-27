module

public import Certificates.Data.Kernel.U6.HuntK
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntRankData
import all CFSG.Certificates.Kernel.U6Sec3.ProdAll
import CFSG.Certificates.Kernel.Spor.RawSiftK

public section

namespace CFSG.KC.U6.CountPf

open CFSG.KLie.CT CFSG.EvenSmallLie.UnitarySix.Hunt CFSG.Sporadic.Th.Native
  CFSG.ComponentClassification.WittDesign

private theorem strictN_eq (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

private theorem sumN_eq (n : Nat) (f : Nat → Nat) : sumN n f = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change f n + sumN n f = _
    rw [ih, Finset.sum_range_succ, Nat.add_comm]

private theorem allN_iff {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ n ih =>
    change Bool.rec false (allN n f) (f n) = true ↔ _
    cases h : f n
    · exact ⟨fun h' => Bool.noConfusion h', fun H => by rw [H n (Nat.lt_succ_self n)] at h; cases h⟩
    · change allN n f = true ↔ _
      rw [ih]
      constructor
      · intro H i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact H i hi
        · exact h
      · exact fun H i hi => H i (Nat.lt_succ_of_lt hi)

private theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl
private theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl
private theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

private theorem maskN_eq (w : Nat) : maskN w = 2 ^ w - 1 := by
  change (1 <<< w) - 1 = 2 ^ w - 1
  rw [Nat.shiftLeft_eq, Nat.one_mul]

private theorem fget_eq (X i w : Nat) : fget X i w = X / 2 ^ (i * w) % 2 ^ w := by
  change (X >>> (i * w)) &&& maskN w = _
  rw [maskN_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

private theorem fget5 (X i : Nat) : fget X i 5 = X / 32 ^ i % 32 := by
  rw [fget_eq, Nat.mul_comm, pow_mul]
  norm_num

private theorem ap5_eq (X i : Nat) : ap5 X i = X / 32 ^ i % 32 := fget5 X i

private theorem pg5 (X i : Nat) : CFSG.KC.Enum.pg 5 (CFSG.KS.mask 5) X i = X / 32 ^ i % 32 := by
  change (X >>> (5 * i)) &&& CFSG.KS.mask 5 = _
  rw [CFSG.KS.PF.mask_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

private theorem dsum_lt {B : Nat} (g : Nat → Nat) : ∀ m, (∀ v < m, g v < B) →
    ∑ v ∈ Finset.range m, g v * B ^ v < B ^ m
  | 0, _ => by simp
  | m + 1, hg => by
    rw [Finset.sum_range_succ, pow_succ]
    have h1 := dsum_lt g m fun v hv => hg v (by omega)
    have h2 := hg m (by omega)
    calc _ < B ^ m + g m * B ^ m := Nat.add_lt_add_right h1 _
      _ = (g m + 1) * B ^ m := by ring
      _ ≤ B * B ^ m := Nat.mul_le_mul_right _ h2
      _ = B ^ m * B := Nat.mul_comm _ _

private theorem dsum_get {B : Nat} : ∀ m (g : Nat → Nat), (∀ v < m, g v < B) → ∀ u < m,
    (∑ v ∈ Finset.range m, g v * B ^ v) / B ^ u % B = g u
  | 0, _, _, u, hu => absurd hu (Nat.not_lt_zero _)
  | m + 1, g, hg, u, hu => by
    have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) (hg 0 (by omega))
    have e : ∑ v ∈ Finset.range (m + 1), g v * B ^ v =
        g 0 + B * ∑ v ∈ Finset.range m, g (v + 1) * B ^ v := by
      rw [Finset.sum_range_succ', Finset.mul_sum, Nat.add_comm]
      simp only [pow_zero, mul_one]
      congr 1
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [pow_succ]
      ring
    rw [e]
    rcases u with _ | u
    · rw [pow_zero, Nat.div_one, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (hg 0 (by omega))
    · rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hB,
        Nat.div_eq_of_lt (hg 0 (by omega)), Nat.zero_add]
      exact dsum_get m (fun v => g (v + 1)) (fun v hv => hg _ (by omega)) u (by omega)

private theorem digits_eq {B : Nat} (hB : 0 < B) : ∀ m (a b : Nat), a < B ^ m → b < B ^ m →
    (∀ u < m, a / B ^ u % B = b / B ^ u % B) → a = b
  | 0, a, b, ha, hb, _ => by simp at ha hb; omega
  | m + 1, a, b, ha, hb, h => by
    have h0 := h 0 (by omega)
    simp only [pow_zero, Nat.div_one] at h0
    have hq : a / B = b / B := digits_eq hB m _ _
      (by rw [Nat.div_lt_iff_lt_mul hB, ← pow_succ]; exact ha)
      (by rw [Nat.div_lt_iff_lt_mul hB, ← pow_succ]; exact hb)
      (fun u hu => by
        have := h (u + 1) (by omega)
        rwa [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at this)
    rw [← Nat.div_add_mod a B, ← Nat.div_add_mod b B, hq, h0]

private theorem memK_iff (L : List Nat) (k : Nat) : memK L k = true ↔ k ∈ L := by
  induction L with
  | nil => exact ⟨fun h => Bool.noConfusion h, fun h => absurd h List.not_mem_nil⟩
  | cons y L ih =>
    change orB (Nat.beq y k) (memK L k) = true ↔ _
    rw [orB_eq, Bool.or_eq_true, ih, List.mem_cons, Nat.beq_eq, eq_comm]

private theorem unkey_eq (k : Nat) :
    unkey k = ∑ i ∈ Finset.range 22, k / 32 ^ (21 - i) % 32 * 32 ^ i := by
  unfold unkey
  rw [sumN_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  change fget k (21 - i) 5 <<< (5 * i) = _
  rw [Nat.shiftLeft_eq, fget5, pow_mul]
  norm_num

private theorem unkey_lt (k : Nat) : unkey k < 32 ^ 22 := by
  rw [unkey_eq]
  exact dsum_lt _ 22 fun v _ => Nat.mod_lt _ (by norm_num)

private theorem unkey_dig (k : Nat) {i : Nat} (hi : i < 22) :
    unkey k / 32 ^ i % 32 = k / 32 ^ (21 - i) % 32 := by
  rw [unkey_eq]
  exact dsum_get 22 (fun i => k / 32 ^ (21 - i) % 32) (fun v _ => Nat.mod_lt _ (by norm_num)) i hi

private theorem keyK_eq (x : Nat) :
    keyK x = ∑ j ∈ Finset.range 22, x / 32 ^ (21 - j) % 32 * 32 ^ j := by
  unfold keyK
  rw [sumN_eq, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  change ap5 x (22 - 1 - j) <<< (5 * (21 - (22 - 1 - j))) = _
  rw [Nat.shiftLeft_eq, ap5_eq, pow_mul, show 21 - (22 - 1 - j) = j by omega,
    show 22 - 1 - j = 21 - j by omega]
  norm_num

private theorem ap_decodeT (y : Nat) {i : Nat} (hi : i < 22) :
    ap (decodeT y) i = y / 32 ^ (21 - i) % 32 := by
  unfold ap decodeT
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  exact UInt32.toNat_ofNat_of_lt' (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by decide))

private theorem decodeT_eq_iff (y : Nat) (f : Fin 22 → Fin 22) :
    decodeT y = tableF f ↔ ∀ i : Fin 22, y / 32 ^ (21 - (i : Nat)) % 32 = (f i : Nat) := by
  unfold decodeT tableF
  have hinj : ∀ {F G : Fin 22 → UInt32}, Array.ofFn F = Array.ofFn G ↔ F = G := fun {F G} =>
    ⟨fun h => List.ofFn_inj.1 (by simpa using congrArg Array.toList h), fun h => by rw [h]⟩
  rw [hinj, funext_iff]
  refine forall_congr' fun i => ⟨fun h => ?_, fun h => by rw [h]⟩
  have h1 := congrArg UInt32.toNat h
  rwa [UInt32.toNat_ofNat_of_lt' (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by decide)),
    UInt32.toNat_ofNat_of_lt' (lt_of_lt_of_le (f i).isLt (by decide))] at h1

private theorem memK_keyK {x : Nat} {f : Fin 22 → Fin 22}
    (hx : ∀ i : Fin 22, x / 32 ^ (i : Nat) % 32 = (f i : Nat)) {L : List Nat}
    (hL : ∀ y ∈ L, y < 2 ^ 110) :
    memK L (keyK x) = (L.map decodeT).contains (tableF f) := by
  have hdig : ∀ v < 22, x / 32 ^ (21 - v) % 32 < 32 := fun v _ => Nat.mod_lt _ (by norm_num)
  have hK : keyK x < 32 ^ 22 := by rw [keyK_eq]; exact dsum_lt _ 22 hdig
  have hKd : ∀ u < 22, keyK x / 32 ^ u % 32 = x / 32 ^ (21 - u) % 32 := fun u hu => by
    rw [keyK_eq]
    exact dsum_get 22 _ hdig u hu
  rw [Bool.eq_iff_iff, memK_iff, List.contains_iff_mem, List.mem_map]
  constructor
  · intro h
    refine ⟨keyK x, h, (decodeT_eq_iff _ f).2 fun i => ?_⟩
    rw [hKd _ (by omega), show 21 - (21 - (i : Nat)) = i by omega]
    exact hx i
  · rintro ⟨y, hy, e⟩
    have hy' : y < 32 ^ 22 := by have := hL y hy; norm_num at this ⊢; omega
    have hd := (decodeT_eq_iff y f).1 e
    have : y = keyK x := digits_eq (by norm_num) 22 y _ hy' hK fun u hu => by
      rw [hKd u hu, hx ⟨21 - u, by omega⟩]
      have := hd ⟨21 - u, by omega⟩
      rwa [show 21 - (21 - u) = u by omega] at this
    exact this ▸ hy

private def Rp (x : Nat) (f : Fin 22 → Fin 22) : Prop :=
  (∀ i : Fin 22, x / 32 ^ (i : Nat) % 32 = (f i : Nat)) ∧ x < 32 ^ 22

private theorem Rp.congr {x : Nat} {f g : Fin 22 → Fin 22} (h : Rp x f) (e : ∀ i, f i = g i) :
    Rp x g := ⟨fun i => by rw [h.1 i, e], h.2⟩

private theorem Rp.ap {x : Nat} {f : Fin 22 → Fin 22} (h : Rp x f) (i : Fin 22) :
    ap5 x i = (f i : Nat) := by rw [ap5_eq, h.1 i]

private theorem pc22_eq (p q : Nat) :
    pc22 p q = CFSG.KC.Enum.pcomp 22 5 (CFSG.KS.mask 5) p q := by
  unfold pc22
  rw [strictN_eq, strictN_eq]
  rfl

private theorem Rp.pc22 {p q : Nat} {g h : Fin 22 → Fin 22} (hp : Rp p g) (hq : Rp q h) :
    Rp (pc22 p q) (fun i => g (h i)) := by
  refine ⟨fun i => ?_, ?_⟩
  · rw [← pg5, pc22_eq, CFSG.KS.PF.pg_pcomp (by norm_num) i.2, pg5 q, hq.1 i, pg5 p]
    exact hp.1 (h i)
  · have e := CFSG.KS.PF.pcomp_shr (n := 22) (w := 5) p q (by norm_num) (by norm_num)
    rw [← pc22_eq, Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff_lt (by positivity)] at e
    norm_num at e ⊢
    exact e

private theorem Rp.root {k : Nat} (hd : ∀ i < 22, fget (unkey k) i 5 < 22) :
    Rp (unkey k) (tf (decodeT k)) := by
  refine ⟨fun i => ?_, unkey_lt k⟩
  have h := hd i i.2
  rw [fget5, unkey_dig k i.2] at h
  rw [unkey_dig k i.2]
  change _ = CFSG.Sporadic.Th.Native.ap (decodeT k) i % 22
  rw [ap_decodeT k i.2, Nat.mod_eq_of_lt h]

private theorem beq_fin (a b : Fin 22) : Nat.beq a.val b.val = (a == b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq, Fin.ext_iff]

private theorem allN_fin {q : Nat → Bool} {p : Fin 22 → Bool} (h : ∀ i : Fin 22, q i = p i) :
    allN 22 q = (List.finRange 22).all p := by
  rw [Bool.eq_iff_iff, allN_iff, List.all_eq_true]
  constructor
  · intro H i _
    rw [← h]
    exact H i i.2
  · intro H i hi
    rw [h ⟨i, hi⟩]
    exact H _ (List.mem_finRange _)

private theorem commM_eq {x r : Nat} {f R : Fin 22 → Fin 22} (hx : Rp x f) (hr : Rp r R) :
    commM r x = commB R f :=
  allN_fin fun i => by rw [hr.ap, hx.ap, hx.ap, hr.ap, beq_fin]

private theorem sqK_eq {x : Nat} {f : Fin 22 → Fin 22} (hx : Rp x f) : sqK x = sqB f :=
  allN_fin fun i => by rw [hx.ap, hx.ap, beq_fin]

private theorem isIdK_eq {x : Nat} {f : Fin 22 → Fin 22} (hx : Rp x f) : isIdK x = eqB id f :=
  allN_fin fun i => by rw [hx.ap, beq_fin]; rfl

private theorem sqMulK_eq {x s : Nat} {f T : Fin 22 → Fin 22} (hx : Rp x f) (hs : Rp s T) :
    sqMulK s x = sqMulB T f :=
  allN_fin fun i => by rw [hs.ap, hx.ap, hs.ap, hx.ap, beq_fin]

private theorem beq_eq {x r : Nat} {f R : Fin 22 → Fin 22} (hx : Rp x f) (hr : Rp r R) :
    Nat.beq x r = eqB R f := by
  rw [Bool.eq_iff_iff, Nat.beq_eq]
  unfold eqB
  rw [List.all_eq_true]
  constructor
  · rintro rfl i _
    rw [beq_iff_eq]
    exact Fin.ext ((hx.1 i).symm.trans (hr.1 i))
  · intro H
    refine digits_eq (by norm_num) 22 x r hx.2 hr.2 fun u hu => ?_
    rw [hx.1 ⟨u, hu⟩, hr.1 ⟨u, hu⟩]
    have := H ⟨u, hu⟩ (List.mem_finRange _)
    rw [beq_iff_eq] at this
    rw [this]

private theorem missOutK_eq {x r : Nat} {f R : Fin 22 → Fin 22} (hx : Rp x f) (hr : Rp r R)
    {L : List Nat} (hL : ∀ y ∈ L, y < 2 ^ 110) :
    missOutK r L x = missOut R (L.map decodeT) f := by
  unfold missOutK missOut
  rw [andB_eq, andB_eq, andB_eq, orB_eq, notB_eq, notB_eq, notB_eq, sqK_eq hx, commM_eq hx hr,
    isIdK_eq hx, memK_keyK hx.1 hL, memK_keyK (hx.pc22 hr).1 hL]
  simp only [Bool.and_assoc]

private theorem missInK_eq {x r : Nat} {f R : Fin 22 → Fin 22} (hx : Rp x f) (hr : Rp r R)
    {L : List Nat} (hL : ∀ y ∈ L, y < 2 ^ 110) :
    missInK r L x = missIn R (L.map decodeT) f := by
  unfold missInK missIn
  rw [andB_eq, andB_eq, andB_eq, andB_eq, notB_eq, notB_eq, notB_eq, sqK_eq hx, commM_eq hx hr,
    isIdK_eq hx, beq_eq hx hr, memK_keyK hx.1 hL]
  simp only [Bool.and_assoc]

private noncomputable def Qv (R8 R0 RY : Nat) (L8 L0 LY : List Nat) (x : Nat) : List Bool :=
  [orB (missOutK R8 L8 x) (orB (missOutK R0 L0 x) (missInK RY LY x)), sqMulK R8 x,
    andB (sqK x) (notB (isIdK x)), commM R8 x, commM R0 x, commM RY x]

private def Sp (T8 T0 TY : Fin 22 → Fin 22) (C8 C0 CY : List Table) (f : Fin 22 → Fin 22) :
    List Bool :=
  [missOut T8 C8 f || missOut T0 C0 f || missIn TY CY f, sqMulB T8 f, sqB f && !eqB id f,
    commB T8 f, commB T0 f, commB TY f]

private theorem Qv_eq {x : Nat} {f T8 T0 TY : Fin 22 → Fin 22} {R8 R0 RY : Nat}
    {L8 L0 LY : List Nat} (hx : Rp x f) (h8 : Rp R8 T8) (h0 : Rp R0 T0) (hY : Rp RY TY)
    (hL8 : ∀ y ∈ L8, y < 2 ^ 110) (hL0 : ∀ y ∈ L0, y < 2 ^ 110) (hLY : ∀ y ∈ LY, y < 2 ^ 110) :
    Qv R8 R0 RY L8 L0 LY x = Sp T8 T0 TY (L8.map decodeT) (L0.map decodeT) (LY.map decodeT) f := by
  unfold Qv Sp
  rw [orB_eq, orB_eq, missOutK_eq hx h8 hL8, missOutK_eq hx h0 hL0, missInK_eq hx hY hLY,
    sqMulK_eq hx h8, andB_eq, notB_eq, sqK_eq hx, isIdK_eq hx, commM_eq hx h8, commM_eq hx h0,
    commM_eq hx hY, Bool.or_assoc]

private theorem ind_eq (b : Bool) (k : Nat) :
    ind b k = (if b = true then 1 else 0) * (2 ^ 20) ^ k := by
  cases b
  · simp [ind]
  · change 1 <<< (20 * k) = _
    rw [Nat.shiftLeft_eq, ← pow_mul]
    simp

private theorem cntVec_eq (R8 R0 RY : Nat) (L8 L0 LY : List Nat) (x : Nat) :
    cntVec R8 R0 RY L8 L0 LY x = ∑ k ∈ Finset.range 6,
      (if (Qv R8 R0 RY L8 L0 LY x).getD k false = true then 1 else 0) * (2 ^ 20) ^ k := by
  unfold cntVec
  simp only [ind_eq, Finset.sum_range_succ, Finset.sum_range_zero, Qv, List.getD_cons_zero,
    List.getD_cons_succ, Nat.add_eq]
  ring

private def box : Finset (Nat × Nat × Nat × Nat × Nat) :=
  Finset.range 22 ×ˢ Finset.range 21 ×ˢ Finset.range 20 ×ˢ Finset.range 16 ×ˢ Finset.range 3

private theorem box_card : box.card = 443520 := by
  simp [box, Finset.card_product]

private theorem count_box {G : Subgroup (Equiv.Perm (Fin 22))}
    {E : Nat × Nat × Nat × Nat × Nat → Equiv.Perm (Fin 22)}
    (hmem : ∀ κ ∈ box, E κ ∈ G) (hsurj : ∀ g ∈ G, ∃ κ ∈ box, E κ = g)
    (hcard : box.card ≤ Nat.card G) (P : Equiv.Perm (Fin 22) → Bool) :
    Nat.card {x : G // P x = true} = ∑ κ ∈ box, if P (E κ) = true then 1 else 0 := by
  let f : box → G := fun κ => ⟨E κ, hmem κ κ.2⟩
  have hfs : Function.Surjective f := fun g => by
    obtain ⟨κ, hκ, e⟩ := hsurj g g.2
    exact ⟨⟨κ, hκ⟩, Subtype.ext e⟩
  have hfb : Function.Bijective f := hfs.bijective_of_nat_card_le (by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact hcard)
  rw [← Finset.card_filter]
  let g : {κ // κ ∈ box.filter fun κ => P (E κ) = true} → {x : G // P x = true} := fun κ =>
    ⟨f ⟨κ.1, (Finset.mem_filter.1 κ.2).1⟩, (Finset.mem_filter.1 κ.2).2⟩
  have hg : Function.Bijective g := by
    refine ⟨fun a b hab => ?_, fun x => ?_⟩
    · have := hfb.1 (congrArg Subtype.val hab)
      exact Subtype.ext (congrArg (fun z : box => z.1) this)
    · obtain ⟨κ, hκ⟩ := hfb.2 x.1
      refine ⟨⟨κ.1, Finset.mem_filter.2 ⟨κ.2, ?_⟩⟩, Subtype.ext hκ⟩
      have := x.2
      rw [← hκ] at this
      exact this
  rw [← Nat.card_eq_of_bijective g hg, Nat.card_eq_fintype_card, Fintype.card_coe]

section Chain

open CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.Certificates CFSG.Certificates.ChainArrays
  CFSG.Monster.B.Co2

private noncomputable def E5 (S : Array (Array Nat)) (base : Array Nat)
    (κ : Nat × Nat × Nat × Nat × Nat) : Equiv.Perm (Fin 22) :=
  levT 22 S base 0 κ.1 * levT 22 S base 1 κ.2.1 * levT 22 S base 2 κ.2.2.1 *
    levT 22 S base 3 κ.2.2.2.1 * levT 22 S base 4 κ.2.2.2.2

private theorem raw_one {O S : Array (Array Nat)} {base : Array Nat} {W : Array (List ℤ)}
    {c : Nat} (hc : 0 < c) (h : Native.rawChainOK 22 O S base W c = true) :
    Native.rawChainOK 22 O S base W 1 = true := by
  have hF := chainCheckFacts h
  unfold Native.rawChainOK at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  refine ⟨h.1, allLt_iff.2 fun i hi => ?_⟩
  have := hF.schreier i hi
  unfold CFSG.Monster.B.Co2.Native.schreierOK at this ⊢
  exact parLt_of_forall (parLt_spec hc this)

private theorem Rp_of_canon {p : Nat} {g : Equiv.Perm (Fin 22)}
    (hc : CFSG.KS.Prim.canonK 22 5 (CFSG.KS.mask 5) (22 * 5) p = true)
    (h : ∀ z : Fin 22, CFSG.KC.Enum.pg 5 (CFSG.KS.mask 5) p z = (g z : Nat)) : Rp p ⇑g := by
  refine ⟨fun z => by rw [← pg5, h z], ?_⟩
  have e := (CFSG.KS.PF.canon_facts hc).2.2.1
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff_lt (by positivity)] at e
  norm_num at e ⊢
  exact e

private theorem chunkK_eq (R8 R0 RY : Nat) (L8 L0 LY : List Nat) (TR : Nat → Nat) (o a : Nat) :
    chunkK R8 R0 RY L8 L0 LY TR o a =
      ∑ b ∈ Finset.range 21, ∑ c ∈ Finset.range 20, ∑ d ∈ Finset.range 16, ∑ e ∈ Finset.range 3,
        cntVec R8 R0 RY L8 L0 LY (pc22 (pc22 (pc22 (pc22 (TR (fget o 0 32 + a))
          (TR (fget o 1 32 + b))) (TR (fget o 2 32 + c))) (TR (fget o 3 32 + d)))
          (TR (fget o 4 32 + e))) := by
  simp only [chunkK, strictN_eq, sumN_eq]
  rfl

private noncomputable def Xc (TR LR : Nat → Nat) (κ : Nat × Nat × Nat × Nat × Nat) : Nat :=
  pc22 (pc22 (pc22 (pc22 (TR (roff 22 (22 * 5) (LR 0) + κ.1))
    (TR (roff 22 (22 * 5) (LR 1) + κ.2.1))) (TR (roff 22 (22 * 5) (LR 2) + κ.2.2.1)))
    (TR (roff 22 (22 * 5) (LR 3) + κ.2.2.2.1))) (TR (roff 22 (22 * 5) (LR 4) + κ.2.2.2.2))

private theorem sum_box (F : Nat × Nat × Nat × Nat × Nat → Nat) :
    ∑ κ ∈ box, F κ = ∑ a ∈ Finset.range 22, ∑ b ∈ Finset.range 21, ∑ c ∈ Finset.range 20,
      ∑ d ∈ Finset.range 16, ∑ e ∈ Finset.range 3, F (a, b, c, d, e) := by
  simp only [box, Finset.sum_product]

theorem sound3003C' {PS PSI LR TR TRI : Nat → Nat} {kS BP chunks : Nat}
    {S : Array (Array Nat)} {base : Array Nat} {W : Array (List ℤ)} {g₁ g₂ : Equiv.Perm (Fin 22)}
    {k8 k0 kY : Nat} {L8 L0 LY : List Nat} {V : Nat → Nat}
    (hb : CFSG.KS.Raw.Binds 22 5 PS kS 5 BP S base)
    (hp : CFSG.KC.Enum.allN kS (fun j => CFSG.KC.Enum.permOK 22 5 (CFSG.KS.mask 5) (22 * 5) (PS j)
      (PSI j)) = true)
    (hl : CFSG.KS.Raw.LevelsOK 22 5 PS PSI LR TR TRI kS 5 BP)
    (hraw : CFSG.Certificates.Native.rawChainOK 22 (S.extract 0 2) S base W chunks = true)
    (hg : CFSG.Monster.B.Co2.Rep 22 S[0]! g₁ ∧ CFSG.Monster.B.Co2.Rep 22 S[1]! g₂)
    (hsz : ∀ i < 5, CFSG.KS.Raw.rcnt (LR i) = [22, 21, 20, 16, 3].getD i 0)
    (hd : ∀ k ∈ [k8, k0, kY], ∀ i < 22, fget (unkey k) i 5 < 22)
    (hL : ∀ k ∈ L8 ++ L0 ++ LY, k < 2 ^ 110)
    (hk : ∀ a < 22, chunkK (unkey k8) (unkey k0) (unkey kY) L8 L0 LY TR
      (sumN 5 fun i => Nat.shiftLeft (CFSG.KS.Raw.roff 22 (22 * 5) (LR i)) (Nat.mul 32 i)) a =
        V a)
    (hc : 0 < chunks) :
    let G := Subgroup.closure ({g₁, g₂} : Set (Equiv.Perm (Fin 22)))
    let N := fun k => fget (sumN 22 V) k 20
    Nat.card {x : G // (missOut (tf (decodeT k8)) (L8.map decodeT) ⇑(x : Equiv.Perm (Fin 22)) ||
        missOut (tf (decodeT k0)) (L0.map decodeT) ⇑(x : Equiv.Perm (Fin 22)) ||
        missIn (tf (decodeT kY)) (LY.map decodeT) ⇑(x : Equiv.Perm (Fin 22))) = true} = N 0 ∧
      Nat.card {x : G // sqMulB (tf (decodeT k8)) ⇑(x : Equiv.Perm (Fin 22)) = true} = N 1 ∧
      Nat.card {x : G // (sqB ⇑(x : Equiv.Perm (Fin 22)) &&
        !eqB id ⇑(x : Equiv.Perm (Fin 22))) = true} = N 2 ∧
      Nat.card {x : G // commB (tf (decodeT k8)) ⇑(x : Equiv.Perm (Fin 22)) = true} = N 3 ∧
      Nat.card {x : G // commB (tf (decodeT k0)) ⇑(x : Equiv.Perm (Fin 22)) = true} = N 4 ∧
      Nat.card {x : G // commB (tf (decodeT kY)) ⇑(x : Equiv.Perm (Fin 22)) = true} = N 5 := by
  intro G N
  have hSsz : S.size = kS := hb.2.2.2.1
  have hbs : base.size = 5 := hb.2.2.2.2.2.1
  have hraw1 := raw_one hc hraw
  have hF := chainCheckFacts hraw
  have hF1 := chainCheckFacts hraw1
  have hS2 : 2 ≤ S.size := by
    by_contra hlt
    have e : S[1]! = (default : Array Nat) := getElem!_neg S 1 (by omega)
    have h0 := hg.2 ⟨0, by norm_num⟩
    have h1 := hg.2 ⟨1, by norm_num⟩
    rw [e] at h0 h1
    have h00 : (default : Array Nat)[0]! = 0 := getElem!_neg _ 0 (by
      change ¬ 0 < (#[] : Array Nat).size; simp)
    have h11 : (default : Array Nat)[1]! = 0 := getElem!_neg _ 1 (by
      change ¬ 1 < (#[] : Array Nat).size; simp)
    have : g₂ ⟨0, by norm_num⟩ = g₂ ⟨1, by norm_num⟩ := Fin.ext (by
      have a0 : (default : Array Nat)[0]! = (g₂ ⟨0, by norm_num⟩ : Nat) := h0
      have a1 : (default : Array Nat)[1]! = (g₂ ⟨1, by norm_num⟩ : Nat) := h1
      omega)
    exact absurd (g₂.injective this) (by decide)
  have hO : (S.extract 0 2).size = 2 := by simp [Array.size_extract]; omega
  have hH : Hd 22 S base 2 W :=
    ⟨hS2, hF.strong_inv, fun j hj h2 => hF.words j hj (by rw [hO]; exact h2), hF.base_lt⟩
  have hbl := base_lt_of_levels hb hl
  have rep_eq : ∀ {t : Array Nat} {a b : Equiv.Perm (Fin 22)}, Rep 22 t a → Rep 22 t b → a = b :=
    fun ha hb' => Equiv.ext fun z => Fin.ext ((ha z).symm.trans (hb' z))
  have e0 : permOfArr 22 S[0]! = g₁ := rep_eq (rep_S hH (by omega)) hg.1
  have e1 : permOfArr 22 S[1]! = g₂ := rep_eq (rep_S hH (by omega)) hg.2
  have hext : ∀ j < 2, (S.extract 0 2)[j]! = S[j]! := fun j hj => by
    rw [getElem!_pos (S.extract 0 2) j (by omega), Array.getElem_extract,
      getElem!_pos S j (by omega)]
    simp
  have hGen : Gen 22 S 2 = G := by
    unfold Gen
    congr 1
    ext g
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩
      fin_cases j
      · exact Or.inl e0
      · exact Or.inr e1
    · rintro (rfl | rfl)
      · exact ⟨0, e0⟩
      · exact ⟨1, e1⟩
  have hGA : G ≤ Subgroup.closure (CFSG.RankThree.Native.permsA 22 (S.extract 0 2)) := by
    refine Subgroup.closure_mono ?_
    rintro g (rfl | rfl)
    · exact ⟨0, by simp [hO], by simp only; rw [hext 0 (by norm_num)]; exact e0⟩
    · exact ⟨1, by simp [hO], by simp only; rw [hext 1 (by norm_num)]; exact e1⟩
  have hsz' : ∀ i < 5, (lev 22 S base i).pts.size = [22, 21, 20, 16, 3].getD i 0 := fun i hi => by
    rw [← hsz i hi]
    exact ((agree_levelK hb hp hbl (R := LR) (TRI := TRI) hi (hl i hi)).1.cnt).symm
  have hT : ∀ i < 5, ∀ k < [22, 21, 20, 16, 3].getD i 0,
      Rp (TR (roff 22 (22 * 5) (LR i) + k)) ⇑(levT 22 S base i k) ∧ levT 22 S base i k ∈ G :=
    fun i hi k hk => by
      have hk' : k < (lev 22 S base i).pts.size := by rw [hsz' i hi]; exact hk
      obtain ⟨-, hcan, hpg⟩ := CFSG.KC.U6Sec3.ProdPf.kernel_T hb hp hl hF1 hi hk'
      refine ⟨Rp_of_canon hcan hpg, hGen ▸ ?_⟩
      exact (mem_Fix.1 (tr_spec hH (by omega) k hk').1).1
  have hmem : ∀ κ ∈ box, E5 S base κ ∈ G := by
    intro κ hκ
    simp only [box, Finset.mem_product, Finset.mem_range] at hκ
    obtain ⟨h0, h1, h2, h3, h4⟩ := hκ
    unfold E5
    exact mul_mem (mul_mem (mul_mem (mul_mem (hT 0 (by norm_num) _ h0).2
      (hT 1 (by norm_num) _ h1).2) (hT 2 (by norm_num) _ h2).2) (hT 3 (by norm_num) _ h3).2)
      (hT 4 (by norm_num) _ h4).2
  have hsurj : ∀ g ∈ G, ∃ κ ∈ box, E5 S base κ = g := by
    intro g hg'
    obtain ⟨κ, hκ, e⟩ := CFSG.KC.U6Sec3.ProdPf.decomp hF1 (hGA hg')
    rw [hbs] at hκ e
    refine ⟨(κ 0, κ 1, κ 2, κ 3, κ 4), ?_, ?_⟩
    · have := fun i (hi : i < 5) => (hsz' i hi) ▸ hκ i hi
      simp only [box, Finset.mem_product, Finset.mem_range]
      exact ⟨this 0 (by norm_num), this 1 (by norm_num), this 2 (by norm_num),
        this 3 (by norm_num), this 4 (by norm_num)⟩
    · rw [e, show List.range 5 = [0, 1, 2, 3, 4] from rfl]
      simp [E5, mul_assoc]
  have hle : Nat.card (Gen 22 S 2) ≤ (Native.rawOrbitSizes 22 S base).prod := by
    rw [rawOrbitSizesK_sound hb hp hl, hGen]
    have h1 : Nat.card G ≤ box.card := by
      let f : box → G := fun κ => ⟨E5 S base κ, hmem κ κ.2⟩
      have hf : Function.Surjective f := fun g => by
        obtain ⟨κ, hκ, e⟩ := hsurj g g.2
        exact ⟨⟨κ, hκ⟩, Subtype.ext e⟩
      have := Nat.card_le_card_of_surjective f hf
      rwa [Nat.card_eq_finsetCard] at this
    rw [box_card] at h1
    rw [show List.range 5 = [0, 1, 2, 3, 4] from rfl]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    rw [hsz 0 (by norm_num), hsz 1 (by norm_num), hsz 2 (by norm_num), hsz 3 (by norm_num),
      hsz 4 (by norm_num)]
    norm_num
    exact h1
  have hcard : box.card ≤ Nat.card G := by
    obtain ⟨c5, cs⟩ := card_facts hH hle
    rw [hbs] at c5 cs
    rw [← hGen, ← Fix_zero (base := base), cs 0 (by norm_num), cs 1 (by norm_num),
      cs 2 (by norm_num), cs 3 (by norm_num), cs 4 (by norm_num), c5, hsz' 0 (by norm_num),
      hsz' 1 (by norm_num), hsz' 2 (by norm_num), hsz' 3 (by norm_num), hsz' 4 (by norm_num),
      box_card]
    norm_num
  have hR8 : Rp (unkey k8) (tf (decodeT k8)) := Rp.root (hd k8 (by simp))
  have hR0 : Rp (unkey k0) (tf (decodeT k0)) := Rp.root (hd k0 (by simp))
  have hRY : Rp (unkey kY) (tf (decodeT kY)) := Rp.root (hd kY (by simp))
  have hL8 : ∀ y ∈ L8, y < 2 ^ 110 := fun y hy => hL y (by simp [hy])
  have hL0 : ∀ y ∈ L0, y < 2 ^ 110 := fun y hy => hL y (by simp [hy])
  have hLY : ∀ y ∈ LY, y < 2 ^ 110 := fun y hy => hL y (by simp [hy])
  have hX : ∀ κ ∈ box, Rp (Xc TR LR κ) ⇑(E5 S base κ) := by
    intro κ hκ
    simp only [box, Finset.mem_product, Finset.mem_range] at hκ
    obtain ⟨h0, h1, h2, h3, h4⟩ := hκ
    exact (((((hT 0 (by norm_num) _ h0).1.pc22 (hT 1 (by norm_num) _ h1).1).pc22
      (hT 2 (by norm_num) _ h2).1).pc22 (hT 3 (by norm_num) _ h3).1).pc22
      (hT 4 (by norm_num) _ h4).1).congr fun i => rfl
  have ho : ∀ i < 5, fget (sumN 5 fun i => Nat.shiftLeft (roff 22 (22 * 5) (LR i))
      (Nat.mul 32 i)) i 32 = roff 22 (22 * 5) (LR i) := by
    intro i hi
    have e : (sumN 5 fun i => Nat.shiftLeft (roff 22 (22 * 5) (LR i)) (Nat.mul 32 i)) =
        ∑ v ∈ Finset.range 5, roff 22 (22 * 5) (LR v) * (2 ^ 32) ^ v := by
      rw [sumN_eq]
      refine Finset.sum_congr rfl fun v _ => ?_
      change roff 22 (22 * 5) (LR v) <<< (32 * v) = _
      rw [Nat.shiftLeft_eq, pow_mul]
    rw [fget_eq, e, Nat.mul_comm i 32, pow_mul]
    exact dsum_get 5 _ (fun v _ => by
      unfold roff
      exact lt_of_le_of_lt Nat.and_le_right (by norm_num)) i hi
  have htot : sumN 22 V =
      ∑ κ ∈ box, cntVec (unkey k8) (unkey k0) (unkey kY) L8 L0 LY (Xc TR LR κ) := by
    rw [sumN_eq, sum_box]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [← hk a (Finset.mem_range.1 ha), chunkK_eq, ho 0 (by norm_num), ho 1 (by norm_num),
      ho 2 (by norm_num), ho 3 (by norm_num), ho 4 (by norm_num)]
    rfl
  have hN : ∀ j < 6, N j = ∑ κ ∈ box,
      if (Qv (unkey k8) (unkey k0) (unkey kY) L8 L0 LY (Xc TR LR κ)).getD j false = true then 1
        else 0 := by
    intro j hj
    have e : ∑ κ ∈ box, cntVec (unkey k8) (unkey k0) (unkey kY) L8 L0 LY (Xc TR LR κ) =
        ∑ v ∈ Finset.range 6, (∑ κ ∈ box,
          if (Qv (unkey k8) (unkey k0) (unkey kY) L8 L0 LY (Xc TR LR κ)).getD v false = true
            then 1 else 0) * (2 ^ 20) ^ v := by
      simp only [cntVec_eq]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun v _ => (Finset.sum_mul _ _ _).symm
    show fget (sumN 22 V) j 20 = _
    rw [htot, fget_eq, e, Nat.mul_comm j 20, pow_mul]
    refine dsum_get 6 _ (fun v _ => ?_) j hj
    rw [← Finset.card_filter]
    exact lt_of_le_of_lt (Finset.card_filter_le _ _) (by rw [box_card]; norm_num)
  have hQ : ∀ j < 6, Nat.card {x : G // (Sp (tf (decodeT k8)) (tf (decodeT k0)) (tf (decodeT kY))
      (L8.map decodeT) (L0.map decodeT) (LY.map decodeT) ⇑(x : Equiv.Perm (Fin 22))).getD j false =
        true} = N j := by
    intro j hj
    refine (count_box hmem hsurj hcard (fun x => (Sp (tf (decodeT k8)) (tf (decodeT k0))
      (tf (decodeT kY)) (L8.map decodeT) (L0.map decodeT) (LY.map decodeT) ⇑x).getD j false)).trans
      ?_
    rw [hN j hj]
    refine Finset.sum_congr rfl fun κ hκ => ?_
    rw [Qv_eq (hX κ hκ) hR8 hR0 hRY hL8 hL0 hLY]
  exact ⟨hQ 0 (by norm_num), hQ 1 (by norm_num), hQ 2 (by norm_num), hQ 3 (by norm_num),
    hQ 4 (by norm_num), hQ 5 (by norm_num)⟩

end Chain

end CFSG.KC.U6.CountPf

end
