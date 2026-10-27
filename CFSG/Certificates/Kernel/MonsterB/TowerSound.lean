module

public import Certificates.Data.Kernel.MonsterB.Tower
public import Certificates.Data.CFSGNative.MonsterB.Max2Tower
public import Certificates.Data.CFSGNative.MonsterB.Co2Data
public import CFSG.Certificates.Kernel.Co1BMulSound
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.Tower

open CFSG.Monster.B.Max2.Native CFSG.KC.M1F2 CFSG.KC.F2W CFSG.KC.Co1F2
  CFSG.Sporadic.SmallF2.Native

theorem bAnd_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem bIf_eq' (c t e : Bool) : Bool.rec (motive := fun _ => Bool) e t c = if c then t else e := by
  cases c <;> rfl

theorem hexAt_eq (b : ByteArray) (o : Nat) : ∀ w,
    CFSG.Monster.B.Max2.Native.hexAt b o w = CFSG.Monster.B.Co2.Native.hexAt b o w
  | 0 => rfl
  | w + 1 => by
    rw [CFSG.Monster.B.Max2.Native.hexAt, CFSG.Monster.B.Co2.Native.hexAt, hexAt_eq b o w]
    rfl

theorem hexAt_add (b : ByteArray) (o m : Nat) : ∀ n,
    CFSG.Monster.B.Co2.Native.hexAt b o (m + n) =
      CFSG.Monster.B.Co2.Native.hexAt b o m * 16 ^ n + CFSG.Monster.B.Co2.Native.hexAt b (o + m) n
  | 0 => by simp [CFSG.Monster.B.Co2.Native.hexAt]
  | n + 1 => by
    rw [← Nat.add_assoc, CFSG.Monster.B.Co2.Native.hexAt, hexAt_add b o m n,
      CFSG.Monster.B.Co2.Native.hexAt, Nat.add_assoc o m n, Nat.pow_succ]
    ring

theorem actGo_eq (rows : Array Nat) (v : Nat) : ∀ n acc,
    CFSG.Monster.VisCert.Native.actGo rows v n acc = acc ^^^ vecMulN n rows v
  | 0, acc => by simp [CFSG.Monster.VisCert.Native.actGo, vecMulN]
  | n + 1, acc => by
    have hs : vecMulN (n + 1) rows v =
        if v.testBit n then vecMulN n rows v ^^^ rows[n]?.getD 0 else vecMulN n rows v := by
      simp only [vecMulN, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have e : rows[n]! = rows[n]?.getD 0 := by
      simp only [getElem!_def]
      split <;> simp_all
    rw [CFSG.Monster.VisCert.Native.actGo, actGo_eq rows v n, hs, e]
    cases v.testBit n
    · rfl
    · simp only [↓reduceIte]
      rw [Nat.xor_assoc, Nat.xor_comm (rows[n]?.getD 0)]

theorem act22_unpack (M v : Nat) : act22 (unpackR 22 M) v = vmF 22 M v := by
  rw [act22, actGo_eq, Nat.zero_xor, vecMulN_unpackR]

theorem unpackR_size (M : Nat) : (unpackR 22 M).size = 22 := by simp [unpackR]

theorem mul22_unpack (A B : Nat) :
    mul22 (unpackR 22 A) (unpackR 22 B) = unpackR 22 (mulW 22 A B) := by
  rw [← mulRows_unpackW]
  apply Array.ext
  · simp [mul22, mulRows, unpackR]
  · intro i h1 h2
    have hi : i < 22 := by simpa [mul22] using h1
    simp only [mul22, mulRows, Array.getElem_map, Array.getElem_range]
    rw [act22, actGo_eq, Nat.zero_xor, getElem!_pos _ i (by rw [unpackR_size]; exact hi)]

theorem id22_eq : id22 () = unpackR 22 (idF 22) := by
  apply Array.ext
  · simp [id22, unpackR]
  · intro i h1 h2
    have hi : i < 22 := by simpa [id22] using h1
    have hf : ∀ k < 22, CFSG.KLie.CT.pw2 k < 2 ^ 22 := fun k hk => by
      change 1 <<< k < 2 ^ 22
      rw [Nat.one_shiftLeft]
      exact Nat.pow_lt_pow_right (by norm_num) hk
    have e := rowF_orN 22 hf hi
    rw [rowF_eq] at e
    simp only [id22, unpackR, Array.getElem_map, Array.getElem_range, Array.getElem_ofFn]
    change 1 <<< i = idF 22 / 2 ^ (22 * i) % 2 ^ 22
    rw [show idF 22 = CFSG.KLie.CT.orN 22 fun i => CFSG.KLie.CT.pw2 i <<< (22 * i) from rfl, e,
      CFSG.KLie.CT.pw2]
    rfl

theorem eq22_self (X : Array Nat) (h : X.size = 22) : eq22 X X = true := by
  simp [eq22, h]

theorem nodeK_spec {DA DB T : Nat → Nat} {j : Nat} (h : nodeK DA DB T j = true) :
    (DA j = 2 → T j = idF 22) ∧ (DA j = 1 → T j = T 1) ∧ (DA j = 0 → T j = T 2) ∧
      (DA j = 3 → DB j < j ∧ mulW 22 (T (DB j)) (T j) = idF 22) ∧
      (4 ≤ DA j → DA j - 4 < j ∧ DB j < j ∧ T j = mulW 22 (T (DA j - 4)) (T (DB j))) := by
  unfold nodeK at h
  simp only [bIf_eq', Nat.beq_eq, Nat.blt_eq] at h
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
  · rw [ite_eq_left e] at h
    exact Nat.eq_of_beq_eq_true h
  · rw [ite_eq_right (by omega), ite_eq_left e] at h
    exact Nat.eq_of_beq_eq_true h
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left e] at h
    exact Nat.eq_of_beq_eq_true h
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left e] at h
    split_ifs at h with h1
    exact ⟨h1, Nat.eq_of_beq_eq_true h⟩
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)] at h
    split_ifs at h with h1 h2
    exact ⟨h1, h2, Nat.eq_of_beq_eq_true h⟩

structure NodeBind (DA DB T : Nat → Nat) : Prop where
  dag : ∀ j < 5282, (towerDag ())[j]! = ((DA j : Int) - 4, DB j)
  node : ∀ j < 5282, nodeK DA DB T j = true
  inv : ∀ j < 5282, DA j = 3 → inv22 (unpackR 22 (T (DB j))) = unpackR 22 (T j)
  r1 : r1Rows = unpackR 22 (T 1)
  r2 : r2Rows = unpackR 22 (T 2)

theorem towerDag_size : (towerDag ()).size = 5282 := by
  unfold towerDag
  rw [Array.size_ofFn]
  rfl

theorem push_get {A : Array (Array Nat)} {x : Array Nat} {j : Nat} (hj : j < A.size) :
    (A.push x)[j]! = A[j]! := by
  rw [getElem!_pos _ j (by simp; omega), getElem!_pos _ j hj, Array.getElem_push_lt]

theorem push_last {A : Array (Array Nat)} {x : Array Nat} : (A.push x)[A.size]! = x := by
  rw [getElem!_pos _ _ (by simp), Array.getElem_push_eq]

theorem nodeStep_val {DA DB T : Nat → Nat} (hb : NodeBind DA DB T) {i : Nat} (hi : i < 5282)
    {acc : Array (Array Nat)} (hg : ∀ j < i, acc[j]! = unpackR 22 (T j)) :
    nodeStep acc ((DA i : Int) - 4, DB i) = acc.push (unpackR 22 (T i)) := by
  obtain ⟨k2, k1, k0, k3, k4⟩ := nodeK_spec (hb.node i hi)
  unfold nodeStep
  dsimp only
  by_cases e2 : DA i = 2
  · rw [ite_eq_left (by omega), k2 e2, id22_eq]
  rw [ite_eq_right (by omega)]
  by_cases e1 : DA i = 1
  · rw [ite_eq_left (by omega), k1 e1, hb.r1]
  rw [ite_eq_right (by omega)]
  by_cases e0 : DA i = 0
  · rw [ite_eq_left (by omega), k0 e0, hb.r2]
  rw [ite_eq_right (by omega)]
  by_cases e3 : DA i = 3
  · rw [ite_eq_left (by omega), hg _ (k3 e3).1, hb.inv i hi e3]
  rw [ite_eq_right (by omega)]
  obtain ⟨ha, hb', ht⟩ := k4 (by omega)
  have et : ((DA i : Int) - 4).toNat = DA i - 4 := by omega
  rw [et, hg _ ha, hg _ hb', mul22_unpack, ← ht]

theorem foldl_nodeStep {DA DB T : Nat → Nat} (hb : NodeBind DA DB T) (D : Array (Int × Nat))
    (hD : D.size = 5282) (hDj : ∀ j < 5282, D[j]! = ((DA j : Int) - 4, DB j)) :
    (D.foldl nodeStep #[]).size = 5282 ∧
      ∀ j < 5282, (D.foldl nodeStep #[])[j]! = unpackR 22 (T j) := by
  have h := Array.foldl_induction (as := D) (f := nodeStep) (init := #[])
    (fun i acc => acc.size = i ∧ ∀ j < i, acc[j]! = unpackR 22 (T j))
    ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    (fun i acc hacc => by
      obtain ⟨hs, hg⟩ := hacc
      have hi : i.1 < 5282 := hD ▸ i.2
      have e : D[i] = ((DA i : Int) - 4, DB i) := by
        rw [Fin.getElem_fin, ← getElem!_pos D i.1 i.2]
        exact hDj i hi
      rw [e, nodeStep_val hb hi hg]
      refine ⟨by simp [hs], fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · rw [push_get (by omega), hg j hj]
      · subst hj
        rw [← hs, push_last, hs])
  obtain ⟨h1, h2⟩ := h
  exact ⟨h1.trans hD, fun j hj => h2 j (hD ▸ hj)⟩

theorem nodeMats_eq {DA DB T : Nat → Nat} (hb : NodeBind DA DB T) :
    (nodeMats ()).size = 5282 ∧ ∀ j < 5282, (nodeMats ())[j]! = unpackR 22 (T j) := by
  unfold nodeMats
  exact foldl_nodeStep hb _ towerDag_size hb.dag

theorem nodesOK_of {DA DB T : Nat → Nat} (hb : NodeBind DA DB T) : nodesOK () = true := by
  obtain ⟨hs, hg⟩ := nodeMats_eq hb
  unfold nodesOK
  rw [List.all_eq_true]
  intro j hjm
  have hj : j < 5282 := List.mem_range.1 hjm
  obtain ⟨k2, k1, k0, k3, k4⟩ := nodeK_spec (hb.node j hj)
  unfold nodeOK
  rw [hb.dag j hj]
  dsimp only
  by_cases e2 : DA j = 2
  · rw [ite_eq_left (by omega), hg j hj, k2 e2, id22_eq]
    exact eq22_self _ (unpackR_size _)
  rw [ite_eq_right (by omega)]
  by_cases e1 : DA j = 1
  · rw [ite_eq_left (by omega), hg j hj, k1 e1, ← hb.r1]
    exact eq22_self _ (by decide)
  rw [ite_eq_right (by omega)]
  by_cases e0 : DA j = 0
  · rw [ite_eq_left (by omega), hg j hj, k0 e0, ← hb.r2]
    exact eq22_self _ (by decide)
  rw [ite_eq_right (by omega)]
  by_cases e3 : DA j = 3
  · obtain ⟨h1, h2⟩ := k3 e3
    rw [ite_eq_left (by omega), hg j hj, hg _ (by omega), mul22_unpack, h2, ← id22_eq,
      Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h1, eq22_self _ (by simp [id22])⟩
  rw [ite_eq_right (by omega)]
  obtain ⟨ha, hb', ht⟩ := k4 (by omega)
  have et : ((DA j : Int) - 4).toNat = DA j - 4 := by omega
  rw [et, hg j hj, hg _ (by omega), hg _ (by omega), mul22_unpack, ← ht]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨by omega, by omega⟩, by omega⟩, eq22_self _ (unpackR_size _)⟩

theorem sizesOK_of {DA DB T : Nat → Nat} (hb : NodeBind DA DB T) : sizesOK () = true := by
  simp [sizesOK, (nodeMats_eq hb).1, towerDag_size, dagSize]

theorem allL_spec {bs : List Nat} {f : Nat → Bool} (h : allL bs f = true) : ∀ c ∈ bs, f c = true := by
  induction bs with
  | nil => simp
  | cons c bs ih =>
    have e : allL (c :: bs) f = bAnd(f c, allL bs f) := rfl
    rw [e, bAnd_eq, Bool.and_eq_true] at h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact ih h.2 x hx

theorem strict_of_succ {f S : Nat → Nat} {len : Nat}
    (h : ∀ m, m + 1 < len → f (S m) < f (S (m + 1))) :
    ∀ a b, a < b → b < len → f (S a) < f (S b) := by
  intro a b hab hb
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h' | rfl
    · exact lt_trans (ih h' (by omega)) (h b hb)
    · exact h a hb

theorem inj_of_sorted {f S : Nat → Nat} {len : Nat} (hS : ∀ m < len, S m < len)
    (h : ∀ m, m + 1 < len → f (S m) < f (S (m + 1))) :
    ∀ a < len, ∀ b < len, f a = f b → a = b := by
  have hst := strict_of_succ h
  have hinj : Function.Injective (fun m : Fin len => (⟨S m, hS m m.2⟩ : Fin len)) := by
    intro x y e
    have e' : S x = S y := congrArg Fin.val e
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hl | hl
    · have := hst _ _ hl y.2
      rw [e'] at this
      exact lt_irrefl _ this
    · have := hst _ _ hl x.2
      rw [e'] at this
      exact lt_irrefl _ this
  have hsurj := (Finite.injective_iff_surjective.1 hinj)
  intro a ha b hb e
  obtain ⟨x, hx⟩ := hsurj ⟨a, ha⟩
  obtain ⟨y, hy⟩ := hsurj ⟨b, hb⟩
  have hx' : S x = a := congrArg Fin.val hx
  have hy' : S y = b := congrArg Fin.val hy
  rw [← hx', ← hy'] at e ⊢
  by_contra hne
  rcases Nat.lt_or_gt_of_ne (fun h => hne (congrArg S h)) with hl | hl
  · exact absurd e (ne_of_lt (hst _ _ hl y.2))
  · exact absurd e.symm (ne_of_lt (hst _ _ hl x.2))

theorem srtK_spec {V S : Nat → Nat} {off len : Nat} (h : ∀ m < len, srtK V S off len m = true) :
    (∀ m < len, S m < len) ∧ ∀ m, m + 1 < len → V (off + S m) < V (off + S (m + 1)) := by
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · have := h m hm
    unfold srtK at this
    rw [bAnd_eq, Bool.and_eq_true] at this
    exact Nat.le_of_ble_eq_true this.1
  · have := h m (by omega)
    have hb : Nat.blt (Nat.succ m) len = true := Nat.ble_eq_true_of_le hm
    unfold srtK at this
    rw [bAnd_eq, Bool.and_eq_true, bIf_eq', ite_eq_left hb] at this
    exact Nat.le_of_ble_eq_true this.2

theorem ptK_spec {V W T : Nat → Nat} {off b k : Nat} {bs : List Nat}
    (h : ptK V W T off b bs k = true) :
    V (off + k) < 2 ^ 22 ∧ W (off + k) < 5282 ∧ vmF 22 (T (W (off + k))) b = V (off + k) ∧
      ∀ c ∈ bs, vmF 22 (T (W (off + k))) c = c := by
  unfold ptK at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2, Nat.eq_of_beq_eq_true h3,
    fun c hc => Nat.eq_of_beq_eq_true (allL_spec h4 c hc)⟩

theorem levelOK_of {DA DB T V W S : Nat → Nat} (hb : NodeBind DA DB T) {i : Nat}
    (hP : ∀ k < 4802, (towerPointsAll ())[k]! = (V k, W k))
    (hlen : levelOffsets[i + 1]! - levelOffsets[i]! = towerLevels[i]!.2)
    (hoff : levelOffsets[i + 1]! ≤ 4802) (hbase : towerLevels[i]!.1 < 2 ^ 22)
    (hpt : ∀ k < towerLevels[i]!.2, ptK V W T levelOffsets[i]! towerLevels[i]!.1
      ((List.range i).map fun k => towerLevels[k]!.1) k = true)
    (hsrt : ∀ m < towerLevels[i]!.2, srtK V S levelOffsets[i]! towerLevels[i]!.2 m = true) :
    levelOK (towerPointsAll ()) (nodeMats ()) i = true := by
  obtain ⟨hs, hg⟩ := nodeMats_eq hb
  have hpts : levelPoints (towerPointsAll ()) i = (List.range towerLevels[i]!.2).map
      fun k => (V (levelOffsets[i]! + k), W (levelOffsets[i]! + k)) := by
    unfold levelPoints
    rw [hlen]
    refine List.map_congr_left fun k hk => hP _ ?_
    have := List.mem_range.1 hk
    omega
  unfold levelOK
  dsimp only
  rw [hpts]
  obtain ⟨hS1, hS2⟩ := srtK_spec hsrt
  have hinj := inj_of_sorted (f := fun x => V (levelOffsets[i]! + x)) hS1 hS2
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨?_, decide_eq_true hbase⟩, ?_⟩, ?_⟩
  · simp
  · apply decide_eq_true
    rw [List.map_map]
    refine List.Nodup.map_on (fun x hx y hy e => ?_) List.nodup_range
    exact hinj x (List.mem_range.1 hx) y (List.mem_range.1 hy) e
  · rw [List.all_eq_true]
    intro p hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hp
    have hk' := List.mem_range.1 hk
    obtain ⟨h1, h2, h3, h4⟩ := ptK_spec (hpt k hk')
    dsimp only
    rw [hs, hg _ h2, act22_unpack, h3]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_self_eq_true, and_true, List.all_eq_true,
      List.mem_range, beq_iff_eq]
    refine ⟨⟨h1, h2⟩, fun k' hk2 => ?_⟩
    rw [act22_unpack, h4 _ (List.mem_map.2 ⟨k', List.mem_range.2 hk2, rfl⟩)]

end CFSG.KC.Tower

end
