
module

public import Certificates.Data.Kernel.SporSch.HNF5KronT
public import CFSG.Certificates.Kernel.SporSch.HNF5KronSound
public import CFSG.Certificates.Kernel.SporSch.HNF5RankSound
import CFSG.Certificates.Kernel.PackSetSound

public section

namespace CFSG.KS.SporSch.F5Kron

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.KS.SporSch.F5Lane Finset

attribute [local irreducible] krConst

set_option exponentiation.threshold 2200

theorem lane_inj {ι : Type*} (I : Finset ι) (v p : ι → Nat) (n : Nat) (hp : ∀ i ∈ I, p i < n)
    (hv : ∀ i ∈ I, v i < 2 ^ 16) (hinj : ∀ a ∈ I, ∀ b ∈ I, p a = p b → a = b) {i0 : ι}
    (hi0 : i0 ∈ I) {t : Nat} (ht : p i0 = t) : lane5 (∑ i ∈ I, v i * 2 ^ (16 * p i)) t = v i0 := by
  subst ht
  have hcard : ∀ t, (I.filter fun i => p i = t).card ≤ 1 := fun t =>
    Finset.card_le_one.2 fun a ha b hb => by
      rw [Finset.mem_filter] at ha hb
      exact hinj a ha.1 b hb.1 (ha.2.trans hb.2.symm)
  have hv' : ∀ i ∈ I, v i ≤ 65535 := fun i hi => by
    have h := hv i hi
    norm_num at h
    omega
  have hb : ∀ t < n, ∑ i ∈ I with p i = t, v i < 2 ^ 16 := fun t _ =>
    fib1 I v _ hv' (by norm_num) (hcard t)
  rw [lane_fiber I v p n hp hb (hp i0 hi0)]
  have e : (I.filter fun i => p i = p i0) = {i0} := by
    ext i
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · exact fun h => hinj i h.1 i0 hi0 h.2
    · rintro rfl
      exact ⟨hi0, rfl⟩
  rw [e, Finset.sum_singleton]

theorem krP2_eq : krP2 = range 133 ×ˢ range 133 :=
  Finset.ext fun i => by rw [mem_krP2, Finset.mem_product, mem_range, mem_range]

theorem krColF_eq {Y : Nat → Nat} (hY : Canon5 Y) :
    krColF (krConst 1 264) (krConst 65535 265) Y = ∑ i ∈ krP2,
      lane5 (Y i.1) i.2 * 2 ^ (16 * (265 * i.2 + i.1)) := by
  unfold krColF
  rw [krP2_eq]
  rw [CFSG.KC.Pack.foldN_eq, foldr_range_add (fun j => krSpr (krConst 1 264) (krConst 65535 265) (Y j)
    * 2 ^ (16 * j)), Nat.zero_add, Finset.sum_product]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [krSpr_eq (hY j (mem_range.1 hj)), Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Nat.mul_add 16, Nat.pow_add]
    ring
  · intro j acc
    change acc + _ <<< (16 * j) = _
    rw [Nat.shiftLeft_eq]

theorem krRowF_eq {X : Nat → Nat} (hX : Canon5 X) :
    krRowF X = ∑ i ∈ krP2, lane5 (X i.1) i.2 * 2 ^ (16 * (265 * i.1 + i.2)) := by
  unfold krRowF
  rw [krP2_eq]
  rw [CFSG.KC.Pack.foldN_eq, foldr_range_add (fun c => X c * 2 ^ (16 * (265 * c))), Nat.zero_add,
    Finset.sum_product]
  · refine Finset.sum_congr rfl fun c hc => ?_
    conv_lhs => rw [row_expand (canon5_lt (hX c (mem_range.1 hc)))]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.mul_add 16, Nat.pow_add]
    ring
  · intro c acc
    change acc + X c <<< (4240 * c) = _
    rw [Nat.shiftLeft_eq]
    congr 3
    ring

theorem trRow5_lt (T : Nat → Nat) (i : Nat) : trRow5 T i < 2 ^ 2128 := by
  unfold trRow5
  rw [CFSG.KC.Pack.foldN_eq]
  have key : ∀ l : List Nat, (∀ j ∈ l, j < 133) → l.foldr (fun j acc => Nat.lor acc
      (Nat.shiftLeft (lane5 (T j) i) (Nat.mul 16 j))) 0 < 2 ^ 2128 := by
    intro l
    induction l with
    | nil => intro _; exact Nat.two_pow_pos _
    | cons j l ih =>
      intro hl
      rw [List.foldr_cons]
      refine Nat.or_lt_two_pow (ih fun x hx => hl x (List.mem_cons_of_mem _ hx)) ?_
      change _ <<< (16 * j) < _
      rw [Nat.shiftLeft_eq]
      have hj := hl j List.mem_cons_self
      calc _ < 2 ^ 16 * 2 ^ (16 * j) :=
            Nat.mul_lt_mul_of_pos_right (lane5_lt (T j) i) (Nat.two_pow_pos _)
        _ = 2 ^ (16 * (j + 1)) := by rw [← Nat.pow_add]; ring_nf
        _ ≤ 2 ^ 2128 := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact key _ fun j hj => List.mem_range.1 hj

theorem krTr_sound {Y X : Nat → Nat} (hY : Canon5 Y) (hX : Canon5 X)
    (h : Nat.beq (krColF (krConst 1 264) (krConst 65535 265) Y) (krRowF X) = true) :
    ∀ i < 133, trRow5 Y i = X i := by
  have he := Nat.eq_of_beq_eq_true h
  rw [krColF_eq hY, krRowF_eq hX] at he
  have hlane : ∀ c < 133, ∀ j < 133, lane5 (Y j) c = lane5 (X c) j := fun c hc j hj => by
    have hjc : ((j, c) : Nat × Nat) ∈ krP2 := mem_krP2.2 ⟨hj, hc⟩
    have hcj : ((c, j) : Nat × Nat) ∈ krP2 := mem_krP2.2 ⟨hc, hj⟩
    have A := lane_inj krP2 (fun i : Nat × Nat => lane5 (Y i.1) i.2)
      (fun i : Nat × Nat => 265 * i.2 + i.1) (265 * 133)
      (fun i hi => by rw [mem_krP2] at hi; omega) (fun i _ => lane5_lt _ _)
      (fun a ha b hb hab => by
        rw [mem_krP2] at ha hb
        exact Prod.ext (by omega) (by omega))
      hjc (t := 265 * c + j) rfl
    have B := lane_inj krP2 (fun i : Nat × Nat => lane5 (X i.1) i.2)
      (fun i : Nat × Nat => 265 * i.1 + i.2) (265 * 133)
      (fun i hi => by rw [mem_krP2] at hi; omega) (fun i _ => lane5_lt _ _)
      (fun a ha b hb hab => by
        rw [mem_krP2] at ha hb
        exact Prod.ext (by omega) (by omega))
      hcj (t := 265 * c + j) rfl
    exact A.symm.trans ((congrArg (fun z => lane5 z (265 * c + j)) he).trans B)
  intro c hc
  refine eq_of_lanes (trRow5_lt Y c) (canon5_lt (hX c hc)) fun j hj => ?_
  rw [lane5_trRow5 _ _ hj]
  exact hlane c hc j hj

theorem krBlkT_sound {MT OP L R : Nat → Nat} {a n : Nat} (h : krBlkT MT OP L R a n = true)
    {k : Nat} (hk1 : a ≤ k) (hk2 : k < a + n) :
    Canon5 (slice5 MT k) ∧
    (OP k = 0 → Canon5 (slice5 MT (L k)) → Canon5 (slice5 MT (R k)) →
      ∀ i < 133, vm5 (slice5 MT (R k)) (slice5 MT (L k) i) = slice5 MT k i) ∧
    (OP k = 1 → ∀ i < 133, slice5 MT (L k) i = slice5 MT k i) ∧
    (OP k = 3 → Canon5 (slice5 MT (L k)) →
      ∀ i < 133, trRow5 (slice5 MT (L k)) i = slice5 MT k i) := by
  unfold krBlkT at h
  simp only [CFSG.KC.Pack.strictB_eq] at h
  have hk := CFSG.KC.Pack.allBlk_spec h (k - a) (by omega)
  have e : Nat.add a (k - a) = k := by
    change a + (k - a) = k
    omega
  rw [e] at hk
  unfold krEntT at hk
  simp only [CFSG.KC.Pack.strictB_eq, CFSG.KC.Pack.band_iff] at hk
  obtain ⟨hcan, hrest⟩ := hk
  have hC : Canon5 (slice5 MT k) := fun i hi => krCanon_sound (CFSG.KC.Pack.allN_spec hcan i hi)
  refine ⟨hC, fun ho hl hr => ?_, fun ho => ?_, fun ho hl => ?_⟩
  · have e0 : Nat.beq 0 0 = true := rfl
    rw [ho, e0] at hrest
    exact krProd_sound hr hl hC hrest
  · have e1 : Nat.beq 1 0 = false := rfl
    have e2 : Nat.beq 1 1 = true := rfl
    rw [ho, e1, e2] at hrest
    intro i hi
    exact Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec hrest i hi)
  · have e1 : Nat.beq 3 0 = false := rfl
    have e2 : Nat.beq 3 1 = false := rfl
    have e3 : Nat.beq 3 3 = true := rfl
    rw [ho, e1, e2, e3] at hrest
    exact krTr_sound hl hC hrest

open CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native in
theorem chainK_eq {MT OP L R : Nat → Nat} {n : Nat}
    (hmul : ∀ k < n, OP k = 0 →
      ∀ i < 133, vm5 (slice5 MT (R k)) (slice5 MT (L k) i) = slice5 MT k i)
    (hcopy : ∀ k < n, OP k = 1 → ∀ i < 133, slice5 MT (L k) i = slice5 MT k i)
    (hcan : ∀ k < n, Canon5 (slice5 MT k)) {S Si : Array (Array (Array Nat))} {lt : Int → Nat}
    {w : List Int} {o : Nat} (hlet : ∀ l ∈ w, mletter S Si l = rows5 (slice5 MT (lt l)))
    (h : chainOK OP L R lt n w o = true) :
    mword S Si w = rows5 (slice5 MT (o + w.length - 1)) := by
  simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨h1, hlen⟩, hl⟩, ho⟩, hL⟩, hs⟩ := h
  have hlt : ∀ t < w.length, mletter S Si (w.getD t 0) = rows5 (slice5 MT (lt (w.getD t 0))) ∧
      lt (w.getD t 0) < n := fun t ht => by
    have hm : w.getD t 0 ∈ w := by
      rw [List.getD_eq_getElem _ _ ht]
      exact List.getElem_mem ht
    exact ⟨hlet _ hm, hl _ hm⟩
  have key : ∀ t, t < w.length →
      mword S Si (w.drop (w.length - 1 - t)) = rows5 (slice5 MT (o + t)) := by
    intro t
    induction t with
    | zero =>
      intro _
      have e : w.drop (w.length - 1 - 0) = [w.getD (w.length - 1) 0] := by
        rw [Nat.sub_zero, List.drop_eq_getElem_cons (by omega), List.drop_of_length_le (by omega),
          List.getD_eq_getElem _ _ (by omega)]
      rw [e, mword_one, (hlt _ (by omega)).1, mulM5_idR (hcan _ (hlt _ (by omega)).2),
        Nat.add_zero]
      have hc := hcopy o (by omega) ho
      rw [hL] at hc
      exact rows5_congr hc
    | succ t ih =>
      intro ht
      obtain ⟨⟨a, b⟩, c⟩ := hs t (by omega)
      have e : w.drop (w.length - 1 - (t + 1)) =
          w.getD (w.length - 2 - t) 0 :: w.drop (w.length - 1 - t) := by
        rw [List.drop_eq_getElem_cons (by omega), List.getD_eq_getElem _ _ (by omega)]
        congr 2 <;> omega
      have hm := hmul _ (by omega) a
      rw [b, c] at hm
      rw [e, mword, ih (by omega), (hlt _ (by omega)).1,
        mulM5_sound (hcan _ (hlt _ (by omega)).2) (hcan _ (by omega)) hm]
      rfl
  have := key (w.length - 1) (by omega)
  rwa [show w.length - 1 - (w.length - 1) = 0 by omega, List.drop_zero,
    show o + (w.length - 1) = o + w.length - 1 by omega] at this

end CFSG.KS.SporSch.F5Kron

end
