module

public import CFSG.Certificates.Kernel.SporSch.HNXCnt.Asm
public import CFSG.Certificates.Kernel.SporSch.HNXCnt.Core
public import CFSG.Certificates.Kernel.SporSch.HNXCnt.Count
public import CFSG.Certificates.Kernel.SporSch.HNXCnt.Seed
public import CFSG.Certificates.Kernel.SporSch.HNXCnt.Lanes
public import CFSG.Certificates.Kernel.SporSch.HNXCnt.Spread
public import CFSG.Certificates.Kernel.SporSch.HNXCertSound

public section

namespace CFSG.KS.SporSch.HNXP

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KS.SporSch CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.F5.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.He.Native CFSG.KS.Ord
open Finset

theorem andB_true' {a b : Bool} (h : CFSG.KC.Ord.andB a b = true) : a = true ∧ b = true := by
  revert h
  cases a <;> cases b <;> decide

theorem constsM {CM3 M : Nat} (hc : constsOK CM3 M = true) : M = 2 ^ 399 - 1 := by
  unfold constsOK at hc
  have h := ((CFSG.KS.bAnd_iff _ _).1 hc).2
  have e := Nat.eq_of_beq_eq_true h
  rw [e]
  change (1 <<< 399) - 1 = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem xv_leaf (T : Nat → Nat) (b r : Nat) (hr : r < 64) :
    xv T (64 * b + r) = T b / 2 ^ (464 * r) % 2 ^ 399 := by
  unfold xv
  rw [fldW_eq, getRec_leaf T b r hr, Nat.pow_zero, Nat.div_one,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by norm_num))]

theorem leaf_split {i : Nat} (hi : i < 1140000) :
    i = 64 * (i / 64) + i % 64 ∧ i / 64 < 17813 ∧ i % 64 < hnxC (i / 64) := by
  refine ⟨(Nat.div_add_mod i 64).symm, by omega, ?_⟩
  rw [hnxC_eq]
  split <;> omega

theorem hnxC_le (b : Nat) : hnxC b ≤ 64 := by
  rw [hnxC_eq]
  split <;> omega

theorem rootRun_spec {V : Nat} : ∀ (cs : List Char) (k : Nat), rootRun V cs k = true →
    k + cs.length = 133 ∧ V < 2 ^ 399 ∧ ∀ m (hm : m < cs.length),
      48 ≤ (cs[m]).toNat ∧ (cs[m]).toNat ≤ 52 ∧ (cs[m]).toNat - 48 = V / 2 ^ (3 * (k + m)) % 8
  | [], k, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false
        (Nat.blt V (Nat.shiftLeft (nat_lit 1) (nat_lit 399))) (Nat.beq k (nat_lit 133)) = true := h
    obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h'
    have e1 := Nat.eq_of_beq_eq_true h1
    have e2 : V < 1 <<< 399 := Nat.blt_eq.mp h2
    rw [Nat.shiftLeft_eq, Nat.one_mul] at e2
    exact ⟨by simpa using e1, e2, fun m hm => absurd hm (by simp)⟩
  | ch :: cs, k, h => by
    have h' : strictB (Char.toNat ch) (fun c =>
        Bool.rec (motive := fun _ => Bool) false
          (Bool.rec (motive := fun _ => Bool) false
            (Bool.rec (motive := fun _ => Bool) false
              (strictB (Nat.succ k) (rootRun V cs))
              (Nat.beq (Nat.sub c (nat_lit 48)) (fldW V (Nat.mul (nat_lit 3) k) (nat_lit 3))))
            (Nat.ble c (nat_lit 52)))
          (Nat.ble (nat_lit 48) c)) = true := h
    rw [strictB_eq] at h'
    obtain ⟨h1, h'⟩ := (CFSG.KS.bAnd_iff _ _).1 h'
    obtain ⟨h2, h'⟩ := (CFSG.KS.bAnd_iff _ _).1 h'
    obtain ⟨h3, h4⟩ := (CFSG.KS.bAnd_iff _ _).1 h'
    rw [strictB_eq] at h4
    obtain ⟨ih1, ih2, ih3⟩ := rootRun_spec cs (Nat.succ k) h4
    have e1 : 48 ≤ ch.toNat := Nat.le_of_ble_eq_true h1
    have e2 : ch.toNat ≤ 52 := Nat.le_of_ble_eq_true h2
    have e3 : ch.toNat - 48 = fldW V (3 * k) 3 := Nat.eq_of_beq_eq_true h3
    rw [fldW_eq] at e3
    refine ⟨by simp only [List.length_cons]; omega, ih2, fun m hm => ?_⟩
    rcases m with _ | m
    · simp only [List.getElem_cons_zero, Nat.add_zero]
      exact ⟨e1, e2, by rw [e3]; rfl⟩
    · simp only [List.getElem_cons_succ]
      obtain ⟨a, b, c⟩ := ih3 m (by simp at hm; omega)
      refine ⟨a, b, ?_⟩
      rw [c]
      congr 3
      omega

theorem char_le_iff (c d : Char) : (c ≤ d) ↔ c.toNat ≤ d.toNat := UInt32.le_iff_toNat_le

theorem root_vec {V : Nat} {cs : List Char} (h : rootK V cs = true) :
    orbitVector 133 V = bytesOfDigits (String.ofList cs) ∧ V < 2 ^ 399 ∧
      ∀ j < 133, V / 2 ^ (3 * j) % 8 < 5 := by
  obtain ⟨hl, hV, hc⟩ := rootRun_spec cs 0 h
  simp only [Nat.zero_add] at hl hc
  refine ⟨?_, hV, fun j hj => ?_⟩
  · unfold orbitVector bytesOfDigits
    rw [String.toList_ofList]
    congr 1
    congr 1
    apply List.ext_getElem
    · rw [List.length_ofFn, List.length_map, hl]
    · intro m h1 h2
      simp only [List.getElem_ofFn, List.getElem_map]
      have hm : m < cs.length := by simpa using h2
      obtain ⟨a, b, c⟩ := hc m hm
      have hd : ('0' ≤ cs[m] && cs[m] ≤ '9') = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq, char_le_iff]
        exact ⟨by simpa using a, by have : '9'.toNat = 57 := rfl; omega⟩
      rw [hd, if_pos rfl, Nat.shiftRight_eq_div_pow, ← c]
      rfl
  · obtain ⟨a, b, c⟩ := hc j (by omega)
    omega

section Kernel

variable {D : F5Data} {T CNT SGT : Nat → Nat} {MS CM3 M GA GB W1 W2 V0C : Nat}
  {cs1 cs2 cr : List Char}

theorem core_at (h : HNXChecks D T CNT SGT MS CM3 M GA GB W1 W2 V0C cs1 cs2 cr)
    (hcnt : ∀ b < 17813, CNT b < 1048576) {i : Nat} (hi : i < 1140000) :
    CoreRec T 1140000 MS (mulC CM3 (leafA (T (i / 64)) 464 (hnxC (i / 64)) M) GA)
      (mulC CM3 (leafA (T (i / 64)) 464 (hnxC (i / 64)) M) GB) i (i % 64) := by
  obtain ⟨e, hb, hr⟩ := leaf_split hi
  have hc := h.2.2.2.2.2.2.2.2.2.2.1 (i / 64) hb
  have hlt : coreLeaf T 464 1140000 MS CM3 M GA GB (i / 64) (hnxC (i / 64)) < 1048576 := by
    rw [Nat.eq_of_beq_eq_true hc]; exact hcnt _ hb
  have := (coreLeaf_sound (hnxC_le _) hlt).1 (i % 64) hr
  rwa [← e] at this

theorem core_count (h : HNXChecks D T CNT SGT MS CM3 M GA GB W1 W2 V0C cs1 cs2 cr)
    (hcnt : ∀ b < 17813, CNT b < 1048576) :
    ∑ i ∈ range 1140000, ((if pp T (qv T 0 i) = 2 * i + 1 then 1 else 0) +
      (if pp T (qv T 1 i) = 2 * i + 2 then 1 else 0)) = 1140000 - 1 := by
  rw [← sum_leaves]
  have hsum := Nat.eq_of_beq_eq_true h.2.2.2.2.2.2.2.2.2.2.2.1
  rw [sumK_eq] at hsum
  rw [show (1140000 - 1 : Nat) = 1139999 from rfl, ← hsum]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hb' := Finset.mem_range.1 hb
  have hc := h.2.2.2.2.2.2.2.2.2.2.1 b hb'
  have hlt : coreLeaf T 464 1140000 MS CM3 M GA GB b (hnxC b) < 1048576 := by
    rw [Nat.eq_of_beq_eq_true hc]; exact hcnt _ hb'
  rw [← Nat.eq_of_beq_eq_true hc, (coreLeaf_sound (hnxC_le _) hlt).2]

theorem img_lanes {CM3 M MS G W : Nat} (hc : constsOK CM3 M = true) (hm : masksOK MS = true)
    (hG : G = trM W) (hv : validHN W = true) {T : Nat → Nat} {b c r t : Nat} (hc64 : c ≤ 64)
    (hr : r < c)
    (he : fldW (mulC CM3 (leafA (T b) 464 c M) G) (1729 * r) 1729 = spread MS (xv T t)) :
    ∀ l < 133, xe T t l = (∑ k ∈ range 133, xe T (64 * b + r) k * ent13 W l k) % 5 := by
  intro l hl
  have e1 : fldW (mulC CM3 (leafA (T b) 464 c M) G) (1729 * r) 1729 / 2 ^ (13 * l) % 2 ^ 13 =
      spread MS (xv T t) / 2 ^ (13 * l) % 2 ^ 13 := by rw [he]
  rw [row_lane _ _ _ hl, spread_lane hm (by have := xv_lt T t; simpa using this) l hl] at e1
  rw [mulC_lane hc (a := fun r => if r < c then T b / 2 ^ (464 * r) % 2 ^ 399 else 0)
    (leafA_eq hc (T b) c hc64) (fun r _ => by
      split
      · exact Nat.mod_lt _ (Nat.two_pow_pos _)
      · exact Nat.two_pow_pos _)
    (g := fun k l => ent13 W l k) (by rw [hG, trM_eq])
    (fun k hk l hl => (validHN_spec hv).2 l hl k hk) r (by omega) l hl] at e1
  unfold xe
  rw [← e1]
  refine congrArg (· % 5) (Finset.sum_congr rfl fun k _ => ?_)
  simp only [if_pos hr]
  rw [xv_leaf T b r (by omega)]

theorem gf_of_checks (h : HNXChecks D T CNT SGT MS CM3 M GA GB W1 W2 V0C cs1 cs2 cr)
    (hcnt : ∀ b < 17813, CNT b < 1048576) (hvA : validHN W1 = true) (hvB : validHN W2 = true)
    (hA2 : Nat.beq (CFSG.KC.LL.HN.mm W1 W1) CFSG.KD.OrdHN.ONE = true)
    (hB3 : Nat.beq (CFSG.KC.LL.HN.mm (CFSG.KC.LL.HN.mm W2 W2) W2) CFSG.KD.OrdHN.ONE = true) :
    GF T W1 W2 := by
  have hcount := core_count h hcnt
  have hR := fun {i} (hi : i < 1140000) => core_at h hcnt hi
  obtain ⟨-, -, -, -, -, hcm, -, -, hGA, hGB, -, -, hsort, hlink, hrec0, hroot⟩ := h
  obtain ⟨hc, hm⟩ := andB_true' hcm
  have eGA : GA = trM W1 := (Nat.eq_of_beq_eq_true hGA).symm
  have eGB : GB = trM W2 := (Nat.eq_of_beq_eq_true hGB).symm
  have imgA : ∀ i < 1140000, ∀ l < 133,
      xe T (qv T 0 i) l = (∑ k ∈ range 133, xe T i k * ent13 W1 l k) % 5 := by
    intro i hi
    obtain ⟨e, hb, hr⟩ := leaf_split hi
    have := img_lanes hc hm eGA hvA (hnxC_le _) hr (hR hi).2.2.2.1
    rwa [← e] at this
  have imgB : ∀ i < 1140000, ∀ l < 133,
      xe T (qv T 1 i) l = (∑ k ∈ range 133, xe T i k * ent13 W2 l k) % 5 := by
    intro i hi
    obtain ⟨e, hb, hr⟩ := leaf_split hi
    have := img_lanes hc hm eGB hvB (hnxC_le _) hr (hR hi).2.2.2.2.2.2.1
    rwa [← e] at this
  have q_lt : ∀ i < 1140000, ∀ s < 2, qv T s i < 1140000 := by
    intro i hi s hs
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
    · exact (hR hi).2.2.1
    · exact (hR hi).2.2.2.2.2.1
  have pp0 : pp T 0 = 0 := (hR (i := 0) (by norm_num)).1 rfl
  have first := first_of_count (pp := pp T) (q := fun s i => qv T s i) q_lt pp0 hcount
  have hx0 : xv T 0 = V0C := by
    have e := Nat.eq_of_beq_eq_true hrec0
    rw [constsM hc] at e
    rw [← e]
    unfold xv
    rw [fldW_eq, Nat.pow_zero, Nat.div_one]
    change _ = getRec T 464 0 &&& (2 ^ 399 - 1)
    rw [Nat.and_two_pow_sub_one_eq_mod]
  refine ⟨q_lt, imgA, imgB, ?_, sort_inj hsort hlink, pp0, ?_, ?_, first, sq_one hvA hA2,
    cube_one hvB hB3⟩
  · intro t ht j hj
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · unfold xe
      rw [hx0]
      exact (root_vec hroot).2.2 j hj
    · obtain ⟨i, hi, s, hs, hqs, -⟩ := first t ht0 ht
      rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
      · rw [← hqs, imgA i hi j hj]; exact Nat.mod_lt _ (by norm_num)
      · rw [← hqs, imgB i hi j hj]; exact Nat.mod_lt _ (by norm_num)
  · intro i hi0 hi
    exact ⟨((hR hi).2.1 hi0).2, ((hR hi).2.1 hi0).1⟩
  · intro i hi s hs
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
    · exact (hR hi).2.2.2.2.1
    · exact (hR hi).2.2.2.2.2.2.2

end Kernel

end CFSG.KS.SporSch.HNXP

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX
open CFSG.Sporadic.F5.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.HNSchreier.Native

theorem orbitCert_sound_of_cnt {D : F5Data} {T CNT SGT : Nat → Nat}
    {MS CM3 M GA GB W1 W2 V0C QG : Nat}
    {cs1 cs2 cr : List Char} {Q : List Nat} {P : PackedOrbitData}
    (h : HNXChecks D T CNT SGT MS CM3 M GA GB W1 W2 V0C cs1 cs2 cr)
    (hcnt : ∀ b < 17813, CNT b < 1048576)
    (hO : D.orbit () = P.toOrbit) (hP : hnxBindK T P = true)
    (hexp : D.expA = 2 ∧ D.expB = 3) (hvA : validHN W1 = true) (hvB : validHN W2 = true)
    (hone : isIdK CFSG.KD.OrdHN.ONE = true)
    (hA2 : Nat.beq (CFSG.KC.LL.HN.mm W1 W1) CFSG.KD.OrdHN.ONE = true)
    (hB3 : Nat.beq (CFSG.KC.LL.HN.mm (CFSG.KC.LL.HN.mm W2 W2) W2) CFSG.KD.OrdHN.ONE = true)
    (hQ : D.Q.toList = Q) (hQn : ∀ q ∈ Q, q < 1140000) (hbasis : qBasisK T CM3 Q QG = true) :
    (matrixChecks D && orbitChecks D (D.orbit ()) 3 &&
      bfsOrderOK D.n (D.orbit ()).alpha (D.orbit ()).beta) = true := by
  have hg := HNXP.gf_of_checks h hcnt hvA hvB hA2 hB3
  obtain ⟨hd, hn, hsA, hsB, hroot, hcm, hseedA, hseedB, -, -, -, -, -, -, hrec0, hrootK⟩ := h
  obtain ⟨hc, -⟩ := HNXP.andB_true' hcm
  obtain ⟨hQl, hG5, hXG⟩ := HNXP.qBasisK_sound hc hbasis
  have hx0 : HNXP.xv T 0 = V0C := by
    have e := Nat.eq_of_beq_eq_true hrec0
    rw [HNXP.constsM hc] at e
    rw [← e]
    unfold HNXP.xv
    rw [HNXP.fldW_eq, Nat.pow_zero, Nat.div_one]
    change _ = getRec T 464 0 &&& (2 ^ 399 - 1)
    rw [Nat.and_two_pow_sub_one_eq_mod]
  refine HNXP.native_goal (G := fun k l => HNXP.ent13 QG k l) hg hP hO hd hn hexp
    (fun i hi j hj => ?_) (fun i hi j hj => ?_) ?_ hQ hQl hQn hG5 hXG
  · change ((CFSG.Sporadic.He.Native.rowsOf 5 D.d D.seedA)[i]!)[j]! = _
    rw [hd, hsA]
    exact HNXP.seedRK_rows hseedA i hi j hj
  · change ((CFSG.Sporadic.He.Native.rowsOf 5 D.d D.seedB)[i]!)[j]! = _
    rw [hd, hsB]
    exact HNXP.seedRK_rows hseedB i hi j hj
  · change bytesOfDigits D.root = _
    rw [hroot, hx0]
    exact (HNXP.root_vec hrootK).1.symm

end CFSG.KS.SporSch

end
