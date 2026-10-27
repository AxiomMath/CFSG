module

public import Certificates.Data.Kernel.Fi22Rk.Defs
public import Certificates.Data.Fi24Rank.Common
public import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.BfsPinBaseSound

public section

namespace CFSG.KC.Fi22RkS

open CFSG.KC.Enum CFSG.KC.Fi22Rk CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative

variable {n w : Nat}

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem bIf_eq (c a b : Bool) : Bool.rec (motive := fun _ => Bool) b a c = if c = true then a else b := by
  cases c <;> rfl

theorem get_unpack {P i : Nat} (hi : i < n) : (unpack n w P)[i]! = pg w (mask w) P i :=
  CFSG.KS.Raw.Orb.unpack_get hi

theorem rows_of {m K F : Nat} {R : Nat → Nat} (hm : 0 < m) (hsz : szOK m w = true)
    (h : rowsK m w K F R = true) :
    (rowsOf m (unpack (m * K) w F)).size = K ∧
      ∀ k < K, (rowsOf m (unpack (m * K) w F))[k]! = unpack m w (R k) ∧ PP m w (R k) := by
  have hs : (unpack (m * K) w F).size = m * K := Array.size_ofFn
  have hsize : (rowsOf m (unpack (m * K) w F)).size = K := by
    unfold rowsOf
    rw [Array.size_ofFn, hs, Nat.mul_div_cancel_left K hm]
  refine ⟨hsize, fun k hk => ?_⟩
  have h1 := allN_spec h k hk
  rw [strictB_eq] at h1
  obtain ⟨hp, hx⟩ := (bAnd_iff _ _).1 h1
  refine ⟨?_, PP_of_permOK hsz hp⟩
  have hle : k * m + m ≤ m * K := by
    have : k + 1 ≤ K := hk
    calc k * m + m = (k + 1) * m := by ring
      _ ≤ K * m := Nat.mul_le_mul_right m this
      _ = m * K := Nat.mul_comm K m
  have e1 : (rowsOf m (unpack (m * K) w F))[k]! =
      (unpack (m * K) w F).extract (k * m) (k * m + m) := by
    rw [getElem!_pos (rowsOf m (unpack (m * K) w F)) k (by rw [hsize]; exact hk)]
    unfold rowsOf
    rw [Array.getElem_ofFn]
  rw [e1]
  apply Array.ext
  · have e2 : (unpack m w (R k)).size = m := Array.size_ofFn
    rw [Array.size_extract, hs, Nat.min_eq_left hle, Nat.add_sub_cancel_left, e2]
  · intro x h2 h3
    have hxm : x < m := by simpa [unpack] using h3
    have l : ∀ (a : Array Nat) (y : Nat) (hy : y < a.size), a[y] = a[y]! := fun a y hy =>
      (getElem!_pos a y hy).symm
    have hkx : k * m + x < (unpack (m * K) w F).size := by
      rw [hs]
      have : k + 1 ≤ K := hk
      nlinarith
    rw [Array.getElem_extract, l _ _ hkx, l _ _ h3, get_unpack hxm,
      get_unpack (by rw [← hs]; exact hkx)]
    have e := Nat.eq_of_beq_eq_true (allN_spec hx x hxm)
    rw [← e]
    congr 1
    change k * m + x = m * k + x
    rw [Nat.mul_comm]

theorem canon_pc {p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) : canonK n w (mask w) (n * w) (pc n w p q) = true :=
  canonK_pcomp hp hq

theorem compA_pc {p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) :
    compA n (unpack n w p) (unpack n w q) = unpack n w (pc n w p q) :=
  compA_unpack hp hq

variable {A : Array (Array Nat)} {AK : Nat → Nat}

theorem multOK_of (hsz : szOK n w = true) (hA : ∀ k < 5, A[k]! = unpack n w (AK k))
    (hc : ∀ k < 5, canonK n w (mask w) (n * w) (AK k) = true) (h : multK n w AK = true) :
    multOK n A = true := by
  have cid := (PP.id (n := n) (w := w) hsz).1
  have hid : idA n = unpack n w (pidn n w) := idA_eq hsz
  unfold multK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  unfold multOK
  rw [Bool.and_eq_true, allLt_iff, allLt_iff]
  constructor
  · intro k hk
    rw [allLt_iff]
    intro l hl
    rw [hA k hk, hA l hl, compA_pc (hc k hk) (hc l hl), compA_pc (hc l hl) (hc k hk),
      eqA_unpack (canon_pc (hc k hk) (hc l hl)) (canon_pc (hc l hl) (hc k hk))]
    exact allN_spec (allN_spec h1 k hk) l hl
  · intro k hk
    change eqA n (compA n A[k]! (compA n A[k]! (compA n A[k]! (idA n)))) (idA n) = true
    have c1 := canon_pc (hc k hk) cid
    have c2 := canon_pc (hc k hk) c1
    rw [hA k hk, hid, compA_pc (hc k hk) cid, compA_pc (hc k hk) c1, compA_pc (hc k hk) c2,
      eqA_unpack (canon_pc (hc k hk) c2) cid]
    exact allN_spec h2 k hk

variable {PW : Nat → Nat}

theorem pow_of (hsz : szOK n w = true) (hA : ∀ k < 5, A[k]! = unpack n w (AK k))
    (hc : ∀ k < 5, canonK n w (mask w) (n * w) (AK k) = true) (h : powK n w AK PW = true)
    {k d : Nat} (hk : k < 5) (hd : d < 3) :
    powA n A[k]! d = unpack n w (PW (3 * k + d)) ∧ canonK n w (mask w) (n * w) (PW (3 * k + d)) =
      true := by
  have cid := (PP.id (n := n) (w := w) hsz).1
  have hid : idA n = unpack n w (pidn n w) := idA_eq hsz
  have h1 := allN_spec h k hk
  obtain ⟨e0, h1⟩ := (bAnd_iff _ _).1 h1
  obtain ⟨e1, e2⟩ := (bAnd_iff _ _).1 h1
  have e0' : PW (3 * k + 0) = pidn n w := Nat.eq_of_beq_eq_true e0
  have e1' : PW (3 * k + 1) = pc n w (AK k) (pidn n w) := Nat.eq_of_beq_eq_true e1
  have e2' : PW (3 * k + 2) = pc n w (AK k) (pc n w (AK k) (pidn n w)) := Nat.eq_of_beq_eq_true e2
  have c1 := canon_pc (hc k hk) cid
  interval_cases d
  · rw [e0']
    exact ⟨hid, cid⟩
  · rw [e1']
    refine ⟨?_, c1⟩
    change compA n A[k]! (idA n) = _
    rw [hA k hk, hid, compA_pc (hc k hk) cid]
  · rw [e2']
    refine ⟨?_, canon_pc (hc k hk) c1⟩
    change compA n A[k]! (compA n A[k]! (idA n)) = _
    rw [hA k hk, hid, compA_pc (hc k hk) cid, compA_pc (hc k hk) c1]

theorem layer_of {k N : Nat} {J J' : Nat → Nat} (h : layerK n w k N PW J J' = true)
    {i : Nat} (hi : i < N) :
    J i = pc n w (PW (3 * k + i % 3)) (J' (i / 3)) :=
  Nat.eq_of_beq_eq_true (allN_spec h i hi)

variable {J3 J2 J1 IK : Nat → Nat}

theorem iotaA_of (hsz : szOK n w = true) (hA : ∀ k < 5, A[k]! = unpack n w (AK k))
    (hc : ∀ k < 5, canonK n w (mask w) (n * w) (AK k) = true) (hp : powK n w AK PW = true)
    (h3 : layerK n w 3 9 PW J3 (pw4 PW)) (h2 : layerK n w 2 27 PW J2 J3)
    (h1 : layerK n w 1 81 PW J1 J2) (h0 : ∀ i < 243, IK i = pc n w (PW (i % 3)) (J1 (i / 3)))
    {i : Nat} (hi : i < 243) :
    iotaA n A i = unpack n w (IK i) ∧ canonK n w (mask w) (n * w) (IK i) = true := by
  have P := fun k (hk : k < 5) d (hd : d < 3) => pow_of hsz hA hc hp (k := k) (d := d) hk hd
  have d0 : dig i 0 = i % 3 := by simp [dig]
  have d1 : dig i 1 = i / 3 % 3 := by simp [dig]
  have d2 : dig i 2 = i / 3 / 3 % 3 := by simp [dig, Nat.div_div_eq_div_mul]
  have d3 : dig i 3 = i / 3 / 3 / 3 % 3 := by simp [dig, Nat.div_div_eq_div_mul]
  have d4 : dig i 4 = i / 3 / 3 / 3 / 3 := by
    simp only [dig, Nat.div_div_eq_div_mul]
    exact Nat.mod_eq_of_lt (by omega)
  have m3 : ∀ x, x % 3 < 3 := fun x => Nat.mod_lt _ (by decide)
  obtain ⟨E4, C4⟩ := P 4 (by decide) (i / 3 / 3 / 3 / 3) (by omega)
  obtain ⟨E3p, C3p⟩ := P 3 (by decide) (i / 3 / 3 / 3 % 3) (m3 _)
  have L3 := layer_of (k := 3) h3 (i := i / 3 / 3 / 3) (by omega)
  have E3 : compA n (powA n A[3]! (dig i 3)) (powA n A[4]! (dig i 4)) =
      unpack n w (J3 (i / 3 / 3 / 3)) := by
    rw [d3, d4, E3p, E4, compA_pc C3p C4, L3]
    rfl
  have C3 : canonK n w (mask w) (n * w) (J3 (i / 3 / 3 / 3)) = true := by
    rw [L3]
    exact canon_pc C3p C4
  obtain ⟨E2p, C2p⟩ := P 2 (by decide) (i / 3 / 3 % 3) (m3 _)
  have L2 := layer_of (k := 2) h2 (i := i / 3 / 3) (by omega)
  have E2 : compA n (powA n A[2]! (dig i 2)) (compA n (powA n A[3]! (dig i 3))
      (powA n A[4]! (dig i 4))) = unpack n w (J2 (i / 3 / 3)) := by
    rw [E3, d2, E2p, compA_pc C2p C3, L2]
  have C2 : canonK n w (mask w) (n * w) (J2 (i / 3 / 3)) = true := by
    rw [L2]
    exact canon_pc C2p C3
  obtain ⟨E1p, C1p⟩ := P 1 (by decide) (i / 3 % 3) (m3 _)
  have L1 := layer_of (k := 1) h1 (i := i / 3) (by omega)
  have E1 : compA n (powA n A[1]! (dig i 1)) (compA n (powA n A[2]! (dig i 2))
      (compA n (powA n A[3]! (dig i 3)) (powA n A[4]! (dig i 4)))) = unpack n w (J1 (i / 3)) := by
    rw [E2, d1, E1p, compA_pc C1p C2, L1]
  have C1 : canonK n w (mask w) (n * w) (J1 (i / 3)) = true := by
    rw [L1]
    exact canon_pc C1p C2
  obtain ⟨E0p, C0p⟩ := P 0 (by decide) (i % 3) (m3 _)
  have z : 3 * 0 + i % 3 = i % 3 := by omega
  rw [z] at E0p C0p
  have L0 := h0 i hi
  refine ⟨?_, by rw [L0]; exact canon_pc C0p C1⟩
  unfold iotaA
  rw [E1, d0, E0p, compA_pc C0p C1, L0]

theorem injOK_of {I : Array (Array Nat)} {SO : Nat → Nat} {p₀ : Nat} (hp : p₀ < n)
    (hI : ∀ i < 243, I[i]! = unpack n w (IK i)) (h : injK w p₀ IK SO = true) : injOK I p₀ = true := by
  have hinj := distinctK_inj h
  unfold injOK
  rw [allLt_iff]
  intro i hi
  rw [allLt_iff]
  intro j hj
  by_cases e : i = j
  · rw [e, beq_self_eq_true, Bool.true_or]
  · rw [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, hI i hi, hI j hj, get_unpack hp, get_unpack hp]
    exact Or.inr fun h' => e (hinj i hi j hj h')

theorem permOK_isInvA {p q : Nat} (h : permOK n w (mask w) (n * w) p q = true) :
    isInvA n (unpack n w p) (unpack n w q) = true := by
  obtain ⟨-, -, hf⟩ := CFSG.KS.Raw.Orb.permOK_facts h
  unfold isInvA
  rw [allLt_iff]
  intro i hi
  obtain ⟨h1, h2⟩ := hf i hi
  rw [get_unpack hi, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, get_unpack h1]
  exact ⟨h1, h2⟩

theorem isInvA_PP {p : Nat} (hp : PP n w p) :
    isInvA n (unpack n w p) (invCand n (unpack n w p)) = true := by
  rw [invCand_PP hp]
  exact permOK_isInvA (CFSG.KS.PinvS.permOK_pinvS hp.1 hp.2)

theorem permsOK_of {G mus : Array (Array Nat)} {GK MUK : Nat → Nat} (hAs : A.size = 5)
    (hGs : G.size = 2) (hMs : mus.size = 2)
    (hA : ∀ k < 5, A[k]! = unpack n w (AK k) ∧ PP n w (AK k))
    (hG : ∀ l < 2, G[l]! = unpack n w (GK l) ∧ PP n w (GK l))
    (hM : ∀ l < 2, mus[l]! = unpack 243 8 (MUK l) ∧ PP 243 8 (MUK l)) :
    permsOK n A G mus = true := by
  unfold permsOK
  simp only [Bool.and_eq_true, beq_iff_eq, allLt_iff]
  refine ⟨⟨⟨⟨⟨hAs, hGs⟩, hMs⟩, fun k hk => ?_⟩, fun l hl => ?_⟩, fun l hl => ?_⟩
  · rw [(hA k hk).1]
    exact isInvA_PP (hA k hk).2
  · rw [(hG l hl).1]
    exact isInvA_PP (hG l hl).2
  · rw [(hM l hl).1]
    exact isInvA_PP (hM l hl).2

theorem conjOK_of (hsz : szOK n w = true) {I G mus : Array (Array Nat)} {GK MUK : Nat → Nat}
    (hI : ∀ i < 243, I[i]! = unpack n w (IK i) ∧ canonK n w (mask w) (n * w) (IK i) = true)
    (hG : ∀ l < 2, G[l]! = unpack n w (GK l) ∧ PP n w (GK l))
    (hM : ∀ l < 2, mus[l]! = unpack 243 8 (MUK l))
    (h : ∀ l < 2, ∀ c < 16, conjC n w GK MUK IK l c = true) : conjOK n I G mus = true := by
  unfold conjOK
  rw [allLt_iff]
  intro l hl
  rw [allLt_iff]
  intro i hi
  have h1 := allN_spec (h l hl (i / 16) (by omega)) (i % 16) (Nat.mod_lt _ (by decide))
  rw [strictB_eq] at h1
  have ei : Nat.add (Nat.mul 16 (i / 16)) (i % 16) = i := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rw [ei, bIf_eq, if_pos (Nat.blt_eq.mpr hi)] at h1
  unfold conjAt at h1
  rw [strictB_eq, strictB_eq, strictB_eq] at h1
  obtain ⟨hj, he⟩ := (bAnd_iff _ _).1 h1
  have hj' := Nat.blt_eq.mp hj
  have hmu : (mus[l]!)[i]! = pg 8 255 (MUK l) i := by
    rw [hM l hl, get_unpack hi]
    rfl
  obtain ⟨hGe, hGp⟩ := hG l hl
  have cgi := (PP.inv hGp).1
  rw [Bool.and_eq_true, decide_eq_true_eq, hmu, hGe, invCand_PP hGp, (hI i hi).1,
    (hI _ hj').1, compA_pc (hI i hi).2 cgi, compA_pc hGp.1 (canon_pc (hI i hi).2 cgi),
    eqA_unpack (canon_pc hGp.1 (canon_pc (hI i hi).2 cgi)) (hI _ hj').2]
  exact ⟨hj', he⟩

end CFSG.KC.Fi22RkS

end
