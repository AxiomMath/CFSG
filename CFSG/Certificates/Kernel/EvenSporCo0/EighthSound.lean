module

public import Certificates.Data.Kernel.EvenSporCo0.Eighth
public import Certificates.Data.Kernel.BfsPin
public import CFSG.Certificates.Kernel.Spor.RawDefs
import CFSG.Certificates.Kernel.MonsterB.BfsReplaySound
import CFSG.Certificates.Kernel.MonsterB.PermBfsSound
import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.BfsPinBaseSound
import CFSG.Certificates.Kernel.Spor.PackWord
import all CFSG.Certificates.Kernel.Spor.PEnumSound
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.Loops
public import Certificates.Data.CFSGNative.Co3Schreier.Basic
import CFSG.Certificates.Kernel.BfsPinSound

public section

namespace CFSG.KC.EvenSporCo0

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KLie.CT CFSG.Monster.Code
  CFSG.Monster.B.TwoA.Census CFSG.EvenSporadicStandard.TwoCo1 CFSG.KC.Bfs CFSG.KC.BfsPin

theorem treeSumN_xor_lt (F m : ℕ → ℕ) :
    ∀ k j, j < k → ∀ a, treeSumN F m k (a ^^^ m j) = treeSumN F m k a
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | k + 1, j, h, a => by
    simp only [treeSumN]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · have e : a ^^^ m j ^^^ m k = (a ^^^ m k) ^^^ m j := by
        rw [Nat.xor_assoc, Nat.xor_comm (m j), ← Nat.xor_assoc]
      rw [treeSumN_xor_lt F m k j h a, e, treeSumN_xor_lt F m k j h (a ^^^ m k)]
    · rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.add_comm]

theorem treeSumN_xorSub (F m : ℕ → ℕ) (s : ℕ) :
    ∀ k' k, k' ≤ k → ∀ a, treeSumN F m k (a ^^^ xorSub m s k') = treeSumN F m k a
  | 0, _, _, a => by simp [xorSub]
  | k' + 1, k, h, a => by
    simp only [xorSub]
    split
    · rw [Nat.xor_comm (xorSub m s k') (m k'), ← Nat.xor_assoc,
        treeSumN_xorSub F m s k' k (by omega), treeSumN_xor_lt F m k k' (by omega) a]
    · rw [Nat.xor_zero, treeSumN_xorSub F m s k' k (by omega) a]

theorem treeSumW_eq {F m : ℕ → ℕ} {W : ℕ → Option ℕ} {n : ℕ} (hW : witsOK m W n = true) :
    ∀ k, k ≤ n → ∀ a, treeSumW F m W k a = treeSumN F m k a
  | 0, _, _ => rfl
  | k + 1, hk, a => by
    have hk' := List.all_eq_true.1 hW k (List.mem_range.2 (by omega))
    simp only [treeSumW, treeSumN]
    split
    · next s hs =>
      rw [hs] at hk'
      have e : m k = xorSub m s k := by simpa using hk'
      rw [treeSumW_eq hW k (by omega) a, e, treeSumN_xorSub F m s k k le_rfl a, two_mul]
    · rw [treeSumW_eq hW k (by omega) a, treeSumW_eq hW k (by omega) (a ^^^ m k)]

theorem popTab_get {y : ℕ} (hy : y < 4096) : popTab[y]! = CFSG.Monster.Code.popc 12 y := by
  rw [getElem!_pos popTab y (by simp [popTab, hy])]
  simp [popTab]

theorem pop24_wt : (fun x => badWt (pop24 x)) = wtF := by
  funext x
  rw [pop24, popTab_get (Nat.mod_lt _ (by norm_num)), popTab_get (Nat.mod_lt _ (by norm_num))]
  rfl

theorem unpack_get24 (p : ℕ) {i : ℕ} (hi : i < 24) : (unpack 24 5 p)[i]! = pg 5 (mask 5) p i := by
  rw [unpack_getElem!, if_pos hi]

theorem sigRec_unpack (p w : ℕ) : ∀ n, n ≤ 24 → sigRec (unpack 24 5 p) w n = sigRecP p w n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [sigRec, sigRecP]
    rw [sigRec_unpack p w n (by omega), unpack_get24 p (by omega)]

theorem powSumN_unpack (p w : ℕ) : ∀ k, powSumN (unpack 24 5 p) w k = powSumP p w k
  | 0 => rfl
  | k + 1 => by
    simp only [powSumN, powSumP, sigN]
    rw [powSumN_unpack p w k, sigRec_unpack p _ 24 le_rfl]

theorem eighthImgs_unpack (p : ℕ) : eighthImgs (unpack 24 5 p) = imsP p := by
  simp only [eighthImgs, imsP, powSumN_unpack]

theorem amul_unpack {p q : ℕ} (hp : canonK 24 5 (mask 5) (24 * 5) p = true)
    (hq : canonK 24 5 (mask 5) (24 * 5) q = true) :
    amul (unpack 24 5 p) (unpack 24 5 q) = unpack 24 5 (pcomp 24 5 (mask 5) p q) := by
  rw [← compA_unpack hp hq]
  apply Array.ext
  · simp [amul, CFSG.Monster.B.Co2.Native.compA, unpack]
  · intro i h1 h2
    have hi : i < 24 := by simpa [amul, unpack] using h1
    simp only [amul, Array.getElem_map, CFSG.Monster.B.Co2.Native.compA, Array.getElem_ofFn]
    rw [getElem!_pos (unpack 24 5 q) i (by simp [unpack, hi])]

theorem idArr_eq : CFSG.Monster.B.Co2.Native.idA 24 = idArr := by decide

theorem pow8_unpack {p : ℕ} (hp : canonK 24 5 (mask 5) (24 * 5) p = true) (h : pow8P p = true) :
    (amul (amul (amul (unpack 24 5 p) (unpack 24 5 p)) (amul (unpack 24 5 p) (unpack 24 5 p)))
      (amul (amul (unpack 24 5 p) (unpack 24 5 p)) (amul (unpack 24 5 p) (unpack 24 5 p))) ==
      idArr) = true := by
  have h2 := canonK_pcomp hp hp
  have h4 := canonK_pcomp h2 h2
  rw [amul_unpack hp hp, amul_unpack h2 h2, amul_unpack h4 h4]
  unfold pow8P at h
  rw [Nat.eq_of_beq_eq_true h]
  have hsz : szOK 24 5 = true := by decide +kernel
  rw [← idA_eq hsz, idArr_eq]
  exact beq_self_eq_true _

theorem eighthPermOK_unpack {p : ℕ} (hp : canonK 24 5 (mask 5) (24 * 5) p = true)
    (h : eighthOKP p = true) : eighthPermOK (unpack 24 5 p) = true := by
  unfold eighthOKP at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h8, hb⟩ := h
  have hb' := Nat.eq_of_beq_eq_true hb
  unfold eighthBadP at hb'
  simp only at hb'
  split at hb'
  · next hw =>
    unfold eighthPermOK eighthWeightBad
    rw [pow8_unpack hp h8, Bool.true_and, eighthImgs_unpack]
    simp only
    rw [pop24_wt, ← treeSumW_eq hw 12 le_rfl 0, hb']
    rfl
  · exact absurd hb' (by decide)

theorem akey_unpack_inj {p q : ℕ} (hp : canonK 24 5 (mask 5) (24 * 5) p = true)
    (hq : canonK 24 5 (mask 5) (24 * 5) q = true)
    (h : akey (unpack 24 5 p) = akey (unpack 24 5 q)) : p = q := by
  have hl : ∀ r, canonK 24 5 (mask 5) (24 * 5) r = true → ∀ l ∈ (unpack 24 5 r).toList, l < 24 := by
    intro r hr l hl
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
    have hi' : i < 24 := by simpa [unpack] using hi
    have e := unpack_get24 r hi'
    rw [getElem!_pos (unpack 24 5 r) i (by simp [unpack, hi']), ← Array.getElem_toList] at e
    rw [e]
    exact (CFSG.KS.PF.canon_facts hr).2.2.2 i hi'
  have hlen : (unpack 24 5 p).toList.length = (unpack 24 5 q).toList.length := by simp [unpack]
  exact CFSG.KS.PEnum.unpack_inj hp hq
    (Array.toList_inj.1 (Nat.ofDigits_inj_of_len_eq (by norm_num) hlen (hl p hp) (hl q hq) h))

theorem sylowCert_pts {N : ℕ} {G T E S : ℕ → ℕ} (hs : sylowGens.size = 10)
    (hg : ∀ k < 10, sylowGens[k]! = unpack 24 5 (G k))
    (hk : bfsK 24 5 10 G N T E S = true) (he : edgesK 10 N G T E = true)
    (hr : replayK 10 N E = true) (hN0 : 0 < N) (hN : N ≤ 2000) :
    sylowCert.pts = Array.ofFn (n := N) fun i => unpack 24 5 (T i.val) := by
  have hk' := hk
  unfold bfsK at hk'
  simp only [bAnd_iff] at hk'
  obtain ⟨hsz, hcG', hcT', hT0, hd, -⟩ := hk'
  have hcG : ∀ k < 10, canonK 24 5 (mask 5) (24 * 5) (G k) = true := allN_spec hcG'
  have hcT : ∀ i < N, canonK 24 5 (mask 5) (24 * 5) (T i) = true := allN_spec hcT'
  set L : Array (Array ℕ) := Array.ofFn (n := N) fun i => unpack 24 5 (T i.val) with hL
  have hLs : L.size = N := by simp [hL]
  have hLg : ∀ i < N, L[i]! = unpack 24 5 (T i) := fun i hi => by
    rw [getElem!_pos L i (by rw [hLs]; exact hi)]
    simp [hL]
  have hE : ∀ i < L.size, ∀ k < sylowGens.size,
      fget (E i) k 16 < L.size ∧ L[fget (E i) k 16]! = amul sylowGens[k]! L[i]! := by
    intro i hi k hk1
    rw [hLs] at hi ⊢
    rw [hs] at hk1
    have h1 := List.all_eq_true.1 (List.all_eq_true.1 he i (List.mem_range.2 hi)) k
      (List.mem_range.2 hk1)
    rw [Bool.and_eq_true, decide_eq_true_eq] at h1
    refine ⟨h1.1, ?_⟩
    rw [hLg _ h1.1, hLg i hi, hg k hk1, Nat.eq_of_beq_eq_true h1.2,
      amul_unpack (hcG k hk1) (hcT i hi)]
  have h0 : L[0]! = idArr := by
    rw [hLg 0 hN0, Nat.eq_of_beq_eq_true hT0, ← idA_eq hsz, idArr_eq]
  have hkey : ∀ a < L.size, ∀ b < L.size, akey L[a]! = akey L[b]! → a = b := by
    intro a ha b hb e
    rw [hLs] at ha hb
    rw [hLg a ha, hLg b hb] at e
    exact distinctK_inj hd a ha b hb (akey_unpack_inj (hcT a ha) (hcT b hb) e)
  have hrep : replayOK (fun i k => fget (E i) k 16) sylowGens.size L.size = true := by
    rw [hs, hLs]
    exact hr
  have hpts := gBfs_eq_of_replay (act := fun k x => amul sylowGens[k]! x) (key := akey)
    (by rw [hLs]; exact hN0) h0 hkey hE hrep (fuel := 2000) (by rw [hLs]; exact hN)
  rw [sylowCert, bfsCert_eq]
  exact hpts

theorem eighthCheck_of {N : ℕ} {G T E S : ℕ → ℕ} (hs : sylowGens.size = 10)
    (hg : ∀ k < 10, sylowGens[k]! = unpack 24 5 (G k))
    (hk : bfsK 24 5 10 G N T E S = true) (he : edgesK 10 N G T E = true)
    (hr : replayK 10 N E = true) (hN0 : 0 < N) (hN : N ≤ 2000)
    (hall : ∀ i < N, eighthOKP (T i) = true) : eighthCheck = true := by
  have hcT : ∀ i < N, canonK 24 5 (mask 5) (24 * 5) (T i) = true := bfsK_canon hk
  unfold eighthCheck
  rw [sylowCert_pts hs hg hk he hr hN0 hN, List.all_eq_true]
  intro i hi
  rw [List.mem_range, Array.size_ofFn] at hi
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  exact eighthPermOK_unpack (hcT i hi) (hall i hi)

end CFSG.KC.EvenSporCo0
