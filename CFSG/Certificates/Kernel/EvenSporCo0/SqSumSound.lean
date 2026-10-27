module

public import Certificates.Data.Kernel.EvenSporCo0.SqSum
public import CFSG.Certificates.Kernel.EvenSporCo0.EighthSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.OctadSylowCert
import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0TypEighthData
import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.BfsPinUnpack
import all CFSG.Certificates.Kernel.Spor.PEnumSound
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Common.BvecLoop
import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0Data
import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0Mono

public section

namespace CFSG.KC.EvenSporCo0

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KLie.CT CFSG.Monster.Code
  CFSG.Monster.B.TwoA.Census CFSG.EvenSporadicStandard.TwoCo1 CFSG.KC.Bfs CFSG.KC.BfsPin

theorem treeSumN_comp {M : Type*} [Add M] (G : ℕ → M) (L m : ℕ → ℕ)
    (hL : ∀ x y, L (x ^^^ y) = L x ^^^ L y) :
    ∀ k a, treeSumN (fun x => G (L x)) m k a = treeSumN G (fun i => L (m i)) k (L a)
  | 0, _ => rfl
  | k + 1, a => by
    simp only [treeSumN]
    rw [treeSumN_comp G L m hL k a, treeSumN_comp G L m hL k (a ^^^ m k), hL]

theorem treeSumN_congr {M : Type*} [Add M] (F : ℕ → M) {m m' : ℕ → ℕ} :
    ∀ k, (∀ j < k, m j = m' j) → ∀ a, treeSumN F m k a = treeSumN F m' k a
  | 0, _, _ => rfl
  | k + 1, h, a => by
    simp only [treeSumN]
    rw [treeSumN_congr F k (fun j hj => h j (by omega)) a,
      treeSumN_congr F k (fun j hj => h j (by omega)) (a ^^^ m k), h k (by omega)]

theorem sumR_eq (f : ℕ → ℕ) : ∀ n, sumR f n = ∑ i ∈ Finset.range n, f i
  | 0 => rfl
  | n + 1 => by rw [sumR, sumR_eq f n, Finset.sum_range_succ]

theorem testBit_sigRec (a : Array ℕ) (w : ℕ) :
    ∀ n j, (sigRec a w n).testBit j = (decide (j < n) && w.testBit a[j]!)
  | 0, j => by simp [sigRec]
  | n + 1, j => by
    rw [sigRec, Nat.testBit_xor, testBit_sigRec a w n j]
    by_cases hj : j = n
    · subst hj
      by_cases hb : w.testBit a[j]! = true
      · simp [hb, Nat.testBit_two_pow]
      · simp [hb]
    · have e : (if w.testBit a[n]! = true then 2 ^ n else 0 : ℕ).testBit j = false := by
        split <;> simp [Nat.testBit_two_pow, Ne.symm hj]
      have e2 : (j < n + 1) ↔ (j < n) := by omega
      rw [e, Bool.xor_false]
      simp only [e2]

theorem sigRec_xor (a : Array ℕ) (x y n : ℕ) :
    sigRec a (x ^^^ y) n = sigRec a x n ^^^ sigRec a y n := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_xor, testBit_sigRec, testBit_sigRec, testBit_sigRec, Nat.testBit_xor]
  by_cases hj : j < n <;> simp [hj]

theorem sigN_zero (a : Array ℕ) : sigN a 0 = 0 :=
  Nat.eq_of_testBit_eq fun j => by simp [sigN, testBit_sigRec]

theorem lin_xor (a : Array ℕ) (x y : ℕ) :
    (x ^^^ y) ^^^ sigN a (x ^^^ y) = (x ^^^ sigN a x) ^^^ (y ^^^ sigN a y) := by
  rw [sigN, sigRec_xor, ← sigN, ← sigN]
  refine Nat.eq_of_testBit_eq fun j => ?_
  simp only [Nat.testBit_xor]
  cases x.testBit j <;> cases y.testBit j <;> cases (sigN a x).testBit j <;>
    cases (sigN a y).testBit j <;> rfl

theorem bvec24_eq_iff (y d : ℕ) (hd : d < 2 ^ 24) : bvec 24 y = bvec 24 d ↔ y % 16777216 = d := by
  have hm : bvec 24 (y % 16777216) = bvec 24 y := by
    funext i
    simp only [bvec_apply]
    rw [show (16777216 : ℕ) = 2 ^ 24 by norm_num, Nat.testBit_mod_two_pow]
    simp [i.2]
  constructor
  · intro h
    exact CFSG.KC.BvecLoop.bvec_inj (Nat.mod_lt _ (by norm_num)) hd (hm.trans h)
  · intro h
    rw [← hm, h]

theorem ainv_of_sq {a : Array ℕ} (ha : PermArr a = true) (h : amul a a = idArr) : ainv a = a := by
  apply decode_inj (PermArr_ainv ha) ha
  rw [decode_ainv ha]
  have e : decode a * decode a = 1 := by rw [← decode_amul ha ha, h, decode_idArr]
  exact inv_eq_of_mul_eq_one_right e

theorem sumCount_eq {a : Array ℕ} (ha : PermArr a = true) (h : amul a a = idArr) {d : ℕ}
    (hd : d < 2 ^ 24) :
    sumCount a d = treeSumN (hitF d) (fun i => Bmask i ^^^ sigN a (Bmask i)) 12 0 := by
  have hF : (fun x => if bvec 24 x + bvec 24 x ∘ arrFun (ainv a) = bvec 24 d then 1 else 0) =
      fun x => hitF d (x ^^^ sigN a x) := by
    funext x
    rw [ainv_of_sq ha h, ← bvec_sigN ha, ← bvec_xor, hitF]
    exact if_congr (bvec24_eq_iff _ d hd) rfl rfl
  dsimp only [sumCount]
  rw [hF]
  refine (treeSumN_comp (hitF d) (fun x => x ^^^ sigN a x) Bmask (lin_xor a) 12 0).trans ?_
  simp only [sigN_zero, Nat.xor_zero]

theorem imsS_getD (p : ℕ) {i : ℕ} (hi : i < 12) : (imsS p).getD i 0 = linP p (Bmask i) := by
  simp [imsS, hi]

theorem cntS_eq (p d : ℕ) : cntS p d = treeSumN (hitF d) (fun i => linP p (Bmask i)) 12 0 := by
  unfold cntS
  dsimp only
  split
  · next hw =>
    rw [treeSumW_eq hw 12 le_rfl 0]
    exact treeSumN_congr _ 12 (fun j hj => imsS_getD p hj) 0
  · exact treeSumN_congr _ 12 (fun j hj => imsS_getD p hj) 0

theorem linP_eq (p w : ℕ) : w ^^^ sigN (unpack 24 5 p) w = linP p w := by
  rw [sigN, sigRec_unpack p w 24 le_rfl, linP]

theorem sq_unpack {p : ℕ} (hp : canonK 24 5 (mask 5) (24 * 5) p = true) :
    amul (unpack 24 5 p) (unpack 24 5 p) = idArr ↔
      Nat.beq (pcomp 24 5 (mask 5) p p) (pidn 24 5) = true := by
  have hsz : szOK 24 5 = true := by decide +kernel
  have hid : canonK 24 5 (mask 5) (24 * 5) (pidn 24 5) = true := by decide +kernel
  rw [amul_unpack hp hp, ← idArr_eq, idA_eq hsz, Nat.beq_eq]
  exact ⟨CFSG.KS.PEnum.unpack_inj (canonK_pcomp hp hp) hid, fun e => by rw [e]⟩

theorem sqTerm_eq {p d : ℕ} (hp : canonK 24 5 (mask 5) (24 * 5) p = true)
    (ha : PermArr (unpack 24 5 p) = true) (hd : d < 2 ^ 24) :
    (if amul (unpack 24 5 p) (unpack 24 5 p) = idArr then sumCount (unpack 24 5 p) d else 0) =
      sqTermP d p := by
  unfold sqTermP
  by_cases h : amul (unpack 24 5 p) (unpack 24 5 p) = idArr
  · rw [if_pos h, if_pos ((sq_unpack hp).1 h), sumCount_eq ha h hd, cntS_eq]
    simp only [linP_eq]
  · rw [if_neg h, if_neg fun h' => h ((sq_unpack hp).2 h')]

theorem sqOK_sound {T : ℕ → ℕ} {N d n : ℕ} (h : sqOK T N d n = true) : sqK T N d = n :=
  Nat.eq_of_beq_eq_true h

theorem sqSum_of {N : ℕ} {G T E S : ℕ → ℕ} (hs : sylowGens.size = 10)
    (hg : ∀ k < 10, sylowGens[k]! = unpack 24 5 (G k))
    (hk : bfsK 24 5 10 G N T E S = true) (he : edgesK 10 N G T E = true)
    (hr : replayK 10 N E = true) (hN0 : 0 < N) (hN : N ≤ 2000)
    (hperm : ∀ i < N, PermArr (unpack 24 5 (T i)) = true)
    {d n : ℕ} (hd : d < 2 ^ 24) (h : sqOK T N d n = true) : sqSum d = n := by
  have hcT : ∀ i < N, canonK 24 5 (mask 5) (24 * 5) (T i) = true := bfsK_canon hk
  rw [← sqOK_sound h, sqK, sumR_eq, sqSum, sylowCert_pts hs hg hk he hr hN0 hN, Array.size_ofFn]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  rw [getElem!_pos _ i (by simpa using hi'), Array.getElem_ofFn]
  exact sqTerm_eq (hcT i hi') (hperm i hi') hd

theorem comp_inv_eq_iff (w : Fin 24 → ZMod 2) (σ : Equiv.Perm (Fin 24)) :
    w ∘ ⇑σ⁻¹ = w ↔ w ∘ ⇑σ = w := by
  constructor
  · intro h
    funext i
    have e := congrFun h (σ i)
    simp only [Function.comp_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply] at e
    exact e.symm
  · intro h
    funext i
    have e := congrFun h (σ⁻¹ i)
    simp only [Function.comp_apply, Equiv.Perm.inv_def, Equiv.apply_symm_apply] at e
    exact e.symm

theorem add_eq_zero_iff' (u v : Fin 24 → ZMod 2) : u + v = 0 ↔ v = u := by
  constructor
  · intro h
    funext i
    have e := congrFun h i
    simp only [Pi.add_apply, Pi.zero_apply] at e
    revert e
    generalize u i = x
    generalize v i = y
    revert x y
    decide
  · intro h
    rw [h]
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    generalize u i = x
    revert x
    decide

theorem fixed_iff {g : Array ℕ} (hg : PermArr g = true) (a : ℕ) :
    permWordArr g (bvec 24 a) = bvec 24 a ↔ (a ^^^ sigN g a) % 16777216 = 0 := by
  rw [permWordArr, ← coe_decode (PermArr_ainv hg), decode_ainv hg, comp_inv_eq_iff,
    coe_decode hg, ← bvec_sigN hg, ← add_eq_zero_iff', ← bvec_xor, ← bvec_zero 24]
  exact bvec24_eq_iff _ 0 (by norm_num)

theorem fixOK_eq {G : ℕ → ℕ} (hg : ∀ k < 10, sylowGens[k]! = unpack 24 5 (G k))
    (hp : ∀ k < 10, PermArr sylowGens[k]! = true) (a : ℕ) : fixOK a = fixOKP G a := by
  have hfix : ∀ k < 10, (permWordArr sylowGens[k]! (bvec 24 a) = bvec 24 a ↔
      Nat.beq (linP (G k) a % 16777216) 0 = true) := fun k hk => by
    rw [fixed_iff (hp k hk), Nat.beq_eq, hg k hk, linP_eq]
  have hall : (∀ k : Fin 10, permWordArr sylowGens[(k : ℕ)]! (bvec 24 a) = bvec 24 a) ↔
      fixAllP G a = true := by
    rw [fixAllP, List.all_eq_true]
    constructor
    · intro h k hk
      exact (hfix k (List.mem_range.1 hk)).1 (h ⟨k, List.mem_range.1 hk⟩)
    · intro h k
      exact (hfix k k.2).2 (h k (List.mem_range.2 k.2))
  have hw : ∀ c, c < 2 ^ 24 → (bvec 24 a = bvec 24 c ↔ Nat.beq (a % 16777216) c = true) :=
    fun c hc => by rw [Nat.beq_eq]; exact bvec24_eq_iff a c hc
  unfold fixOK fixOKP
  rw [Bool.eq_iff_iff, decide_eq_true_iff, hall,hw 0 (by norm_num), hw 255 (by norm_num), hw 16776960 (by norm_num),
    hw 16777215 (by norm_num)]
  generalize fixAllP G a = b
  generalize Nat.beq (a % 16777216) 0 = b0
  generalize Nat.beq (a % 16777216) 255 = b1
  generalize Nat.beq (a % 16777216) 16776960 = b2
  generalize Nat.beq (a % 16777216) 16777215 = b3
  revert b b0 b1 b2 b3
  decide

theorem fixK_sound {G : ℕ → ℕ} (h : fixK G = true) : fixBadP G = 0 := Nat.eq_of_beq_eq_true h

theorem fixBad_of {G : ℕ → ℕ} (hg : ∀ k < 10, sylowGens[k]! = unpack 24 5 (G k))
    (hp : ∀ k < 10, PermArr sylowGens[k]! = true) (h : fixK G = true) : fixBad = 0 := by
  rw [← fixK_sound h, fixBad, fixBadP]
  exact congrArg (fun F => treeSumN F Bmask 12 0) (funext fun a => by rw [fixOK_eq hg hp a])

end CFSG.KC.EvenSporCo0
