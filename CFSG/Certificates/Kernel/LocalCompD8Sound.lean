module

public import Certificates.Data.Kernel.WeylE8.D8
public import CFSG.Certificates.Kernel.LocalCompE8Sound
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylD8Data
import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KLC.E8

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def permArrL (L : List (List ℤ)) (σ : Equiv.Perm (Fin 8)) : Array ℕ :=
  Array.ofFn (n := 240) fun i =>
    L.idxOf ((List.finRange 8).map fun k => (L.getD i.val []).getD (σ.symm k : ℕ) 0)

@[expose] def reflArrsL (L : List (List ℤ)) : Array (Array ℕ) :=
  ((List.range 240).map (reflArrL L)).toArray

@[expose] def signArrsL (L : List (List ℤ)) : Array (Array ℕ) :=
  ((List.range 256).map fun m => signArrL L (frameDecode m)).toArray

@[expose] def dCheckWithL (L : List (List ℤ)) (P : List (ℕ × ℕ)) (RA SA : Array (Array ℕ)) : Bool :=
  (List.range 240).all (fun r => decide (r < 112) || (List.range 256).all fun m =>
    !(framePop m % 2 == 0) || m == 0 || (SA[m]!)[r]! != r) &&
  allLt 240 (fun r => memE SA (compA 240 RA[1]! RA[r]!) == decide (r < 4)) &&
  P.all (fun p => [0, 1].all fun s => (List.range 256).all fun m => !(framePop m % 2 == 0) ||
    eqA 240 (compA 240 (compA 240 RA[4 * P.idxOf p + s]! SA[m]!) RA[4 * P.idxOf p + s]!)
      SA[permMask (Equiv.swap (Fin.ofNat 8 p.1) (Fin.ofNat 8 p.2)) m]!) &&
  allLt 240 (fun r => L.idxOf (L.getD r []) == r) && L.length == 240 &&
  allLt 240 (fun r => (L.getD r []).length == 8) &&
  P.all (fun p => allLt 240 (fun r => decide
      (L.idxOf (permVecL (Equiv.swap (Fin.ofNat 8 p.1) (Fin.ofNat 8 p.2)) (L.getD r [])) < 240)) &&
    eqA 240 (permArrL L (Equiv.swap (Fin.ofNat 8 p.1) (Fin.ofNat 8 p.2))) RA[4 * P.idxOf p + 1]!)

theorem dCheck_eq : dCheck = dCheckWithL rootList dPairs (reflArrsL rootList) (signArrsL rootList) :=
  rfl

end CFSG.KLC.E8

end

namespace CFSG.KLC.E8

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

public theorem arr_ext8 {A B : Array ℕ} {n : ℕ} (hA : A.size = n) (hB : B.size = n)
    (h : ∀ i < n, A[i]! = B[i]!) : A = B := by
  apply Array.ext (by omega)
  intro i h1 h2
  have := h i (by omega)
  rwa [getElem!_pos A i h1, getElem!_pos B i h2] at this

public theorem eqA_of {t u : Array ℕ} (h : ∀ i < 240, t[i]! = u[i]!) : eqA 240 t u = true := by
  unfold eqA
  rw [allLt_iff]
  intro i hi
  rw [h i hi]
  exact beq_self_eq_true _

public theorem eqA_spec {t u : Array ℕ} (h : eqA 240 t u = true) : ∀ i < 240, t[i]! = u[i]! := by
  unfold eqA at h
  rw [allLt_iff] at h
  intro i hi
  exact beq_iff_eq.mp (h i hi)

public theorem reflArrs_get {L : List (List ℤ)} {r : ℕ} (hr : r < 240) :
    (reflArrsL L)[r]! = reflArrL L r := by
  unfold reflArrsL
  rw [getElem!_pos _ r (by simp [hr])]
  simp

public theorem signArrs_get {L : List (List ℤ)} {m : ℕ} (hm : m < 256) :
    (signArrsL L)[m]! = signArrL L (frameDecode m) := by
  unfold signArrsL
  rw [getElem!_pos _ m (by simp [hm])]
  simp

public theorem notB'_eq (b : Bool) : notB' b = !b := by cases b <;> rfl

public theorem evenB_eq (m : ℕ) : evenB m = decide (framePop m % 2 = 0) := by
  unfold evenB
  change Nat.beq (pop8 m &&& 1) 0 = _
  rw [Nat.and_one_is_mod, pop8_eq, Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]

public theorem pg_low8 {X i : Nat} (hi : i < 240) :
    pg 8 (mask 8) (Nat.land X (mask (nat_lit 1920))) i = pg 8 (mask 8) X i := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [PF.testBit_pgM, PF.testBit_pgM]
  by_cases hk : k < 8
  · have e : Nat.land X (mask (nat_lit 1920)) = X &&& (2 ^ 1920 - 1) := by
      rw [← PF.mask_eq]
      rfl
    have h1 : 8 * i + k < 1920 := by omega
    rw [e, Nat.testBit_and, Nat.testBit_two_pow_sub_one]
    simp [hk, h1]
  · simp [hk]

public theorem low_shr (Y : ℕ) : Nat.land Y (mask (nat_lit 1920)) >>> (240 * 8) = 0 := by
  have e : Nat.land Y (mask (nat_lit 1920)) = Y &&& (2 ^ 1920 - 1) := by
    rw [← PF.mask_eq]
    rfl
  rw [e, Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt (Nat.and_lt_two_pow _ (by norm_num))

public theorem eqA_low {X : ℕ} (hX : X >>> (240 * 8) = 0) (Y : ℕ) :
    eqA 240 (unpack 240 8 X) (unpack 240 8 Y) = Nat.beq X (Nat.land Y (mask (nat_lit 1920))) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq]
  constructor
  · intro h
    apply PF.eq_of_fields (n := 240) (w := 8) (by norm_num) hX (low_shr Y)
    intro i hi
    have := eqA_spec h i hi
    rw [Orb.unpack_get hi, Orb.unpack_get hi] at this
    rw [this, pg_low8 hi]
  · intro h
    apply eqA_of
    intro i hi
    rw [Orb.unpack_get hi, Orb.unpack_get hi, h, pg_low8 hi]

public theorem rt_lt8 {RK RT : Nat → Nat} (hr : ∀ r < 240, reflRowOK RK r (RT r) = true) {r : Nat}
    (hr' : r < 240) {i : Nat} (hi : i < 240) : pg 8 (mask 8) (RT r) i < 240 := by
  have h := hr r hr'
  unfold reflRowOK at h
  rw [Orb.strictB_eq, Orb.allN_iff] at h
  have h1 := h i hi
  rw [Orb.strictB_eq] at h1
  exact blt_true (band_true h1).1

noncomputable def flipv (m : ℕ) (x : List ℤ) : List ℤ :=
  (List.finRange 8).map fun k => if frameDecode m k = 1 then -x.getD k 0 else x.getD k 0

theorem mapFin_getD (f : Fin 8 → ℤ) (k : Fin 8) : ((List.finRange 8).map f).getD k 0 = f k := by
  rw [← List.ofFn_eq_map, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

public theorem z2 : ∀ u : ZMod 2, u = 0 ∨ u = 1 := by decide

theorem flipv_flipv (m m' : ℕ) (x : List ℤ) : flipv m (flipv m' x) = flipv (m ^^^ m') x := by
  unfold flipv
  congr 1
  funext k
  rw [mapFin_getD, frameDecode_xor, Pi.add_apply]
  have o : (1 : ZMod 2) + 1 = 0 := by decide
  have o' : (0 : ZMod 2) ≠ 1 := by decide
  rcases z2 (frameDecode m k) with h1 | h1 <;> rcases z2 (frameDecode m' k) with h2 | h2 <;>
    simp [h1, h2, o, o']

theorem flipv_zero (K : ℕ) : flipv 0 (vecOf K) = vecOf K := by
  have h0 : ∀ k : Fin 8, frameDecode 0 k ≠ 1 := fun k => by simp [frameDecode]
  conv_rhs => rw [vecOf, List.ofFn_eq_map]
  rw [flipv]
  congr 1
  funext k
  rw [ite_eq_right_of_eq_false _ _ (eq_false (h0 k)), vecOf_getD]

theorem st_facts {L : List (List ℤ)} {RK ST : ℕ → ℕ} (hb : bindRoots RK L = true)
    (hst : ∀ m < 256, signRowOK RK m (ST m) = true) {m i : ℕ} (hm : m < 256)
    (he : framePop m % 2 = 0) (hi : i < 240) :
    pg 8 (mask 8) (ST m) i < 240 ∧
      L.getD (pg 8 (mask 8) (ST m) i) [] = flipv m (L.getD i []) := by
  obtain ⟨-, hf⟩ := bind_facts hb
  have hrow := hst m hm
  have hp : Nat.beq (Nat.land (pop8 m) (nat_lit 1)) (nat_lit 0) = true := by
    rw [Nat.beq_eq]
    change pop8 m &&& 1 = 0
    rw [Nat.and_one_is_mod, pop8_eq, he]
  unfold signRowOK at hrow
  rw [hp] at hrow
  change allN 240 _ = true at hrow
  rw [Orb.allN_iff] at hrow
  have h1 := hrow i hi
  simp only [Orb.strictB_eq] at h1
  obtain ⟨he1, he2⟩ := band_true h1
  obtain ⟨-, he3⟩ := band_true he2
  have he240 : pg 8 (mask 8) (ST m) i < 240 := blt_true he1
  refine ⟨he240, ?_⟩
  obtain ⟨xi, si, vi⟩ := hf i hi
  obtain ⟨-, -, ve⟩ := hf _ he240
  rw [ve, vi]
  exact (flip_vec xi si (Nat.eq_of_beq_eq_true he3)).symm

public theorem even_xor {m m' : ℕ} (hm : m < 256) (hm' : m' < 256) (he : framePop m % 2 = 0)
    (he' : framePop m' % 2 = 0) : m ^^^ m' < 256 ∧ framePop (m ^^^ m') % 2 = 0 := by
  have hx : m ^^^ m' < 256 := Nat.xor_lt_two_pow (n := 8) hm hm'
  refine ⟨hx, (evenSub_iff_frameDecode _ hx).1 ?_⟩
  rw [frameDecode_xor]
  exact mem_evenSub.1 (evenSub.add_mem (mem_evenSub.2 ((evenSub_iff_frameDecode _ hm).2 he))
    (mem_evenSub.2 ((evenSub_iff_frameDecode _ hm').2 he')))

public theorem st_mul {L : List (List ℤ)} {RK ST : ℕ → ℕ} {SO : ℕ} (hb : bindRoots RK L = true)
    (hs : sortedOK RK SO = true) (hst : ∀ m < 256, signRowOK RK m (ST m) = true) {m m' i : ℕ}
    (hm : m < 256) (hm' : m' < 256) (he : framePop m % 2 = 0) (he' : framePop m' % 2 = 0)
    (hi : i < 240) :
    pg 8 (mask 8) (ST (m ^^^ m')) i = pg 8 (mask 8) (ST m) (pg 8 (mask 8) (ST m') i) := by
  obtain ⟨hx, hxe⟩ := even_xor hm hm' he he'
  have h' := st_facts hb hst hm' he' hi
  have h := st_facts hb hst hm he h'.1
  have h2 := st_facts hb hst hx hxe hi
  rw [← idxOf_root hb hs h2.1, ← idxOf_root hb hs h.1, h2.2, h.2, h'.2, flipv_flipv]

public theorem st_zero {L : List (List ℤ)} {RK ST : ℕ → ℕ} {SO : ℕ} (hb : bindRoots RK L = true)
    (hs : sortedOK RK SO = true) (hst : ∀ m < 256, signRowOK RK m (ST m) = true) {i : ℕ}
    (hi : i < 240) : pg 8 (mask 8) (ST 0) i = i := by
  obtain ⟨-, hf⟩ := bind_facts hb
  have h := st_facts hb hst (m := 0) (by norm_num) (by decide) hi
  rw [← idxOf_root hb hs h.1, h.2, (hf i hi).2.2, flipv_zero, ← (hf i hi).2.2,
    idxOf_root hb hs hi]

theorem permMask_xor (σ : Equiv.Perm (Fin 8)) (m m' : ℕ) :
    permMask σ (m ^^^ m') = permMask σ m ^^^ permMask σ m' := by
  unfold permMask
  rw [frameDecode_xor, permVec_add, frameEncode_add]

theorem permMask_zero (σ : Equiv.Perm (Fin 8)) : permMask σ 0 = 0 := by
  have h0 : frameDecode 0 = 0 := by
    funext i
    simp [frameDecode]
  unfold permMask
  rw [h0]
  simp [frameEncode, permVec]
  rfl

theorem permMask_even (σ : Equiv.Perm (Fin 8)) {m : ℕ} (hm : m < 256) (he : framePop m % 2 = 0) :
    permMask σ m < 256 ∧ framePop (permMask σ m) % 2 = 0 := by
  unfold permMask
  refine ⟨frameEncode_lt _, (evenSub_iff_frameDecode _ (frameEncode_lt _)).1 ?_⟩
  rw [frameDecode_frameEncode]
  exact mem_evenSub.1 (permVec_mem_evenSub σ (mem_evenSub.2 ((evenSub_iff_frameDecode _ hm).2 he)))

theorem bit_val (m : ℕ) (i : Fin 8) : Nat.land (Nat.shiftRight m i) 1 = (frameDecode m i).val := by
  by_cases h : m.testBit i = true
  · rw [(bit_testBit m i).2 h]
    simp only [frameDecode, h, ite_true]
    rfl
  · rcases bit01 m i with h' | h'
    · rw [h']
      simp [frameDecode, h]
    · exact absurd ((bit_testBit m i).1 h') h

theorem permMask_swap {a b m : ℕ} (hab : a < b) (hb : b < 8) (hm : m < 256) :
    permMask (Equiv.swap (Fin.ofNat 8 a) (Fin.ofNat 8 b)) m = swapMask a b m := by
  obtain ⟨ia, hia⟩ : ∃ ia : Fin 8, ia = Fin.ofNat 8 a := ⟨_, rfl⟩
  obtain ⟨ib, hib⟩ : ∃ ib : Fin 8, ib = Fin.ofNat 8 b := ⟨_, rfl⟩
  rw [← hia, ← hib]
  have ha' : (ia : ℕ) = a := by rw [hia, Fin.val_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hb' : (ib : ℕ) = b := by rw [hib, Fin.val_ofNat]; exact Nat.mod_eq_of_lt hb
  have hne : ia ≠ ib := fun h => by
    have := congrArg Fin.val h
    omega
  obtain ⟨d, hd⟩ : ∃ d : Fin 8 → ℕ, d = fun i => (frameDecode m i).val := ⟨_, rfl⟩
  have em : m = ∑ i : Fin 8, d i * 2 ^ (i : ℕ) := by
    conv_lhs => rw [← frameEncode_frameDecode m hm]
    rw [hd]
    rfl
  have ep : permMask (Equiv.swap ia ib) m = ∑ i : Fin 8, d (Equiv.swap ia ib i) * 2 ^ (i : ℕ) := by
    unfold permMask frameEncode
    simp only [permVec, Equiv.symm_swap, hd]
    rfl
  have hsplit : ∀ f : Fin 8 → ℤ, (∀ c, c ≠ ia → c ≠ ib → f c = 0) →
      ∑ i : Fin 8, f i = f ia + f ib := fun f hf =>
    Finset.sum_eq_add ia ib hne (fun c _ hc => hf c hc.1 hc.2) (by simp) (by simp)
  have hdiff : (∑ i : Fin 8, (d (Equiv.swap ia ib i) : ℤ) * 2 ^ (i : ℕ)) -
      ∑ i : Fin 8, (d i : ℤ) * 2 ^ (i : ℕ) =
      ((d ib : ℤ) - d ia) * 2 ^ a + ((d ia : ℤ) - d ib) * 2 ^ b := by
    rw [← Finset.sum_sub_distrib]
    rw [hsplit (fun i => (d (Equiv.swap ia ib i) : ℤ) * 2 ^ (i : ℕ) - (d i : ℤ) * 2 ^ (i : ℕ))
      (fun c h1 h2 => by simp only [Equiv.swap_apply_of_ne_of_ne h1 h2, sub_self])]
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, ha', hb']
    ring
  have hle : d ia * 2 ^ a + d ib * 2 ^ b ≤ m := by
    rw [em]
    have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i : Fin 8 => d i * 2 ^ (i : ℕ))
      (Finset.subset_univ {ia, ib}) (fun _ _ _ => Nat.zero_le _)
    rw [Finset.sum_pair hne, ha', hb'] at this
    exact this
  have hba : Nat.land (Nat.shiftRight m a) 1 = d ia := by rw [← ha', hd]; exact bit_val m ia
  have hbb : Nat.land (Nat.shiftRight m b) 1 = d ib := by rw [← hb', hd]; exact bit_val m ib
  have hsw : swapMask a b m = m - d ia * 2 ^ a - d ib * 2 ^ b + (d ib * 2 ^ a + d ia * 2 ^ b) := by
    unfold swapMask
    rw [Orb.strictN_eq, Orb.strictN_eq, hba, hbb]
    simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.add_eq, Nat.sub_eq]
  have hint : (permMask (Equiv.swap ia ib) m : ℤ) = (m : ℤ) - ((d ia * 2 ^ a : ℕ) : ℤ) -
      ((d ib * 2 ^ b : ℕ) : ℤ) + ((d ib * 2 ^ a : ℕ) : ℤ) + ((d ia * 2 ^ b : ℕ) : ℤ) := by
    have em' : (m : ℤ) = ∑ i : Fin 8, (d i : ℤ) * 2 ^ (i : ℕ) := by exact_mod_cast em
    have ep' : (permMask (Equiv.swap ia ib) m : ℤ) =
        ∑ i : Fin 8, (d (Equiv.swap ia ib i) : ℤ) * 2 ^ (i : ℕ) := by exact_mod_cast ep
    rw [ep', em']
    push_cast
    linear_combination hdiff
  generalize d ia * 2 ^ a = A1 at hle hsw hint
  generalize d ib * 2 ^ b = A2 at hle hsw hint
  generalize d ib * 2 ^ a = A3 at hsw hint
  generalize d ia * 2 ^ b = A4 at hsw hint
  omega

public theorem xor_pow_add {w j : ℕ} (h : w < 2 ^ j) : w ^^^ 2 ^ j = w + 2 ^ j := by
  rw [← Nat.or_two_pow_eq_add_of_lt h]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_two_pow]
  by_cases hij : j = i
  · subst hij
    rw [Nat.testBit_lt_two_pow h]
    simp
  · simp [hij]

theorem gk_even {k : ℕ} (hk : k < 7) : 1 + 2 ^ (k + 1) < 256 ∧ framePop (1 + 2 ^ (k + 1)) % 2 = 0 := by
  interval_cases k <;> decide

theorem gen_even (Q : ℕ → Prop) (h0 : Q 0)
    (hstep : ∀ m k, m < 2 ^ (k + 1) → k < 7 → framePop m % 2 = 0 → Q m →
      Q (m ^^^ (1 + 2 ^ (k + 1)))) :
    ∀ m < 256, framePop m % 2 = 0 → Q m := by
  have key : ∀ t, 1 ≤ t → t ≤ 8 → ∀ m < 2 ^ t, framePop m % 2 = 0 → Q m := by
    intro t
    induction t with
    | zero => intro h; omega
    | succ t ih =>
      intro _ ht m hm he
      rcases Nat.eq_zero_or_pos t with rfl | ht1
      · interval_cases m
        · exact h0
        · exact absurd he (by decide)
      by_cases hlt : m < 2 ^ t
      · exact ih ht1 (by omega) m hlt he
      have hpow : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by rw [pow_succ]; ring
      have h1 : 1 < 2 ^ t := Nat.one_lt_two_pow (by omega)
      have hg : 1 + 2 ^ t = 1 ^^^ 2 ^ t := by rw [xor_pow_add h1]
      obtain ⟨r, hrdef⟩ : ∃ r, r = m - 2 ^ t := ⟨_, rfl⟩
      have hr : r < 2 ^ t := by omega
      have hm' : m = r ^^^ 2 ^ t := by rw [xor_pow_add hr]; omega
      obtain ⟨m', hm'def⟩ : ∃ m', m' = r ^^^ 1 := ⟨_, rfl⟩
      have hm'lt : m' < 2 ^ t := by rw [hm'def]; exact Nat.xor_lt_two_pow hr h1
      have hmm : m = m' ^^^ (1 + 2 ^ t) := by
        rw [hg, hm'def, Nat.xor_assoc, ← Nat.xor_assoc 1 1, Nat.xor_self, Nat.zero_xor]
        exact hm'
      obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
      have hk : k < 7 := by omega
      have h256 : 2 ^ (k + 1) ≤ 128 := by
        calc 2 ^ (k + 1) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 128 := by norm_num
      have hm256 : m < 256 := by omega
      obtain ⟨hg256, hge⟩ := gk_even hk
      have hme' : framePop m' % 2 = 0 := by
        have hx : m' = m ^^^ (1 + 2 ^ (k + 1)) := by
          rw [hmm, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
        rw [hx]
        exact (even_xor hm256 hg256 he hge).2
      rw [hmm]
      exact hstep m' k hm'lt hk hme' (ih (by omega) (by omega) m' hm'lt hme')
  exact fun m hm he => key 8 (by norm_num) le_rfl m hm he

theorem conj_all (ρ : ℕ → ℕ) (s : ℕ → ℕ → ℕ) (π : ℕ → ℕ)
    (hρ : ∀ i < 240, ρ i < 240) (hρρ : ∀ i < 240, ρ (ρ i) = i)
    (hs : ∀ m < 256, framePop m % 2 = 0 → ∀ i < 240, s m i < 240)
    (hmul : ∀ m m', m < 256 → m' < 256 → framePop m % 2 = 0 → framePop m' % 2 = 0 →
      ∀ i < 240, s (m ^^^ m') i = s m (s m' i))
    (hs0 : ∀ i < 240, s 0 i = i)
    (hπ : ∀ m m', π (m ^^^ m') = π m ^^^ π m') (hπ0 : π 0 = 0)
    (hπe : ∀ m < 256, framePop m % 2 = 0 → π m < 256 ∧ framePop (π m) % 2 = 0)
    (hgen : ∀ k < 7, ∀ i < 240, ρ (s (1 + 2 ^ (k + 1)) (ρ i)) = s (π (1 + 2 ^ (k + 1))) i) :
    ∀ m < 256, framePop m % 2 = 0 → ∀ i < 240, ρ (s m (ρ i)) = s (π m) i := by
  suffices h : ∀ m < 256, framePop m % 2 = 0 → m < 256 → ∀ i < 240, ρ (s m (ρ i)) = s (π m) i from
    fun m hm he => h m hm he hm
  refine gen_even (fun m => m < 256 → ∀ i < 240, ρ (s m (ρ i)) = s (π m) i) ?_ ?_
  · intro _ i hi
    rw [hs0 _ (hρ i hi), hρρ i hi, hπ0, hs0 i hi]
  · intro m k hm hk he ih hm256
    obtain ⟨hg256, hge⟩ := gk_even hk
    have hm1 : m < 256 := by
      have : 2 ^ (k + 1) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    intro i hi
    obtain ⟨hpm, hpme⟩ := hπe m hm1 he
    obtain ⟨hpg, hpge⟩ := hπe _ hg256 hge
    have a1 := hs _ hg256 hge _ (hρ i hi)
    rw [hmul m _ hm1 hg256 he hge _ (hρ i hi), ← hρρ _ a1, ih hm1 _ (hρ _ a1), hgen k hk i hi,
      ← hmul _ _ hpm hpg hpme hpge _ hi, hπ]

theorem bindPairs_aux (DP : ℕ) : ∀ (P : List (ℕ × ℕ)) (p : ℕ),
    List.rec (motive := fun _ => Nat → Bool) (fun p => Nat.beq p (nat_lit 28))
      (fun ab _ ih p => bAnd(Nat.blt ab.1 (nat_lit 8), bAnd(Nat.blt ab.2 (nat_lit 8),
        bAnd(Nat.beq ab.1 (pa DP p), bAnd(Nat.beq ab.2 (pb DP p), ih (Nat.succ p)))))) P p = true →
    p + P.length = 28 ∧ ∀ j (hj : j < P.length), P[j] = (pa DP (p + j), pb DP (p + j))
  | [], p, h => by
    have : p = 28 := Nat.eq_of_beq_eq_true h
    simp [this]
  | ab :: P, p, h => by
    obtain ⟨-, h2⟩ := band_true h
    obtain ⟨-, h3⟩ := band_true h2
    obtain ⟨h3, h4⟩ := band_true h3
    obtain ⟨h4, h5⟩ := band_true h4
    obtain ⟨ih1, ih2⟩ := bindPairs_aux DP P (Nat.succ p) h5
    refine ⟨by simp only [List.length_cons]; omega, ?_⟩
    intro j hj
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero, Nat.add_zero]
      exact Prod.ext (Nat.eq_of_beq_eq_true h3) (Nat.eq_of_beq_eq_true h4)
    | succ j =>
      have e : p + (j + 1) = Nat.succ p + j := by omega
      simpa [e] using ih2 j (by simpa using hj)

theorem code_eq (c : ℕ) : c = 8 * Nat.shiftRight c (nat_lit 3) + Nat.land c (nat_lit 7) := by
  have e1 : Nat.shiftRight c 3 = c / 8 := Nat.shiftRight_eq_div_pow c 3
  have e2 : Nat.land c 7 = c % 8 := Nat.and_two_pow_sub_one_eq_mod c 3
  change c = 8 * Nat.shiftRight c 3 + Nat.land c 7
  rw [e1, e2]
  omega

theorem pairs_facts {DP : ℕ} {P : List (ℕ × ℕ)} (hp : bindPairs DP P = true) :
    P.length = 28 ∧ (∀ q (hq : q < P.length), P[q] = (pa DP q, pb DP q)) ∧ P.Nodup := by
  obtain ⟨h1, h2⟩ := band_true hp
  obtain ⟨l1, l2⟩ := bindPairs_aux DP P 0 h2
  rw [Orb.allN_iff] at h1
  have hstep : ∀ q < 27, pg (nat_lit 8) (nat_lit 255) DP q < pg (nat_lit 8) (nat_lit 255) DP (q + 1) :=
    fun q hq => blt_true (h1 q hq)
  have mono : ∀ a b, a < b → b < 28 →
      pg (nat_lit 8) (nat_lit 255) DP a < pg (nat_lit 8) (nat_lit 255) DP b := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | h
      · exact (ih h (by omega)).trans (hstep b (by omega))
      · subst h
        exact hstep a (by omega)
  refine ⟨by omega, fun q hq => by simpa using l2 q hq, ?_⟩
  rw [List.nodup_iff_injective_getElem]
  intro a b hab
  have ea := l2 a.val a.isLt
  have eb := l2 b.val b.isLt
  simp only [Nat.zero_add] at ea eb
  have hc : pg (nat_lit 8) (nat_lit 255) DP a.val = pg (nat_lit 8) (nat_lit 255) DP b.val := by
    have h' : (pa DP a.val, pb DP a.val) = (pa DP b.val, pb DP b.val) := by
      rw [← ea, ← eb]
      exact hab
    simp only [Prod.mk.injEq] at h'
    unfold pa pb at h'
    have c1 := code_eq (pg (nat_lit 8) (nat_lit 255) DP a.val)
    have c2 := code_eq (pg (nat_lit 8) (nat_lit 255) DP b.val)
    omega
  apply Fin.ext
  rcases Nat.lt_trichotomy a.val b.val with h | h | h
  · exact absurd hc (mono _ _ h (by omega)).ne
  · exact h
  · exact absurd hc (mono _ _ h (by omega)).ne'

theorem swap_cf {a b x : ℕ} (hab : a < b) (hb : b < 8) (hx : x < 4294967296) :
    ∀ k < 8, cf (swapKey a b x) k = if k = a then cf x b else if k = b then cf x a else cf x k := by
  have hs : swapKey a b x = x - cf x a * 16 ^ a - cf x b * 16 ^ b +
      (cf x b * 16 ^ a + cf x a * 16 ^ b) := by
    unfold swapKey
    rw [Orb.strictN_eq, Orb.strictN_eq]
    simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.add_eq, Nat.sub_eq, Nat.mul_eq, pow_mul]
    norm_num
  have hsumN : ∀ f : ℕ → ℕ, ∑ k ∈ Finset.range 8, f k * 16 ^ k = f 0 + 16 * f 1 + 256 * f 2 +
      4096 * f 3 + 65536 * f 4 + 1048576 * f 5 + 16777216 * f 6 + 268435456 * f 7 := fun f => by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  have hsumZ : ∀ f : ℕ → ℤ, ∑ k ∈ Finset.range 8, f k * 16 ^ k = f 0 + 16 * f 1 + 256 * f 2 +
      4096 * f 3 + 65536 * f 4 + 1048576 * f 5 + 16777216 * f 6 + 268435456 * f 7 := fun f => by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  have exN : x = ∑ k ∈ Finset.range 8, cf x k * 16 ^ k := by
    rw [hsumN]
    exact expand8 hx
  have exZ : (x : ℤ) = ∑ k ∈ Finset.range 8, (cf x k : ℤ) * 16 ^ k := by exact_mod_cast exN
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ, c = fun k => if k = a then cf x b else if k = b then cf x a
      else cf x k := ⟨_, rfl⟩
  have hcl : ∀ k, c k < 16 := fun k => by
    rw [hc]
    dsimp only
    split_ifs <;> exact cf_lt _ _
  have hdiff : ∑ k ∈ Finset.range 8, (c k : ℤ) * 16 ^ k - ∑ k ∈ Finset.range 8, (cf x k : ℤ) * 16 ^ k =
      ((cf x b : ℤ) - cf x a) * 16 ^ a + ((cf x a : ℤ) - cf x b) * 16 ^ b := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_add a b (by omega)
      (fun k _ hk => by simp [hc, hk.1, hk.2]) (fun h => by simp at h; omega)
      (fun h => by simp at h; omega)]
    have hba : b ≠ a := by omega
    simp only [hc, ite_true, hba, ite_false]
    ring
  have hle : cf x a * 16 ^ a + cf x b * 16 ^ b ≤ x := by
    have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k => cf x k * 16 ^ k)
      (s := {a, b}) (t := Finset.range 8)
      (fun k hk => by simp only [Finset.mem_insert, Finset.mem_singleton] at hk; simp; omega)
      (fun _ _ _ => Nat.zero_le _)
    rw [Finset.sum_pair (by omega)] at this
    exact this.trans exN.symm.le
  have hY : (swapKey a b x : ℤ) = ∑ k ∈ Finset.range 8, (c k : ℤ) * 16 ^ k := by
    have h1 : (swapKey a b x : ℤ) = x - ((cf x a * 16 ^ a : ℕ) : ℤ) - ((cf x b * 16 ^ b : ℕ) : ℤ) +
        ((cf x b * 16 ^ a : ℕ) : ℤ) + ((cf x a * 16 ^ b : ℕ) : ℤ) := by
      rw [hs]
      generalize cf x a * 16 ^ a = A1 at hle ⊢
      generalize cf x b * 16 ^ b = A2 at hle ⊢
      generalize cf x b * 16 ^ a = A3
      generalize cf x a * 16 ^ b = A4
      omega
    rw [h1]
    push_cast
    linear_combination exZ - hdiff
  have hYlt : swapKey a b x < 4294967296 := by
    have h := hY
    rw [hsumZ] at h
    have := hcl 0
    have := hcl 1
    have := hcl 2
    have := hcl 3
    have := hcl 4
    have := hcl 5
    have := hcl 6
    have := hcl 7
    omega
  have u := digitsZ hYlt (fun k => (c k : ℤ)) (fun k _ => ⟨by positivity, by exact_mod_cast hcl k⟩)
    (by rw [hY, hsumZ])
  intro k hk
  have := u k hk
  rw [hc] at this
  exact_mod_cast this

theorem swap_vec {a b x : ℕ} (hab : a < b) (hb : b < 8) (hx : x < 4294967296) (ia ib : Fin 8)
    (ha' : (ia : ℕ) = a) (hb' : (ib : ℕ) = b) :
    vecOf (swapKey a b x) = permVecL (Equiv.swap ia ib) (vecOf x) := by
  conv_lhs => rw [vecOf, List.ofFn_eq_map]
  rw [permVecL]
  congr 1
  funext k
  rw [vecOf_getD, swap_cf hab hb hx k k.isLt, Equiv.symm_swap, Equiv.swap_apply_def]
  by_cases h1 : (k : ℕ) = a
  · have : k = ia := Fin.ext (by rw [h1, ha'])
    rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true this), hb']
  · have n1 : k ≠ ia := fun h => h1 (by rw [h, ha'])
    rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false n1)]
    by_cases h2 : (k : ℕ) = b
    · have : k = ib := Fin.ext (by rw [h2, hb'])
      rw [ite_eq_left_of_eq_true _ _ (eq_true h2), ite_eq_left_of_eq_true _ _ (eq_true this), ha']
    · have n2 : k ≠ ib := fun h => h2 (by rw [h, hb'])
      rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ite_eq_right_of_eq_false _ _ (eq_false n2)]

public theorem swap_tab {L : List (List ℤ)} {RK : ℕ → ℕ} {SO a b T : ℕ}
    (hb : bindRoots RK L = true) (hs : sortedOK RK SO = true) (hrow : swapRowOK RK a b T = true)
    (ia ib : Fin 8) (ha' : (ia : ℕ) = a) (hb' : (ib : ℕ) = b) :
    permArrL L (Equiv.swap ia ib) = unpack 240 8 T ∧ ∀ i < 240, pg 8 (mask 8) T i < 240 := by
  obtain ⟨-, hf⟩ := bind_facts hb
  unfold swapRowOK at hrow
  obtain ⟨w1, w2⟩ := band_true hrow
  obtain ⟨w2, w3⟩ := band_true w2
  rw [Orb.allN_iff] at w3
  have hrow' : ∀ i < 240, pg 8 (mask 8) T i < 240 ∧ RK (pg 8 (mask 8) T i) = swapKey a b (RK i) :=
    fun i hi => by
      have := w3 i hi
      rw [Orb.strictB_eq] at this
      obtain ⟨e1, e2⟩ := band_true this
      exact ⟨blt_true e1, Nat.eq_of_beq_eq_true e2⟩
  refine ⟨?_, fun i hi => (hrow' i hi).1⟩
  unfold permArrL unpack
  apply congrArg Array.ofFn
  funext i
  obtain ⟨e1, e2⟩ := hrow' i.val i.isLt
  obtain ⟨xi, -, vi⟩ := hf i.val i.isLt
  obtain ⟨-, -, ve⟩ := hf _ e1
  have : (List.finRange 8).map (fun k => (L.getD i.val []).getD ((Equiv.swap ia ib).symm k : ℕ) 0) =
      L.getD (pg 8 (mask 8) T i.val) [] := by
    rw [ve, e2, swap_vec (blt_true w1) (blt_true w2) xi ia ib ha' hb', vi]
    rfl
  rw [this, idxOf_root hb hs e1]

end CFSG.KLC.E8

public section

namespace CFSG.KLC.E8

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem d8_sound {L : List (List ℤ)} {P : List (ℕ × ℕ)} {RK RT ST PT : Nat → Nat} {SO DP : Nat}
    (hb : bindRoots RK L = true) (hs : sortedOK RK SO = true)
    (hr : ∀ r < 240, reflRowOK RK r (RT r) = true) (hst : ∀ m < 256, signRowOK RK m (ST m) = true)
    (hinv : allN 112 (fun r => permOK 240 8 (nat_lit 255) (nat_lit 1920) (RT r) (RT r)) = true)
    (hp : bindPairs DP P = true) (h1 : d1K ST = true) (h2 : d2K RT ST = true)
    (h3 : ∀ p < 28, d3At RT ST DP p = true) (h5 : d5K RK RT PT DP = true) :
    dCheckWithL L P (reflArrsL L) (signArrsL L) = true := by
  obtain ⟨hl, hf⟩ := bind_facts hb
  obtain ⟨pl, pget, pnd⟩ := pairs_facts hp
  have hrefl := refl_sound hb hs hr
  have hsign := signs_sound hb hs hst
  have RA_get : ∀ r < 240, ∀ i < 240, ((reflArrsL L)[r]!)[i]! = pg 8 (mask 8) (RT r) i :=
    fun r hr' i hi => by rw [reflArrs_get hr', hrefl r hr', Orb.unpack_get hi]
  have SA_get : ∀ m < 256, framePop m % 2 = 0 → ∀ i < 240,
      ((signArrsL L)[m]!)[i]! = pg 8 (mask 8) (ST m) i :=
    fun m hm he i hi => by rw [signArrs_get hm, hsign m hm he, Orb.unpack_get hi]
  have pair_q : ∀ p ∈ P, ∃ q < 28, P.idxOf p = q ∧ p = (pa DP q, pb DP q) := fun p hp' => by
    obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.1 hp'
    exact ⟨q, by omega, pnd.idxOf_getElem q hq, pget q hq⟩
  have d5q : ∀ q < 28, pa DP q < pb DP q ∧ pb DP q < 8 ∧
      (∀ i < 240, pg 8 (mask 8) (PT q) i < 240 ∧
        RK (pg 8 (mask 8) (PT q) i) = swapKey (pa DP q) (pb DP q) (RK i)) ∧
      PT q = RT (4 * q + 1) := fun q hq => by
    unfold d5K at h5
    rw [Orb.allN_iff] at h5
    obtain ⟨hw, he⟩ := band_true (h5 q hq)
    unfold swapRowOK at hw
    obtain ⟨w1, w2⟩ := band_true hw
    obtain ⟨w2, w3⟩ := band_true w2
    rw [Orb.allN_iff] at w3
    refine ⟨blt_true w1, blt_true w2, fun i hi => ?_, Nat.eq_of_beq_eq_true he⟩
    have := w3 i hi
    rw [Orb.strictB_eq] at this
    obtain ⟨e1, e2⟩ := band_true this
    exact ⟨blt_true e1, Nat.eq_of_beq_eq_true e2⟩
  have permq : ∀ q < 28, permArrL L (Equiv.swap (Fin.ofNat 8 (pa DP q)) (Fin.ofNat 8 (pb DP q))) =
      unpack 240 8 (PT q) := fun q hq => by
    obtain ⟨ab, bb, -, -⟩ := d5q q hq
    unfold d5K at h5
    rw [Orb.allN_iff] at h5
    obtain ⟨hw, -⟩ := band_true (h5 q hq)
    refine (swap_tab hb hs hw _ _ ?_ ?_).1
    · rw [Fin.val_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    · rw [Fin.val_ofNat]
      exact Nat.mod_eq_of_lt bb
  unfold dCheckWithL
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  ·
    rw [List.all_eq_true]
    intro r hr'
    rw [List.mem_range] at hr'
    by_cases h112 : r < 112
    · simp [h112]
    unfold d1K at h1
    rw [Orb.allN_iff] at h1
    have hx := h1 r hr'
    have hc : Nat.blt r (nat_lit 112) = false := by
      rw [Bool.eq_false_iff]
      intro h
      exact h112 (blt_true h)
    rw [hc] at hx
    change allN 256 _ = true at hx
    rw [Orb.allN_iff] at hx
    simp only [Bool.or_eq_true, decide_eq_true_eq, h112, false_or, List.all_eq_true, List.mem_range]
    intro m hm
    have hm' := hx m hm
    by_cases he : framePop m % 2 = 0
    · by_cases h0 : m = 0
      · simp [h0]
      have hb' : bAnd(evenB m, Nat.blt (nat_lit 0) m) = true := by
        rw [Orb.bAnd_eq, evenB_eq, Bool.and_eq_true, decide_eq_true_iff, Nat.blt_eq]
        exact ⟨he, Nat.pos_of_ne_zero h0⟩
      rw [hb'] at hm'
      change notB' _ = true at hm'
      rw [notB'_eq, Bool.not_eq_true', Bool.eq_false_iff] at hm'
      have hne : ((signArrsL L)[m]!)[r]! ≠ r := by
        rw [SA_get m hm he r hr']
        intro hfix
        exact hm' (by rw [Nat.beq_eq]; exact hfix)
      simp [he, h0, hne]
    · simp [he]
  ·
    rw [allLt_iff]
    intro r hr'
    unfold d2K at h2
    rw [Orb.strictB_eq, Orb.allN_iff] at h2
    have hx := h2 r hr'
    rw [Orb.strictB_eq] at hx
    set X := pcomp (nat_lit 240) (nat_lit 8) (nat_lit 255) (RT (nat_lit 1)) (RT r) with hXdef
    have hX' : X = pcomp 240 8 (mask 8) (RT 1) (RT r) := rfl
    have hXlt : ∀ i < 240, pg 8 (mask 8) X i < 240 := fun i hi => by
      rw [hX', PF.pg_pcomp (by norm_num) hi]
      exact rt_lt8 hr (by norm_num) (rt_lt8 hr hr' hi)
    have hXshr : X >>> (240 * 8) = 0 := by
      rw [hX']
      exact PF.pcomp_shr _ _ (by norm_num) (by norm_num)
    have hx_arr : compA 240 (reflArrsL L)[1]! (reflArrsL L)[r]! = unpack 240 8 X := by
      apply arr_ext8 (n := 240) (by simp [compA]) (by simp [unpack])
      intro i hi
      rw [compA_get hi, RA_get r hr' i hi, RA_get 1 (by norm_num) _ (rt_lt8 hr hr' hi),
        Orb.unpack_get hi, hX', PF.pg_pcomp (by norm_num) hi]
    have hv := hXlt 112 (by norm_num)
    have key : ∀ m < 256, (framePop m % 2 == 0 && eqA 240 (unpack 240 8 X) (signArrsL L)[m]!) =
        (evenB m && Nat.beq X (Nat.land (ST m) (mask (nat_lit 1920)))) := by
      intro m hm
      rw [evenB_eq]
      by_cases he : framePop m % 2 = 0
      · rw [signArrs_get hm, hsign m hm he, eqA_low hXshr]
        simp [he]
      · simp [he]
    have hmemE : memE (signArrsL L) (compA 240 (reflArrsL L)[1]! (reflArrsL L)[r]!) =
        (decide (112 ≤ pg 8 (mask 8) X 112) &&
          ((evenB (2 * (pg 8 (mask 8) X 112 - 112)) &&
            Nat.beq X (Nat.land (ST (2 * (pg 8 (mask 8) X 112 - 112))) (mask (nat_lit 1920)))) ||
          (evenB (2 * (pg 8 (mask 8) X 112 - 112) + 1) &&
            Nat.beq X (Nat.land (ST (2 * (pg 8 (mask 8) X 112 - 112) + 1)) (mask (nat_lit 1920)))))) := by
      rw [hx_arr]
      unfold memE
      dsimp only
      rw [Orb.unpack_get (by norm_num : 112 < 240), key (2 * (pg 8 (mask 8) X 112 - 112)) (by omega),
        key (2 * (pg 8 (mask 8) X 112 - 112) + 1) (by omega)]
    have hmemK : memK ST X =
        (Nat.ble 112 (pg 8 (mask 8) X 112) &&
          ((evenB (2 * (pg 8 (mask 8) X 112 - 112)) &&
            Nat.beq X (Nat.land (ST (2 * (pg 8 (mask 8) X 112 - 112))) (mask (nat_lit 1920)))) ||
          (evenB (2 * (pg 8 (mask 8) X 112 - 112) + 1) &&
            Nat.beq X (Nat.land (ST (2 * (pg 8 (mask 8) X 112 - 112) + 1)) (mask (nat_lit 1920)))))) := by
      unfold memK
      simp only [Orb.strictB_eq]
      rfl
    have heq : memE (signArrsL L) (compA 240 (reflArrsL L)[1]! (reflArrsL L)[r]!) = memK ST X := by
      rw [hmemE, hmemK]
      have hble : Nat.ble 112 (pg 8 (mask 8) X 112) = decide (112 ≤ pg 8 (mask 8) X 112) := by
        rw [Bool.eq_iff_iff, Nat.ble_eq, decide_eq_true_iff]
      rw [hble]
    rw [heq]
    cases hk : memK ST X
    · rw [hk] at hx
      change notB' _ = true at hx
      rw [notB'_eq, Bool.not_eq_true', Bool.eq_false_iff] at hx
      have : ¬ r < 4 := fun h => hx (by rw [Nat.blt_eq]; exact h)
      simp [this]
    · rw [hk] at hx
      change Nat.blt _ _ = true at hx
      have : r < 4 := blt_true hx
      simp [this]
  ·
    rw [List.all_eq_true]
    intro p hp'
    obtain ⟨q, hq, hidx, rfl⟩ := pair_q p hp'
    obtain ⟨ab, bb, -, -⟩ := d5q q hq
    rw [hidx]
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    have hconj : ∀ s < 2, (List.range 256).all (fun m => !(framePop m % 2 == 0) ||
        eqA 240 (compA 240 (compA 240 (reflArrsL L)[4 * q + s]! (signArrsL L)[m]!)
          (reflArrsL L)[4 * q + s]!)
          (signArrsL L)[permMask (Equiv.swap (Fin.ofNat 8 (pa DP q)) (Fin.ofNat 8 (pb DP q))) m]!) =
        true := by
      intro s hs2
      have hj : 4 * q + s < 112 := by omega
      set ρ := fun i => pg 8 (mask 8) (RT (4 * q + s)) i
      set σ := Equiv.swap (Fin.ofNat 8 (pa DP q)) (Fin.ofNat 8 (pb DP q))
      have hρ : ∀ i < 240, ρ i < 240 := fun i hi => rt_lt8 hr (by omega) hi
      have hρρ : ∀ i < 240, ρ (ρ i) = i := fun i hi => by
        rw [Orb.allN_iff] at hinv
        exact (Orb.permOK_facts (n := 240) (w := 8) (hinv _ hj)).2.2 i hi |>.2
      have hgen : ∀ k < 7, ∀ i < 240, ρ (pg 8 (mask 8) (ST (1 + 2 ^ (k + 1))) (ρ i)) =
          pg 8 (mask 8) (ST (permMask σ (1 + 2 ^ (k + 1)))) i := by
        intro k hk i hi
        obtain ⟨hg256, -⟩ := gk_even hk
        rw [permMask_swap ab bb hg256]
        have h3q := h3 q hq
        unfold d3At at h3q
        rw [Orb.allN_iff] at h3q
        have hx := h3q s hs2
        rw [Orb.strictB_eq, Orb.allN_iff] at hx
        have hx2 := hx k hk
        rw [Orb.strictB_eq] at hx2
        have e := Nat.eq_of_beq_eq_true hx2
        have hm : Nat.add (nat_lit 1) (Nat.shiftLeft (nat_lit 2) k) = 1 + 2 ^ (k + 1) := by
          rw [Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, pow_succ]
          ring
        have hR : Nat.add (Nat.mul (nat_lit 4) q) s = 4 * q + s := rfl
        rw [hm, hR] at e
        have e' := congrArg (fun Y => pg 8 (mask 8) Y i) e
        change pg 8 (mask 8) (pcomp 240 8 (mask 8) (pcomp 240 8 (mask 8) (RT (4 * q + s))
          (ST (1 + 2 ^ (k + 1)))) (RT (4 * q + s))) i =
          pg 8 (mask 8) (Nat.land (ST (swapMask (pa DP q) (pb DP q) (1 + 2 ^ (k + 1))))
            (mask (nat_lit 1920))) i at e'
        rw [PF.pg_pcomp (by norm_num) hi, PF.pg_pcomp (by norm_num) (hρ i hi), pg_low8 hi] at e'
        exact e'
      have hall := conj_all ρ (fun m i => pg 8 (mask 8) (ST m) i) (permMask σ) hρ hρρ
        (fun m hm he i hi => (st_facts hb hst hm he hi).1)
        (fun m m' hm hm' he he' i hi => st_mul hb hs hst hm hm' he he' hi)
        (fun i hi => st_zero hb hs hst hi) (permMask_xor σ) (permMask_zero σ)
        (fun m hm he => permMask_even σ hm he) hgen
      rw [List.all_eq_true]
      intro m hm
      rw [List.mem_range] at hm
      by_cases he : framePop m % 2 = 0
      · simp only [he, beq_self_eq_true, Bool.not_true, Bool.false_or]
        obtain ⟨hpm, hpme⟩ := permMask_even σ hm he
        apply eqA_of
        intro i hi
        have hRi : ((reflArrsL L)[4 * q + s]!)[i]! < 240 := by
          rw [RA_get (4 * q + s) (by omega) i hi]
          exact hρ i hi
        rw [compA_get hi, compA_get hRi, RA_get (4 * q + s) (by omega) i hi,
          SA_get m hm he _ (hρ i hi),
          RA_get (4 * q + s) (by omega) _ (st_facts hb hst hm he (hρ i hi)).1,
          SA_get _ hpm hpme i hi]
        exact hall m hm he i hi
      · simp [he]
    exact ⟨hconj 0 (by norm_num), hconj 1 (by norm_num)⟩
  · rw [allLt_iff]
    intro r hr'
    rw [idxOf_root hb hs hr']
    exact beq_self_eq_true r
  · simp [hl]
  · rw [allLt_iff]
    intro r hr'
    rw [(hf r hr').2.2]
    simp [vecOf]
  ·
    rw [List.all_eq_true]
    intro p hp'
    obtain ⟨q, hq, hidx, rfl⟩ := pair_q p hp'
    obtain ⟨ab, bb, hrow, hPT⟩ := d5q q hq
    rw [hidx, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [allLt_iff]
      intro r hr'
      have e := congrArg (fun A => A[r]!) (permq q hq)
      simp only [permArrL, getElem!_ofFn_nat _ hr', Orb.unpack_get hr'] at e
      rw [decide_eq_true_iff]
      unfold permVecL
      rw [e]
      exact (hrow r hr').1
    · rw [permq q hq, hPT, reflArrs_get (r := 4 * q + 1) (by omega), hrefl (4 * q + 1) (by omega)]
      exact eqA_of fun i _ => rfl

end CFSG.KLC.E8

end
