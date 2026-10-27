module

public import CFSG.Certificates.Kernel.KStep.Defs
import CFSG.Monster.AxisCount.DenseNative
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.KC.KStep

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP
open CFSG.Monster.AxisCount CFSG.Monster.B.Rep4371.Native

variable {M : ℕ} {h : ZMod M}

theorem kn_pow_cancel (h2 : 2 * h = 1) (n : ℕ) : (2 : ZMod M) ^ n * h ^ n = 1 := by
  rw [← mul_pow, h2, one_pow]

theorem kn_map_range_get {α : Type} [Inhabited α] (f : ℕ → α) {n a : ℕ} (ha : a < n) :
    ((Array.range n).map f)[a]! = f a := by
  rw [getElem!_pos _ a (by simp [ha]), Array.getElem_map, Array.getElem_range]

theorem kn_map_ite_sum (L : List (ℕ × ℤ)) (q : ℕ) (x : ℤ) :
    (L.map fun t => if t.1 = q then t.2 * x else 0).sum =
      ((L.filter fun t => decide (t.1 = q)).map Prod.snd).sum * x := by
  induction L with
  | nil => simp
  | cons t L ih => by_cases ht : t.1 = q <;> simp [ht, ih, add_mul]

theorem kn_scatter_getD (off n : ℕ) (T : ℕ → List (ℕ × ℤ)) (D : Array ℤ) {q : ℕ} (hq : q < n) :
    (Native.scatterAt off n T D).getD q 0 =
      ∑ p ∈ Finset.range n, scat T p q * D.getD (off + p) 0 := by
  rw [Native.scatterAt_getD _ _ _ _ _ hq]
  simp only [kn_map_ite_sum]
  rfl

theorem kn_aPos_lt : ∀ z < 300, (Native.aPos z).1 < 24 ∧ (Native.aPos z).2 < 24 := by
  decide +kernel

theorem kn_latA_getD (G D : Array ℤ) {z : ℕ} (hz : z < 300) :
    (Native.latA G D).getD z 0 = ∑ k ∈ Finset.range 24, ∑ l ∈ Finset.range 24,
      G.getD (k * 24 + (Native.aPos z).1) 0 * D.getD (Native.aIdx k l) 0 *
        G.getD (l * 24 + (Native.aPos z).2) 0 := by
  obtain ⟨h1, h2⟩ := kn_aPos_lt z hz
  simp only [Native.latA]
  rw [Native.getD_ofFn _ _ hz, Native.getElem!_eq_getD']
  exact Native.latA_aIdx_aux G D _ _ h1 h2

theorem kn_wMul_getD (G D : Array ℤ) {p : ℕ} (hp : p < 98304) :
    (Native.wMul G D).getD p 0 =
      ∑ j ∈ Finset.range 24, D.getD (98580 + p / 24 * 24 + j) 0 * G.getD (j * 24 + p % 24) 0 := by
  unfold Native.wMul
  rw [Native.getD_ofFn _ _ hp, Native.sumRange_eq]
  simp only [Native.getElem!_eq_getD']

theorem kn_popcN_zero : ∀ k, popcN k 0 = 0
  | 0 => rfl
  | k + 1 => by simp [popcN, kn_popcN_zero k]

theorem kn_parN_zero (k : ℕ) : parN k 0 = false := by simp [parN, kn_popcN_zero]

theorem kn_pairN_zero_r (x : ℕ) : pairN x 0 = false := by simp [pairN, kn_parN_zero]

theorem kn_pairN_zero_l (x : ℕ) : pairN 0 x = false := by simp [pairN, kn_parN_zero]

theorem kn_qGN_zero : qGN 0 = false := by decide

theorem kn_bGN_zero_r (μ : ℕ) : bGN μ 0 = false := by simp [bGN, kn_parN_zero]

theorem kn_bGN_zero_l (ν : ℕ) : bGN 0 ν = false := by simp [bGN, kn_parN_zero]

theorem kn_thetaN_zero : thetaN 0 = 0 := by decide

theorem kn_combN_zero (m : ℕ → ℕ) : ∀ n, combN m n 0 = 0
  | 0 => rfl
  | n + 1 => by simp [combN, kn_combN_zero m n]

theorem kn_combN_xor (m : ℕ → ℕ) (n a b : ℕ) :
    combN m n (a ^^^ b) = combN m n a ^^^ combN m n b := by
  induction n with
  | zero => simp [combN]
  | succ n ih =>
    rw [combN, combN, combN, ih, Nat.testBit_xor]
    apply Nat.eq_of_testBit_eq
    intro i
    cases a.testBit n <;> cases b.testBit n <;>
      simp only [Bool.xor_false, Bool.xor_true, Bool.not_true, Bool.not_false, Bool.false_eq_true,
        ↓reduceIte, Nat.testBit_xor, Nat.zero_testBit] <;>
      cases (combN m n a).testBit i <;> cases (combN m n b).testBit i <;>
      cases (m n).testBit i <;> rfl

theorem kn_testBit_packN (f : ℕ → Bool) :
    ∀ n j, (packN f n).testBit j = (decide (j < n) && f j)
  | 0, j => by simp [packN]
  | n + 1, j => by
    rw [packN, Nat.testBit_or, kn_testBit_packN f n]
    by_cases hj : j = n
    · subst hj
      cases f j <;> simp
    · have hj' : (decide (j < n + 1)) = decide (j < n) := by
        rcases Nat.lt_or_ge j n with h | h
        · simp [h, Nat.lt_succ_of_lt h]
        · have : n < j := lt_of_le_of_ne h (Ne.symm hj)
          simp [Nat.not_lt.2 h, Nat.not_lt.2 (Nat.succ_le_of_lt this)]
      rw [hj']
      split_ifs <;> simp [Ne.symm hj]

theorem kn_packN_lt (f : ℕ → Bool) (n : ℕ) : packN f n < 2 ^ n := by
  induction n with
  | zero => simp [packN]
  | succ n ih =>
    simp only [packN]
    refine Nat.or_lt_two_pow (lt_trans ih (Nat.pow_lt_pow_right (by norm_num) (by omega))) ?_
    split_ifs
    · exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    · positivity

theorem kn_permCN_lt (p : Array ℕ) (a : ℕ) : permCN p a < 4096 := by
  unfold permCN coeffN
  exact kn_packN_lt _ 12

theorem kn_xorSum_succ' (f : ℕ → Bool) : ∀ k,
    xorSum f (k + 1) = (f 0 ^^ xorSum (fun i => f (i + 1)) k)
  | 0 => by simp [xorSum]
  | k + 1 => by
    rw [xorSum, kn_xorSum_succ' f k, xorSum, Bool.xor_assoc]

theorem kn_parN_eq : ∀ k a, parN k a = xorSum a.testBit k
  | 0, _ => rfl
  | k + 1, a => by
    have ih := kn_parN_eq k (a / 2)
    have hf : (fun i => a.testBit (i + 1)) = (a / 2).testBit := funext fun i => Nat.testBit_succ a i
    unfold parN at ih ⊢
    rw [kn_xorSum_succ', hf, ← ih, popcN, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one a with h | h <;>
      rcases Nat.mod_two_eq_zero_or_one (popcN k (a / 2)) with h' | h' <;>
      simp [Nat.add_mod, h, h']

theorem kn_xorSum_congr {f g : ℕ → Bool} : ∀ {n}, (∀ i < n, f i = g i) → xorSum f n = xorSum g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [xorSum]
    rw [kn_xorSum_congr (fun i hi => h i (by omega)), h n (by omega)]

theorem kn_xorSum_false : ∀ n, xorSum (fun _ => false) n = false
  | 0 => rfl
  | n + 1 => by simp [xorSum, kn_xorSum_false n]

theorem kn_xorSum_xor (f g : ℕ → Bool) : ∀ n,
    xorSum (fun i => f i ^^ g i) n = (xorSum f n ^^ xorSum g n)
  | 0 => rfl
  | n + 1 => by
    simp only [xorSum]
    rw [kn_xorSum_xor f g n]
    have h4 : ∀ a b c d : Bool, ((a ^^ b) ^^ (c ^^ d)) = ((a ^^ c) ^^ (b ^^ d)) := by decide
    exact h4 _ _ _ _

theorem kn_dualN_xor (u v : ℕ) : dualN (u ^^^ v) = dualN u ^^^ dualN v := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [dualN, Nat.testBit_xor, kn_testBit_packN]
  rw [kn_parN_eq, kn_parN_eq, kn_parN_eq]
  have hf : ((u ^^^ v) &&& bmaskN i).testBit =
      fun j => (u &&& bmaskN i).testBit j ^^ (v &&& bmaskN i).testBit j := by
    funext j
    simp only [Nat.testBit_and, Nat.testBit_xor]
    cases u.testBit j <;> cases v.testBit j <;> cases (bmaskN i).testBit j <;> rfl
  rw [hf, kn_xorSum_xor]
  cases decide (i < 12) <;> simp

theorem kn_permDN_xor (p : Array ℕ) (x y : ℕ) :
    permDN p (x ^^^ y) = permDN p x ^^^ permDN p y := by
  unfold permDN permWordN CFSG.Monster.B.Rep4371.Native.repN
  rw [kn_combN_xor, kn_combN_xor, kn_dualN_xor]

theorem kn_permCN_zero (p : Array ℕ) : permCN p 0 = 0 := by
  unfold permCN permWordN wordN
  rw [kn_combN_zero, kn_combN_zero]
  decide

theorem kn_kappaN_zero (p : Array ℕ) : kappaN p 0 = false := by
  simp [kappaN, kn_xorSum_false]

theorem kn_betaTab_get (p : Array ℕ) {i j : ℕ} (hi : i < 12) (hj : j < 12) :
    (Native.betaTab p)[12 * i + j]! = betaPN p i j := by
  have h : 12 * i + j < 144 := by omega
  have e1 : (12 * i + j) / 12 = i := by omega
  have e2 : (12 * i + j) % 12 = j := by omega
  rw [Native.getElem!_eq_getD_gen, Native.betaTab, Native.getD_ofFn _ _ h]
  simp only [e1, e2]

theorem kn_kappaT_eq (p : Array ℕ) (a : ℕ) : Native.kappaT (Native.betaTab p) a = kappaN p a := by
  unfold Native.kappaT kappaN
  refine kn_xorSum_congr fun i hi => kn_xorSum_congr fun j hj => ?_
  rw [kn_betaTab_get p hi hj]

theorem applyGD_e (c : Native.Ctx) (g : Native.GD) (v : Native.DVec) :
    (Native.applyGD c g v).e = v.e + g.eNew := rfl

theorem applyGD_resA (h2 : 2 * h = 1) (c : Native.Ctx) (g : Native.GD) (v : Native.DVec) {z : ℕ}
    (hz : z < 300) :
    resM h (Native.applyGD c g v) z = h ^ (2 * g.latS) *
      ∑ k ∈ Finset.range 24, ∑ l ∈ Finset.range 24,
        ((g.G[k * 24 + (Native.aPos z).1]! : ℤ) : ZMod M) * ((g.G[l * 24 + (Native.aPos z).2]! : ℤ) : ZMod M) *
          resM h v (Native.aIdx k l) := by
  have hge : 2 * g.latS ≤ g.eNew := le_max_left _ _
  have key : (2 : ZMod M) ^ (g.eNew - 2 * g.latS) * h ^ (v.e + g.eNew) =
      h ^ (2 * g.latS) * h ^ v.e := by
    have he : v.e + g.eNew = v.e + 2 * g.latS + (g.eNew - 2 * g.latS) := by omega
    rw [he, pow_add, pow_add]
    linear_combination (h ^ v.e * h ^ (2 * g.latS)) * kn_pow_cancel h2 (g.eNew - 2 * g.latS)
  unfold resM
  rw [Native.applyGD_getD, ite_eq_left hz, kn_latA_getD _ _ hz, applyGD_e]
  simp only [Native.getElem!_eq_getD']
  push_cast
  rw [mul_assoc, key]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem applyGD_resX (h2 : 2 * h = 1) (c : Native.Ctx) (g : Native.GD) (v : Native.DVec) {q : ℕ}
    (hq : q < 98280) :
    resM h (Native.applyGD c g v) (300 + q) =
      ∑ p ∈ Finset.range 98280, ((scat (g.xT c) p q : ℤ) : ZMod M) * resM h v (300 + p) := by
  have key : (2 : ZMod M) ^ g.eNew * h ^ (v.e + g.eNew) = h ^ v.e := by
    rw [pow_add]
    linear_combination (h ^ v.e) * kn_pow_cancel h2 g.eNew
  unfold resM
  rw [Native.applyGD_getD, ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left,
    kn_scatter_getD _ _ _ _ hq, applyGD_e]
  push_cast
  rw [mul_assoc, key, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

theorem applyGD_resW (h2 : 2 * h = 1) (c : Native.Ctx) (g : Native.GD) (v : Native.DVec) {k : ℕ}
    (hk : k < 98304) :
    resM h (Native.applyGD c g v) (98580 + k) = h ^ (g.latS + g.rowS) *
      ∑ p ∈ Finset.range 98304, ((scat g.wT p k : ℤ) : ZMod M) *
        ∑ j ∈ Finset.range 24, ((g.G[j * 24 + p % 24]! : ℤ) : ZMod M) * resM h v (98580 + p / 24 * 24 + j) := by
  have hge : g.latS + g.rowS ≤ g.eNew := le_max_right _ _
  have key : (2 : ZMod M) ^ (g.eNew - g.latS - g.rowS) * h ^ (v.e + g.eNew) =
      h ^ (g.latS + g.rowS) * h ^ v.e := by
    have he : v.e + g.eNew = v.e + (g.latS + g.rowS) + (g.eNew - g.latS - g.rowS) := by omega
    rw [he, pow_add, pow_add]
    linear_combination (h ^ v.e * h ^ (g.latS + g.rowS)) *
      kn_pow_cancel h2 (g.eNew - g.latS - g.rowS)
  have hS : ∑ p ∈ Finset.range 98304, scat g.wT p k * (Native.wMul g.G v.D).getD (0 + p) 0 =
      ∑ p ∈ Finset.range 98304, scat g.wT p k * ∑ j ∈ Finset.range 24,
        v.D.getD (98580 + p / 24 * 24 + j) 0 * g.G.getD (j * 24 + p % 24) 0 :=
    Finset.sum_congr rfl fun p hp => by rw [zero_add, kn_wMul_getD _ _ (Finset.mem_range.1 hp)]
  unfold resM
  rw [Native.applyGD_getD, ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_sub_cancel_left,
    kn_scatter_getD _ _ _ _ hk, hS, applyGD_e]
  simp only [Native.getElem!_eq_getD']
  push_cast
  rw [mul_assoc, key]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem applyTau_res (h2 : 2 * h = 1) (c : Native.Ctx) (v : Native.DVec) {k : ℕ} (hk : k < 196884) :
    resM h (Native.applyTau c v) k = h ^ 3 *
      ∑ p ∈ Finset.range 196884, ((scat (Native.tauT c.tau) p k : ℤ) : ZMod M) * resM h v p := by
  have hD : (Native.applyTau c v).D = Native.scatterAt 0 196884 (Native.tauT c.tau) v.D := by
    simp only [Native.applyTau]
  have he : (Native.applyTau c v).e = v.e + 3 := by simp only [Native.applyTau]
  unfold resM
  rw [hD, he, kn_scatter_getD _ _ _ _ hk, pow_add]
  simp only [zero_add]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

theorem kn_scat_single {T : ℕ → List (ℕ × ℤ)} {p s : ℕ} {x : ℤ} (hp : T p = [(s, x)]) (q : ℕ) :
    scat T p q = if s = q then x else 0 := by
  unfold scat
  rw [hp]
  by_cases h : s = q <;> simp [h]

theorem sum_scat_single {n : ℕ} {T : ℕ → List (ℕ × ℤ)} {σ : ℕ → ℕ} {c : ℕ → ℤ}
    (hT : ∀ p < n, T p = [(σ p, c p)]) (hσ : ∀ p < n, ∀ p' < n, σ p = σ p' → p = p')
    (r : ℕ → ZMod M) (q : ℕ) :
    ∑ p ∈ Finset.range n, ((scat T p q : ℤ) : ZMod M) * r p =
      if h : ∃ p < n, σ p = q then ((c h.choose : ℤ) : ZMod M) * r h.choose else 0 := by
  have hterm : ∀ p ∈ Finset.range n, ((scat T p q : ℤ) : ZMod M) * r p =
      if σ p = q then ((c p : ℤ) : ZMod M) * r p else 0 := by
    intro p hp
    rw [kn_scat_single (hT p (Finset.mem_range.1 hp))]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hterm]
  by_cases hex : ∃ p < n, σ p = q
  · rw [dite_eq_left hex]
    obtain ⟨h1, h2⟩ := hex.choose_spec
    rw [Finset.sum_eq_single hex.choose]
    · rw [ite_eq_left h2]
    · intro b hb hne
      rw [ite_eq_right]
      intro hb'
      exact hne (hσ b (Finset.mem_range.1 hb) _ h1 (hb'.trans h2.symm))
    · intro hn
      exact absurd (Finset.mem_range.2 h1) hn
  · rw [dite_eq_right hex]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [ite_eq_right]
    intro h
    exact hex ⟨p, Finset.mem_range.1 hp, h⟩

theorem thetaTab_get {a : ℕ} (ha : a < 4096) : (Native.thetaTab ())[a]! = thetaN a :=
  kn_map_range_get thetaN ha

theorem kn_key_pair : ∀ q < 552, keyQ q ≠ (0, 0) := by decide +kernel

theorem kn_dual_pow_ne : ∀ i < 24, dualN (2 ^ i) ≠ 0 := by decide +kernel

theorem kn_octTab_size : (Native.octTab ()).size = 759 := by decide +kernel

theorem kn_octTab_ne {x : ℕ} (hx : x ∈ Native.octTab ()) : x ≠ 0 ∧ x ≠ 63 := by
  unfold Native.octTab at hx
  rw [List.mem_toArray, List.mem_filter] at hx
  obtain ⟨-, hx⟩ := hx
  constructor <;> rintro rfl <;> revert hx <;> decide +kernel

theorem kn_getElem!_mem {T : Array ℕ} {i : ℕ} (hi : i < T.size) : T[i]! ∈ T := by
  rw [getElem!_pos T i hi]
  exact Array.getElem_mem hi

theorem keyQ_ne_zero {q : ℕ} (hq : q < 98280) : keyQ q ≠ (0, 0) := by
  by_cases hp1 : q < 552
  · exact kn_key_pair q hp1
  intro he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  unfold keyQ Native.keyAt at h1 h2
  by_cases hp2 : q < 49704
  · simp only [hp1, hp2, ↓reduceIte] at h1 h2
    rw [h1, thetaTab_get (by norm_num), kn_thetaN_zero, Nat.zero_xor] at h2
    exact kn_dual_pow_ne _ (Nat.mod_lt _ (by norm_num)) h2
  · simp only [hp1, hp2, ↓reduceIte] at h1
    have hi : (q - 49704) / 64 < (Native.octTab ()).size := by rw [kn_octTab_size]; omega
    have hmem : (Native.octTab ())[(q - 49704) / 64]! ∈ Native.octTab () := kn_getElem!_mem hi
    obtain ⟨hne0, hne63⟩ := kn_octTab_ne hmem
    unfold Native.octCodeG at h1
    generalize (Native.octTab ())[(q - 49704) / 64]! = x at h1 hne0 hne63
    split_ifs at h1
    · apply hne63
      have hx : x = x ^^^ 63 ^^^ 63 := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      rw [hx, h1, Nat.zero_xor]
    · rw [Nat.xor_zero] at h1
      exact hne0 h1

theorem kn_mkCtx_keys :
    (Native.mkCtx ()).keys = (Array.range 98280).map (Native.keyAt (Native.thetaTab ())) :=
  rfl

theorem mkCtx_keys {p : ℕ} (hp : p < 98280) : (Native.mkCtx ()).keys[p]! = keyQ p := by
  rw [kn_mkCtx_keys, kn_map_range_get _ hp]
  rfl

theorem kn_foldl_insert_of_ne (f : ℕ → ℕ) (k : ℕ) :
    ∀ (l : List ℕ) (m : Std.HashMap ℕ ℕ), (∀ q ∈ l, f q ≠ k) →
      (l.foldl (fun m p => m.insert (f p) p) m)[k]? = m[k]?
  | [], _, _ => rfl
  | a :: l, m, h => by
    rw [List.foldl_cons, kn_foldl_insert_of_ne f k l _ fun q hq => h q (List.mem_cons_of_mem _ hq),
      Std.HashMap.getElem?_insert]
    simp [h a List.mem_cons_self]

theorem kn_foldl_insert (f : ℕ → ℕ) :
    ∀ (l : List ℕ) (m : Std.HashMap ℕ ℕ), l.Nodup → (∀ p ∈ l, ∀ q ∈ l, f p = f q → p = q) →
      ∀ p ∈ l, (l.foldl (fun m p => m.insert (f p) p) m)[f p]? = some p
  | [], _, _, _, p, hp => absurd hp List.not_mem_nil
  | a :: l, m, hnd, hinj, p, hp => by
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hp with rfl | hp
    · rw [kn_foldl_insert_of_ne f _ l _ ?_, Std.HashMap.getElem?_insert_self]
      intro q hq hfq
      obtain rfl := hinj q (List.mem_cons_of_mem _ hq) p List.mem_cons_self hfq
      exact (List.nodup_cons.1 hnd).1 hq
    · exact kn_foldl_insert f l _ (List.nodup_cons.1 hnd).2
        (fun p hp q hq => hinj p (List.mem_cons_of_mem _ hp) q (List.mem_cons_of_mem _ hq)) p hp

theorem kn_mkCtx_pos : (Native.mkCtx ()).pos = Native.mkPos (Native.mkCtx ()).keys := by
  simp only [Native.mkCtx, Native.mkCtxOf]

theorem mkCtx_find (hG : KeysGood) {p : ℕ} (hp : p < 98280) :
    (Native.mkCtx ()).find (keyQ p).1 (keyQ p).2 = p := by
  have hinj : ∀ q ∈ List.range 98280, ∀ q' ∈ List.range 98280,
      Native.keyCode (Native.mkCtx ()).keys[q]!.1 (Native.mkCtx ()).keys[q]!.2 =
        Native.keyCode (Native.mkCtx ()).keys[q']!.1 (Native.mkCtx ()).keys[q']!.2 → q = q' := by
    intro q hq q' hq' h
    rw [List.mem_range] at hq hq'
    rw [mkCtx_keys hq, mkCtx_keys hq'] at h
    obtain ⟨h1, h2⟩ := hG.1 q hq
    obtain ⟨h1', h2'⟩ := hG.1 q' hq'
    unfold Native.keyCode at h
    rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h1', Nat.mod_eq_of_lt h2'] at h
    exact hG.2 q hq q' hq' (Prod.ext (by omega) (by omega))
  have h := kn_foldl_insert
    (fun q => Native.keyCode (Native.mkCtx ()).keys[q]!.1 (Native.mkCtx ()).keys[q]!.2)
    (List.range 98280) ∅ List.nodup_range hinj p (List.mem_range.2 hp)
  rw [← mkCtx_keys hp]
  unfold Native.Ctx.find
  rw [kn_mkCtx_pos, Native.mkPos, Std.HashMap.getD_eq_getD_getElem?, h, Option.getD_some]

theorem mkCtx_th : (Native.mkCtx ()).th = Native.thetaTab () := rfl

theorem mkCtx_tau : (Native.mkCtx ()).tau = Native.mkTauTab () := rfl

theorem kn_xiT (a : ℕ) : conjXiN (false, a, 0) = (false, a &&& 4032, gammaLowN (a % 64)) := by
  simp only [conjXiN, Pauli.s, Pauli.a, Pauli.d, Nat.zero_mod, kn_parN_zero, Bool.false_eq_true,
    ↓reduceIte, Nat.xor_zero, Nat.zero_xor, kn_qGN_zero, kn_bGN_zero_r, Bool.xor_false,
    Nat.zero_and]

theorem kn_xiD (d : ℕ) : conjXiN (false, 0, d) =
    (qGN (gammaLowN (d % 64)), gammaLowN (d % 64), gammaLowN (gammaLowN (d % 64)) ^^^ (d &&& 4032)) := by
  have hν : (d % 64 ^^^ if parN 6 (d % 64) = true then 63 else 0) = gammaLowN (d % 64) := by
    simp only [gammaLowN, Nat.mod_mod]
  simp only [conjXiN, Pauli.s, Pauli.a, Pauli.d, hν, Nat.zero_mod, Nat.zero_xor, Nat.zero_and,
    Nat.xor_zero, kn_bGN_zero_l, Bool.xor_false, Bool.false_xor]

theorem fastAct_rho (q : Pauli) {a d : ℕ} (ha : a < 4096) (hd : d < 4096) :
    Native.fastAct (Native.tabT (conjPauliN q)) (Native.tabD (conjPauliN q)) (false, a, d) =
      (pairN a q.2.2 ^^ pairN q.2.1 d, a, d) := by
  simp only [Native.fastAct, Native.tabT, Native.tabD]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hd, kn_map_range_get _ ha, kn_map_range_get _ hd]
  simp only [Pauli.mul, conjPauliN, Pauli.s, Pauli.a, Pauli.d, kn_pairN_zero_l, kn_pairN_zero_r,
    Nat.xor_zero, Nat.zero_xor, Bool.xor_false, Bool.false_xor]

private theorem fastAct_perm_T {arr : Array Nat} {T : Array Nat}
    (hT : ∀ {i : ℕ}, i < 4096 → T[i]! = thetaN i) {a d : ℕ} (ha : a < 4096) (hd : d < 4096) :
    Native.fastAct (Native.tabTPerm arr (Native.betaTab arr) T) (Native.tabDPerm arr T)
        (false, a, d) =
      (kappaN arr a, permCN arr a, thetaN (permCN arr a) ^^^ permDN arr (thetaN a ^^^ d)) := by
  simp only [Native.fastAct, Native.tabTPerm, Native.tabDPerm]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hd, kn_map_range_get _ ha, kn_map_range_get _ hd]
  simp only [kn_permCN_zero, kn_kappaN_zero, kn_kappaT_eq,
    hT (kn_permCN_lt arr a), hT ha, hT (by norm_num : 0 < 4096),
    kn_thetaN_zero, Pauli.mul, Pauli.s, Pauli.a, Pauli.d, kn_pairN_zero_l, kn_pairN_zero_r,
    Nat.xor_zero, Nat.zero_xor, Bool.xor_false, Bool.false_xor, kn_permDN_xor, Nat.xor_assoc]

theorem fastAct_perm {arr : Array Nat} (hv : Native.permValid arr = true) {a d : ℕ} (ha : a < 4096)
    (hd : d < 4096) :
    Native.fastAct (Native.tabTPerm arr (Native.betaTab arr) (Native.thetaTab ()))
        (Native.tabDPerm arr (Native.thetaTab ())) (false, a, d) =
      (kappaN arr a, permCN arr a, thetaN (permCN arr a) ^^^ permDN arr (thetaN a ^^^ d)) :=
  fastAct_perm_T thetaTab_get ha hd

theorem fastAct_xi {a d : ℕ} (ha : a < 4096) (hd : d < 4096) :
    Native.fastAct (Native.tabT conjXiN) (Native.tabD conjXiN) (false, a, d) =
      (qGN (gammaLowN (d % 64)) ^^ pairN (gammaLowN (d % 64)) (gammaLowN (a % 64)),
        gammaLowN (d % 64) ^^^ (a &&& 4032),
        gammaLowN (a % 64) ^^^ gammaLowN (gammaLowN (d % 64)) ^^^ (d &&& 4032)) := by
  simp only [Native.fastAct, Native.tabT, Native.tabD]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hd, kn_map_range_get _ ha, kn_map_range_get _ hd]
  simp only [kn_xiT, kn_xiD, Pauli.mul, Pauli.s, Pauli.a, Pauli.d, kn_pairN_zero_r, Nat.zero_xor, Bool.xor_false, Bool.false_xor, Nat.xor_assoc]
  rw [Nat.xor_comm (a &&& 4032)]

end CFSG.KC.KStep

end
