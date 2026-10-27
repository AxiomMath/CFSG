module

public import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.HexaKGlue
import CFSG.Certificates.Kernel.BfsPinBaseSound
import CFSG.Certificates.Kernel.Q47KOSound
import CFSG.Certificates.Kernel.PackSetSound
public import CFSG.Certificates.Kernel.HexaKSound
public import Certificates.Data.Kernel.Q47K

public section

namespace CFSG.KC.Q47K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.ComponentClassification.AS81.HeSylow
open CFSG.ComponentClassification.AS81.Q47
open CFSG.KLie.CT (sumN anyN notB andB orB)

theorem pg4 (m e : Nat) : pg 4 15 m e = m / 2 ^ (4 * e) % 16 := by
  change (m >>> (4 * e)) &&& (2 ^ 4 - 1) = _
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.and_two_pow_sub_one_eq_mod _ 4

noncomputable def lorP (v : Nat → Nat) (E : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun e acc => Nat.lor acc (Nat.shiftLeft (v e) (Nat.mul 4 e))) E

theorem lorP_spec (v : Nat → Nat) (hv : ∀ e, v e < 16) : ∀ E,
    lorP v E < 2 ^ (4 * E) ∧ ∀ e < E, pg 4 15 (lorP v E) e = v e
  | 0 => ⟨by simp [lorP], fun e he => absurd he (Nat.not_lt_zero e)⟩
  | E + 1 => by
    obtain ⟨h1, h2⟩ := lorP_spec v hv E
    have e1 : lorP v (E + 1) = v E * 2 ^ (4 * E) + lorP v E := by
      change (lorP v E) ||| ((v E) <<< (4 * E)) = _
      rw [Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt h1, Nat.shiftLeft_eq]
    have hp : 0 < 2 ^ (4 * E) := Nat.pos_of_ne_zero (by positivity)
    have h16 : 2 ^ (4 * (E + 1)) = 16 * 2 ^ (4 * E) := by
      rw [Nat.mul_succ, Nat.pow_add]
      ring
    refine ⟨?_, fun e he => ?_⟩
    · rw [e1, h16]
      have := hv E
      nlinarith
    · rw [pg4, e1]
      rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | rfl
      · have hpe : 0 < 2 ^ (4 * e) := Nat.pos_of_ne_zero (by positivity)
        have hsplit : 2 ^ (4 * E) = 2 ^ (4 * e) * (16 * 2 ^ (4 * (E - e - 1))) := by
          have h16' : (16 : Nat) = 2 ^ 4 := rfl
          rw [h16', ← Nat.pow_add, ← Nat.pow_add]
          congr 1
          omega
        rw [hsplit, ← Nat.mul_assoc, Nat.mul_comm (v E) (2 ^ (4 * e)), Nat.mul_assoc,
          Nat.mul_add_div hpe, ← Nat.mul_assoc, Nat.mul_comm (v E) 16, Nat.mul_assoc,
          Nat.mul_add_mod, ← pg4]
        exact h2 e he
      · rw [Nat.mul_comm, Nat.mul_add_div hp, Nat.div_eq_of_lt h1, Nat.add_zero]
        exact Nat.mod_eq_of_lt (hv e)

theorem getElem!_matOf {d m e : Nat} (he : e < d * d) : (matOf d m)[e]! = pg 4 15 m e := by
  unfold matOf
  rw [getElem!_pos _ e (by simpa using he), List.getElem_map, List.getElem_range]

theorem sumN_list' (f : Nat → Nat) : ∀ N, sumN N f = ((List.range N).map f).sum
  | 0 => rfl
  | N + 1 => by
    change Nat.add (f N) (sumN N f) = _
    rw [sumN_list' f N, List.range_succ, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Nat.add_eq]
    omega

theorem matMul_matOf {d p a b : Nat} (hp : 0 < p) (hp16 : p ≤ 16) :
    matMul d p (matOf d a) (matOf d b) = matOf d (mulMK d p a b) := by
  have hv : ∀ e, (fun e => Nat.mod (sumN d fun k => Nat.mul (pg 4 15 a (Nat.add (Nat.mul (Nat.div e d) d) k))
      (pg 4 15 b (Nat.add (Nat.mul k d) (Nat.mod e d)))) p) e < 16 :=
    fun e => lt_of_lt_of_le (Nat.mod_lt _ hp) hp16
  have hs := (lorP_spec _ hv (Nat.mul d d)).2
  unfold matMul
  apply List.ext_getElem (by simp [matOf])
  intro e h1 h2
  have he : e < d * d := by simpa using h1
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h
      simp at he
    · exact h
  rw [List.getElem_map, List.getElem_range, ← getElem!_pos (matOf d (mulMK d p a b)) e h2,
    getElem!_matOf he]
  change _ = pg 4 15 (lorP _ (Nat.mul d d)) e
  rw [hs e he, sumN_list']
  change _ = (((List.range d).map fun k => pg 4 15 a (e / d * d + k) * pg 4 15 b (k * d + e % d)).sum) % p
  refine congrArg (· % p) (congrArg List.sum (List.map_congr_left fun k hk => ?_))
  have hk' := List.mem_range.1 hk
  have hq : e / d < d := (Nat.div_lt_iff_lt_mul hd).2 he
  have i1 : e / d * d + k < d * d := by nlinarith
  have i2 : k * d + e % d < d * d := by
    have := Nat.mod_lt e hd
    nlinarith
  rw [getElem!_matOf i1, getElem!_matOf i2]

theorem keyFold_spec (K : Nat → Nat) : ∀ n, (∀ i < n, K i < 262144) →
    (∀ i < n, ∀ j < n, K i = K j → i = j) →
    ((List.range n).foldl (fun a i => a.set! (K i) i) (Array.replicate 262144 0)).size = 262144 ∧
      ∀ i < n, ((List.range n).foldl (fun a i => a.set! (K i) i) (Array.replicate 262144 0))[K i]! = i
  | 0, _, _ => ⟨by simp, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | n + 1, hK, hinj => by
    obtain ⟨h1, h2⟩ := keyFold_spec K n (fun i hi => hK i (by omega))
      (fun i hi j hj e => hinj i (by omega) j (by omega) e)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl (fun a i => a.set! (K i) i) (Array.replicate 262144 0) = A at h1 h2
    refine ⟨by simp [h1], fun i hi => ?_⟩
    have hKi := hK i hi
    rw [Array.set!_eq_setIfInBounds, getElem!_pos _ (K i) (by simp [h1]; exact hKi),
      Array.getElem_setIfInBounds (by rw [h1]; exact hKi)]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · have hne : K n ≠ K i := fun e => by
        have := hinj n (by omega) i (by omega) e
        omega
      rw [ite_eq_right hne, ← getElem!_pos A (K i) (by rw [h1]; exact hKi)]
      exact h2 i hi
    · rw [ite_eq_left rfl]

theorem key3_unpack (t : Nat) : key3 (unpack 64 7 t) = key3K t := by
  unfold key3 key3K
  rw [unpack_getElem!, unpack_getElem!, unpack_getElem!, ite_eq_left (by decide), ite_eq_left (by decide),
    ite_eq_left (by decide)]
  simp only [Nat.add_eq, Nat.mul_eq]
  omega

theorem key3_lt {t : Nat} (ht : PP 64 7 t) : key3 (unpack 64 7 t) < 262144 := by
  rw [key3_unpack t]
  unfold key3K
  have a := ht.2.1 1 (by decide)
  have b := ht.2.1 4 (by decide)
  have c := ht.2.1 16 (by decide)
  simp only [Nat.add_eq, Nat.mul_eq]
  omega

theorem key3Mul_eq (a b : Array Nat) : key3Mul a b = key3 (compA 64 a b) := by
  unfold key3 key3Mul
  rw [compA_get _ _ (by decide : 1 < 64), compA_get _ _ (by decide : 4 < 64),
    compA_get _ _ (by decide : 16 < 64)]

theorem findRec_lt {N : Nat} {T S : Nat → Nat} {p : Nat} : ∀ r lo hi, lo < N → hi ≤ N →
    Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun lo _ => lo)
      (fun _ ih lo hi => strictN (Nat.div (Nat.add lo hi) 2) fun mid =>
        nIf(Nat.blt p (T (S mid)), ih lo mid, ih mid hi)) r lo hi < N
  | 0, lo, _, hlo, _ => hlo
  | r + 1, lo, hi, hlo, hhi => by
    change strictN (Nat.div (Nat.add lo hi) 2) (fun mid =>
      nIf(Nat.blt p (T (S mid)), Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun lo _ => lo)
        (fun _ ih lo hi => strictN (Nat.div (Nat.add lo hi) 2) fun mid =>
          nIf(Nat.blt p (T (S mid)), ih lo mid, ih mid hi)) r lo mid,
        Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun lo _ => lo)
        (fun _ ih lo hi => strictN (Nat.div (Nat.add lo hi) 2) fun mid =>
          nIf(Nat.blt p (T (S mid)), ih lo mid, ih mid hi)) r mid hi)) < N
    rw [strictN_eq']
    have hm : Nat.div (Nat.add lo hi) 2 < N := by
      change (lo + hi) / 2 < N
      omega
    cases Nat.blt p (T (S (Nat.div (Nat.add lo hi) 2)))
    · exact findRec_lt r _ _ hm hhi
    · exact findRec_lt r _ _ hlo hm.le

theorem findK_lt {N : Nat} {T S : Nat → Nat} (hS : ∀ k < N, S k < N) (hN : 0 < N) (p : Nat) :
    findK N T S p < N :=
  hS _ (findRec_lt 12 0 N hN le_rfl)

theorem tab_sound {gs : List (Array Nat)} {g N : Nat} {G T E S MP : Nat → Nat}
    {Ms : List (List Nat)} {d p : Nat} {one : List Nat} {mulL : List Nat → List Nat → Bool}
    {scal : List Nat → Bool} {mulOK : Nat → Nat → Bool}
    (pin : Pin 64 7 gs g G N T E S) (hN : 0 < N) (hp : 0 < p) (hp16 : p ≤ 16)
    (hMs : Ms.length = N)
    (hMsD : Ms.all (fun m => m.length == d * d && m.all fun x => decide (x < p)) = true)
    (h1 : (Ms[0]! == one) = true)
    (hMP : allN N (fun i => matOf d (MP i) == Ms[i]!) = true)
    (hmul : ∀ a b, mulOK a b = true → mulL (matOf d a) (matOf d b) = true)
    (hHead : tableHeadK N T MP d scal = true)
    (hRow : ∀ i < N, tableRowK N T S MP d p mulOK i = true) :
    tableOK (certN 64 gs).pts Ms d p one mulL scal = true := by
  have hPT : ∀ i < N, PP 64 7 (T i) := PP_pts pin.ok pin.perm
  have hL : (certN 64 gs).pts = Array.ofFn (n := N) fun i => unpack 64 7 (T i.val) := by
    unfold certN
    exact enumBfs_pts pin.size pin.bind pin.ok pin.fuel
  have hdist : ∀ a < N, ∀ b < N, T a = T b → a = b := by
    have hk := pin.ok
    unfold bfsK at hk
    simp only [bAnd_iff] at hk
    exact distinctK_inj hk.2.2.2.2.1
  have hS : ∀ k < N, S k < N := by
    have hk := pin.ok
    unfold bfsK at hk
    simp only [bAnd_iff] at hk
    have hd := hk.2.2.2.2.1
    unfold distinctK at hd
    simp only [bAnd_iff] at hd
    exact fun k hk' => Nat.blt_eq.mp (CFSG.KC.Pack.allN_spec hd.2.1 k hk')
  have hT0 : T 0 = pidn 64 7 := by
    have hk := pin.ok
    unfold bfsK at hk
    simp only [bAnd_iff] at hk
    exact Nat.eq_of_beq_eq_true hk.2.2.2.1
  have hMi : ∀ i < N, Ms[i]! = matOf d (MP i) := fun i hi =>
    (beq_iff_eq.1 (CFSG.KC.Pack.allN_spec hMP i hi)).symm
  have hLi : ∀ i < N, (certN 64 gs).pts[i]! = unpack 64 7 (T i) := by
    intro i hi
    rw [hL, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  have hLs : (certN 64 gs).pts.size = N := by rw [hL, Array.size_ofFn]
  unfold tableHeadK at hHead
  rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at hHead
  obtain ⟨hkeys, hid, hsc⟩ := hHead
  have hkinj : ∀ i < N, ∀ j < N, key3 (unpack 64 7 (T i)) = key3 (unpack 64 7 (T j)) → i = j := by
    intro i hi j hj e
    rw [key3_unpack (T i), key3_unpack (T j)] at e
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := CFSG.KC.Pack.allN_spec (CFSG.KC.Pack.allN_spec hkeys j hj) i h
      rw [notB_eq, e] at this
      simp [Nat.beq_refl] at this
    · have := CFSG.KC.Pack.allN_spec (CFSG.KC.Pack.allN_spec hkeys i hi) j h
      rw [notB_eq, e] at this
      simp [Nat.beq_refl] at this
  obtain ⟨-, hKT⟩ := keyFold_spec (fun i => key3 (certN 64 gs).pts[i]!) N
    (fun i hi => by rw [hLi i hi]; exact key3_lt (hPT i hi))
    (fun i hi j hj e => hkinj i hi j hj (by rwa [hLi i hi, hLi j hj] at e))
  have hkt : ∀ i < N, (keyTable (certN 64 gs).pts)[key3 (unpack 64 7 (T i))]! = i := by
    intro i hi
    unfold keyTable
    rw [hLs, ← hLi i hi]
    exact hKT i hi
  unfold tableOK
  simp only [Bool.and_eq_true, hLs]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, hMsD⟩, h1⟩, ?_⟩, ?_⟩
  · rw [hMs]
    exact beq_self_eq_true N
  · rw [hLi 0 hN, hT0, ← idA_eq (by decide)]
    exact beq_self_eq_true _
  · refine List.all_eq_true.2 fun i hi => ?_
    have hi' := List.mem_range.1 hi
    rw [hLi i hi', hkt i hi']
    exact beq_self_eq_true i
  · refine List.all_eq_true.2 fun i hi => List.all_eq_true.2 fun j hj => ?_
    have hi' := List.mem_range.1 hi
    have hj' := List.mem_range.1 hj
    have hr := CFSG.KC.Pack.allN_spec (hRow i hi') j hj'
    rw [strictB_eq', andB_eq, Bool.and_eq_true] at hr
    have hf := findK_lt (T := T) hS hN (HexaK.mul 64 7 (T i) (T j))
    generalize findK N T S (HexaK.mul 64 7 (T i) (T j)) = f at hr hf
    have hq : pcomp 64 7 (mask 7) (T i) (T j) = T f := (Nat.eq_of_beq_eq_true hr.1).symm
    rw [hLi i hi', hLi j hj', key3Mul_eq, compA_PP (hPT i hi') (hPT j hj'), hq, hkt f hf,
      hMi i hi', hMi j hj', hMi f hf, matMul_matOf hp hp16]
    exact hmul _ _ hr.2
  · refine List.all_eq_true.2 fun i hi => ?_
    have hi' := List.mem_range.1 hi
    have := CFSG.KC.Pack.allN_spec hsc i hi'
    rw [orB_eq, notB_eq] at this
    rw [beq_nat, hMi i hi']
    exact this

end CFSG.KC.Q47K

end
