module

public import Certificates.Data.Kernel.Spor.FpBfs
public import CFSG.Sporadic.SuzRecog.LevelTwoCheck
public import CFSG.Certificates.Kernel.Spor.KeyBfsGen
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.RawSlSound

public section

namespace CFSG.KS.FpBfs

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.SuzRecog.LevelTwo

@[expose] def aSearchG (M k : Nat) (gens gensInv : Array (Array Nat)) (root : Array Nat) :
    Array (Array Nat) × Array Nat × Array Nat × Array (Array Nat) := Id.run do
  let mut pts : Array (Array Nat) := #[root]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut tr : Array (Array Nat) := #[idA 1782]
  let mut idx : Std.HashSet Nat := (∅ : Std.HashSet Nat).insert (fp root)
  for h in [0:M] do
    if h < pts.size then
      for s in [0:k] do
        let f := fpConj gens[s]! gensInv[s]! pts[h]!
        if !idx.contains f then
          idx := idx.insert f
          pts := pts.push (conjA gens[s]! gensInv[s]! pts[h]!)
          par := par.push h
          lab := lab.push s
          tr := tr.push (compA 1782 gens[s]! tr[h]!)
  return (pts, par, lab, tr)

theorem aSearch_eq : aSearch = aSearchG 2835 2 gens gensInv t1Arr := rfl

theorem aSearchG_eq_T (M k : Nat) (gens gensInv : Array (Array Nat)) (root : Array Nat) :
    aSearchG M k gens gensInv root =
      CFSG.KS.KeyBfsG.keyBfsT (fun s a => fpConj gens[s]! gensInv[s]! a)
        (fun s a => conjA gens[s]! gensInv[s]! a) (fun s u => compA 1782 gens[s]! u) k root
        (idA 1782) (fp root) M := rfl

theorem compA_get {t u : Array Nat} {x : Nat} (hx : x < 1782) :
    (compA 1782 t u)[x]! = t[u[x]!]! := by
  rw [compA, getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem fpConj_eq (g gi a : Array Nat) : fpConj g gi a = fp (conjA g gi a) := by
  unfold fp fpConj conjA
  simp only [compA_get (by norm_num : (17 : Nat) < 1782), compA_get (by norm_num : (333 : Nat) < 1782),
    compA_get (by norm_num : (901 : Nat) < 1782), compA_get (by norm_num : (1500 : Nat) < 1782),
    compA_get (by norm_num : (1234 : Nat) < 1782), compA_get (by norm_num : (77 : Nat) < 1782)]

theorem unpack_get {p i : Nat} (hi : i < 1782) : (unpack 1782 11 p)[i]! = pg 11 (mask 11) p i := by
  rw [unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem canon_lt {p i : Nat} (hp : CFSG.KS.Prim.canonK 1782 11 (mask 11) (1782 * 11) p = true)
    (hi : i < 1782) : pg 11 (mask 11) p i < 1782 := by
  unfold CFSG.KS.Prim.canonK at hp
  simp only [bAnd_iff] at hp
  simpa [Nat.blt_eq] using allN_spec hp.2.2 i hi

theorem unpack_lt {p : Nat} (hp : CFSG.KS.Prim.canonK 1782 11 (mask 11) (1782 * 11) p = true)
    (y : Nat) : (unpack 1782 11 p)[y]! < 1782 := by
  rcases Nat.lt_or_ge y 1782 with hy | hy
  · rw [unpack_get hy]
    exact canon_lt hp hy
  · rw [getElem!_neg _ y (by simp [unpack]; omega)]
    decide

theorem fpConj_unpack {G GI T : Nat} (hgi : ∀ i < 1782, pg 11 (mask 11) GI i < 1782)
    (ht : ∀ i < 1782, pg 11 (mask 11) T i < 1782) :
    fpConj (unpack 1782 11 G) (unpack 1782 11 GI) (unpack 1782 11 T) = fpCK 11 (mask 11) G GI T := by
  have e : ∀ i < 1782, (unpack 1782 11 G)[(unpack 1782 11 T)[(unpack 1782 11 GI)[i]!]!]! =
      pg 11 (mask 11) G (pg 11 (mask 11) T (pg 11 (mask 11) GI i)) := fun i hi => by
    rw [unpack_get hi, unpack_get (hgi i hi), unpack_get (ht _ (hgi i hi))]
  unfold fpConj fpCK fpOf
  simp only []
  rw [e 17 (by norm_num), e 333 (by norm_num), e 901 (by norm_num), e 1500 (by norm_num),
    e 1234 (by norm_num), e 77 (by norm_num)]
  rfl

theorem fp_unpack (T : Nat) : fp (unpack 1782 11 T) = fpK 11 (mask 11) T := by
  have g : ∀ i < 1782, (unpack 1782 11 T)[i]! = pg 11 (mask 11) T i := fun i hi => by
    rw [getElem!_pos (unpack 1782 11 T) i (by simp [unpack, hi])]
    simp [unpack]
  unfold fp
  rw [g 17 (by norm_num), g 333 (by norm_num), g 901 (by norm_num), g 1500 (by norm_num),
    g 1234 (by norm_num), g 77 (by norm_num)]
  rfl

theorem blt_true {a b : Nat} (h : Nat.blt a b = true) : a < b := by simpa [Nat.blt_eq] using h

theorem fpBfsK_sound {M k cnt E R : Nat} {G GI T V PL POS FP : Nat → Nat}
    {gens gensInv : Array (Array Nat)} {root : Array Nat}
    (hg : ∀ s < k, gens[s]! = unpack 1782 11 (G s))
    (hgi : ∀ s < k, gensInv[s]! = unpack 1782 11 (GI s))
    (hr : root = unpack 1782 11 R)
    (hh : fpBfsHdK 1782 11 (mask 11) (1782 * 11) k M cnt E R G GI T PL FP = true)
    (hp : ∀ i < cnt, 0 < i → fpBfsPtK 1782 11 (mask 11) (1782 * 11) k cnt G GI T V PL FP i = true)
    (hs : ∀ e < E, fpBfsStK 11 (mask 11) k cnt G GI T PL POS FP e = true) :
    cnt ≤ (aSearchG M k gens gensInv root).1.size ∧
      ∀ i < cnt, (aSearchG M k gens gensInv root).1[i]! = unpack 1782 11 (T i) := by
  unfold fpBfsHdK at hh
  simp only [bAnd_iff] at hh
  obtain ⟨hc1, hk0, hT0, hcR, hcG, hE, hM, hF0, hFd⟩ := hh
  have hc1 := blt_true hc1
  have hk0 := blt_true hk0
  have hT0 : T 0 = R := Nat.eq_of_beq_eq_true hT0
  have hE : E = PL (cnt - 1) + 1 := Nat.eq_of_beq_eq_true hE
  have hM : PL (cnt - 1) / k < M := blt_true hM
  have hcan : ∀ s < k, CFSG.KS.Prim.canonK 1782 11 (mask 11) (1782 * 11) (G s) = true ∧
      CFSG.KS.Prim.canonK 1782 11 (mask 11) (1782 * 11) (GI s) = true := fun s hs =>
    (bAnd_iff _ _).1 (allN_spec hcG s hs)
  have hpt : ∀ i < cnt, 0 < i → PL i / k < i ∧
      CFSG.KS.Prim.compEqK 1782 11 (mask 11) (1782 * 11) (T (PL i / k)) (GI (PL i % k)) (V i) =
        true ∧
      CFSG.KS.Prim.compEqK 1782 11 (mask 11) (1782 * 11) (G (PL i % k)) (V i) (T i) = true ∧
      FP i = fpK 11 (mask 11) (T i) ∧ (i + 1 < cnt → PL i < PL (i + 1)) := by
    intro i hi h0
    have h := hp i hi h0
    unfold fpBfsPtK at h
    simp only [CFSG.KS.Raw.strictB_eq, bAnd_iff] at h
    obtain ⟨a1, a2, a3, a4, a5⟩ := h
    refine ⟨blt_true a1, a2, a3, Nat.eq_of_beq_eq_true a4, fun hlt => ?_⟩
    have hb : Nat.blt (Nat.succ i) cnt = true := by simpa [Nat.blt_eq] using hlt
    rw [hb] at a5
    exact blt_true a5
  have hFP : ∀ i < cnt, FP i = fpK 11 (mask 11) (T i) := fun i hi => by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0
      rw [hT0]
      exact Nat.eq_of_beq_eq_true hF0
    · exact (hpt i hi h0).2.2.2.1
  have hdist : ∀ i < cnt, ∀ j < i, FP i ≠ FP j := fun i hi j hj e => by
    have h := allN_spec hFd i hi
    rw [CFSG.KS.Raw.strictB_eq] at h
    have h' := allN_spec h j hj
    rw [e, Nat.beq_refl] at h'
    exact Bool.false_ne_true h'
  have hbd : ∀ h < cnt, ∀ y < 1782, pg 11 (mask 11) (T h) y < 1782 := fun h hh y hy => by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · subst h0
      rw [hT0]
      exact canon_lt hcR hy
    · have h3 := (hpt h hh h0).2.2.1
      have hcan' : CFSG.KS.Prim.canonK 1782 11 (mask 11) (1782 * 11) (G (PL h % k)) = true := by
        unfold CFSG.KS.Prim.compEqK at h3
        exact ((bAnd_iff _ _).1 h3).1
      rw [← unpack_get hy, ← CFSG.KS.Prim.compEqK_sound h3, compA_get hy]
      exact unpack_lt hcan' _
  have hdm : ∀ c, k * (c / k) + c % k = c := fun c => Nat.div_add_mod c k
  have Rec : CFSG.KS.KeyBfsG.GRec fp (fun s a => conjA gens[s]! gensInv[s]! a) k root (fp root)
      cnt E (fun i => unpack 1782 11 (T i)) (fun i => if i = 0 then 0 else PL i / k)
      (fun i => if i = 0 then 0 else PL i % k) POS := by
    refine ⟨hk0, by omega, by rw [hT0, hr], rfl, by simp, by simp, fun a ha b hb e => ?_,
      fun i h0 hi => ?_, fun i h0 hi => ?_, ?_, fun e he => ?_⟩
    · rw [fp_unpack, fp_unpack, ← hFP a ha, ← hFP b hb] at e
      rcases Nat.lt_trichotomy a b with c | c | c
      · exact absurd e.symm (hdist b hb a c)
      · exact c
      · exact absurd e (hdist a ha b c)
    · obtain ⟨a1, a2, a3, -, -⟩ := hpt i hi h0
      have hs : PL i % k < k := Nat.mod_lt _ hk0
      simp only [Nat.pos_iff_ne_zero.1 h0, ↓reduceIte]
      refine ⟨a1, hs, ?_⟩
      rw [hg _ hs, hgi _ hs]
      unfold conjA
      rw [CFSG.KS.Prim.compEqK_sound a2, CFSG.KS.Prim.compEqK_sound a3]
    · have h1 : i + 1 ≠ 0 := by omega
      simp only [Nat.pos_iff_ne_zero.1 h0, h1, ↓reduceIte, hdm]
      exact (hpt i (by omega) h0).2.2.2.2 hi
    · have h1 : cnt - 1 ≠ 0 := by omega
      simp only [h1, ↓reduceIte, hdm]
      omega
    · have h := hs e he
      unfold fpBfsStK at h
      simp only [CFSG.KS.Raw.strictB_eq, bAnd_iff] at h
      obtain ⟨a1, a2, a3⟩ := h
      have hj := blt_true a1
      have hek : e % k < k := Nat.mod_lt _ hk0
      have hed : e / k < cnt := by
        have := Nat.div_le_div_right (c := k) (Nat.le_of_lt_succ (hE ▸ he))
        have := (hpt (cnt - 1) (by omega) (by omega)).1
        omega
      refine ⟨hj, ?_, ?_⟩
      · rw [hg _ hek, hgi _ hek, ← fpConj_eq,
          fpConj_unpack (fun i hi => canon_lt (hcan _ hek).2 hi) (hbd _ hed), fp_unpack,
          ← hFP _ hj]
        exact (Nat.eq_of_beq_eq_true a2).symm
      · by_cases hz : POS e = 0
        · exact Or.inl hz
        · right
          have hz' : Nat.beq (POS e) 0 = false := Bool.eq_false_iff.2 fun h => hz (Nat.eq_of_beq_eq_true h)
          rw [hz'] at a3
          simp only [hz, ↓reduceIte, hdm]
          simpa [Nat.ble_eq] using a3
  have hcap : (if cnt - 1 = 0 then 0 else PL (cnt - 1) / k) < M := by
    have h1 : cnt - 1 ≠ 0 := by omega
    simp only [h1, ↓reduceIte]
    exact hM
  obtain ⟨r1, r2, -⟩ := CFSG.KS.KeyBfsG.keyBfsG_rec Rec hcap
  have ent := CFSG.KS.KeyBfsG.keyBfsT_entries (κ := fp) (stB := fun s u => compA 1782 gens[s]! u)
    (rootB := idA 1782) (key0 := fp root) (cap := M) (k := k) (root := root)
    (sk := fun s a => fpConj gens[s]! gensInv[s]! a) (st := fun s a => conjA gens[s]! gensInv[s]! a)
    (fun j x => fpConj_eq _ _ _)
  rw [aSearchG_eq_T, ent]
  exact ⟨r1, fun i hi => (r2 i hi).1⟩

end CFSG.KS.FpBfs

end
