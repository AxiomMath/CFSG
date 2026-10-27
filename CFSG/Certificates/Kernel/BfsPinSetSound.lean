module

public import Certificates.Data.Kernel.BfsPinKeys
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Certificates.Kernel.BfsPinSliceSound
public import CFSG.Certificates.Kernel.MonsterB.ArrBfsSound
public import CFSG.Certificates.Kernel.RankThree.F2Perm
public import CFSG.Certificates.Kernel.Spor.BindList

public section

namespace CFSG.KC.BfsPin

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.Native CFSG.Monster.B.Fischer CFSG.KC.Bfs
open CFSG.KLie.CT (fget)

theorem nIf_ite (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem strictB_app (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem genStep_eq (n w m : Nat) (T : Nat → Nat) (t row g k c : Nat) :
    genStep n w m T t row g k c =
      if c = 0 then 0
      else if fget row k 16 < c then
        (if T (fget row k 16) = pcomp n w m g t then c else 0)
      else if fget row k 16 = c then (if T c = pcomp n w m g t then c + 1 else 0) else 0 := by
  unfold genStep
  simp only [strictN_app, nIf_ite, Nat.beq_eq, Nat.blt_eq]

theorem genStep_zero (n w m : Nat) (T : Nat → Nat) (t row g k : Nat) :
    genStep n w m T t row g k 0 = 0 := by
  simp only [genStep_eq, ↓reduceIte]

theorem genStep_spec {n w m : Nat} {T : Nat → Nat} {t row g k c r : Nat}
    (hr : genStep n w m T t row g k c = r) (h0 : r ≠ 0) :
    c ≠ 0 ∧ c ≤ r ∧ (∃ j < r, T j = pcomp n w m g t) ∧
      ∀ j, c ≤ j → j < r → T j = pcomp n w m g t := by
  rw [genStep_eq] at hr
  by_cases h1 : c = 0
  · simp only [h1, ↓reduceIte] at hr
    exact absurd hr.symm h0
  simp only [h1, ↓reduceIte] at hr
  by_cases h2 : fget row k 16 < c
  · simp only [h2, ↓reduceIte] at hr
    by_cases h3 : T (fget row k 16) = pcomp n w m g t
    · simp only [h3, ↓reduceIte] at hr
      subst hr
      exact ⟨h1, le_refl _, ⟨_, h2, h3⟩, fun j a b => absurd (lt_of_le_of_lt a b) (lt_irrefl _)⟩
    · simp only [h3, ↓reduceIte] at hr
      exact absurd hr.symm h0
  · simp only [h2, ↓reduceIte] at hr
    by_cases h4 : fget row k 16 = c
    · by_cases h5 : T c = pcomp n w m g t
      · simp only [h4, h5, ↓reduceIte] at hr
        subst hr
        refine ⟨h1, Nat.le_succ c, ⟨c, Nat.lt_succ_self c, h5⟩, fun j a b => ?_⟩
        have e : j = c := by omega
        rw [e]
        exact h5
      · simp only [h4, h5, ↓reduceIte] at hr
        exact absurd hr.symm h0
    · simp only [h4, ↓reduceIte] at hr
      exact absurd hr.symm h0

@[expose] noncomputable def pointF (n w m : Nat) (G T E : Nat → Nat) (i len : Nat) :
    Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ c => c)
    (fun _ ih lo c => ih (Nat.succ lo) (genStep n w m T (T i) (E i) (G lo) lo c)) len

@[expose] noncomputable def pointRec (n w m ng : Nat) (G T E : Nat → Nat) (i r : Nat) :
    Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun c => c)
    (fun r ih c => strictN (genStep n w m T (T i) (E i) (G (Nat.sub (Nat.sub ng r) (nat_lit 1)))
      (Nat.sub (Nat.sub ng r) (nat_lit 1)) c) ih) r

theorem pointRec_eq {n w m ng : Nat} {G T E : Nat → Nat} (i : Nat) : ∀ r, r ≤ ng → ∀ c,
    pointRec n w m ng G T E i r c = pointF n w m G T E i r (ng - r) c
  | 0, _, _ => rfl
  | r + 1, h, c => by
    have e1 : Nat.sub (Nat.sub ng r) (nat_lit 1) = ng - (r + 1) := by
      change ng - r - 1 = ng - (r + 1)
      omega
    have e2 : Nat.succ (ng - (r + 1)) = ng - r := by omega
    have s1 : pointRec n w m ng G T E i (r + 1) c = pointRec n w m ng G T E i r
        (genStep n w m T (T i) (E i) (G (Nat.sub (Nat.sub ng r) (nat_lit 1)))
          (Nat.sub (Nat.sub ng r) (nat_lit 1)) c) := strictN_app _ _
    have s2 : pointF n w m G T E i (r + 1) (ng - (r + 1)) c = pointF n w m G T E i r
        (Nat.succ (ng - (r + 1)))
        (genStep n w m T (T i) (E i) (G (ng - (r + 1))) (ng - (r + 1)) c) := rfl
    rw [s1, s2, e1, e2, pointRec_eq i r (by omega)]

theorem pointStep_eq {n w m ng : Nat} {G T E : Nat → Nat} (i c : Nat) :
    pointStep n w m ng G T E i c = pointF n w m G T E i ng 0 c := by
  have h := pointRec_eq (n := n) (w := w) (m := m) (ng := ng) (G := G) (T := T) (E := E) i ng
    (Nat.le_refl ng) c
  rw [Nat.sub_self] at h
  rw [← h]
  unfold pointStep
  rw [strictN_app, strictN_app]
  rfl

theorem pointF_zero {n w m : Nat} {G T E : Nat → Nat} (i : Nat) :
    ∀ len lo, pointF n w m G T E i len lo 0 = 0
  | 0, _ => rfl
  | len + 1, lo => by
    change pointF n w m G T E i len (Nat.succ lo) (genStep n w m T (T i) (E i) (G lo) lo 0) = 0
    rw [genStep_zero]
    exact pointF_zero i len _

theorem pointF_spec {n w m ng : Nat} {G T E : Nat → Nat} (Q : Nat → Prop) (i : Nat)
    (hQ : ∀ k < ng, Q (pcomp n w m (G k) (T i))) :
    ∀ len lo c r, lo + len ≤ ng → pointF n w m G T E i len lo c = r → r ≠ 0 →
      (∀ j < c, Q (T j)) →
      c ≤ r ∧ (∀ j < r, Q (T j)) ∧
        ∀ k, lo ≤ k → k < lo + len → ∃ j < r, T j = pcomp n w m (G k) (T i)
  | 0, lo, c, r, _, hr, _, hc => by
    have e : c = r := hr
    subst e
    exact ⟨le_refl _, hc, fun k a b => absurd b (by omega)⟩
  | len + 1, lo, c, r, hl, hr, h0, hc => by
    change pointF n w m G T E i len (Nat.succ lo) (genStep n w m T (T i) (E i) (G lo) lo c) = r
      at hr
    have hc0 : genStep n w m T (T i) (E i) (G lo) lo c ≠ 0 := by
      intro e
      rw [e, pointF_zero] at hr
      exact h0 hr.symm
    obtain ⟨-, hle, ⟨j, hj, hjT⟩, hnew⟩ := genStep_spec rfl hc0
    have hc' : ∀ j < genStep n w m T (T i) (E i) (G lo) lo c, Q (T j) := by
      intro j hj'
      rcases Nat.lt_or_ge j c with h | h
      · exact hc j h
      · rw [hnew j h hj']
        exact hQ lo (by omega)
    obtain ⟨hle', hQ', hcl'⟩ := pointF_spec Q i hQ len (Nat.succ lo) _ r (by omega) hr h0 hc'
    refine ⟨le_trans hle hle', hQ', fun k a b => ?_⟩
    rcases Nat.lt_or_ge lo k with h | h
    · exact hcl' k (by omega) (by omega)
    · have e : k = lo := by omega
      subst e
      exact ⟨j, lt_of_lt_of_le hj hle', hjT⟩

theorem runF_zero {n w m ng : Nat} {G T E : Nat → Nat} :
    ∀ len lo, runF n w m ng G T E len lo 0 = 0
  | 0, _ => rfl
  | len + 1, lo => by
    rw [runF_succ]
    have hb : Nat.blt lo 0 = false := by
      cases h : Nat.blt lo 0
      · rfl
      · exact absurd (Nat.blt_eq.mp h) (Nat.not_lt_zero lo)
    rw [hb]
    exact runF_zero len _

theorem runF_spec {n w m ng : Nat} {G T E : Nat → Nat} (Q : Nat → Prop)
    (hQ : ∀ y, Q y → ∀ k < ng, Q (pcomp n w m (G k) y)) :
    ∀ len lo c r, runF n w m ng G T E len lo c = r → r ≠ 0 → (∀ j < c, Q (T j)) →
      (∀ i < lo, ∀ k < ng, ∃ j < c, T j = pcomp n w m (G k) (T i)) →
      c ≤ r ∧ (∀ j < r, Q (T j)) ∧
        ∀ i < lo + len, ∀ k < ng, ∃ j < r, T j = pcomp n w m (G k) (T i)
  | 0, lo, c, r, hr, _, hc, hcl => by
    have e : c = r := hr
    subst e
    exact ⟨le_refl _, hc, hcl⟩
  | len + 1, lo, c, r, hr, h0, hc, hcl => by
    rw [runF_succ] at hr
    cases hb : Nat.blt lo c
    · rw [hb] at hr
      change runF n w m ng G T E len (Nat.succ lo) 0 = r at hr
      rw [runF_zero] at hr
      exact absurd hr.symm h0
    · rw [hb] at hr
      change runF n w m ng G T E len (Nat.succ lo) (pointStep n w m ng G T E lo c) = r at hr
      have hlo : lo < c := Nat.blt_eq.mp hb
      have hp0 : pointStep n w m ng G T E lo c ≠ 0 := by
        intro e
        rw [e, runF_zero] at hr
        exact h0 hr.symm
      obtain ⟨hle, hQp, hclp⟩ := pointF_spec Q lo (fun k hk => hQ _ (hc lo hlo) k hk) ng 0 c
        _ (by omega) (pointStep_eq lo c).symm hp0 hc
      have hcl' : ∀ i < Nat.succ lo, ∀ k < ng,
          ∃ j < pointStep n w m ng G T E lo c, T j = pcomp n w m (G k) (T i) := by
        intro i hi k hk
        rcases Nat.lt_or_ge i lo with h | h
        · obtain ⟨j, hj, e⟩ := hcl i h k hk
          exact ⟨j, lt_of_lt_of_le hj hle, e⟩
        · have e : i = lo := by omega
          subst e
          exact hclp k (Nat.zero_le k) (by omega)
      obtain ⟨hle', hQ', hcl''⟩ := runF_spec Q hQ len (Nat.succ lo) _ r hr h0 hQp hcl'
      refine ⟨le_trans hle hle', hQ', fun i hi k hk => hcl'' i (by omega) k hk⟩

theorem bfsK_points {n w ng N : Nat} {G T E S : Nat → Nat} (Q : Nat → Prop)
    (h0 : Q (pidn n w)) (hQ : ∀ y, Q y → ∀ k < ng, Q (pcomp n w (mask w) (G k) y))
    (hk : bfsK n w ng G N T E S = true) :
    0 < N ∧ T 0 = pidn n w ∧ (∀ j < N, Q (T j)) ∧
      ∀ i < N, ∀ k < ng, ∃ j < N, T j = pcomp n w (mask w) (G k) (T i) := by
  unfold bfsK at hk
  simp only [bAnd_iff] at hk
  obtain ⟨-, -, -, hT0, -, hrun⟩ := hk
  have hT : T 0 = pidn n w := Nat.eq_of_beq_eq_true hT0
  have hR : runF n w (mask w) ng G T E N 0 1 = N := by
    rw [← runK_eq]
    exact Nat.eq_of_beq_eq_true hrun
  have hN : N ≠ 0 := by
    intro e
    subst e
    have e1 : runF n w (mask w) ng G T E 0 0 1 = 1 := rfl
    omega
  have hc1 : ∀ j < 1, Q (T j) := by
    intro j hj
    have e : j = 0 := by omega
    rw [e, hT]
    exact h0
  obtain ⟨-, hQN, hcl⟩ := runF_spec Q hQ N 0 1 N hR hN hc1 (fun i hi => absurd hi (by omega))
  exact ⟨Nat.pos_of_ne_zero hN, hT, hQN, fun i hi k hk => hcl i (by omega) k hk⟩

theorem unpack_get' {n w P p : Nat} (hp : p < n) : (unpack n w P)[p]! = pg w (mask w) P p := by
  unfold unpack
  rw [getElem!_pos _ p (by rw [Array.size_ofFn]; exact hp), Array.getElem_ofFn]

theorem keyA_unpack {n w : Nat} {ps : List Nat} (hps : ∀ p ∈ ps, p < n) (P : Nat) :
    keyA n ps (unpack n w P) = pkeyK n w ps P := by
  unfold keyA
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have e1 : (unpack n w P)[p]! = pg w (mask w) P p := unpack_get' (hps p List.mem_cons_self)
    rw [List.map_cons, Nat.ofDigits_cons, ih fun q hq => hps q (List.mem_cons_of_mem p hq)]
    erw [e1]
    rfl

theorem keysK_spec {n w : Nat} {ps : List Nat} {N : Nat} {T : Nat → Nat}
    (h : keysK n w ps N T = true) :
    ∀ i < N, ∀ j < N, pkeyK n w ps (T i) = pkeyK n w ps (T j) → i = j := by
  have hlt : ∀ i < N, ∀ j < i, pkeyK n w ps (T i) ≠ pkeyK n w ps (T j) := by
    intro i hi j hj e
    have h1 := allN_spec h i hi
    rw [strictB_app] at h1
    have h2 := allN_spec h1 j hj
    rw [e, Nat.beq_refl] at h2
    exact Bool.false_ne_true h2
  intro i hi j hj e
  rcases Nat.lt_trichotomy i j with h' | h' | h'
  · exact absurd e.symm (hlt j hj i h')
  · exact h'
  · exact absurd e (hlt i hi j h')

theorem validA_unpack {n w p : Nat}
    (h : permOK n w (mask w) (n * w) p (pinvS n w (mask w) p) = true) :
    validA n (unpack n w p) = true := by
  obtain ⟨h1, h2⟩ := invEqK_sound h
  unfold validA
  rw [h1]
  exact h2

theorem enumBfs_of_bfsK_set {n w ng N fuel : Nat} {G T E S : Nat → Nat}
    {gs : Array (Array Nat)} {ps : List Nat}
    (hs : gs.size = ng) (hg : ∀ k < ng, gs[k]! = unpack n w (G k))
    (hp : ∀ k < ng, permOK n w (mask w) (n * w) (G k) (pinvS n w (mask w) (G k)) = true)
    (hid : idK n w (mask w) = true) (hpid : canonK n w (mask w) (n * w) (pidn n w) = true)
    (hk : bfsK n w ng G N T E S = true) (hps : ∀ p ∈ ps, p < n)
    (hkey : keysK n w ps N T = true) (hf : N ≤ fuel) :
    enumOK n gs ps (enumBfs n gs ps fuel) = true ∧
      (∀ x, x ∈ (enumBfs n gs ps fuel).pts ↔ ∃ i < N, unpack n w (T i) = x) ∧
      (enumBfs n gs ps fuel).pts.size = N := by
  have hk' := hk
  unfold bfsK at hk'
  simp only [bAnd_iff] at hk'
  have hcG : ∀ k < ng, canonK n w (mask w) (n * w) (G k) = true := allN_spec hk'.2.1
  have hvg : ∀ k < gs.size, validA n gs[k]! = true := by
    intro k hk1
    rw [hg k (hs ▸ hk1)]
    exact validA_unpack (hp k (hs ▸ hk1))
  have hleft : ∀ k < ng, ∀ y, canonK n w (mask w) (n * w) y = true →
      leftA n gs k (unpack n w y) = unpack n w (pcomp n w (mask w) (G k) y) := by
    intro k hk1 y hy
    unfold leftA
    rw [hg k hk1, compA_unpack (hcG k hk1) hy]
  have hidA : unpack n w (pidn n w) = idA n := idK_sound hid
  let Q : Nat → Prop := fun y =>
    canonK n w (mask w) (n * w) y = true ∧ Reach (leftA n gs) gs.size (idA n) (unpack n w y)
  have hQ0 : Q (pidn n w) := ⟨hpid, by rw [hidA]; exact Reach.root⟩
  have hQ : ∀ y, Q y → ∀ k < ng, Q (pcomp n w (mask w) (G k) y) := by
    intro y hy k hk1
    refine ⟨canonK_pcomp (hcG k hk1) hy.1, ?_⟩
    rw [← hleft k hk1 y hy.1]
    exact Reach.step k (hs ▸ hk1) hy.2
  obtain ⟨hN, hT0, hQT, hcl⟩ := bfsK_points Q hQ0 hQ hk
  have hinj : ∀ i < N, ∀ j < N, unpack n w (T i) = unpack n w (T j) → i = j := by
    intro i hi j hj e
    refine keysK_spec hkey i hi j hj ?_
    rw [← keyA_unpack hps, ← keyA_unpack hps, e]
  let U : Nat → Array Nat := fun i => unpack n w (T i)
  let Sf : Finset (Array Nat) := (Finset.range N).image U
  have hmemS : ∀ x, x ∈ Sf ↔ ∃ i < N, unpack n w (T i) = x := by
    intro x
    simp only [Sf, U, Finset.mem_image, Finset.mem_range]
  have hroot : idA n ∈ Sf := (hmemS _).2 ⟨0, hN, by rw [hT0, hidA]⟩
  have hclosed : ∀ x ∈ Sf, ∀ k < gs.size, leftA n gs k x ∈ Sf := by
    intro x hx k hk1
    obtain ⟨i, hi, rfl⟩ := (hmemS x).1 hx
    obtain ⟨j, hj, e⟩ := hcl i hi k (hs ▸ hk1)
    rw [hleft k (hs ▸ hk1) _ (hQT i hi).1, ← e]
    exact (hmemS _).2 ⟨j, hj, rfl⟩
  have hR : ∀ x ∈ Sf, Reach (leftA n gs) gs.size (idA n) x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := (hmemS x).1 hx
    exact (hQT i hi).2
  have hS : ∀ x, Reach (leftA n gs) gs.size (idA n) x ↔ x ∈ Sf :=
    reach_iff_of_closed hroot hclosed hR
  have hv : ∀ x ∈ Sf, validA n x = true := by
    intro x hx
    have hr := hR x hx
    clear hx
    induction hr with
    | root => exact CFSG.RankThree.Native.F2.validA_of_rep rep_idA
    | step k hk1 _ ih =>
      unfold leftA
      exact CFSG.RankThree.Native.F2.validA_of_rep
        (rep_compA (rep_of_validA (hvg k hk1)) (rep_of_validA ih))
  have hkeyS : ∀ x ∈ Sf, ∀ y ∈ Sf, keyA n ps x = keyA n ps y → x = y := by
    intro x hx y hy e
    obtain ⟨i, hi, rfl⟩ := (hmemS x).1 hx
    obtain ⟨j, hj, rfl⟩ := (hmemS y).1 hy
    rw [keyA_unpack hps, keyA_unpack hps] at e
    rw [keysK_spec hkey i hi j hj e]
  have hcard : Sf.card = N := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj e
    exact hinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) e
  obtain ⟨hcert, hmem, hsize, -⟩ := arrBfs_spec (act := leftA n gs) (ngen := gs.size)
    (valid := validA n) (key := keyA n ps) (root := idA n) (fuel := fuel) Sf hS hv hkeyS
    (by rw [hcard]; exact hf)
  refine ⟨?_, fun x => (hmem x).trans (hmemS x), hsize.trans hcard⟩
  unfold enumOK enumBfs
  rw [Bool.and_eq_true]
  exact ⟨allLt_iff.2 hvg, hcert⟩

@[expose] noncomputable def pkA (w : Nat) (t : Array Nat) : Nat := packA w t.toList

theorem eq_unpack_of_bindListK {n w P : Nat} {A : Array Nat} (h : bindListK n w P A.toList = true) :
    A = unpack n w P := by
  rw [← toArray_eq_of_bindListK h, Array.toArray_toList]

theorem binds_of_listK {gs : Array (Array Nat)} {n w ng : Nat} {G : Nat → Nat}
    (hs : gs.size = ng) (h : allN ng (fun k => bindListK n w (G k) gs[k]!.toList) = true) :
    gs.size = ng ∧ ∀ k < ng, gs[k]! = unpack n w (G k) :=
  ⟨hs, fun k hk => eq_unpack_of_bindListK (allN_spec h k hk)⟩

theorem any_eqA_unpack_range {n w N P : Nat} {T : Nat → Nat}
    (hP : canonK n w (mask w) (n * w) P = true)
    (hT : ∀ k < N, canonK n w (mask w) (n * w) (T k) = true) :
    (List.range N).any (fun k => eqA n (unpack n w P) (unpack n w (T k))) =
      (List.range N).any (fun k => Nat.beq P (T k)) := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨k, hk, h⟩
    exact ⟨k, hk, by rwa [eqA_unpack hP (hT k hk)] at h⟩
  · rintro ⟨k, hk, h⟩
    exact ⟨k, hk, by rwa [eqA_unpack hP (hT k hk)]⟩

theorem allLt_pts {c : ArrCert} {N : Nat} {U : Nat → Array Nat} {f : Array Nat → Bool}
    (hmem : ∀ x, x ∈ c.pts ↔ ∃ i < N, U i = x) (h : ∀ i < N, f (U i) = true) :
    allLt c.pts.size (fun i => f c.pts[i]!) = true := by
  rw [allLt_iff]
  intro i hi
  obtain ⟨j, hj, e⟩ := (hmem c.pts[i]!).1 (by rw [getElem!_pos c.pts i hi]; exact Array.getElem_mem hi)
  rw [← e]
  exact h j hj

theorem any_pts {c : ArrCert} {N : Nat} {U : Nat → Array Nat}
    (hmem : ∀ x, x ∈ c.pts ↔ ∃ i < N, U i = x) (f : Array Nat → Bool) :
    c.pts.toList.any f = (List.range N).any (fun i => f (U i)) := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨x, hx, hfx⟩
    obtain ⟨i, hi, rfl⟩ := (hmem x).1 (Array.mem_def.2 hx)
    exact ⟨i, hi, hfx⟩
  · rintro ⟨i, hi, hfi⟩
    exact ⟨U i, Array.mem_def.1 ((hmem _).2 ⟨i, hi, rfl⟩), hfi⟩

end CFSG.KC.BfsPin

end
