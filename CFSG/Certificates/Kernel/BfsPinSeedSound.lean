module

public import Certificates.Data.Kernel.BfsPinSeed
public import CFSG.Certificates.Kernel.BfsPinKeySound
public import CFSG.Certificates.Kernel.BfsPinSetSound
public import CFSG.Certificates.Kernel.MonsterB.ArrBfsSound
import CFSG.Certificates.Kernel.Spor.PrimSound
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.BfsPinSound

public section

namespace CFSG.KC.BfsPin

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.Native CFSG.Monster.B.Fischer CFSG.KC.Bfs
open CFSG.KLie.CT (fget)

theorem pcomp_assocS {n w p q r : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) (hr : canonK n w (mask w) (n * w) r = true) :
    pcomp n w (mask w) (pcomp n w (mask w) p q) r =
      pcomp n w (mask w) p (pcomp n w (mask w) q r) := by
  obtain ⟨hn, hw, -, -⟩ := PF.canon_facts hp
  obtain ⟨-, -, -, hrr⟩ := PF.canon_facts hr
  have hn32 : n < 2 ^ 32 := by omega
  have hw0 := PF.w_pos hw
  refine PF.eq_of_fields hw0 (PF.pcomp_shr _ _ hn32 hw0) (PF.pcomp_shr _ _ hn32 hw0) fun i hi => ?_
  rw [PF.pg_pcomp hn32 hi, PF.pg_pcomp hn32 (hrr i hi), PF.pg_pcomp hn32 hi,
    PF.pg_pcomp hn32 hi]

theorem genStepB_new {n w m : Nat} {ps : List Nat} {T : Nat → Nat} {t row g k c : Nat}
    (h0 : genStepB n w m ps T t row g k c ≠ 0) :
    genStepB n w m ps T t row g k c = c ∨
      (T c = pcomp n w m g t ∧ genStepB n w m ps T t row g k c = c + 1) := by
  have hv := genStepB_eq n w m ps T t row g k c
  generalize genStepB n w m ps T t row g k c = r at h0 hv ⊢
  by_cases h1 : c = 0
  · simp only [h1, ↓reduceIte] at hv
    exact absurd hv h0
  simp only [h1, ↓reduceIte] at hv
  by_cases h2 : fget row k 16 < c
  · simp only [h2, ↓reduceIte] at hv
    by_cases h3 : keyK n w ps (T (fget row k 16)) = keyM n w m ps g t
    · simp only [h3, ↓reduceIte] at hv
      exact Or.inl hv
    · simp only [h3, ↓reduceIte] at hv
      exact absurd hv h0
  · simp only [h2, ↓reduceIte] at hv
    by_cases h4 : fget row k 16 = c
    · by_cases h5 : T c = pcomp n w m g t
      · simp only [h4, h5, ↓reduceIte] at hv
        exact Or.inr ⟨h5, hv⟩
      · simp only [h4, h5, ↓reduceIte] at hv
        exact absurd hv h0
    · simp only [h4, ↓reduceIte] at hv
      exact absurd hv h0

theorem pointRecB_eqS {n w m ng : Nat} {ps : List Nat} {G T E : Nat → Nat} (i : Nat) :
    ∀ r, r ≤ ng → ∀ c, pointRecB n w m ng ps G T E i r c = pointFB n w m ps G T E i r (ng - r) c
  | 0, _, _ => rfl
  | r + 1, h, c => by
    have e1 : Nat.sub (Nat.sub ng r) (nat_lit 1) = ng - (r + 1) := by
      change ng - r - 1 = ng - (r + 1)
      omega
    have e2 : Nat.succ (ng - (r + 1)) = ng - r := by omega
    have s1 : pointRecB n w m ng ps G T E i (r + 1) c = pointRecB n w m ng ps G T E i r
        (genStepB n w m ps T (T i) (E i) (G (Nat.sub (Nat.sub ng r) (nat_lit 1)))
          (Nat.sub (Nat.sub ng r) (nat_lit 1)) c) := strictN_app _ _
    have s2 : pointFB n w m ps G T E i (r + 1) (ng - (r + 1)) c = pointFB n w m ps G T E i r
        (Nat.succ (ng - (r + 1)))
        (genStepB n w m ps T (T i) (E i) (G (ng - (r + 1))) (ng - (r + 1)) c) := rfl
    rw [s1, s2, e1, e2, pointRecB_eqS i r (by omega)]

theorem pointFB_foldlS {n w m : Nat} {ps : List Nat} {G T E : Nat → Nat} (i : Nat) :
    ∀ len lo c, pointFB n w m ps G T E i len lo c =
      (List.range' lo len).foldl (fun c k => genStepB n w m ps T (T i) (E i) (G k) k c) c
  | 0, _, _ => rfl
  | len + 1, lo, c => by
    rw [List.range'_succ, List.foldl_cons]
    exact pointFB_foldlS i len (lo + 1) _

theorem pointStepB_eqS {n w m ng : Nat} {ps : List Nat} {G T E : Nat → Nat} (i c : Nat) :
    pointStepB n w m ng ps G T E i c = pointFB n w m ps G T E i ng 0 c := by
  have h := pointRecB_eqS (n := n) (w := w) (m := m) (ng := ng) (ps := ps) (G := G) (T := T)
    (E := E) i ng (Nat.le_refl ng) c
  rw [Nat.sub_self] at h
  rw [← h]
  unfold pointStepB
  rw [strictN_app, strictN_app]
  rfl

theorem pointStepB_foldlS {n w m ng : Nat} {ps : List Nat} {G T E : Nat → Nat} (i c : Nat) :
    pointStepB n w m ng ps G T E i c =
      (List.range ng).foldl (fun c k => genStepB n w m ps T (T i) (E i) (G k) k c) c := by
  rw [pointStepB_eqS, pointFB_foldlS, List.range_eq_range']

theorem foldl_genStepB_zero {n w m : Nat} {ps : List Nat} {G T E : Nat → Nat} (i : Nat) :
    ∀ L : List Nat, L.foldl (fun c k => genStepB n w m ps T (T i) (E i) (G k) k c) 0 = 0
  | [] => rfl
  | k :: L => by
    rw [List.foldl_cons, genStepB_zero, foldl_genStepB_zero i L]

section Points

variable {n w m ng : Nat} {ps : List Nat} {G T E : Nat → Nat} {P : Nat → Prop}

theorem fold_points
    (hP : ∀ i c k, i < c → k < ng → P i → T c = pcomp n w m (G k) (T i) → P c) (i : Nat) :
    ∀ L : List Nat, (∀ k ∈ L, k < ng) → ∀ c, i < c → (∀ j < c, P j) →
      L.foldl (fun c k => genStepB n w m ps T (T i) (E i) (G k) k c) c ≠ 0 →
      ∀ j < L.foldl (fun c k => genStepB n w m ps T (T i) (E i) (G k) k c) c, P j
  | [], _, _, _, hc, _ => hc
  | k :: L, hL, c, hi, hc, h0 => by
    rw [List.foldl_cons] at h0 ⊢
    have hk := hL k List.mem_cons_self
    have hL' : ∀ k' ∈ L, k' < ng := fun k' hk' => hL k' (List.mem_cons_of_mem k hk')
    have h1 : genStepB n w m ps T (T i) (E i) (G k) k c ≠ 0 := fun e => h0 (by
      rw [e]
      exact foldl_genStepB_zero i L)
    rcases genStepB_new h1 with e | ⟨hT, e⟩
    · rw [e] at h0 ⊢
      exact fold_points hP i L hL' c hi hc h0
    · rw [e] at h0 ⊢
      refine fold_points hP i L hL' (c + 1) (by omega) (fun j hj => ?_) h0
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · exact hc j hj
      · rw [hj]
        exact hP i c k hi hk (hc i hi) hT

theorem point_points
    (hP : ∀ i c k, i < c → k < ng → P i → T c = pcomp n w m (G k) (T i) → P c) {i c : Nat}
    (hi : i < c) (hc : ∀ j < c, P j) (h0 : pointStepB n w m ng ps G T E i c ≠ 0) :
    ∀ j < pointStepB n w m ng ps G T E i c, P j := by
  rw [pointStepB_foldlS] at h0 ⊢
  exact fold_points hP i (List.range ng) (fun k hk => List.mem_range.1 hk) c hi hc h0

theorem run_points
    (hP : ∀ i c k, i < c → k < ng → P i → T c = pcomp n w m (G k) (T i) → P c) :
    ∀ len lo c, (∀ j < c, P j) → runFB n w m ng ps G T E len lo c ≠ 0 →
      ∀ j < runFB n w m ng ps G T E len lo c, P j
  | 0, _, _, hc, _ => hc
  | len + 1, lo, c, hc, h => by
    rw [runFB_succ] at h ⊢
    cases hb : Nat.blt lo c
    · rw [hb] at h
      exact absurd (runFB_zero len _) h
    · rw [hb] at h
      have hp : pointStepB n w m ng ps G T E lo c ≠ 0 := fun e => by
        change runFB n w m ng ps G T E len (Nat.succ lo) (pointStepB n w m ng ps G T E lo c) ≠ 0
          at h
        rw [e, runFB_zero] at h
        exact h rfl
      exact run_points hP len (Nat.succ lo) _ (point_points hP (Nat.blt_eq.mp hb) hc hp) h

theorem runFB_points {N : Nat} (h0 : P 0)
    (hP : ∀ i c k, i < c → k < ng → P i → T c = pcomp n w m (G k) (T i) → P c)
    (hR : runFB n w m ng ps G T E N 0 1 = N) (hN : N ≠ 0) : ∀ j < N, P j := by
  have h := run_points hP N 0 1 (fun j hj => by
    rw [Nat.lt_one_iff.1 hj]
    exact h0) (by rw [hR]; exact hN)
  rw [hR] at h
  exact h

end Points

theorem bAnd_eqS (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem seedPt_cons (n w N : Nat) (G T E : Nat → Nat) (i s : Nat) (S : List Nat) :
    seedPt n w N G T E i (s :: S) =
      ((Nat.blt (fget (E i) s 16) N &&
          Nat.beq (pcomp n w (mask w) (G s) (T i)) (T (fget (E i) s 16))) &&
        seedPt n w N G T E i S) := by
  change Bool.rec (motive := fun _ => Bool) false (seedPt n w N G T E i S)
    (strictB (fget (E i) s 16) fun j => Bool.rec (motive := fun _ => Bool) false
      (Nat.beq (pcomp n w (mask w) (G s) (T i)) (T j)) (Nat.blt j N)) = _
  rw [strictB_app, bAnd_eqS, bAnd_eqS]

theorem seedPt_spec {n w N : Nat} {G T E : Nat → Nat} {i : Nat} {S : List Nat}
    (h : seedPt n w N G T E i S = true) : ∀ s ∈ S,
      fget (E i) s 16 < N ∧ pcomp n w (mask w) (G s) (T i) = T (fget (E i) s 16) := by
  induction S with
  | nil => exact fun s hs => absurd hs List.not_mem_nil
  | cons s S ih =>
    rw [seedPt_cons, Bool.and_eq_true, Bool.and_eq_true] at h
    intro s' hs'
    rcases List.mem_cons.1 hs' with e | hs'
    · rw [e]
      exact ⟨Nat.blt_eq.mp h.1.1, Nat.eq_of_beq_eq_true h.1.2⟩
    · exact ih h.2 s' hs'

theorem testBit_or_pow {M s k : Nat} (h : (Nat.lor M (Nat.shiftLeft 1 s)).testBit k = true) :
    M.testBit k = true ∨ s = k := by
  change (M ||| 1 <<< s).testBit k = true at h
  rw [Nat.testBit_lor, Bool.or_eq_true, Nat.one_shiftLeft, Nat.testBit_two_pow,
    decide_eq_true_eq] at h
  exact h

theorem seedMask_spec : ∀ {S : List Nat} {k : Nat}, (seedMask S).testBit k = true → k ∈ S
  | [], k, h => by
    change (0 : Nat).testBit k = true at h
    simp at h
  | s :: S, k, h => by
    rcases testBit_or_pow (M := seedMask S) h with h | e
    · exact List.mem_cons_of_mem s (seedMask_spec h)
    · rw [← e]
      exact List.mem_cons_self

theorem derivK_spec {w : Nat} {G : Nat → Nat} {Q : Nat → Prop}
    (hQ : ∀ i j, Q i → Q j → Q (pg w (mask w) (G i) j)) :
    ∀ (D : List Nat) (M : Nat), (∀ k, M.testBit k = true → Q k) →
      ∀ k, (derivK w G D M).testBit k = true → Q k
  | [], _, hM, k, h => hM k h
  | d :: D, M, hM, k, h => by
    have e : derivK w G (d :: D) M = Bool.rec (motive := fun _ => Nat) 0
        (derivK w G D (Nat.lor M (Nat.shiftLeft 1
          (pg w (mask w) (G (Nat.land d 127)) (Nat.shiftRight d 7)))))
        (Bool.rec (motive := fun _ => Bool) false (Nat.testBit M (Nat.shiftRight d 7))
          (Nat.testBit M (Nat.land d 127))) := rfl
    rw [e] at h
    cases h1 : Nat.testBit M (Nat.land d 127)
    · rw [h1] at h
      change (0 : Nat).testBit k = true at h
      simp at h
    cases h2 : Nat.testBit M (Nat.shiftRight d 7)
    · rw [h1, h2] at h
      change (0 : Nat).testBit k = true at h
      simp at h
    rw [h1, h2] at h
    refine derivK_spec hQ D _ (fun k' hk' => ?_) k h
    rcases testBit_or_pow hk' with hk' | e'
    · exact hM k' hk'
    · rw [← e']
      exact hQ _ _ (hM _ h1) (hM _ h2)

theorem enumOK_of_seed {n w ng N fuel : Nat} {G T E : Nat → Nat} {SK S D : List Nat}
    {gs : Array (Array Nat)} {ps : List Nat} (hs : gs.size = ng)
    (hg : ∀ k < ng, gs[k]! = unpack n w (G k)) (hsz : szOK n w = true)
    (hp : ∀ k < ng, permOK n w (mask w) (n * w) (G k) (pinvS n w (mask w) (G k)) = true)
    (hcG : ∀ k < ng, canonK n w (mask w) (n * w) (G k) = true)
    (hcT : ∀ i < N, canonK n w (mask w) (n * w) (T i) = true) (hT0 : T 0 = pidn n w)
    (hps : ∀ p ∈ ps, p < n) (hK : keysSK n w ps N T SK = true)
    (hR : runFB n w (mask w) ng ps G T E N 0 1 = N) (hf : N ≤ fuel)
    (hS : ∀ s ∈ S, s < ng) (hseed : ∀ i < N, seedPt n w N G T E i S = true)
    (hconj : ∀ i < ng, ∀ j < ng, pg w (mask w) (G i) j < ng ∧
      G (pg w (mask w) (G i) j) = pcomp n w (mask w) (G i) (pcomp n w (mask w) (G j) (G i)))
    (hder : ∀ k < ng, (derivK w G D (seedMask S)).testBit k = true) :
    enumOK n gs ps (enumBfs n gs ps fuel) = true := by
  have hN : N ≠ 0 := by
    intro e
    subst e
    have e1 : runFB n w (mask w) ng ps G T E 0 0 1 = 1 := rfl
    omega
  have hidA : unpack n w (pidn n w) = idA n := idK_sound (idK_of_szOK hsz)
  have hstep : ∀ i < N, ∀ k < ng,
      leftA n gs k (unpack n w (T i)) = unpack n w (pcomp n w (mask w) (G k) (T i)) := by
    intro i hi k hk1
    unfold leftA
    rw [hg k hk1, compA_unpack (hcG k hk1) (hcT i hi)]
  have hcl : ∀ k < ng, ∀ i < N, ∃ j < N, pcomp n w (mask w) (G k) (T i) = T j := by
    let Cl : Nat → Prop := fun k =>
      k < ng ∧ ∀ i < N, ∃ j < N, pcomp n w (mask w) (G k) (T i) = T j
    have hQ : ∀ i j, Cl i → Cl j → Cl (pg w (mask w) (G i) j) := by
      rintro i j ⟨hi, hci⟩ ⟨hj, hcj⟩
      obtain ⟨ht, eG⟩ := hconj i hi j hj
      refine ⟨ht, fun a ha => ?_⟩
      obtain ⟨b, hb, eb⟩ := hci a ha
      obtain ⟨c, hc, ec⟩ := hcj b hb
      obtain ⟨d, hd, ed⟩ := hci c hc
      refine ⟨d, hd, ?_⟩
      rw [eG, pcomp_assocS (hcG i hi) (canonK_pcomp (hcG j hj) (hcG i hi)) (hcT a ha),
        pcomp_assocS (hcG j hj) (hcG i hi) (hcT a ha), eb, ec, ed]
    have h0 : ∀ k, (seedMask S).testBit k = true → Cl k := by
      intro k hk
      have hkS := seedMask_spec hk
      refine ⟨hS k hkS, fun i hi => ?_⟩
      obtain ⟨hlt, e⟩ := seedPt_spec (hseed i hi) k hkS
      exact ⟨_, hlt, e⟩
    exact fun k hk => (derivK_spec hQ D _ h0 k (hder k hk)).2
  have hreach0 := runFB_points
    (P := fun j => j < N → Reach (leftA n gs) gs.size (idA n) (unpack n w (T j)))
    (fun _ => by
      rw [hT0, hidA]
      exact Reach.root)
    (fun i c k hic hk hPi hT hc => by
      have hi : i < N := by omega
      rw [hT, ← hstep i hi k hk]
      exact Reach.step k (hs ▸ hk) (hPi hi)) hR hN
  have hvg : ∀ k < gs.size, validA n gs[k]! = true := by
    intro k hk1
    rw [hg k (hs ▸ hk1)]
    exact validA_unpack (hp k (hs ▸ hk1))
  have hinj : ∀ i < N, ∀ j < N, unpack n w (T i) = unpack n w (T j) → i = j := by
    intro i hi j hj e
    refine keysSK_spec hK i hi j hj ?_
    have e' := congrArg (keyA n ps) e
    rw [keyA_unpack hps, keyA_unpack hps] at e'
    exact e'
  let U : Nat → Array Nat := fun i => unpack n w (T i)
  let Sf : Finset (Array Nat) := (Finset.range N).image U
  have hmemS : ∀ x, x ∈ Sf ↔ ∃ i < N, unpack n w (T i) = x := by
    intro x
    simp only [Sf, U, Finset.mem_image, Finset.mem_range]
  have hroot : idA n ∈ Sf := (hmemS _).2 ⟨0, Nat.pos_of_ne_zero hN, by rw [hT0, hidA]⟩
  have hclosed : ∀ x ∈ Sf, ∀ k < gs.size, leftA n gs k x ∈ Sf := by
    intro x hx k hk1
    obtain ⟨i, hi, rfl⟩ := (hmemS x).1 hx
    obtain ⟨j, hj, e⟩ := hcl k (hs ▸ hk1) i hi
    rw [hstep i hi k (hs ▸ hk1), e]
    exact (hmemS _).2 ⟨j, hj, rfl⟩
  have hR' : ∀ x ∈ Sf, Reach (leftA n gs) gs.size (idA n) x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := (hmemS x).1 hx
    exact hreach0 i hi hi
  have hS' : ∀ x, Reach (leftA n gs) gs.size (idA n) x ↔ x ∈ Sf :=
    reach_iff_of_closed hroot hclosed hR'
  have hv : ∀ x ∈ Sf, validA n x = true := by
    intro x hx
    have hr := hR' x hx
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
    rw [keysSK_spec hK i hi j hj e]
  have hcard : Sf.card = N := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj e
    exact hinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) e
  obtain ⟨hcert, -, -, -⟩ := arrBfs_spec (act := leftA n gs) (ngen := gs.size)
    (valid := validA n) (key := keyA n ps) (root := idA n) (fuel := fuel) Sf hS' hv hkeyS
    (by rw [hcard]; exact hf)
  unfold enumOK enumBfs
  rw [Bool.and_eq_true]
  exact ⟨allLt_iff.2 hvg, hcert⟩

end CFSG.KC.BfsPin

end
