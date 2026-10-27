module

public import Certificates.Data.Kernel.BfsPinKeyY
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import CFSG.Certificates.Kernel.PGrpSound
public import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KC.BfsPin

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.PGrp
open CFSG.KLie.CT (fget)

theorem genStepY_eq (n w N : Nat) (ps : List Nat) (T : Nat → Nat) (t row g k c : Nat) :
    genStepY n w N ps T t row g k c =
      if c = 0 then 0
      else if fget row k 16 < c then
        (if fget row k 16 < N ∧ keyCK n w ps g t = keyK n w ps (T (fget row k 16)) then c else 0)
      else if fget row k 16 = c then (if T c = pcomp n w (mask w) g t then c + 1 else 0)
      else 0 := by
  unfold genStepY
  simp only [strictN_app, nIf_ite, Nat.beq_eq, Nat.blt_eq, bAnd_iff]

theorem genStepY_zero (n w N : Nat) (ps : List Nat) (T : Nat → Nat) (t row g k : Nat) :
    genStepY n w N ps T t row g k 0 = 0 := by
  simp only [genStepY_eq, ↓reduceIte]

theorem genStepY_spec {n w N : Nat} {ps : List Nat} {T : Nat → Nat} {t row g k c r : Nat}
    (hr : genStepY n w N ps T t row g k c = r) (h0 : r ≠ 0) :
    c ≠ 0 ∧ c ≤ r ∧ ∀ j, c ≤ j → j < r → T j = pcomp n w (mask w) g t := by
  rw [genStepY_eq] at hr
  by_cases h1 : c = 0
  · simp only [h1, ↓reduceIte] at hr
    exact absurd hr.symm h0
  simp only [h1, ↓reduceIte] at hr
  by_cases h2 : fget row k 16 < c
  · simp only [h2, ↓reduceIte] at hr
    by_cases h3 : fget row k 16 < N ∧ keyCK n w ps g t = keyK n w ps (T (fget row k 16))
    · rw [if_pos h3] at hr
      subst hr
      exact ⟨h1, le_refl _, fun j a b => absurd (lt_of_le_of_lt a b) (lt_irrefl _)⟩
    · rw [if_neg h3] at hr
      exact absurd hr.symm h0
  · simp only [h2, ↓reduceIte] at hr
    by_cases h4 : fget row k 16 = c
    · by_cases h5 : T c = pcomp n w (mask w) g t
      · simp only [h4, h5, ↓reduceIte] at hr
        subst hr
        refine ⟨h1, Nat.le_succ c, fun j a b => ?_⟩
        have e : j = c := by omega
        rw [e]
        exact h5
      · simp only [h4, h5, ↓reduceIte] at hr
        exact absurd hr.symm h0
    · simp only [h4, ↓reduceIte] at hr
      exact absurd hr.symm h0

theorem genStep_of_genStepY {n w N : Nat} {ps : List Nat} {T : Nat → Nat} {t row g k c : Nat}
    (hb : ∀ j < N, keyCK n w ps g t = keyK n w ps (T j) → T j = pcomp n w (mask w) g t)
    (h0 : genStepY n w N ps T t row g k c ≠ 0) :
    genStep n w (mask w) T t row g k c = genStepY n w N ps T t row g k c := by
  rw [genStepY_eq] at h0 ⊢
  rw [genStep_eq]
  by_cases h1 : c = 0
  · simp only [h1, ↓reduceIte]
  simp only [h1, ↓reduceIte] at h0 ⊢
  by_cases h2 : fget row k 16 < c
  · simp only [h2, ↓reduceIte] at h0 ⊢
    by_cases h3 : fget row k 16 < N ∧ keyCK n w ps g t = keyK n w ps (T (fget row k 16))
    · rw [if_pos h3, if_pos (hb _ h3.1 h3.2)]
    · rw [if_neg h3] at h0
      exact absurd rfl h0
  · simp only [h2, ↓reduceIte]

@[expose] noncomputable def pointFY (n w N : Nat) (ps : List Nat) (G T E : Nat → Nat)
    (i len : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ c => c)
    (fun _ ih lo c => ih (Nat.succ lo) (genStepY n w N ps T (T i) (E i) (G lo) lo c)) len

@[expose] noncomputable def pointRecY (n w ng N : Nat) (ps : List Nat) (G T E : Nat → Nat)
    (i r : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun c => c)
    (fun r ih c => strictN (genStepY n w N ps T (T i) (E i) (G (Nat.sub (Nat.sub ng r) (nat_lit 1)))
      (Nat.sub (Nat.sub ng r) (nat_lit 1)) c) ih) r

theorem pointRecY_eq {n w ng N : Nat} {ps : List Nat} {G T E : Nat → Nat} (i : Nat) :
    ∀ r, r ≤ ng → ∀ c,
      pointRecY n w ng N ps G T E i r c = pointFY n w N ps G T E i r (ng - r) c
  | 0, _, _ => rfl
  | r + 1, h, c => by
    have e1 : Nat.sub (Nat.sub ng r) (nat_lit 1) = ng - (r + 1) := by
      change ng - r - 1 = ng - (r + 1)
      omega
    have e2 : Nat.succ (ng - (r + 1)) = ng - r := by omega
    have s1 : pointRecY n w ng N ps G T E i (r + 1) c = pointRecY n w ng N ps G T E i r
        (genStepY n w N ps T (T i) (E i) (G (Nat.sub (Nat.sub ng r) (nat_lit 1)))
          (Nat.sub (Nat.sub ng r) (nat_lit 1)) c) := strictN_app _ _
    have s2 : pointFY n w N ps G T E i (r + 1) (ng - (r + 1)) c = pointFY n w N ps G T E i r
        (Nat.succ (ng - (r + 1)))
        (genStepY n w N ps T (T i) (E i) (G (ng - (r + 1))) (ng - (r + 1)) c) := rfl
    rw [s1, s2, e1, e2, pointRecY_eq i r (by omega)]

theorem pointStepY_eq {n w ng N : Nat} {ps : List Nat} {G T E : Nat → Nat} (i c : Nat) :
    pointStepY n w ng N ps G T E i c = pointFY n w N ps G T E i ng 0 c := by
  have h := pointRecY_eq (n := n) (w := w) (ng := ng) (N := N) (ps := ps) (G := G) (T := T)
    (E := E) i ng (Nat.le_refl ng) c
  rw [Nat.sub_self] at h
  rw [← h]
  unfold pointStepY
  rw [strictN_app, strictN_app]
  rfl

theorem pointFY_zero {n w N : Nat} {ps : List Nat} {G T E : Nat → Nat} (i : Nat) :
    ∀ len lo, pointFY n w N ps G T E i len lo 0 = 0
  | 0, _ => rfl
  | len + 1, lo => by
    change pointFY n w N ps G T E i len (Nat.succ lo)
      (genStepY n w N ps T (T i) (E i) (G lo) lo 0) = 0
    rw [genStepY_zero]
    exact pointFY_zero i len _

theorem pointFY_spec {n w ng N : Nat} {ps : List Nat} {G T E : Nat → Nat} (Q : Nat → Prop)
    (i : Nat) (hQ : ∀ k < ng, Q (pcomp n w (mask w) (G k) (T i))) :
    ∀ len lo c r, lo + len ≤ ng → pointFY n w N ps G T E i len lo c = r → r ≠ 0 →
      (∀ j < c, Q (T j)) → c ≤ r ∧ ∀ j < r, Q (T j)
  | 0, lo, c, r, _, hr, _, hc => by
    have e : c = r := hr
    subst e
    exact ⟨le_refl _, hc⟩
  | len + 1, lo, c, r, hl, hr, h0, hc => by
    change pointFY n w N ps G T E i len (Nat.succ lo)
      (genStepY n w N ps T (T i) (E i) (G lo) lo c) = r at hr
    have hc0 : genStepY n w N ps T (T i) (E i) (G lo) lo c ≠ 0 := by
      intro e
      rw [e, pointFY_zero] at hr
      exact h0 hr.symm
    obtain ⟨-, hle, hnew⟩ := genStepY_spec rfl hc0
    have hc' : ∀ j < genStepY n w N ps T (T i) (E i) (G lo) lo c, Q (T j) := by
      intro j hj'
      rcases Nat.lt_or_ge j c with h | h
      · exact hc j h
      · rw [hnew j h hj']
        exact hQ lo (by omega)
    obtain ⟨hle', hQ'⟩ := pointFY_spec Q i hQ len (Nat.succ lo) _ r (by omega) hr h0 hc'
    exact ⟨le_trans hle hle', hQ'⟩

theorem pointF_of_pointFY {n w ng N : Nat} {ps : List Nat} {G T E : Nat → Nat} (i : Nat)
    (hb : ∀ k < ng, ∀ j < N, keyCK n w ps (G k) (T i) = keyK n w ps (T j) →
      T j = pcomp n w (mask w) (G k) (T i)) :
    ∀ len lo c, lo + len ≤ ng → pointFY n w N ps G T E i len lo c ≠ 0 →
      pointF n w (mask w) G T E i len lo c = pointFY n w N ps G T E i len lo c
  | 0, _, _, _, _ => rfl
  | len + 1, lo, c, hl, h0 => by
    change pointFY n w N ps G T E i len (Nat.succ lo)
      (genStepY n w N ps T (T i) (E i) (G lo) lo c) ≠ 0 at h0
    change pointF n w (mask w) G T E i len (Nat.succ lo)
      (genStep n w (mask w) T (T i) (E i) (G lo) lo c) = pointFY n w N ps G T E i len (Nat.succ lo)
      (genStepY n w N ps T (T i) (E i) (G lo) lo c)
    have hc0 : genStepY n w N ps T (T i) (E i) (G lo) lo c ≠ 0 := by
      intro e
      rw [e, pointFY_zero] at h0
      exact h0 rfl
    rw [genStep_of_genStepY (hb lo (by omega)) hc0]
    exact pointF_of_pointFY i hb len (Nat.succ lo) _ (by omega) h0

theorem runFY_succ {n w ng N : Nat} {ps : List Nat} {G T E : Nat → Nat} (len lo c : Nat) :
    runFY n w ng N ps G T E (len + 1) lo c =
      runFY n w ng N ps G T E len (Nat.succ lo)
        (nIf(Nat.blt lo c, pointStepY n w ng N ps G T E lo c, nat_lit 0)) :=
  strictN_app _ _

theorem runFY_zero {n w ng N : Nat} {ps : List Nat} {G T E : Nat → Nat} :
    ∀ len lo, runFY n w ng N ps G T E len lo 0 = 0
  | 0, _ => rfl
  | len + 1, lo => by
    rw [runFY_succ]
    have hb : Nat.blt lo 0 = false := by
      cases h : Nat.blt lo 0
      · rfl
      · exact absurd (Nat.blt_eq.mp h) (Nat.not_lt_zero lo)
    rw [hb]
    exact runFY_zero len _

theorem runFY_spec {n w ng N : Nat} {ps : List Nat} {G T E : Nat → Nat} (Q : Nat → Prop)
    (hQ : ∀ y, Q y → ∀ k < ng, Q (pcomp n w (mask w) (G k) y)) :
    ∀ len lo c r, runFY n w ng N ps G T E len lo c = r → r ≠ 0 → (∀ j < c, Q (T j)) →
      ∀ j < r, Q (T j)
  | 0, lo, c, r, hr, _, hc => by
    have e : c = r := hr
    subst e
    exact hc
  | len + 1, lo, c, r, hr, h0, hc => by
    rw [runFY_succ] at hr
    cases hb : Nat.blt lo c
    · rw [hb] at hr
      change runFY n w ng N ps G T E len (Nat.succ lo) 0 = r at hr
      rw [runFY_zero] at hr
      exact absurd hr.symm h0
    · rw [hb] at hr
      change runFY n w ng N ps G T E len (Nat.succ lo) (pointStepY n w ng N ps G T E lo c) = r
        at hr
      have hlo : lo < c := Nat.blt_eq.mp hb
      have hp0 : pointStepY n w ng N ps G T E lo c ≠ 0 := by
        intro e
        rw [e, runFY_zero] at hr
        exact h0 hr.symm
      obtain ⟨-, hQp⟩ := pointFY_spec Q lo (fun k hk => hQ _ (hc lo hlo) k hk) ng 0 c
        _ (by omega) (pointStepY_eq lo c).symm hp0 hc
      exact runFY_spec Q hQ len (Nat.succ lo) _ r hr h0 hQp

theorem runF_of_runFY {n w ng N : Nat} {ps : List Nat} {G T E : Nat → Nat}
    (hb : ∀ i < N, ∀ k < ng, ∀ j < N, keyCK n w ps (G k) (T i) = keyK n w ps (T j) →
      T j = pcomp n w (mask w) (G k) (T i)) :
    ∀ len lo c, lo + len ≤ N → runFY n w ng N ps G T E len lo c ≠ 0 →
      runF n w (mask w) ng G T E len lo c = runFY n w ng N ps G T E len lo c
  | 0, _, _, _, _ => rfl
  | len + 1, lo, c, hl, h0 => by
    rw [runFY_succ] at h0 ⊢
    rw [runF_succ]
    cases hb' : Nat.blt lo c
    · try rw [hb'] at h0
      change runFY n w ng N ps G T E len (Nat.succ lo) 0 ≠ 0 at h0
      rw [runFY_zero] at h0
      exact absurd rfl h0
    · try rw [hb'] at h0
      try rw [hb']
      change runFY n w ng N ps G T E len (Nat.succ lo) (pointStepY n w ng N ps G T E lo c) ≠ 0
        at h0
      change runF n w (mask w) ng G T E len (Nat.succ lo) (pointStep n w (mask w) ng G T E lo c) =
        runFY n w ng N ps G T E len (Nat.succ lo) (pointStepY n w ng N ps G T E lo c)
      have hp0 : pointStepY n w ng N ps G T E lo c ≠ 0 := by
        intro e
        rw [e, runFY_zero] at h0
        exact h0 rfl
      have hpe : pointStep n w (mask w) ng G T E lo c = pointStepY n w ng N ps G T E lo c := by
        rw [pointStep_eq, pointStepY_eq]
        rw [pointStepY_eq] at hp0
        exact pointF_of_pointFY lo (fun k hk => hb lo (by omega) k hk) ng 0 c (by omega) hp0
      rw [hpe]
      exact runF_of_runFY hb len (Nat.succ lo) _ (by omega) h0

theorem runFY_add {n w ng N : Nat} {ps : List Nat} {G T E : Nat → Nat} : ∀ (a b lo c : Nat),
    runFY n w ng N ps G T E (a + b) lo c =
      runFY n w ng N ps G T E b (lo + a) (runFY n w ng N ps G T E a lo c)
  | 0, b, lo, c => by rw [Nat.zero_add, Nat.add_zero]; rfl
  | a + 1, b, lo, c => by
    have e : Nat.succ lo + a = lo + (a + 1) := by omega
    rw [Nat.add_right_comm, runFY_succ, runFY_succ, runFY_add a b (Nat.succ lo), e]

theorem runFY_blocks {n w ng N : Nat} {ps : List Nat} {G T E : Nat → Nat} (L : Nat)
    (C : Nat → Nat) : ∀ K, (∀ s < K, runSlY n w ng N ps G T E L C s = true) →
      runFY n w ng N ps G T E (L * K) 0 (C 0) = C K
  | 0, _ => rfl
  | K + 1, h => by
    rw [Nat.mul_succ, runFY_add, runFY_blocks L C K (fun s hs => h s (by omega)), Nat.zero_add]
    exact Nat.eq_of_beq_eq_true (h K (by omega))

theorem keyed_points {n w ng N L K : Nat} {ps : List Nat} {G T E C : Nat → Nat} (Q : Nat → Prop)
    (h0 : Q (T 0)) (hQ : ∀ y, Q y → ∀ k < ng, Q (pcomp n w (mask w) (G k) y))
    (hN : N = L * K) (hN0 : 0 < N) (hC0 : C 0 = 1) (hCK : C K = N)
    (hr : ∀ s < K, runSlY n w ng N ps G T E L C s = true) : ∀ j < N, Q (T j) := by
  have hR := runFY_blocks L C K hr
  rw [hC0, hCK, ← hN] at hR
  refine runFY_spec Q hQ N 0 1 N hR (by omega) fun j hj => ?_
  have e : j = 0 := by omega
  rw [e]
  exact h0

theorem bfsK_of_keyed {n w ng N L K : Nat} {ps : List Nat} {SK : List Nat}
    {G T E S C : Nat → Nat} (hN : N = L * K) (hL : 0 < L) (hsz : szOK n w = true)
    (hG : allN ng (fun k => canonK n w (mask w) (Nat.mul n w) (G k)) = true)
    (hc : ∀ s < K, canonSl n w T L s = true) (h0 : Nat.beq (T 0) (pidn n w) = true)
    (hD : distinctK N T S = true) (hC0 : C 0 = 1) (hCK : C K = N)
    (hr : ∀ s < K, runSlY n w ng N ps G T E L C s = true)
    (hk : keysSK n w ps N T SK = true) (hps : ∀ p ∈ ps, p < n)
    (hcl : ∀ i < N, ∀ k < ng, ∃ j < N, T j = pcomp n w (mask w) (G k) (T i)) :
    bfsK n w ng G N T E S = true := by
  have hn : n < 2 ^ 32 := by
    have := (szOK_facts' hsz).1
    omega
  have hN0 : 0 < N := by
    unfold keysSK at hk
    simp only [bAnd_iff] at hk
    exact Nat.blt_eq.mp hk.2.1
  have hb : ∀ i < N, ∀ k < ng, ∀ j < N, keyCK n w ps (G k) (T i) = keyK n w ps (T j) →
      T j = pcomp n w (mask w) (G k) (T i) := by
    intro i hi k hk1 j hj e
    obtain ⟨j', hj', e'⟩ := hcl i hi k hk1
    have hkj : keyK n w ps (T j') = keyK n w ps (T j) := by
      rw [e', keyK_pcomp hn _ _ hps, e]
    rw [← keysSK_spec hk j' hj' j hj hkj]
    exact e'
  have hR := runFY_blocks L C K hr
  rw [hC0, hCK, ← hN] at hR
  have hR' : runK n w (mask w) ng G T E N = N := by
    rw [runK_eq, runF_of_runFY hb N 0 1 (by omega) (by omega), hR]
  have hT : ∀ i < N, canonK n w (mask w) (Nat.mul n w) (T i) = true := by
    intro i hi
    rw [hN] at hi
    have hs : i / L < K := (Nat.div_lt_iff_lt_mul hL).2 (by rwa [Nat.mul_comm] at hi)
    have h1 := hc (i / L) hs
    unfold canonSl at h1
    have h2 := allN_spec h1 (i % L) (Nat.mod_lt _ hL)
    have e : Nat.add (Nat.mul L (i / L)) (i % L) = i := Nat.div_add_mod i L
    rwa [e] at h2
  unfold bfsK
  rw [hsz, hG, allN_of_forall hT, h0, hD, hR', Nat.beq_refl]

theorem canon_eq_of_prep {n w P Q : Nat} {g : Equiv.Perm (Fin n)}
    (hP : canonK n w (mask w) (n * w) P = true) (hQ : canonK n w (mask w) (n * w) Q = true)
    (h1 : Orb.PRep n w P g) (h2 : Orb.PRep n w Q g) : P = Q := by
  obtain ⟨-, hw, hp0, -⟩ := CFSG.KS.PF.canon_facts hP
  obtain ⟨-, -, hq0, -⟩ := CFSG.KS.PF.canon_facts hQ
  exact CFSG.KS.PF.eq_of_fields (CFSG.KS.PF.w_pos hw) hp0 hq0 fun i hi =>
    (h1 ⟨i, hi⟩).trans (h2 ⟨i, hi⟩).symm

theorem pts_closed_of_card {n w N : Nat} {T : Nat → Nat} (H : Subgroup (Equiv.Perm (Fin n)))
    (hcard : Nat.card H ≤ N)
    (hT : ∀ i < N, canonK n w (mask w) (n * w) (T i) = true ∧ ∃ g ∈ H, Orb.PRep n w (T i) g)
    (hinj : ∀ a < N, ∀ b < N, T a = T b → a = b) {y : Nat}
    (hy : canonK n w (mask w) (n * w) y = true) {g : Equiv.Perm (Fin n)} (hg : g ∈ H)
    (hyg : Orb.PRep n w y g) : ∃ j < N, T j = y := by
  let σ : Fin N → Equiv.Perm (Fin n) := fun i => Classical.choose (hT i i.2).2
  have hσ : ∀ i : Fin N, σ i ∈ H ∧ Orb.PRep n w (T i) (σ i) := fun i =>
    Classical.choose_spec (hT i i.2).2
  let f : Fin N → H := fun i => ⟨σ i, (hσ i).1⟩
  have hf : Function.Injective f := by
    intro a b e
    have e' : σ a = σ b := congrArg Subtype.val e
    have hab : T a = T b :=
      canon_eq_of_prep (hT a a.2).1 (hT b b.2).1 (hσ a).2 (e' ▸ (hσ b).2)
    exact Fin.ext (hinj a a.2 b b.2 hab)
  obtain ⟨j, hj⟩ := (hf.bijective_of_nat_card_le (by rw [Nat.card_fin]; exact hcard)).2 ⟨g, hg⟩
  have e : σ j = g := congrArg Subtype.val hj
  exact ⟨j, j.2, canon_eq_of_prep (hT j j.2).1 hy (e ▸ (hσ j).2) hyg⟩

end CFSG.KC.BfsPin

end
