module

public import Certificates.Data.Kernel.Spor.Fi24Pair
public import CFSG.Certificates.Kernel.YModel.ChainSem
public import CFSG.Certificates.Kernel.YModel.SchCard
import CFSG.Certificates.Kernel.Spor.Fi24PairSoundAux
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.KC.Fi24Pair

open CFSG.KC CFSG.KC.Benes CFSG.KC.MonsterConv.Perm CFSG.KC.YModel.Chain

theorem closedOK_spec {NW M : ℕ} (h : closedOK NW M = true) :
    ∀ i < 4096, ∀ j < 4096, M.testBit (4096 * benesPerm 12 NW i + benesPerm 12 NW j) = true →
      M.testBit (4096 * i + j) = true := by
  intro i hi j hj hbit
  obtain ⟨hv, he⟩ := andB_true h
  have hM : Nat.lor M (preP NW M) = M := Nat.eq_of_beq_eq_true he
  have e := congrArg (fun x => x.testBit (4096 * i + j)) hM
  simp only [nlor, Nat.testBit_or, testBit_preP hv M hi hj, hbit, Bool.or_true] at e
  exact e.symm

private theorem recB_spec {g : ℕ → Bool} : ∀ n,
    Nat.rec (motive := fun _ => Bool) true
      (fun k ih => Bool.rec (motive := fun _ => Bool) false ih (g k)) n = true →
      ∀ k < n, g k = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, h, k, hk => by
    obtain ⟨h1, h2⟩ := andB_true h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact recB_spec n h2 k hk
    · exact h1

private theorem allBelow_spec' {m hi : ℕ} {f : ℕ → Bool}
    (h : CFSG.KC.Loop.allBelow m hi f = true) : ∀ i < m, i < 64 * hi → f i = true := by
  intro i him hih
  have hq : i / 64 < hi := by omega
  have h1 := recB_spec hi h (i / 64) hq
  have h2 := recB_spec (g := fun l => Bool.rec (motive := fun _ => Bool) true
    (f (Nat.add (Nat.shiftLeft (i / 64) 6) l)) (Nat.blt (Nat.add (Nat.shiftLeft (i / 64) 6) l) m))
    64 h1 (i % 64) (Nat.mod_lt _ (by omega))
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq]
    omega
  simp only [e, Nat.blt_eq.mpr him] at h2
  exact h2

private theorem allBelow_spec3240 {f : ℕ → Bool} (h : CFSG.KC.Loop.allBelow 3240 51 f = true) :
    ∀ p < 3240, f p = true :=
  fun p hp => allBelow_spec' h p hp (by omega)

private theorem testBit_one' (i : ℕ) : (1 : ℕ).testBit i = decide (i = 0) := by
  have h := @Nat.testBit_two_pow 0 i
  rw [Nat.pow_zero] at h
  rw [h]
  by_cases h0 : i = 0
  · subst h0; rfl
  · rw [decide_eq_false h0, decide_eq_false (fun h' => h0 h'.symm)]

private theorem testBit_entAcc (PL p : ℕ) (E : ℕ → ℕ) (h0 : E 0 = 0)
    (hs : ∀ b, E (b + 1) = E b ||| (((PL >>> (4096 * b + p)) &&& 1) <<< b)) :
    ∀ n j, (E n).testBit j = (decide (j < n) && PL.testBit (4096 * j + p)) := by
  intro n
  induction n with
  | zero => intro j; simp [h0]
  | succ n ih =>
    intro j
    rw [hs, Nat.testBit_or, ih, Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight,
      testBit_one']
    rcases lt_trichotomy j n with h | h | h
    · have h1 : decide (j < n) = true := decide_eq_true h
      have h2 : decide (j ≥ n) = false := decide_eq_false (by omega)
      have h3 : decide (j < n + 1) = true := decide_eq_true (by omega)
      rw [h1, h2, h3]
      simp
    · subst h
      have h1 : decide (j < j) = false := decide_eq_false (Nat.lt_irrefl j)
      have h2 : decide (j ≥ j) = true := decide_eq_true (Nat.le_refl j)
      have h3 : decide (j < j + 1) = true := decide_eq_true (by omega)
      rw [h1, h2, h3, Nat.sub_self]
      simp
    · have h1 : decide (j < n) = false := decide_eq_false (by omega)
      have h2 : decide (j ≥ n) = true := decide_eq_true (by omega)
      have h3 : decide (j < n + 1) = false := decide_eq_false (by omega)
      have h4 : decide (j - n = 0) = false := decide_eq_false (by omega)
      rw [h1, h2, h3, h4]
      simp

private theorem testBit_entP (PL p j : ℕ) :
    (entP PL p).testBit j = (decide (j < 12) && PL.testBit (4096 * j + p)) :=
  testBit_entAcc PL p (fun n => Nat.rec (motive := fun _ => ℕ) 0
    (fun b acc => Nat.lor acc (Nat.shiftLeft
      (Nat.land (Nat.shiftRight PL (Nat.add (Nat.mul 4096 b) p)) 1) b)) n)
    rfl (fun _ => rfl) 12 j

private theorem planes_testBit {NW b p : ℕ} (hv : StagesValid 12 NW) (hb : b < 12) (hp : p < 4096) :
    (planesNW NW).testBit (4096 * b + p) = (benesPerm 12 NW p).testBit b := by
  have e := (testBit_netApply (k := 12) (W := 4096) (P := 12) (N := NW) (by norm_num) hv
    (idP 12)).1 b hb p hp
  have e2 := YModel.Sem.testBit_idP (k := 12) hb (benesPerm_lt hv hp)
  exact e.trans e2

private theorem entP_planesNW {NW p : ℕ} (hv : StagesValid 12 NW) (hp : p < 4096) :
    entP (planesNW NW) p = benesPerm 12 NW p := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_entP]
  by_cases hj : j < 12
  · rw [decide_eq_true hj, Bool.true_and, planes_testBit hv hj hp]
  · rw [decide_eq_false hj, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (lt_two_pow_mono (benesPerm_lt hv hp) (by omega))).symm

@[expose] def SigF (LR : ℕ → ℕ → ℕ) (FP : ℕ → ℕ) (NW r : ℕ) : Prop :=
  StagesValid 12 NW ∧ ∀ p < 3240, benesPerm 12 NW p < 3240 ∧ LR r (FP p) = FP (benesPerm 12 NW p)

theorem fOK_spec {FP : ℕ → ℕ} (h : fOK FP = true) :
    (∀ p < 3240, FP p < 306936) ∧ ∀ p q, p < q → q < 3240 → FP p < FP q := by
  unfold fOK at h
  have h1 : ∀ p < 3240, FP p < 306936 ∧ (p + 1 < 3240 → FP p < FP (p + 1)) := by
    intro p hp
    have h3 := allBelow_spec3240 h p hp
    obtain ⟨h4, h5⟩ := YModel.Sem.andB_eq h3
    refine ⟨Nat.blt_eq.mp h4, fun hp1 => ?_⟩
    have hb : Nat.blt (Nat.succ p) 3240 = true := Nat.blt_eq.mpr hp1
    rw [hb] at h5
    exact Nat.blt_eq.mp h5
  have step : ∀ d p, p + d + 1 < 3240 → FP p < FP (p + d + 1) := by
    intro d
    induction d with
    | zero => intro p hp; exact (h1 p (by omega)).2 (by omega)
    | succ d ih =>
      intro p hp
      have h2 := (h1 (p + d + 1) (by omega)).2 (by omega)
      exact lt_trans (ih p (by omega)) h2
  refine ⟨fun p hp => (h1 p hp).1, fun p q hpq hq => ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d, q = p + d + 1 := ⟨q - p - 1, by omega⟩
  exact step d p hq

private theorem testBit_ones (n i : ℕ) : (ones n).testBit i = decide (i < n) := by
  rw [ones_eq, Nat.testBit_two_pow_sub_one]

private theorem testBit_ones_mul_div (W L n c : ℕ) (hL : 0 < L) (hW : W = L * n)
    (hc : ∀ i, L ≤ i → c.testBit i = false) (q : ℕ) :
    (Nat.mul c (Nat.div (ones W) (ones L))).testBit q = (decide (q < W) && c.testBit (q % L)) := by
  rw [nmul, ndiv, ones_eq, ones_eq]
  exact testBit_mul_div hL hW (Nat.lt_pow_two_of_testBit c hc) q

private theorem testBit_region (q : ℕ) :
    region.testBit q = (decide (q < 13271040) && decide (q % 4096 < 3240)) := by
  have hc : ∀ i, 4096 ≤ i → (ones 3240).testBit i = false := fun i hi => by
    rw [testBit_ones]
    exact decide_eq_false (by omega)
  have e := testBit_ones_mul_div 13271040 4096 3240 (ones 3240) (by norm_num) (by norm_num) hc q
  rw [testBit_ones] at e
  unfold region
  exact e

theorem regionOK_spec {M r0 r1 : ℕ} (h : regionOK M r0 r1 = true) :
    r0 < 3240 ∧ r1 < 3240 ∧ M.testBit (4096 * r0 + r1) = true ∧
      ∀ q, M.testBit q = true → q / 4096 < 3240 ∧ q % 4096 < 3240 := by
  unfold regionOK at h
  obtain ⟨h1, h2⟩ := YModel.Sem.andB_eq h
  obtain ⟨h3, h4⟩ := YModel.Sem.andB_eq h1
  obtain ⟨h5, h6⟩ := YModel.Sem.andB_eq h2
  refine ⟨Nat.blt_eq.mp h3, Nat.blt_eq.mp h4, ?_, ?_⟩
  · have e : ((M >>> (4096 * r0 + r1)) &&& 1).testBit 0 = true := by
      rw [show (M >>> (4096 * r0 + r1)) &&& 1 = 1 from Nat.eq_of_beq_eq_true h6]
      rfl
    rw [Nat.testBit_and, Nat.testBit_shiftRight] at e
    simpa using e
  · intro q hq
    have e : (M &&& region).testBit q = true := by
      rw [show M &&& region = M from Nat.eq_of_beq_eq_true h5]
      exact hq
    rw [Nat.testBit_and, hq, testBit_region] at e
    simp only [Bool.true_and, Bool.and_eq_true, decide_eq_true_eq] at e
    omega

@[expose] noncomputable def compL : List ℕ → ℕ → ℕ
  | [], p => p
  | N :: Ns, p => benesPerm 12 N (compL Ns p)

private theorem netsValid_spec :
    ∀ Ns : List ℕ, netsValid 12 Ns = true → ∀ N ∈ Ns, StagesValid 12 N
  | [], _, N, hN => absurd hN (by simp)
  | N' :: Ns, h, N, hN => by
    obtain ⟨h1, h2⟩ := YModel.Sem.andB_eq
      (show andB (netValid 12 N') (netsValid 12 Ns) = true from h)
    rcases List.mem_cons.1 hN with rfl | hN
    · exact stagesValid_of_netValid h1
    · exact netsValid_spec Ns h2 N hN

private theorem compN_eq_compL : ∀ (Ns : List ℕ) (p : ℕ), YModel.Sem.compN 12 Ns p = compL Ns p
  | [], p => rfl
  | N :: Ns, p => by
    change benesPerm 12 N (YModel.Sem.compN 12 Ns p) = benesPerm 12 N (compL Ns p)
    rw [compN_eq_compL Ns p]

theorem hOK_spec {Ns : List ℕ} {HN r0 : ℕ} (hr : r0 < 4096) (h : hOK Ns HN r0 = true) :
    StagesValid 12 HN ∧ (∀ N ∈ Ns, StagesValid 12 N) ∧ (∀ p < 4096, benesPerm 12 HN p = compL Ns p) ∧
      benesPerm 12 HN r0 = r0 := by
  unfold hOK wordNetV at h
  obtain ⟨h1, h2⟩ := YModel.Sem.andB_eq h
  obtain ⟨h3, h4⟩ := YModel.Sem.andB_eq h1
  obtain ⟨h5, h6⟩ := YModel.Sem.andB_eq h3
  have hvN : ∀ N ∈ Ns, StagesValid 12 N := netsValid_spec Ns h5
  have hvH : StagesValid 12 HN := stagesValid_of_netValid h6
  refine ⟨hvH, hvN, fun p hp => ?_, ?_⟩
  · have hF := YModel.Sem.acts_netsApply (k := 12) (P := 12) Ns hvN
    have hG := YModel.Sem.acts_netApply (k := 12) (P := 12) (N := HN) hvH
    unfold wordNet at h4
    have e4 : netsApply 12 (2 ^ 12) (repU (2 ^ 12) 12) Ns (idP 12) =
        netApply 12 (2 ^ 12) (repU (2 ^ 12) 12) HN (idP 12) := Nat.eq_of_beq_eq_true h4
    have := YModel.Sem.eq_of_idP hF hG e4 p hp
    rw [← this, compN_eq_compL]
  · rw [← entP_planesNW (p := r0) hvH hr]
    exact Nat.eq_of_beq_eq_true h2

private theorem absent_spec {FP : ℕ → ℕ} {u : ℕ} (h : absent FP u = true) :
    ∀ p < 3240, FP p ≠ u := by
  intro p hp hpu
  unfold absent at h
  have h1 := allBelow_spec3240 h p hp
  have h2 : Nat.beq (FP p) u = true := Nat.beq_eq.mpr hpu
  have h3 : notB (Nat.beq (FP p) u) = true := h1
  rw [h2] at h3
  exact absurd h3 (by decide)

private theorem locOK_spec {FP : ℕ → ℕ} {u iu : ℕ} (h : locOK FP u iu = true) :
    (iu < 3240 ∧ FP iu = u) ∨ (iu = 3240 ∧ ∀ p < 3240, FP p ≠ u) := by
  unfold locOK at h
  cases hb : Nat.blt iu 3240
  · rw [hb] at h
    change andB (Nat.beq iu 3240) (absent FP u) = true at h
    obtain ⟨h1, h2⟩ := YModel.Sem.andB_eq h
    exact Or.inr ⟨Nat.eq_of_beq_eq_true h1, absent_spec h2⟩
  · rw [hb] at h
    exact Or.inl ⟨Nat.blt_eq.mp hb, Nat.eq_of_beq_eq_true h⟩

theorem outOK_spec {FP : ℕ → ℕ} {M u iu v iv : ℕ} (h : outOK FP M u iu v iv = true) :
    ((iu < 3240 ∧ FP iu = u) ∨ (iu = 3240 ∧ ∀ p < 3240, FP p ≠ u)) ∧
      ((iv < 3240 ∧ FP iv = v) ∨ (iv = 3240 ∧ ∀ p < 3240, FP p ≠ v)) ∧
      (iu < 3240 → iv < 3240 → M.testBit (4096 * iu + iv) = false) := by
  unfold outOK at h
  obtain ⟨h1, h2⟩ := YModel.Sem.andB_eq h
  obtain ⟨hu, hv⟩ := YModel.Sem.andB_eq h1
  refine ⟨locOK_spec hu, locOK_spec hv, fun hiu hiv => ?_⟩
  have hc : andB (Nat.blt iu 3240) (Nat.blt iv 3240) = true := by
    rw [Nat.blt_eq.mpr hiu, Nat.blt_eq.mpr hiv]
    rfl
  rw [hc] at h2
  change Nat.beq _ _ = true at h2
  have e : ((M >>> (4096 * iu + iv)) &&& 1).testBit 0 = false := by
    rw [show (M >>> (4096 * iu + iv)) &&& 1 = 0 from Nat.eq_of_beq_eq_true h2]
    rfl
  rw [Nat.testBit_and, Nat.testBit_shiftRight] at e
  simpa using e

theorem reachK_spec {k : ℕ} {Ns : List ℕ} (hv : ∀ N ∈ Ns, StagesValid k N) {b : ℕ}
    (hb : b < 2 ^ k) (R : ℕ) :
    (∀ p, (reachK k Ns b R).testBit p = true → p < 2 ^ k) ∧
      ∀ C : ℕ → Prop, C b → (∀ p < 2 ^ k, ∀ N ∈ Ns, C (benesPerm k N p) → C p) →
        ∀ p, (reachK k Ns b R).testBit p = true → C p := by
  induction R with
  | zero =>
    have hb' : ∀ p, (reachK k Ns b 0).testBit p = true ↔ p = b := by
      intro p
      have e1 : Nat.shiftLeft 1 b = 2 ^ b := (Nat.shiftLeft_eq 1 b).trans (Nat.one_mul _)
      change (Nat.shiftLeft 1 b).testBit p = true ↔ _
      rw [e1, Nat.testBit_two_pow, decide_eq_true_eq, eq_comm]
    refine ⟨fun p hp => ?_, fun C hC _ p hp => ?_⟩
    · rw [(hb' p).mp hp]
      exact hb
    · rw [(hb' p).mp hp]
      exact hC
  | succ r ih =>
    have e : reachK k Ns b (r + 1) = orbStep k Ns (reachK k Ns b r) := by
      change CFSG.KC.Loop.strictN (orbStep k Ns (reachK k Ns b r)) (fun Y => Y) = _
      exact Benes.strictN_eq _ _
    obtain ⟨i2, i3⟩ := ih
    rw [e]
    refine ⟨fun p hp => ?_, fun C hC hcl p hp => ?_⟩
    · rcases (testBit_orbStep Ns hv _ p).mp hp with h | ⟨h, -⟩
      · exact i2 p h
      · exact h
    · rcases (testBit_orbStep Ns hv _ p).mp hp with h | ⟨h, N, hN, h'⟩
      · exact i3 C hC hcl p h
      · exact hcl p h N hN (i3 C hC hcl _ h')

section Group

variable {G : Type*} [Group G] [MulAction G (Fin 306936)]

@[expose] def letH (g : ℕ → G) : Subgroup G := Subgroup.closure (Set.range fun k : Fin 18 => g k)

theorem g_mem_letH (g : ℕ → G) {k : ℕ} (hk : k < 18) : g k ∈ letH g :=
  Subgroup.subset_closure ⟨⟨k, hk⟩, rfl⟩

@[expose] def wordG (g : ℕ → G) (v : List ℕ) : G := (v.map g).prod

theorem wordG_mem (g : ℕ → G) {v : List ℕ} (hv : ∀ t ∈ v, t < 18) : wordG g v ∈ letH g := by
  induction v with
  | nil => exact Subgroup.one_mem _
  | cons t v ih =>
    change g t * wordG g v ∈ letH g
    exact Subgroup.mul_mem _ (g_mem_letH g (hv t List.mem_cons_self))
      (ih fun t' h => hv t' (List.mem_cons_of_mem _ h))

variable {LR : ℕ → ℕ → ℕ} {FP NT : ℕ → ℕ}

@[expose] def pt (hF : ∀ p < 3240, FP p < 306936) {p : ℕ} (hp : p < 3240) : Fin 306936 :=
  ⟨FP p, hF p hp⟩

theorem letter_pt (g : ℕ → G) (hg : ∀ k < 18, ∀ x : Fin 306936, ((g k) • x).val = LR (4 + k) x.val)
    (hsig : ∀ k < 18, SigF LR FP (NT k) (4 + k)) {k p : ℕ} (hk : k < 18) (hp : p < 3240)
    (x : Fin 306936) (hx : x.val = FP p) :
    ((g k) • x).val = FP (benesPerm 12 (NT k) p) ∧ benesPerm 12 (NT k) p < 3240 := by
  obtain ⟨-, h⟩ := hsig k hk
  obtain ⟨h1, h2⟩ := h p hp
  exact ⟨by rw [hg k hk, hx, h2], h1⟩

theorem word_pt (g : ℕ → G) (hg : ∀ k < 18, ∀ x : Fin 306936, ((g k) • x).val = LR (4 + k) x.val)
    (hsig : ∀ k < 18, SigF LR FP (NT k) (4 + k)) :
    ∀ (v : List ℕ), (∀ t ∈ v, t < 18) → ∀ {p : ℕ}, p < 3240 → ∀ x : Fin 306936, x.val = FP p →
      ((wordG g v) • x).val = FP (compL (v.map NT) p) ∧ compL (v.map NT) p < 3240
  | [], _, p, hp, x, hx => ⟨by simpa [wordG, compL] using hx, hp⟩
  | t :: v, hv, p, hp, x, hx => by
    obtain ⟨e1, e2⟩ := word_pt g hg hsig v (fun t' h => hv t' (List.mem_cons_of_mem _ h)) hp x hx
    obtain ⟨f1, f2⟩ := letter_pt g hg hsig (hv t List.mem_cons_self) e2 _ e1
    refine ⟨?_, f2⟩
    change ((g t * wordG g v) • x).val = _
    rw [mul_smul]
    exact f1

set_option exponentiation.threshold 4096 in
theorem reach0 (g : ℕ → G) (hg : ∀ k < 18, ∀ x : Fin 306936, ((g k) • x).val = LR (4 + k) x.val)
    (hsig : ∀ k < 18, SigF LR FP (NT k) (4 + k)) (hF : ∀ p < 3240, FP p < 306936)
    {Ns : List ℕ} (hNs : ∀ N ∈ Ns, ∃ k < 18, N = NT k) {r0 : ℕ} (hr0 : r0 < 3240)
    (c0 : Fin 306936) (hc0 : c0.val = FP r0) (h0 : reachK 12 Ns r0 8 = ones 3240) :
    ∀ p < 3240, ∃ h ∈ letH g, (h • c0).val = FP p := by
  have hv : ∀ N ∈ Ns, StagesValid 12 N := by
    intro N hN
    obtain ⟨k, hk, rfl⟩ := hNs N hN
    exact (hsig k hk).1
  have spec := (reachK_spec hv (by omega : r0 < 2 ^ 12) 8).2
    (fun p => p < 3240 → ∃ h ∈ letH g, (h • c0).val = FP p)
    (fun _ => ⟨1, Subgroup.one_mem _, by rw [one_smul, hc0]⟩) ?_
  · intro p hp
    refine spec p ?_ hp
    rw [h0, ones_eq, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
    exact hp
  · intro p _ N hN hC hp
    obtain ⟨k, hk, rfl⟩ := hNs N hN
    have hq := ((hsig k hk).2 p hp).1
    obtain ⟨h, hH, he⟩ := hC hq
    obtain ⟨f1, -⟩ := letter_pt g hg hsig hk hp (pt hF hp) rfl
    refine ⟨(g k)⁻¹ * h, Subgroup.mul_mem _ (Subgroup.inv_mem _ (g_mem_letH g hk)) hH, ?_⟩
    have e : h • c0 = g k • pt hF hp := Fin.ext (he.trans f1.symm)
    rw [mul_smul, e, inv_smul_smul]
    rfl

theorem reach1_step (g : ℕ → G)
    (hg : ∀ k < 18, ∀ x : Fin 306936, ((g k) • x).val = LR (4 + k) x.val)
    (hsig : ∀ k < 18, SigF LR FP (NT k) (4 + k)) (hF : ∀ p < 3240, FP p < 306936)
    {v : List ℕ} (hv : ∀ t ∈ v, t < 18) {HN r0 : ℕ} (hr0 : r0 < 3240) (c0 c1 : Fin 306936)
    (hc0 : c0.val = FP r0) (hw : hOK (v.map NT) HN r0 = true) {q : ℕ} (hq4 : q < 2 ^ 12)
    (hC : benesPerm 12 HN q < 3240 → ∃ h ∈ letH g, h • c0 = c0 ∧ (h • c1).val = FP (benesPerm 12 HN q))
    (hq : q < 3240) : ∃ h ∈ letH g, h • c0 = c0 ∧ (h • c1).val = FP q := by
  obtain ⟨-, -, hcomp, hfix⟩ := hOK_spec (by omega) hw
  obtain ⟨e1, e2⟩ := word_pt g hg hsig v hv hq (pt hF hq) rfl
  rw [← hcomp q (by omega)] at e1 e2
  obtain ⟨h, hH, h0, h1⟩ := hC e2
  obtain ⟨f1, -⟩ := word_pt g hg hsig v hv hr0 c0 hc0
  rw [← hcomp r0 (by omega), hfix, ← hc0] at f1
  have hw0 : wordG g v • c0 = c0 := Fin.ext f1
  refine ⟨(wordG g v)⁻¹ * h, Subgroup.mul_mem _ (Subgroup.inv_mem _ (wordG_mem g hv)) hH, ?_, ?_⟩
  · rw [mul_smul, h0, inv_smul_eq_iff, hw0]
  · have e : h • c1 = wordG g v • pt hF hq := Fin.ext (h1.trans e1.symm)
    rw [mul_smul, e, inv_smul_smul]
    rfl

theorem reach1 (g : ℕ → G) (hg : ∀ k < 18, ∀ x : Fin 306936, ((g k) • x).val = LR (4 + k) x.val)
    (hsig : ∀ k < 18, SigF LR FP (NT k) (4 + k)) (hF : ∀ p < 3240, FP p < 306936)
    {v0 v1 : List ℕ} (hv0 : ∀ t ∈ v0, t < 18) (hv1 : ∀ t ∈ v1, t < 18) {HN0 HN1 r0 r1 : ℕ}
    (hr0 : r0 < 3240) (hr1 : r1 < 3240) (c0 c1 : Fin 306936) (hc0 : c0.val = FP r0)
    (hc1 : c1.val = FP r1) (hw0 : hOK (v0.map NT) HN0 r0 = true)
    (hw1 : hOK (v1.map NT) HN1 r0 = true) (R : ℕ) :
    ∀ q, (reachK 12 [HN0, HN1] r1 R).testBit q = true → q < 3240 →
      ∃ h ∈ letH g, h • c0 = c0 ∧ (h • c1).val = FP q := by
  have hv : ∀ N ∈ [HN0, HN1], StagesValid 12 N := by
    intro N hN
    rcases List.mem_pair.1 hN with rfl | rfl
    · exact (hOK_spec (by omega) hw0).1
    · exact (hOK_spec (by omega) hw1).1
  refine (reachK_spec hv (by omega : r1 < 2 ^ 12) R).2
    (fun q => q < 3240 → ∃ h ∈ letH g, h • c0 = c0 ∧ (h • c1).val = FP q)
    (fun _ => ⟨1, Subgroup.one_mem _, one_smul _ _, by rw [one_smul, hc1]⟩) ?_
  intro q hq4 N hN hC
  rcases List.mem_pair.1 hN with rfl | rfl
  · exact reach1_step g hg hsig hF hv0 hr0 c0 c1 hc0 hw0 hq4 hC
  · exact reach1_step g hg hsig hF hv1 hr0 c0 c1 hc0 hw1 hq4 hC

theorem fp_inj {FP : ℕ → ℕ} (hmono : ∀ p q, p < q → q < 3240 → FP p < FP q) {p q : ℕ}
    (hp : p < 3240) (hq : q < 3240) (h : FP p = FP q) : p = q := by
  rcases lt_trichotomy p q with h' | h' | h'
  · exact absurd h (hmono p q h' hq).ne
  · exact h'
  · exact absurd h (hmono q p h' hp).ne'

theorem card_orbit_ge (g : ℕ → G) (hmono : ∀ p q, p < q → q < 3240 → FP p < FP q)
    (c0 c1 : Fin 306936) (P0 Q1 : Finset ℕ)
    (hA : ∀ p ∈ P0, p < 3240 ∧ ∃ h ∈ letH g, (h • c0).val = FP p)
    (hQ1 : ∀ q ∈ Q1, q < 3240 ∧ ∃ h ∈ letH g, h • c0 = c0 ∧ (h • c1).val = FP q) :
    P0.card * Q1.card ≤ Nat.card (MulAction.orbit (letH g) ((c0, c1) : Fin 306936 × Fin 306936)) := by
  have hA' : ∀ p : ℕ, ∃ h : G, p ∈ P0 → h ∈ letH g ∧ (h • c0).val = FP p := by
    intro p
    by_cases hp : p ∈ P0
    · obtain ⟨-, h, hH, he⟩ := hA p hp
      exact ⟨h, fun _ => ⟨hH, he⟩⟩
    · exact ⟨1, fun h => absurd h hp⟩
  have hB' : ∀ q : ℕ, ∃ k : G, q ∈ Q1 → k ∈ letH g ∧ k • c0 = c0 ∧ (k • c1).val = FP q := by
    intro q
    by_cases hq : q ∈ Q1
    · obtain ⟨-, k, hK, h0, h1⟩ := hQ1 q hq
      exact ⟨k, fun _ => ⟨hK, h0, h1⟩⟩
    · exact ⟨1, fun h => absurd h hq⟩
  choose a ha using hA'
  choose b hb using hB'
  have hφ1 : ∀ pq ∈ P0 ×ˢ Q1, (((a pq.1 * b pq.2) • (c0, c1) : Fin 306936 × Fin 306936)).1.val =
      FP pq.1 := by
    intro pq hpq
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hpq
    rw [Prod.smul_fst, mul_smul, (hb pq.2 h2).2.1, (ha pq.1 h1).2]
  have hinj : Set.InjOn (fun pq : ℕ × ℕ => ((a pq.1 * b pq.2) • (c0, c1) :
      Fin 306936 × Fin 306936)) ↑(P0 ×ˢ Q1) := by
    intro x hx y hy hxy
    simp only at hxy
    have hx' := Finset.mem_product.1 hx
    have hy' := Finset.mem_product.1 hy
    have e1 : x.1 = y.1 := fp_inj hmono (hA _ hx'.1).1 (hA _ hy'.1).1
      (by rw [← hφ1 x hx, ← hφ1 y hy, hxy])
    have e2 := congrArg Prod.snd hxy
    simp only [Prod.smul_snd, mul_smul, e1, smul_left_cancel_iff] at e2
    have e3 := congrArg Fin.val e2
    rw [(hb x.2 hx'.2).2.2, (hb y.2 hy'.2).2.2] at e3
    exact Prod.ext e1 (fp_inj hmono (hQ1 _ hx'.2).1 (hQ1 _ hy'.2).1 e3)
  have hsub : (↑((P0 ×ˢ Q1).image (fun pq : ℕ × ℕ => ((a pq.1 * b pq.2) • (c0, c1) :
      Fin 306936 × Fin 306936))) : Set (Fin 306936 × Fin 306936)) ⊆
      MulAction.orbit (letH g) ((c0, c1) : Fin 306936 × Fin 306936) := by
    intro y hy
    obtain ⟨pq, hpq, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hpq
    have hmem : a pq.1 * b pq.2 ∈ letH g := Subgroup.mul_mem _ (ha pq.1 h1).1 (hb pq.2 h2).1
    exact MulAction.mem_orbit_iff.2 ⟨⟨_, hmem⟩, rfl⟩
  have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, Finset.card_image_of_injOn hinj, Finset.card_product] at hcard
  rw [Nat.card_coe_set_eq]
  exact hcard

theorem sig_surj {N : ℕ} (hv : StagesValid 12 N) (hmap : ∀ p < 3240, benesPerm 12 N p < 3240)
    {q : ℕ} (hq : q < 3240) : ∃ p < 3240, benesPerm 12 N p = q := by
  obtain ⟨p, hp, e⟩ := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range 3240)
    (t := Finset.range 3240) (fun p _ => benesPerm 12 N p)
    (fun p hp => Finset.mem_range.2 (hmap p (Finset.mem_range.1 hp)))
    (fun a b _ _ h => by rw [← benesInv_benesPerm hv a, h, benesInv_benesPerm hv b])
    le_rfl q (Finset.mem_range.2 hq)
  exact ⟨p, Finset.mem_range.1 hp, e.symm⟩

@[expose] def pairSet (FP : ℕ → ℕ) (M : ℕ) : Set (Fin 306936 × Fin 306936) :=
  {z | ∃ i < 3240, ∃ j < 3240, z.1.val = FP i ∧ z.2.val = FP j ∧ M.testBit (4096 * i + j) = true}

theorem mapsTo_inv_of_mapsTo {h : G} {T : Set (Fin 306936 × Fin 306936)}
    (hT : Set.MapsTo (fun z => h • z) T T) : Set.MapsTo (fun z => h⁻¹ • z) T T := by
  have hb := (Set.Finite.injOn_iff_bijOn_of_mapsTo (Set.toFinite T) hT).1
    (fun x _ y _ e => smul_left_cancel h e)
  intro z hz
  obtain ⟨w, hw, rfl⟩ := hb.surjOn hz
  change h⁻¹ • h • w ∈ T
  rw [inv_smul_smul]
  exact hw

theorem not_image (g : ℕ → G)
    (hg : ∀ k < 18, ∀ x : Fin 306936, ((g k) • x).val = LR (4 + k) x.val) {M r0 r1 : ℕ}
    (hclo : ∀ k < 18, closedOK (NT k) M = true) (hsig : ∀ k < 18, SigF LR FP (NT k) (4 + k))
    (hpts : fOK FP = true) (hreg : regionOK M r0 r1 = true) (c0 c1 : Fin 306936)
    (hc0 : c0.val = FP r0) (hc1 : c1.val = FP r1) {u iu v iv : ℕ}
    (hout : outOK FP M u iu v iv = true) {h : G} (hh : h ∈ letH g) :
    ¬((h • c0).val = u ∧ (h • c1).val = v) := by
  obtain ⟨hF, hmono⟩ := fOK_spec hpts
  obtain ⟨hr0, hr1, hbit, -⟩ := regionOK_spec hreg
  have hinv : ∀ k < 18, Set.MapsTo (fun z => (g k)⁻¹ • z) (pairSet FP M) (pairSet FP M) := by
    intro k hk z hz
    obtain ⟨i, hi, j, hj, e1, e2, hb⟩ := hz
    obtain ⟨hv, hs⟩ := hsig k hk
    obtain ⟨i', hi', ei⟩ := sig_surj hv (fun p hp => (hs p hp).1) hi
    obtain ⟨j', hj', ej⟩ := sig_surj hv (fun p hp => (hs p hp).1) hj
    have f1 := (letter_pt g hg hsig hk hi' (pt hF hi') rfl).1
    have f2 := (letter_pt g hg hsig hk hj' (pt hF hj') rfl).1
    rw [ei] at f1
    rw [ej] at f2
    have z1 : z.1 = g k • pt hF hi' := Fin.ext (e1.trans f1.symm)
    have z2 : z.2 = g k • pt hF hj' := Fin.ext (e2.trans f2.symm)
    refine ⟨i', hi', j', hj', ?_, ?_, ?_⟩
    · change ((g k)⁻¹ • z.1).val = _
      rw [z1, inv_smul_smul]
      rfl
    · change ((g k)⁻¹ • z.2).val = _
      rw [z2, inv_smul_smul]
      rfl
    · refine closedOK_spec (hclo k hk) i' (by omega) j' (by omega) ?_
      rw [ei, ej]
      exact hb
  have hall : ∀ x ∈ letH g, Set.MapsTo (fun z => x • z) (pairSet FP M) (pairSet FP M) ∧
      Set.MapsTo (fun z => x⁻¹ • z) (pairSet FP M) (pairSet FP M) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨⟨k, hk⟩, rfl⟩ := hx
      have h1 := hinv k hk
      refine ⟨?_, h1⟩
      have h2 := mapsTo_inv_of_mapsTo h1
      simpa only [inv_inv] using h2
    | one => exact ⟨fun z hz => by simpa using hz, fun z hz => by simpa using hz⟩
    | mul x y _ _ hx hy =>
      refine ⟨fun z hz => ?_, fun z hz => ?_⟩
      · change (x * y) • z ∈ _
        rw [mul_smul]
        exact hx.1 (hy.1 hz)
      · change (x * y)⁻¹ • z ∈ _
        rw [mul_inv_rev, mul_smul]
        exact hy.2 (hx.2 hz)
    | inv x _ hx =>
      refine ⟨hx.2, ?_⟩
      simpa only [inv_inv] using hx.1
  rintro ⟨eu, ev⟩
  have h0 : ((c0, c1) : Fin 306936 × Fin 306936) ∈ pairSet FP M := ⟨r0, hr0, r1, hr1, hc0, hc1, hbit⟩
  obtain ⟨i, hi, j, hj, e1, e2, hb⟩ := (hall h hh).1 h0
  change (h • c0).val = FP i at e1
  change (h • c1).val = FP j at e2
  obtain ⟨lu, lv, hno⟩ := outOK_spec hout
  have hiu : iu = i := by
    rcases lu with ⟨hl, hfu⟩ | ⟨-, hab⟩
    · exact fp_inj hmono hl hi (hfu.trans (eu.symm.trans e1))
    · exact absurd (eu.symm.trans e1).symm (hab i hi)
  have hiv : iv = j := by
    rcases lv with ⟨hl, hfv⟩ | ⟨-, hab⟩
    · exact fp_inj hmono hl hj (hfv.trans (ev.symm.trans e2))
    · exact absurd (ev.symm.trans e2).symm (hab j hj)
  subst hiu hiv
  rw [hno hi hj] at hb
  exact absurd hb (by decide)

set_option exponentiation.threshold 4096 in
theorem pair_facts (g : ℕ → G)
    (hg : ∀ k < 18, ∀ x : Fin 306936, ((g k) • x).val = LR (4 + k) x.val) {M r0 r1 HN0 HN1 : ℕ}
    {Ns v0 v1 : List ℕ} (hclo : ∀ k < 18, closedOK (NT k) M = true)
    (hsig : ∀ k < 18, SigF LR FP (NT k) (4 + k)) (hpts : fOK FP = true)
    (hreg : regionOK M r0 r1 = true) (hNs : ∀ N ∈ Ns, ∃ k < 18, N = NT k)
    (h0 : reachK 12 Ns r0 8 = ones 3240) (hv0 : ∀ t ∈ v0, t < 18) (hv1 : ∀ t ∈ v1, t < 18)
    (hw0 : hOK (v0.map NT) HN0 r0 = true) (hw1 : hOK (v1.map NT) HN1 r0 = true)
    (h1 : CFSG.KC.YModel.popc 12 (Nat.land (reachK 12 [HN0, HN1] r1 64) (ones 3240)) = 1080)
    (c0 c1 : Fin 306936) (hc0 : c0.val = FP r0) (hc1 : c1.val = FP r1) :
    3499200 ≤ Nat.card (MulAction.orbit (letH g) ((c0, c1) : Fin 306936 × Fin 306936)) ∧
      ∀ {u iu v iv : ℕ}, outOK FP M u iu v iv = true → ∀ h ∈ letH g,
        ¬((h • c0).val = u ∧ (h • c1).val = v) := by
  obtain ⟨hF, hmono⟩ := fOK_spec hpts
  obtain ⟨hr0, hr1, -, -⟩ := regionOK_spec hreg
  refine ⟨?_, fun hout h hh => not_image g hg hclo hsig hpts hreg c0 c1 hc0 hc1 hout hh⟩
  have hA := reach0 g hg hsig hF hNs hr0 c0 hc0 h0
  have hB := reach1 g hg hsig hF hv0 hv1 hr0 hr1 c0 c1 hc0 hc1 hw0 hw1 64
  set Y := Nat.land (reachK 12 [HN0, HN1] r1 64) (ones 3240) with hYd
  have hbit : ∀ q, Y.testBit q = true ↔ (reachK 12 [HN0, HN1] r1 64).testBit q = true ∧ q < 3240 := by
    intro q
    rw [hYd, nland, Nat.testBit_and, ones_eq, Nat.testBit_two_pow_sub_one, Bool.and_eq_true,
      decide_eq_true_eq]
  have hY : Y < 2 ^ 2 ^ 12 := by
    rw [hYd, nland]
    refine Nat.and_lt_two_pow _ ?_
    rw [ones_eq]
    exact lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)
      (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  let Q1 := (Finset.range (2 ^ 12)).filter fun q => Y.testBit q = true
  have hQ1 : Q1.card = 1080 := by
    rw [← h1, CFSG.KC.YModel.Sch.popc_eq 12 Y hY, Finset.card_filter]
    refine Finset.sum_congr rfl fun r _ => ?_
    cases Y.testBit r <;> rfl
  have hc := card_orbit_ge g hmono c0 c1 (Finset.range 3240) Q1
    (fun p hp => ⟨Finset.mem_range.1 hp, hA p (Finset.mem_range.1 hp)⟩)
    (fun q hq => by
      obtain ⟨hr, hq3⟩ := (hbit q).1 (Finset.mem_filter.1 hq).2
      exact ⟨hq3, hB q hr hq3⟩)
  rw [Finset.card_range, hQ1] at hc
  exact hc

end Group

end CFSG.KC.Fi24Pair

end
