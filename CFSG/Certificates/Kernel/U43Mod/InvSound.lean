
module

public import Certificates.Data.Kernel.U43Mod.InvDefs
public import CFSG.Certificates.Kernel.U43Mod.KTreeSound
public import CFSG.Certificates.Kernel.U43Mod.InvBridge

public section

namespace CFSG.KS.U43Inv

open CFSG.KC.Enum CFSG.KC.U43Inv CFSG.KS CFSG.KS.U43Mod CFSG.LieType.Multipliers.U43
  CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv CFSG.KS.U43Mod.LieOdd

theorem bIf_f {e t : Bool} : Bool.rec (motive := fun _ => Bool) e t false = e := rfl

theorem lwalk_cons {α : Type} (f : ℕ → α → Bool) (n : ℕ) (x : α) (L : List α) (i : ℕ) :
    lwalk f n (x :: L) i = bAnd(f i x, lwalk f n L (Nat.succ i)) := by
  change strictB i (fun i => bAnd(f i x, lwalk f n L (Nat.succ i))) = _
  rw [strictB_eq]

theorem lwalk_spec' {α : Type} [Inhabited α] {f : ℕ → α → Bool} {n : ℕ} :
    ∀ (L : List α) (i0 : ℕ), lwalk f n L i0 = true →
      i0 + L.length = n ∧ ∀ i < L.length, f (i0 + i) L[i]! = true
  | [], i0, h => by
    have h' : Nat.beq i0 n = true := h
    exact ⟨by simpa using beq_iff.1 h', fun i hi => absurd hi (by simp)⟩
  | x :: L, i0, h => by
    rw [lwalk_cons, bAnd_iff] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨e, h3⟩ := lwalk_spec' L _ h2
    refine ⟨by simp only [List.length_cons]; omega, fun i hi => ?_⟩
    cases i with
    | zero => simpa using h1
    | succ i =>
      have h4 := h3 i (by simpa using hi)
      have e2 : Nat.succ i0 + i = i0 + (i + 1) := by omega
      rw [e2] at h4
      simpa using h4

theorem lwalk_spec {α : Type} [Inhabited α] {f : ℕ → α → Bool} {n : ℕ} {L : List α}
    (h : lwalk f n L 0 = true) : L.length = n ∧ ∀ i < n, f i L[i]! = true := by
  obtain ⟨e, h'⟩ := lwalk_spec' L 0 h
  rw [Nat.zero_add] at e
  refine ⟨e, fun i hi => ?_⟩
  have := h' i (by omega)
  rwa [Nat.zero_add] at this

theorem fldsAre_spec {R : ℕ → ℕ} {fa : ℕ → ℕ} {n : ℕ} {A : Array ℕ}
    (h : fldsAre R fa n A.toList = true) : ∀ k < n, A[k]! = fa (R k) := by
  intro k hk
  have := (lwalk_spec h).2 k hk
  rw [Array.getElem!_toList] at this
  exact (beq_iff.1 this).symm

theorem oOrd_inj {κ O : ℕ → ℕ} {n : ℕ} (hn : 2 ≤ n) (h : oOrd κ n O = true) :
    ∀ i < n, ∀ j < n, κ i = κ j → i = j := by
  have hA : ∀ i < n - 1, O i < n ∧ O (i + 1) < n ∧ κ (O i) < κ (O (i + 1)) := by
    intro i hi
    have h1 := allN_spec h i hi
    simp only [bAnd_iff, blt_iff] at h1
    exact h1
  have hlt : ∀ a < n, O a < n := by
    intro a ha
    rcases Nat.lt_or_ge a (n - 1) with h1 | h1
    · exact (hA a h1).1
    · have e : a = (n - 2) + 1 := by omega
      rw [e]
      exact (hA (n - 2) (by omega)).2.1
  have hmono : ∀ b, b < n → ∀ a < b, κ (O a) < κ (O b) := by
    intro b
    induction b with
    | zero => intro _ a ha; omega
    | succ b ih =>
      intro hb a ha
      have h1 := (hA b (by omega)).2.2
      rcases Nat.lt_succ_iff_lt_or_eq.1 ha with h2 | rfl
      · exact (ih (by omega) a h2).trans h1
      · exact h1
  have hinj : ∀ a < n, ∀ b < n, κ (O a) = κ (O b) → a = b := by
    intro a ha b hb e
    rcases lt_trichotomy a b with h1 | h1 | h1
    · exact absurd e (ne_of_lt (hmono b hb a h1))
    · exact h1
    · exact absurd e (ne_of_gt (hmono a ha b h1))
  let f : Fin n → Fin n := fun a => ⟨O a, hlt a a.2⟩
  have hf : Function.Injective f := fun a b e =>
    Fin.ext (hinj a a.2 b b.2 (by rw [show O a = O b from congrArg Fin.val e]))
  have hs := Finite.injective_iff_surjective.1 hf
  intro i hi j hj e
  obtain ⟨a, ha⟩ := hs ⟨i, hi⟩
  obtain ⟨b, hb⟩ := hs ⟨j, hj⟩
  have ha' : O a = i := congrArg Fin.val ha
  have hb' : O b = j := congrArg Fin.val hb
  rw [← ha', ← hb'] at e ⊢
  rw [hinj a a.2 b b.2 e]

@[expose] def KeyOf (r : ℕ) (g : X₀) : Prop :=
  kf r 0 = (psi g ⟨0, by norm_num⟩ : ℕ) ∧ kf r 1 = (psi g ⟨1, by norm_num⟩ : ℕ) ∧
    kf r 2 = (psi g ⟨9, by norm_num⟩ : ℕ)

@[expose] noncomputable def sF (gs : List X₀) (l : ℕ) : X₀ :=
  if l % 2 = 0 then gs.getD (l / 2) 1 else (gs.getD (l / 2) 1)⁻¹

theorem mulStepG_eq (gs : List X₀) (g : X₀) (l : ℕ) : mulStepG gs g l = g * sF gs l := by
  unfold mulStepG sF
  split_ifs <;> rfl

theorem kRecOK_zero {R : ℕ → ℕ} {n nl : ℕ} {Gk : ℕ → ℕ → ℕ} (h : kRecOK R n nl Gk 0 = true) :
    kdep (R 0) = 0 ∧ kf (R 0) 0 = 0 ∧ kf (R 0) 1 = 1 ∧ kf (R 0) 2 = 9 := by
  unfold kRecOK at h
  rw [strictB_eq] at h
  have h' : bAnd(Nat.beq (kdep (R 0)) 0, bAnd(Nat.beq (kf (R 0) 0) 0,
      bAnd(Nat.beq (kf (R 0) 1) 1, Nat.beq (kf (R 0) 2) 9))) = true := h
  simp only [bAnd_iff, beq_iff] at h'
  exact h'

theorem kRecOK_succ {R : ℕ → ℕ} {n nl : ℕ} {Gk : ℕ → ℕ → ℕ} {k : ℕ} (hk : k ≠ 0)
    (h : kRecOK R n nl Gk k = true) :
    kpar (R k) < n ∧ klab (R k) < nl ∧ kdep (R (kpar (R k))) < kdep (R k) ∧ kdep (R k) < 33 ∧
      keys3 (Gk (klab (R k))) (R (kpar (R k))) (R k) = true := by
  unfold kRecOK at h
  simp only [strictB_eq, beq_false hk, bIf_f, bAnd_iff, blt_iff] at h
  exact h

theorem keys3_spec {G : ℕ → ℕ} {r r' : ℕ} (h : keys3 G r r' = true) :
    kf r' 0 = G (kf r 0) ∧ kf r' 1 = G (kf r 1) ∧ kf r' 2 = G (kf r 2) := by
  unfold keys3 at h
  simp only [bAnd_iff, beq_iff] at h
  exact h

theorem eW_succ (R : ℕ → ℕ) (Gr : ℕ → ℕ → ℕ) (f k q : ℕ) : eW R Gr (f + 1) k q =
    Bool.rec (motive := fun _ => ℕ) (eW R Gr f (kpar (R k)) (Gr (klab (R k)) q)) q
      (Nat.beq (kdep (R k)) 0) := by
  have e : eW R Gr (f + 1) k q = strictN (R k) (fun r => nIf(Nat.beq (kdep r) (nat_lit 0), q,
      eW R Gr f (kpar r) (Gr (klab r) q))) := rfl
  rw [e, strictN_eq]

theorem eWi_succ (R : ℕ → ℕ) (Gk : ℕ → ℕ → ℕ) (f k q : ℕ) : eWi R Gk (f + 1) k q =
    Bool.rec (motive := fun _ => ℕ) (Gk (klab (R k)) (eWi R Gk f (kpar (R k)) q)) q
      (Nat.beq (kdep (R k)) 0) := by
  have e : eWi R Gk (f + 1) k q = strictN (R k) (fun r => nIf(Nat.beq (kdep r) (nat_lit 0), q,
      Gk (klab r) (eWi R Gk f (kpar r) q))) := rfl
  rw [e, strictN_eq]

@[expose] def WalkOf (R : ℕ → ℕ) (Gr Gk : ℕ → ℕ → ℕ) (k : ℕ) (g : X₀) : Prop :=
  ∀ f, kdep (R k) ≤ f → ∀ q (hq : q < 820), eW R Gr f k q = (psi g ⟨q, hq⟩ : ℕ) ∧
    eWi R Gk f k q = (psi g⁻¹ ⟨q, hq⟩ : ℕ)

theorem key_tree {R : ℕ → ℕ} {n nl : ℕ} {Gk Gr : ℕ → ℕ → ℕ} {gs : List X₀} {par lab : Array ℕ}
    (hG : ∀ l < nl, ∀ q (hq : q < 820), Gk l q = (psi (sF gs l)⁻¹ ⟨q, hq⟩ : ℕ) ∧
      Gr l q = (psi (sF gs l) ⟨q, hq⟩ : ℕ))
    (hn : 0 < n) (hT : kTree R n nl Gk = true) (hP : ∀ k < n, par[k]! = kpar (R k))
    (hL : ∀ k < n, lab[k]! = klab (R k)) :
    ∀ k < n, KeyOf (R k) (treeG 1 (mulStepG gs) par lab nl fuel k)⁻¹ ∧
      WalkOf R Gr Gk k (treeG 1 (mulStepG gs) par lab nl fuel k) := by
  have hR : ∀ k < n, kRecOK R n nl Gk k = true := allN_spec hT
  obtain ⟨hd0, k0, k1, k2⟩ := kRecOK_zero (hR 0 hn)
  have h0 : KeyOf (R 0) (1 : X₀)⁻¹ ∧ WalkOf R Gr Gk 0 1 := by
    refine ⟨⟨by rw [k0]; simp, by rw [k1]; simp, by rw [k2]; simp⟩, fun f _ q hq => ?_⟩
    cases f with
    | zero => exact ⟨by rw [map_one]; rfl, by rw [inv_one, map_one]; rfl⟩
    | succ f =>
      rw [eW_succ, eWi_succ, hd0]
      exact ⟨by rw [map_one]; rfl, by rw [inv_one, map_one]; rfl⟩
  have hs : ∀ k < n, k ≠ 0 → par[k]! < n ∧ kdep (R par[k]!) < kdep (R k) ∧
      ∀ g, (KeyOf (R par[k]!) g⁻¹ ∧ WalkOf R Gr Gk par[k]! g) →
        KeyOf (R k) (mulStepG gs g (lab[k]! % nl))⁻¹ ∧
          WalkOf R Gr Gk k (mulStepG gs g (lab[k]! % nl)) := by
    intro k hk hk0
    obtain ⟨hp, hl, hdp, -, hks⟩ := kRecOK_succ hk0 (hR k hk)
    rw [hP k hk, hL k hk, Nat.mod_eq_of_lt hl]
    refine ⟨hp, hdp, fun g ⟨⟨g0, g1, g9⟩, hw⟩ => ?_⟩
    rw [mulStepG_eq]
    obtain ⟨e0, e1, e2⟩ := keys3_spec hks
    have hGk : ∀ (x : Fin 820), Gk (klab (R k)) x = (psi (sF gs (klab (R k)))⁻¹ x : ℕ) :=
      fun x => (hG _ hl x x.2).1
    have hmul : ∀ x : Fin 820, (psi (g * sF gs (klab (R k)))⁻¹ x : ℕ) =
        (psi (sF gs (klab (R k)))⁻¹ (psi g⁻¹ x) : ℕ) := fun x => by
      rw [mul_inv_rev, map_mul, Equiv.Perm.mul_apply]
    refine ⟨⟨by rw [e0, g0, hGk, hmul], by rw [e1, g1, hGk, hmul], by rw [e2, g9, hGk, hmul]⟩,
      fun f hf q hq => ?_⟩
    cases f with
    | zero => omega
    | succ f =>
      have hd : kdep (R k) ≠ 0 := by omega
      rw [eW_succ, eWi_succ, beq_false hd]
      dsimp only
      have hq' : (psi (sF gs (klab (R k))) ⟨q, hq⟩ : ℕ) < 820 := Fin.is_lt _
      obtain ⟨w1, -⟩ := hw f (by omega) _ hq'
      obtain ⟨-, w2⟩ := hw f (by omega) q hq
      refine ⟨?_, ?_⟩
      · rw [(hG _ hl q hq).2, w1, Fin.eta, map_mul, Equiv.Perm.mul_apply]
      · rw [w2, hGk, ← hmul]
  intro k hk
  refine treeG_induction_of_depth (Q := fun k g => KeyOf (R k) g⁻¹ ∧ WalkOf R Gr Gk k g)
    (dep := fun k => kdep (R k)) h0 hs fuel k hk ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · change kdep (R 0) ≤ 32
    omega
  · have := (kRecOK_succ (by omega) (hR k hk)).2.2.2.1
    change kdep (R k) ≤ 32
    omega

theorem key_clos {R : ℕ → ℕ} {n nl : ℕ} {Gk : ℕ → ℕ → ℕ} {e s : ℕ → X₀} {tbl : Array ℕ}
    (hnl : 0 < nl) (hK : ∀ k < n, KeyOf (R k) (e k)⁻¹)
    (hG : ∀ l < nl, ∀ q (hq : q < 820), Gk l q = (psi (s l)⁻¹ ⟨q, hq⟩ : ℕ))
    (hsep : ∀ g h : X₀, (psi g ⟨0, by norm_num⟩ : ℕ) = psi h ⟨0, by norm_num⟩ →
      (psi g ⟨1, by norm_num⟩ : ℕ) = psi h ⟨1, by norm_num⟩ →
      (psi g ⟨9, by norm_num⟩ : ℕ) = psi h ⟨9, by norm_num⟩ → g = h)
    (hC : kClos R n nl Gk tbl.toList = true) :
    ∀ k < n, ∀ l < nl, tbl[k * nl + l]! < n ∧ e tbl[k * nl + l]! = e k * s l := by
  intro k hk l hl
  have hi : k * nl + l < Nat.mul n nl := by
    change k * nl + l < n * nl
    nlinarith
  have h := (lwalk_spec hC).2 _ hi
  have h1 : Nat.div (k * nl + l) nl = k := by
    change (k * nl + l) / nl = k
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hnl, Nat.div_eq_of_lt hl, Nat.zero_add]
  have h2 : Nat.mod (k * nl + l) nl = l := by
    change (k * nl + l) % nl = l
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]
  rw [h1, h2, Array.getElem!_toList, bAnd_iff, blt_iff] at h
  obtain ⟨hx, hks⟩ := h
  refine ⟨hx, ?_⟩
  obtain ⟨e0, e1, e2⟩ := keys3_spec hks
  obtain ⟨k0, k1, k9⟩ := hK k hk
  obtain ⟨x0, x1, x9⟩ := hK _ hx
  have hmul : ∀ x : Fin 820, (psi (e k * s l)⁻¹ x : ℕ) = Gk l (psi (e k)⁻¹ x : ℕ) := fun x => by
    rw [hG l hl _ (Fin.is_lt _), mul_inv_rev, map_mul, Equiv.Perm.mul_apply]
  have := hsep (e tbl[k * nl + l]!)⁻¹ (e k * s l)⁻¹ (by rw [← x0, e0, k0, hmul])
    (by rw [← x1, e1, k1, hmul]) (by rw [← x9, e2, k9, hmul])
  exact inv_injective this

theorem kkey_eq {r r' : ℕ} (h0 : kf r 0 = kf r' 0) (h1 : kf r 1 = kf r' 1)
    (h2 : kf r 2 = kf r' 2) : kkey r = kkey r' := by
  have h := mod_eq_of_flds (a := r) (b := r') (w := 10) 3 fun t ht => by
    interval_cases t
    · exact h0
    · exact h1
    · exact h2
  change r &&& (2 ^ 30 - 1) = r' &&& (2 ^ 30 - 1)
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
  exact h

theorem key_inj {R O : ℕ → ℕ} {n : ℕ} {e : ℕ → X₀} (hn : 2 ≤ n)
    (hK : ∀ k < n, KeyOf (R k) (e k)⁻¹) (hO : kOrd R n O = true) :
    ∀ i < n, ∀ j < n, e i = e j → i = j := by
  intro i hi j hj he
  refine oOrd_inj hn hO i hi j hj ?_
  obtain ⟨a0, a1, a9⟩ := hK i hi
  obtain ⟨b0, b1, b9⟩ := hK j hj
  rw [he] at a0 a1 a9
  exact kkey_eq (a0.trans b0.symm) (a1.trans b1.symm) (a9.trans b9.symm)

theorem testBit_orM (f : ℕ → ℕ) : ∀ m q, (orM f m).testBit q = true ↔ ∃ t < m, f t = q
  | 0, q => by
    change (0 : ℕ).testBit q = true ↔ _
    simp
  | m + 1, q => by
    change (Nat.lor (Nat.shiftLeft 1 (f m)) (orM f m)).testBit q = true ↔ _
    have e : Nat.shiftLeft 1 (f m) = 2 ^ f m := by
      change 1 <<< f m = _
      rw [Nat.one_shiftLeft]
    rw [e]
    change (2 ^ f m ||| orM f m).testBit q = true ↔ _
    rw [Nat.testBit_lor, Bool.or_eq_true, testBit_orM f m q, Nat.testBit_two_pow,
      decide_eq_true_eq]
    constructor
    · rintro (h | ⟨t, ht, h⟩)
      · exact ⟨m, by omega, h⟩
      · exact ⟨t, by omega, h⟩
    · rintro ⟨t, ht, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
      · exact Or.inr ⟨t, ht, h⟩
      · exact Or.inl h

theorem testBit_iff_bt (m q : ℕ) : m.testBit q = true ↔ bt m q = 1 := by
  have e : bt m q = m / 2 ^ q % 2 := by
    change (m >>> q) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq, e]

theorem cf_lt (r t : ℕ) : cf r t < 1024 := by
  unfold cf
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem clab_lt (r : ℕ) : clab r < 4 := by
  unfold clab
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem cRecOK_zero {R : ℕ → ℕ} {n : ℕ} {Lp : ℕ → ℕ → ℕ} (h : cRecOK R n Lp 0 = true) :
    cdep (R 0) = 0 := by
  unfold cRecOK at h
  rw [strictB_eq] at h
  have h' : Nat.beq (cdep (R 0)) 0 = true := h
  exact beq_iff.1 h'

theorem cRecOK_succ {R : ℕ → ℕ} {n : ℕ} {Lp : ℕ → ℕ → ℕ} {k : ℕ} (hk : k ≠ 0)
    (h : cRecOK R n Lp k = true) :
    cpar (R k) < n ∧ cdep (R (cpar (R k))) < cdep (R k) ∧ cdep (R k) < 33 ∧
      orM (cf (R k)) 20 = orM (fun t => Lp (clab (R k)) (cf (R (cpar (R k))) t)) 20 := by
  unfold cRecOK at h
  simp only [strictB_eq, beq_false hk, bIf_f, bAnd_iff, blt_iff, beq_iff] at h
  exact h

theorem cFix_spec {R : ℕ → ℕ} {A : ℕ → ℕ} (h : cFix R A = true) :
    ∀ q < 1024, (bt (orM (cf (R 0)) 20) q = 1 ↔ q < 820 ∧ A q = q) := by
  intro q hq
  unfold cFix at h
  rw [strictB_eq] at h
  have h1 := allN_spec h q hq
  set m := orM (cf (R 0)) 20
  cases hb : Nat.blt q 820
  · rw [hb] at h1
    have h2 : Nat.beq (bt m q) 0 = true := h1
    have h3 := beq_iff.1 h2
    have : ¬ q < 820 := by rw [← blt_iff, hb]; simp
    constructor
    · intro e
      omega
    · rintro ⟨h4, -⟩
      exact absurd h4 this
  · rw [hb] at h1
    have h820 : q < 820 := blt_iff.1 hb
    cases hc : Nat.beq (A q) q
    · rw [hc] at h1
      have h2 : Nat.beq (bt m q) 0 = true := h1
      have h3 := beq_iff.1 h2
      have : A q ≠ q := fun e => by rw [beq_iff.2 e] at hc; exact Bool.noConfusion hc
      constructor
      · intro e
        omega
      · rintro ⟨-, h4⟩
        exact absurd h4 this
    · rw [hc] at h1
      have h2 : Nat.beq (bt m q) 1 = true := h1
      exact ⟨fun _ => ⟨h820, beq_iff.1 hc⟩, fun _ => beq_iff.1 h2⟩

theorem fix_tree {R : ℕ → ℕ} {n : ℕ} {Lp : ℕ → ℕ → ℕ} {A : ℕ → ℕ} {par lab : Array ℕ}
    (hLp : ∀ l < 4, ∀ q (hq : q < 820), Lp l q = (psi (letElt l) ⟨q, hq⟩ : ℕ))
    (hA : ∀ q (hq : q < 820), A q = (psi xElt ⟨q, hq⟩ : ℕ)) (hn : 0 < n)
    (hT : cTree R n Lp = true) (hF : cFix R A = true) (hP : ∀ k < n, par[k]! = cpar (R k))
    (hL : ∀ k < n, lab[k]! = clab (R k)) :
    ∀ k < n, ∀ q, (orM (cf (R k)) 20).testBit q = true ↔
      ∃ hq : q < 820, psi (treeG xElt conjStepG par lab 4 fuel k) ⟨q, hq⟩ = ⟨q, hq⟩ := by
  have hR : ∀ k < n, cRecOK R n Lp k = true := allN_spec hT
  have h0 : ∀ q, (orM (cf (R 0)) 20).testBit q = true ↔
      ∃ hq : q < 820, psi xElt ⟨q, hq⟩ = ⟨q, hq⟩ := by
    intro q
    by_cases hq : q < 1024
    · rw [testBit_iff_bt, cFix_spec hF q hq]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, Fin.ext (by rw [← hA q h1]; exact h2)⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [hA q h1, h2]⟩
    · rw [testBit_orM]
      constructor
      · rintro ⟨t, -, ht⟩
        have := cf_lt (R 0) t
        omega
      · rintro ⟨h1, -⟩
        omega
  have hs : ∀ k < n, k ≠ 0 → par[k]! < n ∧ cdep (R par[k]!) < cdep (R k) ∧
      ∀ g, (∀ q, (orM (cf (R par[k]!)) 20).testBit q = true ↔
          ∃ hq : q < 820, psi g ⟨q, hq⟩ = ⟨q, hq⟩) →
        ∀ q, (orM (cf (R k)) 20).testBit q = true ↔
          ∃ hq : q < 820, psi (conjStepG g (lab[k]! % 4)) ⟨q, hq⟩ = ⟨q, hq⟩ := by
    intro k hk hk0
    obtain ⟨hp, hdp, -, hm⟩ := cRecOK_succ hk0 (hR k hk)
    rw [hP k hk, hL k hk, Nat.mod_eq_of_lt (clab_lt _)]
    refine ⟨hp, hdp, fun g hg q => ?_⟩
    have hl := clab_lt (R k)
    unfold conjStepG
    rw [letElt_xor hl, hm, testBit_orM]
    constructor
    · rintro ⟨t, ht, hq⟩
      obtain ⟨hp1, hp2⟩ := (hg (cf (R (cpar (R k))) t)).1 ((testBit_orM _ _ _).2 ⟨t, ht, rfl⟩)
      rw [hLp _ hl _ hp1] at hq
      subst hq
      refine ⟨Fin.is_lt _, ?_⟩
      rw [Fin.eta, map_mul, map_mul, map_inv]
      simp [Equiv.Perm.mul_apply, hp2]
    · rintro ⟨hq, hfix⟩
      set lam := letElt (clab (R k))
      have hp2 : psi g (psi lam⁻¹ ⟨q, hq⟩) = psi lam⁻¹ ⟨q, hq⟩ := by
        have e := congrArg (psi lam⁻¹) hfix
        rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply,
          ← map_mul, inv_mul_cancel, map_one, Equiv.Perm.one_apply] at e
        exact e
      obtain ⟨t, ht, e⟩ := (testBit_orM _ _ _).1
        ((hg (psi lam⁻¹ ⟨q, hq⟩ : ℕ)).2 ⟨Fin.is_lt _, by rw [Fin.eta]; exact hp2⟩)
      refine ⟨t, ht, ?_⟩
      rw [e, hLp _ hl _ (Fin.is_lt _), Fin.eta, ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel,
        map_one, Equiv.Perm.one_apply]
  intro k hk
  refine treeG_induction_of_depth (Q := fun k g => ∀ q, (orM (cf (R k)) 20).testBit q = true ↔
      ∃ hq : q < 820, psi g ⟨q, hq⟩ = ⟨q, hq⟩)
    (dep := fun k => cdep (R k)) h0 hs fuel k hk ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · change cdep (R 0) ≤ 32
    have := cRecOK_zero (hR 0 hn)
    omega
  · have := (cRecOK_succ (by omega) (hR k hk)).2.2.1
    change cdep (R k) ≤ 32
    omega

theorem fix_inj {R O : ℕ → ℕ} {n : ℕ} {e : ℕ → X₀} (hn : 2 ≤ n)
    (hF : ∀ k < n, ∀ q, (orM (cf (R k)) 20).testBit q = true ↔
      ∃ hq : q < 820, psi (e k) ⟨q, hq⟩ = ⟨q, hq⟩) (hO : cOrd R n O = true) :
    ∀ i < n, ∀ j < n, e i = e j → i = j := by
  intro i hi j hj he
  refine oOrd_inj hn hO i hi j hj (Nat.eq_of_testBit_eq fun q => ?_)
  have h1 := hF i hi q
  have h2 := hF j hj q
  rw [he] at h1
  exact Bool.eq_iff_iff.2 (h1.trans h2.symm)

theorem wordElt_cons (l : ℕ) (w : List ℕ) : wordElt (l :: w) = letElt l * wordElt w := by
  have key : ∀ (w : List ℕ) (h : X₀), w.foldl (fun g l => g * letElt l) h =
      h * w.foldl (fun g l => g * letElt l) 1 := by
    intro w
    induction w with
    | nil => intro h; simp
    | cons l w ih =>
      intro h
      rw [List.foldl_cons, List.foldl_cons, ih (h * letElt l), ih (1 * letElt l)]
      group
  unfold wordElt
  rw [List.foldl_cons, key, one_mul]

theorem mwv_eq {Lp : ℕ → ℕ → ℕ}
    (hLp : ∀ l q (hq : q < 820), Lp l q = (psi (letElt l) ⟨q, hq⟩ : ℕ)) :
    ∀ (w : List ℕ) q (hq : q < 820), mwv Lp w q = (psi (wordElt w) ⟨q, hq⟩ : ℕ)
  | [], q, hq => by simp [mwv, wordElt]
  | l :: w, q, hq => by
    change Lp l (mwv Lp w q) = _
    rw [mwv_eq hLp w q hq, hLp l _ (Fin.is_lt _), Fin.eta, wordElt_cons, map_mul,
      Equiv.Perm.mul_apply]

theorem mwvI_eq {Lp : ℕ → ℕ → ℕ}
    (hLp : ∀ l q (hq : q < 820), Lp l q = (psi (letElt l) ⟨q, hq⟩ : ℕ)) :
    ∀ (w : List ℕ), (∀ l ∈ w, l < 4) → ∀ q (hq : q < 820),
      mwvI Lp w q = (psi (wordElt w)⁻¹ ⟨q, hq⟩ : ℕ)
  | [], _, q, hq => by simp [mwvI, wordElt]
  | l :: w, hw, q, hq => by
    change mwvI Lp w (Lp (l ^^^ 2) q) = _
    have hl := hw l List.mem_cons_self
    rw [hLp _ q hq, mwvI_eq hLp w (fun l' h' => hw l' (List.mem_cons_of_mem _ h')) _ (Fin.is_lt _),
      Fin.eta, wordElt_cons, mul_inv_rev, map_mul, Equiv.Perm.mul_apply, letElt_xor hl]

end CFSG.KS.U43Inv

end
