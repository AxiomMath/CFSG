module

public import Certificates.Data.Kernel.Fi22Syl2072
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.SetTheory.Cardinal.Finite
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KC.Syl2072

open CFSG.KC.Enum CFSG.KS

variable {N : ℕ}

@[expose] def onB (σ τ : Equiv.Perm (Fin N)) : Prop :=
  ∀ t < 6, ∀ h : bp t < N, σ ⟨bp t, h⟩ = τ ⟨bp t, h⟩

@[expose] noncomputable def elt (D : ℕ → ℕ) (o : ℕ) (g : ℕ → Equiv.Perm (Fin N)) :
    ℕ → ℕ → Equiv.Perm (Fin N)
  | 0, _ => 1
  | f + 1, i => g (f16 (D (o + i)) 1) * elt D o g f (f16 (D (o + i)) 0)

@[expose, irreducible] noncomputable def el (D : ℕ → ℕ) (o : ℕ) (g : ℕ → Equiv.Perm (Fin N)) (i : ℕ) :
    Equiv.Perm (Fin N) :=
  elt D o g (f16 (D (o + i)) 2) i

theorem s2072_bAnd {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem s2072_allBlk (b : ℕ) (f : ℕ → Bool) :
    ∀ len, allBlk b f len = true ↔ ∀ l < len, f (b + l) = true := by
  intro len
  induction len with
  | zero => exact iff_of_true rfl fun l hl => absurd hl (Nat.not_lt_zero l)
  | succ len ih =>
    change Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) = true ↔ _
    constructor
    · intro h l hl
      obtain ⟨h1, h2⟩ := s2072_bAnd h
      rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | rfl
      · exact (ih.mp h2) l hl
      · exact h1
    · intro h
      have h1 : f (Nat.add b len) = true := h len (Nat.lt_succ_self len)
      rw [h1]
      exact ih.mpr fun l hl => h l (Nat.lt_succ_of_lt hl)

theorem s2072_all6 (P : ℕ → Bool) : all6 P = true ↔ ∀ t < 6, P t = true := by
  have e : all6 P = Bool.rec (motive := fun _ => Bool) false true (allBlk 0 P 6) := rfl
  rw [e]
  have h := s2072_allBlk 0 P 6
  simp only [Nat.zero_add] at h
  rw [← h]
  cases allBlk 0 P 6 <;> simp

theorem s2072_bp_lt : ∀ t < 6, bp t < 7 := by
  intro t ht
  rcases t with _ | _ | _ | _ | _ | _ | t
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · omega

theorem s2072_strictN (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

theorem s2072_iter {F : ℕ → ℕ} {σ : Equiv.Perm (Fin N)} (hF : ∀ y : Fin N, F y = (σ y : ℕ))
    (k : ℕ) (y : ℕ) (hy : y < N) : iter F k y = ((σ ^ k) ⟨y, hy⟩ : ℕ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change strictN (iter F k y) F = _
    rw [s2072_strictN, ih, hF, pow_succ', Equiv.Perm.mul_apply]

theorem s2072_onB_of {F : ℕ → ℕ} {σ : Equiv.Perm (Fin N)} (hF : ∀ y : Fin N, F y = (σ y : ℕ))
    {k : ℕ} (h : all6 (fun t => Nat.beq (iter F k (bp t)) (bp t)) = true) : onB (σ ^ k) 1 := by
  intro t ht hb
  have h1 := Nat.eq_of_beq_eq_true ((s2072_all6 _).mp h t ht)
  have h2 := s2072_iter hF k (bp t) hb
  apply Fin.ext
  rw [Equiv.Perm.one_apply, ← h2]
  exact h1

theorem s2072_all6_of {F : ℕ → ℕ} {σ : Equiv.Perm (Fin N)} (hN : 7 ≤ N)
    (hF : ∀ y : Fin N, F y = (σ y : ℕ)) {k : ℕ} (h : onB (σ ^ k) 1) :
    all6 (fun t => Nat.beq (iter F k (bp t)) (bp t)) = true := by
  refine (s2072_all6 _).mpr fun t ht => ?_
  have hb : bp t < N := lt_of_lt_of_le (s2072_bp_lt t ht) hN
  rw [s2072_iter hF k (bp t) hb, h t ht hb, Equiv.Perm.one_apply]
  exact Nat.beq_refl _

theorem witK_sound {xq hq hiq p o : ℕ} {x h : Equiv.Perm (Fin N)} (hN : 7 ≤ N)
    (hw : witK xq hq hiq p o = true) (hx : ∀ y : Fin N, ap xq y = (x y : ℕ))
    (hh : ∀ y : Fin N, ap hq y = (h y : ℕ)) (hhi : ∀ y : Fin N, ap hiq y = (h⁻¹ y : ℕ)) :
    ¬ onB x 1 ∧ onB (x ^ p) 1 ∧ o % 2 = 0 ∧ onB ((x * h * x * h⁻¹) ^ o) 1 ∧
      ¬ onB ((x * h * x * h⁻¹) ^ (o / 2)) 1 := by
  unfold witK at hw
  obtain ⟨h1, hw⟩ := s2072_bAnd hw
  obtain ⟨h2, hw⟩ := s2072_bAnd hw
  obtain ⟨h3, hw⟩ := s2072_bAnd hw
  obtain ⟨h4, h5⟩ := s2072_bAnd hw
  have hy : ∀ z : Fin N, (fun z => ap xq (ap hq (ap xq (ap hiq z)))) z =
      ((x * h * x * h⁻¹) z : ℕ) := by
    intro z
    simp only [Equiv.Perm.mul_apply]
    rw [hhi, hx, hh, hx]
  refine ⟨fun hon => ?_, s2072_onB_of hx h2, Nat.eq_of_beq_eq_true h3,
    s2072_onB_of (F := fun z => ap xq (ap hq (ap xq (ap hiq z)))) hy h4, fun hon => ?_⟩
  · have hall : all6 (fun t => Nat.beq (ap xq (bp t)) (bp t)) = true := by
      refine (s2072_all6 _).mpr fun t ht => ?_
      have hb : bp t < N := lt_of_lt_of_le (s2072_bp_lt t ht) hN
      have e := hx ⟨bp t, hb⟩
      rw [hon t ht hb, Equiv.Perm.one_apply] at e
      change Nat.beq (ap xq (bp t)) (bp t) = true
      rw [e]
      exact Nat.beq_refl _
    rw [hall] at h1
    exact absurd h1 (by decide)
  · have hall := s2072_all6_of (F := fun z => ap xq (ap hq (ap xq (ap hiq z))))
      (k := Nat.div o 2) hN hy hon
    rw [hall] at h5
    exact absurd h5 (by decide)

theorem s2072_strictB (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem s2072_blt {a b : ℕ} (h : Nat.blt a b = true) : a < b := Nat.le_of_ble_eq_true h

theorem s2072_bim_eq (v t : ℕ) : bim v t = (v >>> (12 * t)) &&& (2 ^ 12 - 1) := rfl

theorem s2072_key_eq' (v : ℕ) : key v = (v >>> 0) &&& (2 ^ 72 - 1) := rfl

theorem s2072_key_eq {a b : ℕ} (h : ∀ t < 6, bim a t = bim b t) : key a = key b := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [s2072_key_eq', s2072_key_eq', Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight,
    Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Nat.zero_add]
  by_cases hk : k < 72
  · have e := congrArg (fun z => z.testBit (k % 12)) (h (k / 12) (by omega))
    simp only [s2072_bim_eq, Nat.testBit_and, Nat.testBit_shiftRight,
      Nat.testBit_two_pow_sub_one] at e
    have hm : k % 12 < 12 := Nat.mod_lt _ (by omega)
    rw [Nat.div_add_mod k 12, decide_eq_true hm, Bool.and_true, Bool.and_true] at e
    rw [e]
  · rw [decide_eq_false hk, Bool.and_false, Bool.and_false]

theorem s2072_elem {L D X : ℕ → ℕ} {s0 m o n p nw i : ℕ}
    (h : elemK L D X s0 m o n p nw i = true) :
    treeK L D s0 m o n (D (o + i)) = true ∧ nxtK L D s0 m o n (D (o + i)) = true ∧
    (i + 1 < n → key (D (o + i)) < key (D (o + (i + 1)))) ∧
    (all6 (fun t => Nat.beq (iter (act L D s0 o i) p (bp t)) (bp t)) = true →
      all6 (fun t => Nat.beq (bim (D (o + i)) t) (bp t)) = false →
      covK L D X s0 o n p nw i (D (o + i)) = true) := by
  unfold elemK at h
  rw [s2072_strictB] at h
  beta_reduce at h
  have e : Nat.add o i = o + i := rfl
  rw [e] at h
  obtain ⟨h1, h⟩ := s2072_bAnd h
  obtain ⟨h2, h⟩ := s2072_bAnd h
  obtain ⟨h3, h4⟩ := s2072_bAnd h
  refine ⟨h1, h2, fun hi => ?_, fun ha hb => ?_⟩
  · have e1 : Nat.blt (Nat.succ i) n = true := Nat.ble_eq_true_of_le hi
    rw [e1] at h3
    exact s2072_blt h3
  · rw [ha, hb] at h4
    exact h4

theorem s2072_tree {L D : ℕ → ℕ} {s0 m o n v : ℕ} (h : treeK L D s0 m o n v = true) :
    (f16 v 2 = 0 ∧ ∀ t < 6, bim v t = bp t) ∨
    (f16 v 2 ≠ 0 ∧ f16 v 0 < n ∧ f16 v 1 < m ∧ f16 (D (o + f16 v 0)) 2 + 1 = f16 v 2 ∧
      ∀ t < 6, bim v t = ap (L (s0 + f16 v 1)) (bim (D (o + f16 v 0)) t)) := by
  unfold treeK at h
  by_cases h0 : f16 v 2 = 0
  · have e : Nat.beq (f16 v 2) 0 = true := by
      rw [h0]
      rfl
    rw [e] at h
    exact Or.inl ⟨h0, fun t ht => Nat.eq_of_beq_eq_true ((s2072_all6 _).mp h t ht)⟩
  · have e : Nat.beq (f16 v 2) 0 = false := by
      cases hb : Nat.beq (f16 v 2) 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) h0
    rw [e] at h
    simp only [s2072_strictB] at h
    obtain ⟨h1, h⟩ := s2072_bAnd h
    obtain ⟨h2, h⟩ := s2072_bAnd h
    obtain ⟨h3, h4⟩ := s2072_bAnd h
    exact Or.inr ⟨h0, s2072_blt h1, s2072_blt h2, Nat.eq_of_beq_eq_true h3,
      fun t ht => Nat.eq_of_beq_eq_true ((s2072_all6 _).mp h4 t ht)⟩

theorem s2072_nxt {L D : ℕ → ℕ} {s0 m o n v : ℕ} (h : nxtK L D s0 m o n v = true) :
    ∀ k < m, ∃ j < n, ∀ t < 6, ap (L (s0 + k)) (bim v t) = bim (D (o + j)) t := by
  intro k hk
  unfold nxtK at h
  have hk' := CFSG.KS.allN_spec h k hk
  simp only [s2072_strictB] at hk'
  obtain ⟨hj, hall⟩ := s2072_bAnd hk'
  exact ⟨_, s2072_blt hj, fun t ht => Nat.eq_of_beq_eq_true ((s2072_all6 _).mp hall t ht)⟩

theorem s2072_cov {L D X : ℕ → ℕ} {s0 o n p nw i v : ℕ} (h : covK L D X s0 o n p nw i v = true) :
    ∃ w < nw, ∃ t < n, ∃ j, 0 < j ∧ j < p ∧ ∀ b < 6,
      act L D s0 o i (bim (D (o + t)) b) = act L D s0 o t (iter (ap (X w)) j (bp b)) := by
  unfold covK at h
  simp only [s2072_strictB] at h
  obtain ⟨h1, h⟩ := s2072_bAnd h
  obtain ⟨h2, h⟩ := s2072_bAnd h
  obtain ⟨h3, h⟩ := s2072_bAnd h
  obtain ⟨h4, h5⟩ := s2072_bAnd h
  exact ⟨_, s2072_blt h1, _, s2072_blt h2, _, s2072_blt h3, s2072_blt h4,
    fun b hb => Nat.eq_of_beq_eq_true ((s2072_all6 _).mp h5 b hb)⟩

theorem s2072_walk (L D : ℕ → ℕ) (s0 o f i y : ℕ) :
    walk L D s0 o (f + 1) i y =
      ap (L (s0 + f16 (D (o + i)) 1)) (walk L D s0 o f (f16 (D (o + i)) 0) y) := by
  change strictN (D (Nat.add o i)) (fun v => strictN (walk L D s0 o f (f16 v (nat_lit 0)) y)
    fun z => ap (L (Nat.add s0 (f16 v (nat_lit 1)))) z) = _
  simp only [s2072_strictN]
  rfl

theorem s2072_act {L D : ℕ → ℕ} {s0 o i d : ℕ} (h : f16 (D (o + i)) 2 = d) (y : ℕ) :
    act L D s0 o i y = walk L D s0 o d i y := by
  change walk L D s0 o (f16 (D (Nat.add o i)) (nat_lit 2)) i y = _
  have e : f16 (D (Nat.add o i)) (nat_lit 2) = d := h
  rw [e]

theorem s2072_el {D : ℕ → ℕ} {o i d : ℕ} {g : ℕ → Equiv.Perm (Fin N)}
    (h : f16 (D (o + i)) 2 = d) : el D o g i = elt D o g d i := by
  unfold el
  rw [h]

theorem recK_sound {L D X : ℕ → ℕ} {s0 m o n p nw r : ℕ} {g x : ℕ → Equiv.Perm (Fin N)}
    (hN : 7 ≤ N) (hrec : recK L D X s0 m o n p nw r = true)
    (hg : ∀ k < m, ∀ y : Fin N, ap (L (s0 + k)) y = (g k y : ℕ))
    (hx : ∀ w < nw, ∀ y : Fin N, ap (X w) y = (x w y : ℕ)) :
    r < n ∧ el D o g r = 1 ∧
    (∀ i < n, el D o g i ∈ Subgroup.closure {σ | ∃ k < m, g k = σ}) ∧
    (∀ i < n, ∀ k < m, ∃ j < n, onB (g k * el D o g i) (el D o g j)) ∧
    (∀ i < n, ∀ j < n, onB (el D o g i) (el D o g j) → i = j) ∧
    (∀ i < n, onB (el D o g i ^ p) 1 → ¬ onB (el D o g i) 1 →
      ∃ w < nw, ∃ t < n, ∃ j, 0 < j ∧ j < p ∧
        onB (el D o g i * el D o g t) (el D o g t * x w ^ j)) := by
  unfold recK at hrec
  obtain ⟨hr, hrec⟩ := s2072_bAnd hrec
  obtain ⟨hd, hall⟩ := s2072_bAnd hrec
  have hE : ∀ i < n, elemK L D X s0 m o n p nw i = true := CFSG.KS.allN_spec hall
  have hbp : ∀ t < 6, bp t < N := fun t ht => lt_of_lt_of_le (s2072_bp_lt t ht) hN
  have hmain : ∀ d, ∀ i < n, f16 (D (o + i)) 2 = d →
      el D o g i ∈ Subgroup.closure {σ | ∃ k < m, g k = σ} ∧
      (∀ y : Fin N, act L D s0 o i y = (el D o g i y : ℕ)) ∧
      (∀ t (ht : t < 6), bim (D (o + i)) t = (el D o g i ⟨bp t, hbp t ht⟩ : ℕ)) := by
    intro d
    induction d with
    | zero =>
      intro i hi hdi
      have h1 : el D o g i = 1 := s2072_el hdi
      refine ⟨by rw [h1]; exact Subgroup.one_mem _, fun y => ?_, fun t ht => ?_⟩
      · rw [h1, s2072_act hdi]
        rfl
      · rcases s2072_tree (s2072_elem (hE i hi)).1 with ⟨_, hb⟩ | ⟨hne, _⟩
        · rw [h1, hb t ht]
          rfl
        · exact absurd hdi hne
    | succ d ih =>
      intro i hi hdi
      rcases s2072_tree (s2072_elem (hE i hi)).1 with ⟨h0, _⟩ | ⟨_, hpar, hlab, hdep, hb⟩
      · omega
      · have hdp : f16 (D (o + f16 (D (o + i)) 0)) 2 = d := by omega
        obtain ⟨ihm, iha, ihb⟩ := ih _ hpar hdp
        have hel : el D o g i = g (f16 (D (o + i)) 1) * el D o g (f16 (D (o + i)) 0) := by
          rw [s2072_el hdi, s2072_el hdp]
          rfl
        refine ⟨?_, fun y => ?_, fun t ht => ?_⟩
        · rw [hel]
          exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨_, hlab, rfl⟩) ihm
        · rw [s2072_act hdi, s2072_walk, ← s2072_act hdp, iha y, hg _ hlab, hel,
            Equiv.Perm.mul_apply]
        · rw [hb t ht, ihb t ht, hg _ hlab, hel, Equiv.Perm.mul_apply]
  have hF := fun i (hi : i < n) => hmain _ i hi rfl
  refine ⟨s2072_blt hr, s2072_el (Nat.eq_of_beq_eq_true hd), fun i hi => (hF i hi).1, ?_, ?_, ?_⟩
  · intro i hi k hk
    obtain ⟨j, hj, he⟩ := s2072_nxt (s2072_elem (hE i hi)).2.1 k hk
    refine ⟨j, hj, fun t ht hb => Fin.ext ?_⟩
    have e := he t ht
    rw [(hF i hi).2.2 t ht, (hF j hj).2.2 t ht, hg k hk] at e
    rw [Equiv.Perm.mul_apply]
    exact e
  · have hkey : ∀ i, i + 1 < n → key (D (o + i)) < key (D (o + (i + 1))) :=
      fun i hi => (s2072_elem (hE i (by omega))).2.2.1 hi
    have hmono : ∀ i j, i < j → j < n → key (D (o + i)) < key (D (o + j)) := by
      intro i j hij hj
      induction j with
      | zero => omega
      | succ j ih =>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
        · exact lt_trans (ih h (by omega)) (hkey j hj)
        · subst h
          exact hkey i hj
    intro i hi j hj hon
    have hk : key (D (o + i)) = key (D (o + j)) := s2072_key_eq fun t ht => by
      rw [(hF i hi).2.2 t ht, (hF j hj).2.2 t ht, hon t ht (hbp t ht)]
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hk (ne_of_lt (hmono i j h hj))
    · exact h
    · exact absurd hk.symm (ne_of_lt (hmono j i h hi))
  · intro i hi hp1 hn1
    have ha := s2072_all6_of hN (hF i hi).2.1 hp1
    have hb : all6 (fun t => Nat.beq (bim (D (o + i)) t) (bp t)) = false := by
      cases hq : all6 (fun t => Nat.beq (bim (D (o + i)) t) (bp t))
      · rfl
      · exfalso
        apply hn1
        intro t ht hbt
        apply Fin.ext
        have e := Nat.eq_of_beq_eq_true ((s2072_all6 _).mp hq t ht)
        rw [(hF i hi).2.2 t ht] at e
        rw [Equiv.Perm.one_apply]
        exact e
    obtain ⟨w, hw, t, ht, j, hj0, hjp, hc⟩ := s2072_cov ((s2072_elem (hE i hi)).2.2.2 ha hb)
    refine ⟨w, hw, t, ht, j, hj0, hjp, fun b hb6 hbb => Fin.ext ?_⟩
    have e := hc b hb6
    rw [(hF t ht).2.2 b hb6, (hF i hi).2.1, s2072_iter (hx w hw) j (bp b) hbb, (hF t ht).2.1] at e
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    exact e

theorem eq_of_onB {P : Subgroup (Equiv.Perm (Fin N))} (hsep : ∀ G ∈ P, onB G 1 → G = 1)
    {σ τ : Equiv.Perm (Fin N)} (hσ : σ ∈ P) (hτ : τ ∈ P) (h : onB σ τ) : σ = τ := by
  have h1 := hsep (τ⁻¹ * σ) (P.mul_mem (P.inv_mem hτ) hσ) fun t ht hb => by
    change τ⁻¹ (σ ⟨bp t, hb⟩) = ⟨bp t, hb⟩
    rw [h t ht hb]
    exact τ.symm_apply_apply _
  exact (inv_mul_eq_one.1 h1).symm

theorem rec_facts {L D X : ℕ → ℕ} {s0 m o n p nw r : ℕ} {g x : ℕ → Equiv.Perm (Fin N)}
    {P : Subgroup (Equiv.Perm (Fin N))} (hN : 7 ≤ N) (hsep : ∀ G ∈ P, onB G 1 → G = 1)
    (hgP : ∀ k < m, g k ∈ P) (hxP : ∀ w < nw, x w ∈ P)
    (hrec : recK L D X s0 m o n p nw r = true)
    (hg : ∀ k < m, ∀ y : Fin N, ap (L (s0 + k)) y = (g k y : ℕ))
    (hx : ∀ w < nw, ∀ y : Fin N, ap (X w) y = (x w y : ℕ)) :
    Nat.card (Subgroup.closure {σ | ∃ k < m, g k = σ}) = n ∧
    ∀ σ ∈ Subgroup.closure {σ | ∃ k < m, g k = σ}, σ ≠ 1 → σ ^ p = 1 →
      ∃ w < nw, ∃ t ∈ Subgroup.closure {σ | ∃ k < m, g k = σ}, ∃ j, 0 < j ∧ j < p ∧
        σ = t * x w ^ j * t⁻¹ := by
  obtain ⟨hr, h1, hmem, hnxt, hinj, hcov⟩ := recK_sound hN hrec hg hx
  have hSP : Subgroup.closure {σ | ∃ k < m, g k = σ} ≤ P :=
    (Subgroup.closure_le _).2 (by rintro _ ⟨k, hk, rfl⟩; exact hgP k hk)
  have heP : ∀ i < n, el D o g i ∈ P := fun i hi => hSP (hmem i hi)
  have heinj : ∀ i < n, ∀ j < n, el D o g i = el D o g j → i = j :=
    fun i hi j hj h => hinj i hi j hj fun t _ hb => DFunLike.congr_fun h _
  have hstep : ∀ k < m, ∀ i < n, ∃ j < n, g k * el D o g i = el D o g j := by
    intro k hk i hi
    obtain ⟨j, hj, h⟩ := hnxt i hi k hk
    exact ⟨j, hj, eq_of_onB hsep (P.mul_mem (hgP k hk) (heP i hi)) (heP j hj) h⟩
  have hsurj : ∀ k < m, ∀ j < n, ∃ i < n, g k * el D o g i = el D o g j := by
    intro k hk
    choose f hf hfe using hstep k hk
    let F : Fin n → Fin n := fun i => ⟨f i i.2, hf i i.2⟩
    have hF : Function.Injective F := by
      intro a b hab
      have h2 : el D o g (f a a.2) = el D o g (f b b.2) :=
        congrArg (fun z : Fin n => el D o g z.val) hab
      rw [← hfe, ← hfe] at h2
      exact Fin.ext (heinj a a.2 b b.2 (mul_left_cancel h2))
    intro j hj
    obtain ⟨i, hi⟩ := Finite.surjective_of_injective hF ⟨j, hj⟩
    refine ⟨i, i.2, ?_⟩
    rw [hfe i i.2]
    exact congrArg (fun z : Fin n => el D o g z.val) hi
  have hST : ∀ σ ∈ Subgroup.closure {σ | ∃ k < m, g k = σ}, ∃ i < n, el D o g i = σ := by
    intro σ hσ
    induction hσ using Subgroup.closure_induction_left with
    | one => exact ⟨r, hr, h1⟩
    | mul_left a ha b _ ih =>
      obtain ⟨k, hk, rfl⟩ := ha
      obtain ⟨i, hi, rfl⟩ := ih
      obtain ⟨j, hj, h⟩ := hstep k hk i hi
      exact ⟨j, hj, h.symm⟩
    | inv_mul_cancel a ha b _ ih =>
      obtain ⟨k, hk, rfl⟩ := ha
      obtain ⟨j, hj, rfl⟩ := ih
      obtain ⟨i, hi, h⟩ := hsurj k hk j hj
      exact ⟨i, hi, by rw [← h, inv_mul_cancel_left]⟩
  refine ⟨?_, fun σ hσ hσ1 hσp => ?_⟩
  · have hrange : ((Subgroup.closure {σ | ∃ k < m, g k = σ} : Subgroup (Equiv.Perm (Fin N))) :
        Set (Equiv.Perm (Fin N))) = Set.range (fun i : Fin n => el D o g i) := by
      ext σ
      constructor
      · intro hσ
        obtain ⟨i, hi, rfl⟩ := hST σ hσ
        exact ⟨⟨i, hi⟩, rfl⟩
      · rintro ⟨i, rfl⟩
        exact hmem i i.2
    have hinjF : Function.Injective (fun i : Fin n => el D o g i) :=
      fun a b h => Fin.ext (heinj a a.2 b b.2 h)
    rw [← SetLike.coe_sort_coe, hrange, Nat.card_range_of_injective hinjF, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  · obtain ⟨i, hi, rfl⟩ := hST σ hσ
    have hp1 : onB (el D o g i ^ p) 1 := fun t _ hb => by rw [hσp]
    have hn1 : ¬ onB (el D o g i) 1 := fun h => hσ1 (eq_of_onB hsep (heP i hi) P.one_mem h)
    obtain ⟨w, hw, t, ht, j, hj0, hjp, hc⟩ := hcov i hi hp1 hn1
    have e := eq_of_onB hsep (P.mul_mem (heP i hi) (heP t ht))
      (P.mul_mem (heP t ht) (P.pow_mem (hxP w hw) j)) hc
    exact ⟨w, hw, el D o g t, hmem t ht, j, hj0, hjp, by rw [← e, mul_inv_cancel_right]⟩

theorem wit_facts {xq hq hiq p o : ℕ} {x h : Equiv.Perm (Fin N)}
    {P : Subgroup (Equiv.Perm (Fin N))} (hN : 7 ≤ N) (hsep : ∀ G ∈ P, onB G 1 → G = 1)
    (hxP : x ∈ P) (hhP : h ∈ P) (hw : witK xq hq hiq p o = true)
    (hx : ∀ y : Fin N, ap xq y = (x y : ℕ)) (hh : ∀ y : Fin N, ap hq y = (h y : ℕ))
    (hhi : ∀ y : Fin N, ap hiq y = (h⁻¹ y : ℕ)) :
    x ≠ 1 ∧ x ^ p = 1 ∧
      ∃ k, (x * h * x * h⁻¹) ^ k ≠ 1 ∧ ((x * h * x * h⁻¹) ^ k) ^ 2 = 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := witK_sound hN hw hx hh hhi
  have hyP : x * h * x * h⁻¹ ∈ P :=
    P.mul_mem (P.mul_mem (P.mul_mem hxP hhP) hxP) (P.inv_mem hhP)
  refine ⟨fun e => h1 (by rw [e]; exact fun _ _ _ => rfl), hsep _ (P.pow_mem hxP p) h2, o / 2,
    fun e => h5 (by rw [e]; exact fun _ _ _ => rfl), ?_⟩
  have ho : o / 2 * 2 = o := by omega
  rw [← pow_mul, ho]
  exact hsep _ (P.pow_mem hyP o) h4

end CFSG.KC.Syl2072

end
