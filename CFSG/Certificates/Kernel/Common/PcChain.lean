module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.Group
public import CFSG.Certificates.Kernel.Common.F2Dot
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.KC.PcChain

variable {G : Type*} [Group G]

@[expose] def wfrom (x : ℕ → G) (e : ℕ) : ℕ → ℕ → G
  | _, 0 => 1
  | k, m + 1 => if e.testBit k then x k * wfrom x e (k + 1) m else wfrom x e (k + 1) m

theorem wfrom_zero (x : ℕ → G) (e k : ℕ) : wfrom x e k 0 = 1 := rfl

theorem wfrom_succ (x : ℕ → G) (e k m : ℕ) :
    wfrom x e k (m + 1) = if e.testBit k then x k * wfrom x e (k + 1) m else wfrom x e (k + 1) m :=
  rfl

theorem wfrom_congr (x : ℕ → G) {e e' : ℕ} :
    ∀ (m k : ℕ), (∀ j, k ≤ j → j < k + m → e.testBit j = e'.testBit j) →
      wfrom x e k m = wfrom x e' k m
  | 0, _, _ => rfl
  | m + 1, k, h => by
    rw [wfrom_succ, wfrom_succ, h k le_rfl (by omega),
      wfrom_congr x m (k + 1) fun j h1 h2 => h j (by omega) (by omega)]

theorem wfrom_skip (x : ℕ → G) (e : ℕ) :
    ∀ (a k m : ℕ), (∀ j, k ≤ j → j < k + a → e.testBit j = false) →
      wfrom x e k (a + m) = wfrom x e (k + a) m
  | 0, k, m, _ => by simp
  | a + 1, k, m, h => by
    rw [show a + 1 + m = (a + m) + 1 by omega, wfrom_succ, h k le_rfl (by omega)]
    simp only [Bool.false_eq_true, if_false]
    rw [wfrom_skip x e a (k + 1) m fun j h1 h2 => h j (by omega) (by omega),
      show k + 1 + a = k + (a + 1) by omega]

theorem wfrom_mem (x : ℕ → G) (e : ℕ) :
    ∀ (m k : ℕ), wfrom x e k m ∈ Subgroup.closure (x '' Set.Ico k (k + m))
  | 0, _ => Subgroup.one_mem _
  | m + 1, k => by
    have hle : Subgroup.closure (x '' Set.Ico (k + 1) (k + 1 + m)) ≤
        Subgroup.closure (x '' Set.Ico k (k + (m + 1))) :=
      Subgroup.closure_mono (Set.image_mono fun j hj => ⟨by have := hj.1; omega,
        by have := hj.2; omega⟩)
    have hx : x k ∈ Subgroup.closure (x '' Set.Ico k (k + (m + 1))) :=
      Subgroup.subset_closure ⟨k, ⟨le_rfl, by omega⟩, rfl⟩
    rw [wfrom_succ]
    split
    · exact Subgroup.mul_mem _ hx (hle (wfrom_mem x e m (k + 1)))
    · exact hle (wfrom_mem x e m (k + 1))

theorem wfrom_mem' (x : ℕ → G) (e : ℕ) {k m n : ℕ} (h : k + m ≤ n) :
    wfrom x e k m ∈ Subgroup.closure (x '' Set.Ico k n) :=
  Subgroup.closure_mono (Set.image_mono fun j (hj : j ∈ Set.Ico k (k + m)) =>
    (⟨hj.1, by have := hj.2; omega⟩ : j ∈ Set.Ico k n)) (wfrom_mem x e m k)

theorem closure_sub_of_mul [Finite G] {gens S : Set G} (h1 : (1 : G) ∈ S)
    (hcl : ∀ y ∈ S, ∀ g ∈ gens, y * g ∈ S) : ∀ y ∈ Subgroup.closure gens, y ∈ S := by
  intro y hy
  have hsub : (Subgroup.closure gens).toSubmonoid = Submonoid.closure gens :=
    Subgroup.closure_toSubmonoid_of_finite
  have hy' : y ∈ Submonoid.closure gens := by rw [← hsub]; exact hy
  exact Submonoid.closure_induction_right (motive := fun m _ => m ∈ S) h1
    (fun m _ g hg hm => hcl m hm g hg) hy'

structure PcRel (x : ℕ → G) (n : ℕ) : Prop where
  sq : ∀ k < n, x k * x k ∈ Subgroup.closure (x '' Set.Ico (k + 1) n)
  cj : ∀ k j, k < j → j < n → x k * x j * (x k)⁻¹ ∈ Subgroup.closure (x '' Set.Ico (k + 1) n)

theorem exists_setBit (e k : ℕ) (b : Bool) :
    ∃ e' : ℕ, e'.testBit k = b ∧ ∀ j, j ≠ k → e'.testBit j = e.testBit j := by
  by_cases h : e.testBit k = b
  · exact ⟨e, h, fun _ _ => rfl⟩
  · refine ⟨e ^^^ 2 ^ k, ?_, fun j hj => ?_⟩
    · rw [Nat.testBit_xor, Nat.testBit_two_pow_self]
      cases hb : e.testBit k <;> cases b <;> simp_all
    · rw [Nat.testBit_xor, Nat.testBit_two_pow_of_ne (Ne.symm hj), Bool.xor_false]

section Closure

variable [Finite G] {x : ℕ → G} {n : ℕ}

theorem exists_wfrom (h : PcRel x n) :
    ∀ m ≤ n, ∀ g ∈ Subgroup.closure (x '' Set.Ico (n - m) n), ∃ e, g = wfrom x e (n - m) m
  | 0, _, g, hg => by
    have e0 : x '' Set.Ico (n - 0) n = ∅ := by simp
    rw [e0, Subgroup.closure_empty, Subgroup.mem_bot] at hg
    exact ⟨0, hg⟩
  | m + 1, hm, g, hg => by
    set k := n - (m + 1) with hk
    have hk1 : n - m = k + 1 := by omega
    set H := Subgroup.closure (x '' Set.Ico (k + 1) n) with hH
    have ih : ∀ g ∈ H, ∃ e, g = wfrom x e (k + 1) m := by
      intro g hg
      have := exists_wfrom h m (by omega) g (by rw [hk1]; exact hg)
      rwa [hk1] at this
    have hconj : ∀ y ∈ H, x k * y * (x k)⁻¹ ∈ H := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨j, ⟨hj1, hj2⟩, rfl⟩ := hy
        exact h.cj k j (by omega) hj2
      | one => simp
      | mul y y' _ _ ihy ihy' =>
        have e1 : x k * (y * y') * (x k)⁻¹ = (x k * y * (x k)⁻¹) * (x k * y' * (x k)⁻¹) := by
          group
        rw [e1]
        exact Subgroup.mul_mem _ ihy ihy'
      | inv y _ ihy =>
        have e1 : x k * y⁻¹ * (x k)⁻¹ = (x k * y * (x k)⁻¹)⁻¹ := by group
        rw [e1]
        exact Subgroup.inv_mem _ ihy
    have hN : x k ∈ Subgroup.normalizer (H : Set G) :=
      Subgroup.mem_normalizer_fintype fun y hy => hconj y hy
    have hconj' : ∀ y ∈ H, (x k)⁻¹ * y * x k ∈ H := by
      intro y hy
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hN) y).1 hy
      rwa [inv_inv] at this
    have hsq : x k * x k ∈ H := h.sq k (by omega)
    have hS := closure_sub_of_mul (gens := x '' Set.Ico k n)
      (S := {g | ∃ b : Bool, ∃ y ∈ H, g = (if b then x k else 1) * y})
      ⟨false, 1, Subgroup.one_mem _, by simp⟩
      (by
        rintro g ⟨b, y, hy, rfl⟩ _ ⟨j, ⟨hj1, hj2⟩, rfl⟩
        rcases Nat.lt_or_ge k j with hkj | hkj
        · have hxj : x j ∈ H := Subgroup.subset_closure ⟨j, ⟨hkj, hj2⟩, rfl⟩
          exact ⟨b, y * x j, Subgroup.mul_mem _ hy hxj, by rw [mul_assoc]⟩
        · have hjk : j = k := by omega
          rw [hjk]
          cases b
          · refine ⟨true, (x k)⁻¹ * y * x k, hconj' y hy, ?_⟩
            simp only [Bool.false_eq_true, if_false, if_true, one_mul]
            group
          · refine ⟨false, (x k * x k) * ((x k)⁻¹ * y * x k),
              Subgroup.mul_mem _ hsq (hconj' y hy), ?_⟩
            simp only [Bool.false_eq_true, if_false, if_true, one_mul]
            group)
    obtain ⟨b, y, hy, rfl⟩ := hS g hg
    obtain ⟨e, rfl⟩ := ih y hy
    obtain ⟨e', he'k, he'j⟩ := exists_setBit e k b
    refine ⟨e', ?_⟩
    rw [wfrom_succ, he'k,
      wfrom_congr x m (k + 1) (e := e') (e' := e) fun j hj _ => he'j j (by omega)]
    cases b <;> simp

theorem testBit_eq_of_wfrom_eq (h : PcRel x n)
    (hsep : ∀ k < n, ∀ e, x k ≠ wfrom x e (k + 1) (n - (k + 1))) :
    ∀ m ≤ n, ∀ e e', wfrom x e (n - m) m = wfrom x e' (n - m) m →
      ∀ j, n - m ≤ j → j < n → e.testBit j = e'.testBit j
  | 0, _, _, _, _, j, h1, h2 => by omega
  | m + 1, hm, e, e', he, j, h1, h2 => by
    set k := n - (m + 1) with hk
    have hk1 : n - m = k + 1 := by omega
    have hnk : n - (k + 1) = m := by omega
    have ih := testBit_eq_of_wfrom_eq h hsep m (by omega)
    rw [hk1] at ih
    have hmem : ∀ e, wfrom x e (k + 1) m ∈ Subgroup.closure (x '' Set.Ico (k + 1) n) :=
      fun e => wfrom_mem' x e (by omega)
    have hnot : ∀ y y', x k * wfrom x y (k + 1) m = wfrom x y' (k + 1) m → False := by
      intro y y' hyy
      have hxk : x k = wfrom x y' (k + 1) m * (wfrom x y (k + 1) m)⁻¹ := by
        rw [← hyy, mul_inv_cancel_right]
      have hin := Subgroup.mul_mem _ (hmem y') (Subgroup.inv_mem _ (hmem y))
      rw [← hxk, ← hk1] at hin
      obtain ⟨e'', he''⟩ := exists_wfrom h m (by omega) _ hin
      rw [hk1] at he''
      exact hsep k (by omega) e'' (by rw [he'', hnk])
    rw [wfrom_succ, wfrom_succ] at he
    have hrest : wfrom x e (k + 1) m = wfrom x e' (k + 1) m ∧ e.testBit k = e'.testBit k := by
      cases hb : e.testBit k <;> cases hb' : e'.testBit k <;> simp only [hb, hb'] at he
      · exact ⟨he, rfl⟩
      · exact (hnot _ _ he.symm).elim
      · exact (hnot _ _ he).elim
      · exact ⟨mul_left_cancel he, rfl⟩
    rcases Nat.lt_or_ge j (k + 1) with hj | hj
    · rw [show j = k by omega]
      exact hrest.2
    · exact ih e e' hrest.1 j hj h2

theorem card_closure (h : PcRel x n)
    (hsep : ∀ k < n, ∀ e, x k ≠ wfrom x e (k + 1) (n - (k + 1))) :
    Nat.card (Subgroup.closure (x '' Set.Ico 0 n)) = 2 ^ n := by
  have hmem : ∀ e, wfrom x e 0 n ∈ Subgroup.closure (x '' Set.Ico 0 n) :=
    fun e => wfrom_mem' x e (by omega)
  let f : Fin (2 ^ n) → Subgroup.closure (x '' Set.Ico 0 n) := fun e => ⟨wfrom x e 0 n, hmem e⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro e e' hee
      have h1 : wfrom x e (n - n) n = wfrom x e' (n - n) n := by
        rw [Nat.sub_self]
        exact congrArg Subtype.val hee
      have hb := testBit_eq_of_wfrom_eq h hsep n le_rfl e e' h1
      apply Fin.ext
      apply Nat.eq_of_testBit_eq
      intro j
      rcases Nat.lt_or_ge j n with hj | hj
      · exact hb j (by omega) hj
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le e.2 (Nat.pow_le_pow_right two_pos hj)),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le e'.2 (Nat.pow_le_pow_right two_pos hj))]
    · rintro ⟨g, hg⟩
      obtain ⟨e, he⟩ := exists_wfrom h n le_rfl g (by rw [Nat.sub_self]; exact hg)
      refine ⟨⟨e % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩, Subtype.ext ?_⟩
      change wfrom x (e % 2 ^ n) 0 n = g
      rw [he, Nat.sub_self]
      refine wfrom_congr x n 0 fun j _ hj => ?_
      rw [Nat.testBit_mod_two_pow]
      simp [show j < n by omega]
  rw [← Nat.card_eq_of_bijective f hbij, Nat.card_eq_fintype_card, Fintype.card_fin]

end Closure

theorem ne_wfrom_of_orbit {X : Type*} [MulAction G X] (x : ℕ → G) (O : Set X) {k n : ℕ}
    (hkn : k < n) (hO : ∀ y ∈ O, ∀ j, k < j → j < n → (x j)⁻¹ • y ∈ O) {v : X} (hv : v ∈ O)
    (hk : (x k)⁻¹ • v ∉ O) (e : ℕ) : x k ≠ wfrom x e (k + 1) (n - (k + 1)) := by
  have key : ∀ (m a : ℕ), k < a → a + m ≤ n → ∀ y ∈ O, (wfrom x e a m)⁻¹ • y ∈ O := by
    intro m
    induction m with
    | zero => intro a _ _ y hy; simpa [wfrom_zero] using hy
    | succ m ih =>
      intro a ha ham y hy
      rw [wfrom_succ]
      split
      · rw [mul_inv_rev, mul_smul]
        exact ih (a + 1) (by omega) (by omega) _ (hO y hy a ha (by omega))
      · exact ih (a + 1) (by omega) (by omega) y hy
  intro hxk
  apply hk
  rw [hxk]
  exact key _ (k + 1) (by omega) (by omega) v hv

section ClassTwo

@[expose] def phi (C : ℕ → ℕ → ℕ) (j e : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | k, m + 1 => (if e.testBit k then C k j else 0) ^^^ phi C j e (k + 1) m

variable {x : ℕ → G} {z : ℕ → G} {w n j : ℕ} {C : ℕ → ℕ → ℕ}

theorem comm_wfrom {g : G} (e : ℕ) :
    ∀ (m k : ℕ), (∀ i, k ≤ i → i < k + m → g * x i = x i * g) →
      g * wfrom x e k m = wfrom x e k m * g
  | 0, _, _ => by simp [wfrom_zero]
  | m + 1, k, hg => by
    have ih := comm_wfrom e m (k + 1) fun i h1 h2 => hg i (by omega) (by omega)
    rw [wfrom_succ]
    split
    · rw [← mul_assoc, hg k le_rfl (by omega), mul_assoc, ih, mul_assoc]
    · exact ih

theorem wfrom_zero_e (x : ℕ → G) : ∀ (m k : ℕ), wfrom x 0 k m = 1
  | 0, _ => rfl
  | m + 1, k => by rw [wfrom_succ, Nat.zero_testBit, wfrom_zero_e x m (k + 1)]; rfl

theorem wfrom_mul_xor (e e' : ℕ) :
    ∀ (m k : ℕ), (∀ i j, k ≤ i → i < k + m → k ≤ j → j < k + m → x i * x j = x j * x i) →
      (∀ i, k ≤ i → i < k + m → x i * x i = 1) →
      wfrom x e k m * wfrom x e' k m = wfrom x (e ^^^ e') k m
  | 0, _, _, _ => by simp [wfrom_zero]
  | m + 1, k, hc, hi => by
    have ih := wfrom_mul_xor e e' m (k + 1) (fun i j h1 h2 h3 h4 => hc i j (by omega) (by omega)
      (by omega) (by omega)) fun i h1 h2 => hi i (by omega) (by omega)
    have hcw : ∀ f, x k * wfrom x f (k + 1) m = wfrom x f (k + 1) m * x k := fun f =>
      comm_wfrom f m (k + 1) fun i h1 h2 => hc k i le_rfl (by omega) (by omega) (by omega)
    have hkk := hi k le_rfl (by omega)
    rw [wfrom_succ, wfrom_succ, wfrom_succ, Nat.testBit_xor, ← ih]
    cases e.testBit k <;> cases e'.testBit k <;> simp only [Bool.false_xor, Bool.xor_false,
      Bool.true_xor, Bool.not_true, Bool.not_false, Bool.xor_self, Bool.false_eq_true,
      if_true, if_false]
    · rw [← mul_assoc, ← hcw, mul_assoc]
    · rw [mul_assoc]
    · rw [mul_assoc, ← mul_assoc (wfrom x e (k + 1) m), ← hcw, ← mul_assoc, ← mul_assoc, hkk,
        one_mul]

theorem phi_testBit (C : ℕ → ℕ → ℕ) (j e t : ℕ) :
    ∀ (m k : ℕ), (phi C j e k m).testBit t =
      CFSG.KC.F2Dot.dotFrom e (CFSG.KC.F2Dot.maskFrom (fun i => (C i j).testBit t) k m) k m
  | 0, _ => by simp [phi, CFSG.KC.F2Dot.dotFrom]
  | m + 1, k => by
    rw [phi, Nat.testBit_xor, phi_testBit C j e t m (k + 1), CFSG.KC.F2Dot.dotFrom,
      CFSG.KC.F2Dot.testBit_maskFrom]
    have hc : CFSG.KC.F2Dot.dotFrom e
        (CFSG.KC.F2Dot.maskFrom (fun i => (C i j).testBit t) k (m + 1)) (k + 1) m =
        CFSG.KC.F2Dot.dotFrom e
        (CFSG.KC.F2Dot.maskFrom (fun i => (C i j).testBit t) (k + 1) m) (k + 1) m := by
      refine CFSG.KC.F2Dot.dotFrom_congr m (k + 1) fun i h1 h2 => ?_
      rw [CFSG.KC.F2Dot.testBit_maskFrom, CFSG.KC.F2Dot.testBit_maskFrom]
      congr 1
      simp only [decide_eq_decide]
      omega
    rw [hc]
    congr 1
    cases e.testBit k <;> simp

theorem wfrom_mul_comm (hz0 : z 0 = 1)
    (hzm : ∀ a b, a < 2 ^ w → b < 2 ^ w → z a * z b = z (a ^^^ b))
    (hzc : ∀ a < 2 ^ w, ∀ i < n, z a * x i = x i * z a)
    (hC : ∀ i < n, C i j < 2 ^ w ∧ x i * x j = x j * x i * z (C i j)) (e : ℕ) :
    ∀ (m k : ℕ), k + m ≤ n →
      wfrom x e k m * x j = x j * wfrom x e k m * z (phi C j e k m) ∧ phi C j e k m < 2 ^ w
  | 0, _, _ => by simp [wfrom_zero, phi, hz0]
  | m + 1, k, hkm => by
    obtain ⟨ih, ihlt⟩ := wfrom_mul_comm hz0 hzm hzc hC e m (k + 1) (by omega)
    obtain ⟨hClt, hCeq⟩ := hC k (by omega)
    rw [wfrom_succ, phi]
    split
    · refine ⟨?_, Nat.xor_lt_two_pow hClt ihlt⟩
      rw [← hzm _ _ hClt ihlt]
      have hcz := comm_wfrom (x := x) (g := z (C k j)) e m (k + 1) fun i _ h2 =>
        hzc _ hClt i (by omega)
      calc x k * wfrom x e (k + 1) m * x j
          = x k * x j * wfrom x e (k + 1) m * z (phi C j e (k + 1) m) := by
            rw [mul_assoc, ih]; group
        _ = x j * x k * (z (C k j) * wfrom x e (k + 1) m) * z (phi C j e (k + 1) m) := by
            rw [hCeq]; group
        _ = x j * x k * (wfrom x e (k + 1) m * z (C k j)) * z (phi C j e (k + 1) m) := by
            rw [hcz]
        _ = _ := by group
    · rw [Nat.zero_xor]
      exact ⟨ih, ihlt⟩

end ClassTwo

end CFSG.KC.PcChain
