module

public import CFSG.Certificates.Kernel.Spor.CBTrInv
public import CFSG.Certificates.Kernel.Spor.Loops
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

public section

namespace CFSG.KS.CB

open CFSG.KC.Enum CFSG.ONSchreier.Native

@[expose] noncomputable def trK (STEP : Nat → Nat → Nat) (PAR LAB : Nat → Nat) (fuel : Nat) :
    Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ p => p)
    (fun _ ih k p => nIf(Nat.beq k (nat_lit 0), p, STEP (LAB k) (ih (PAR k) p))) fuel

@[expose] noncomputable def cntK (m : Nat) (q : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i ih => Nat.add (nIf(q i, nat_lit 1, nat_lit 0)) ih) m

@[expose] noncomputable def ccQ (Z A : Nat → Nat) (STEP₁ : Nat → Nat → Nat) (PAR₁ LAB₁ : Nat → Nat)
    (m₁ : Nat) (STEP₂ : Nat → Nat → Nat) (PAR₂ LAB₂ : Nat → Nat) (m₂ b₂ k₁ v k₂ : Nat) : Bool :=
  bAnd(Nat.beq (A k₂) v,
    Nat.beq (trK STEP₁ PAR₁ LAB₁ m₁ k₁ (trK STEP₂ PAR₂ LAB₂ m₂ k₂ (Z b₂)))
      (Z (trK STEP₁ PAR₁ LAB₁ m₁ k₁ (trK STEP₂ PAR₂ LAB₂ m₂ k₂ b₂))))

@[expose] noncomputable def ccF (Z A : Nat → Nat) (STEP₁ INV₁ : Nat → Nat → Nat)
    (PAR₁ LAB₁ : Nat → Nat) (m₁ : Nat) (STEP₂ : Nat → Nat → Nat) (PAR₂ LAB₂ : Nat → Nat)
    (m₂ b₁ b₂ k₁ : Nat) : Nat :=
  nIf(Nat.blt k₁ m₁,
    strictN (trInvK PAR₁ LAB₁ INV₁ m₁ k₁ (Z (trK STEP₁ PAR₁ LAB₁ m₁ k₁ b₁))) fun v =>
      cntK m₂ (ccQ Z A STEP₁ PAR₁ LAB₁ m₁ STEP₂ PAR₂ LAB₂ m₂ b₂ k₁ v), nat_lit 0)

@[expose] noncomputable def sumR (f : Nat → Nat) (lo len : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun l ih => Nat.add (f (Nat.add lo l)) ih) len

@[expose] noncomputable def sumR2 (f : Nat → Nat) (lo nb : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun h ih => Nat.add (sumR f (Nat.add lo (Nat.shiftLeft h (nat_lit 6))) (nat_lit 64)) ih) nb

theorem strictN_app (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem nbeq_iff {a b : Nat} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem sumR_eq (f : Nat → Nat) (lo : Nat) :
    ∀ len, sumR f lo len = ∑ l ∈ Finset.range len, f (lo + l)
  | 0 => rfl
  | len + 1 => by
    have e : sumR f lo (len + 1) = f (lo + len) + sumR f lo len := rfl
    rw [e, sumR_eq f lo len, Finset.sum_range_succ, Nat.add_comm]

theorem sumR2_eq (f : Nat → Nat) (lo : Nat) :
    ∀ nb, sumR2 f lo nb = ∑ i ∈ Finset.range (64 * nb), f (lo + i)
  | 0 => rfl
  | nb + 1 => by
    have e : sumR2 f lo (nb + 1) =
        sumR f (Nat.add lo (Nat.shiftLeft nb (nat_lit 6))) (nat_lit 64) + sumR2 f lo nb := rfl
    have e6 : Nat.add lo (Nat.shiftLeft nb (nat_lit 6)) = lo + 64 * nb := by
      change lo + nb <<< 6 = _
      rw [Nat.shiftLeft_eq]
      omega
    rw [e, e6, sumR_eq, sumR2_eq f lo nb, Nat.mul_succ, Finset.sum_range_add, Nat.add_comm]
    simp only [Nat.add_assoc]

theorem cntK_eq (q : Nat → Bool) : ∀ m, cntK m q = ((List.range m).filter q).length
  | 0 => rfl
  | m + 1 => by
    have e : cntK (m + 1) q = nIf(q m, nat_lit 1, nat_lit 0) + cntK m q := rfl
    rw [e, cntK_eq q m, List.range_succ, List.filter_append, List.length_append]
    cases h : q m <;> simp [List.filter, h, Nat.add_comm]

theorem cntK_sum (q : Nat → Bool) :
    ∀ m, cntK m q = ∑ i ∈ Finset.range m, nIf(q i, nat_lit 1, nat_lit 0)
  | 0 => rfl
  | m + 1 => by
    have e : cntK (m + 1) q = nIf(q m, nat_lit 1, nat_lit 0) + cntK m q := rfl
    rw [e, cntK_sum q m, Finset.sum_range_succ, Nat.add_comm]

theorem sum_range_tail {f : Nat → Nat} {M T : Nat} (hf : ∀ i, M ≤ i → f i = 0) (h : M ≤ T) :
    ∑ i ∈ Finset.range M, f i = ∑ i ∈ Finset.range T, f i := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Finset.sum_range_add, Finset.sum_eq_zero (fun i _ => hf (M + i) (Nat.le_add_right M i)),
    Nat.add_zero]

theorem ccF_ge {Z A : Nat → Nat} {STEP₁ INV₁ : Nat → Nat → Nat} {PAR₁ LAB₁ : Nat → Nat}
    {m₁ : Nat} {STEP₂ : Nat → Nat → Nat} {PAR₂ LAB₂ : Nat → Nat} {m₂ b₁ b₂ k₁ : Nat}
    (h : m₁ ≤ k₁) : ccF Z A STEP₁ INV₁ PAR₁ LAB₁ m₁ STEP₂ PAR₂ LAB₂ m₂ b₁ b₂ k₁ = 0 := by
  have hb : Nat.blt k₁ m₁ = false := by
    rw [Bool.eq_false_iff]
    intro e
    exact absurd (Nat.blt_eq ▸ e) (by omega)
  unfold ccF
  rw [hb]

theorem sum_map_range (F : Nat → Nat) :
    ∀ m, ((List.range m).map F).sum = ∑ k ∈ Finset.range m, F k
  | 0 => rfl
  | m + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_map_range F m,
      Finset.sum_range_succ]
    simp

theorem sum_slices (f : Nat → Nat) (c : Nat) :
    ∀ nc, ∑ i ∈ Finset.range (c * nc), f i = ∑ s ∈ Finset.range nc, ∑ l ∈ Finset.range c, f (c * s + l)
  | 0 => by simp
  | nc + 1 => by
    rw [Nat.mul_succ, Finset.sum_range_add, sum_slices f c nc, Finset.sum_range_succ]

variable {n m r : Nat} {PAR LAB : Nat → Nat} {STEP INV : Nat → Nat → Nat}

theorem trK_lt (hm : ∀ k < m, PAR k < m ∧ LAB k < r) (hs : ∀ j < r, ∀ x < n, STEP j x < n) :
    ∀ (fuel k p : Nat), k < m → p < n → trK STEP PAR LAB fuel k p < n
  | 0, _, _, _, hp => hp
  | fuel + 1, k, p, hk, hp => by
    cases k with
    | zero => exact hp
    | succ k =>
      exact hs _ (hm _ hk).2 _ (trK_lt hm hs fuel (PAR (k + 1)) p (hm _ hk).1 hp)

theorem trInvK_lt (hm : ∀ k < m, PAR k < m ∧ LAB k < r) (hs : ∀ j < r, ∀ x < n, INV j x < n) :
    ∀ (fuel k p : Nat), k < m → p < n → trInvK PAR LAB INV fuel k p < n
  | 0, _, _, _, hp => hp
  | fuel + 1, k, p, hk, hp => by
    cases k with
    | zero => exact hp
    | succ k =>
      exact trInvK_lt hm hs fuel (PAR (k + 1)) _ (hm _ hk).1 (hs _ (hm _ hk).2 p hp)

theorem trK_fix {b : Nat} (hm : ∀ k < m, PAR k < m ∧ LAB k < r) (hb : ∀ j < r, STEP j b = b) :
    ∀ (fuel k : Nat), k < m → trK STEP PAR LAB fuel k b = b
  | 0, _, _ => rfl
  | fuel + 1, k, hk => by
    cases k with
    | zero => rfl
    | succ k =>
      change STEP (LAB (k + 1)) (trK STEP PAR LAB fuel (PAR (k + 1)) b) = b
      rw [trK_fix hm hb fuel _ (hm _ hk).1, hb _ (hm _ hk).2]

theorem trInvK_trK (hm : ∀ k < m, PAR k < m ∧ LAB k < r)
    (hs : ∀ j < r, ∀ x < n, STEP j x < n ∧ INV j (STEP j x) = x) :
    ∀ (fuel k p : Nat), k < m → p < n →
      trInvK PAR LAB INV fuel k (trK STEP PAR LAB fuel k p) = p
  | 0, _, _, _, _ => rfl
  | fuel + 1, k, p, hk, hp => by
    cases k with
    | zero => rfl
    | succ k =>
      change trInvK PAR LAB INV fuel (PAR (k + 1))
        (INV (LAB (k + 1)) (STEP (LAB (k + 1)) (trK STEP PAR LAB fuel (PAR (k + 1)) p))) = p
      rw [(hs _ (hm _ hk).2 _ (trK_lt hm (fun j hj x hx => (hs j hj x hx).1) fuel _ p
        (hm _ hk).1 hp)).2]
      exact trInvK_trK hm hs fuel _ p (hm _ hk).1 hp

theorem trK_trInvK (hm : ∀ k < m, PAR k < m ∧ LAB k < r)
    (hs : ∀ j < r, ∀ x < n, INV j x < n ∧ STEP j (INV j x) = x) :
    ∀ (fuel k p : Nat), k < m → p < n →
      trK STEP PAR LAB fuel k (trInvK PAR LAB INV fuel k p) = p
  | 0, _, _, _, _ => rfl
  | fuel + 1, k, p, hk, hp => by
    cases k with
    | zero => rfl
    | succ k =>
      change STEP (LAB (k + 1)) (trK STEP PAR LAB fuel (PAR (k + 1))
        (trInvK PAR LAB INV fuel (PAR (k + 1)) (INV (LAB (k + 1)) p))) = p
      rw [trK_trInvK hm hs fuel _ _ (hm _ hk).1 (hs _ (hm _ hk).2 p hp).1,
        (hs _ (hm _ hk).2 p hp).2]

theorem trApp_eqK {PTS POS : Nat → Nat} {st : Array (Array Nat)}
    (hm : ∀ k < m, PAR k < m ∧ LAB k < r)
    (hs : ∀ j < r, ∀ x < n, (st[j]!)[x]! = STEP j x ∧ STEP j x < n) :
    ∀ (fuel k p : Nat), k < m → p < n →
      trApp st ⟨Array.ofFn (n := m) fun k => PTS k.val, Array.ofFn (n := n) fun z => POS z.val,
        Array.ofFn (n := m) fun k => PAR k.val, Array.ofFn (n := m) fun k => LAB k.val⟩ fuel k p =
      trK STEP PAR LAB fuel k p
  | 0, _, _, _, _ => rfl
  | fuel + 1, k, p, hk, hp => by
    unfold trApp
    cases k with
    | zero => rfl
    | succ k =>
      simp only [Nat.succ_ne_zero, beq_iff_eq, ↓reduceIte]
      have e1 : (Array.ofFn (n := m) fun k => PAR k.val)[k + 1]! = PAR (k + 1) := by
        rw [getElem!_pos _ (k + 1) (by simpa using hk), Array.getElem_ofFn]
      have e2 : (Array.ofFn (n := m) fun k => LAB k.val)[k + 1]! = LAB (k + 1) := by
        rw [getElem!_pos _ (k + 1) (by simpa using hk), Array.getElem_ofFn]
      rw [e1, e2, trApp_eqK hm hs fuel _ p (hm _ hk).1 hp,
        (hs _ (hm _ hk).2 _ (trK_lt hm (fun j hj x hx => (hs j hj x hx).2) fuel _ p (hm _ hk).1
          hp)).1]
      rfl

theorem commCount_eq {m₁ m₂ r₁ r₂ i₁ i₂ b₀ b₁ b₂ : Nat} {levels : Array CLevel}
    {stepsAll : Array (Array (Array Nat))} {z : Array Nat}
    {PTS₁ POS₁ PAR₁ LAB₁ PTS₂ POS₂ PAR₂ LAB₂ Z A : Nat → Nat} {STEP₁ INV₁ STEP₂ : Nat → Nat → Nat}
    (hL₁ : levels[i₁]! = ⟨Array.ofFn (n := m₁) fun k => PTS₁ k.val,
      Array.ofFn (n := n) fun z => POS₁ z.val, Array.ofFn (n := m₁) fun k => PAR₁ k.val,
      Array.ofFn (n := m₁) fun k => LAB₁ k.val⟩)
    (hL₂ : levels[i₂]! = ⟨Array.ofFn (n := m₂) fun k => PTS₂ k.val,
      Array.ofFn (n := n) fun z => POS₂ z.val, Array.ofFn (n := m₂) fun k => PAR₂ k.val,
      Array.ofFn (n := m₂) fun k => LAB₂ k.val⟩)
    (hm₁ : ∀ k < m₁, PAR₁ k < m₁ ∧ LAB₁ k < r₁) (hm₂ : ∀ k < m₂, PAR₂ k < m₂ ∧ LAB₂ k < r₂)
    (hs₁ : ∀ j < r₁, ∀ x < n, ((stepsAll[i₁]!)[j]!)[x]! = STEP₁ j x ∧ STEP₁ j x < n ∧
      INV₁ j x < n ∧ INV₁ j (STEP₁ j x) = x ∧ STEP₁ j (INV₁ j x) = x)
    (hs₂ : ∀ j < r₂, ∀ x < n, ((stepsAll[i₂]!)[j]!)[x]! = STEP₂ j x ∧ STEP₂ j x < n)
    (hf₁ : ∀ j < r₁, STEP₁ j b₀ = b₀) (hf₂ : ∀ j < r₂, STEP₂ j b₀ = b₀ ∧ STEP₂ j b₁ = b₁)
    (hz : ∀ p < n, z[p]! = Z p ∧ Z p < n) (hz₀ : Z b₀ = b₀) (hb : b₀ < n ∧ b₁ < n ∧ b₂ < n)
    (hA : ∀ k < m₂, A k = trK STEP₂ PAR₂ LAB₂ m₂ k (Z b₁)) :
    commCount levels stepsAll i₁ i₂ z #[b₀, b₁, b₂] =
      ∑ k ∈ Finset.range m₁, ccF Z A STEP₁ INV₁ PAR₁ LAB₁ m₁ STEP₂ PAR₂ LAB₂ m₂ b₁ b₂ k := by
  obtain ⟨hb₀, hb₁, hb₂⟩ := hb
  have hs₁' : ∀ j < r₁, ∀ x < n, ((stepsAll[i₁]!)[j]!)[x]! = STEP₁ j x ∧ STEP₁ j x < n :=
    fun j hj x hx => ⟨(hs₁ j hj x hx).1, (hs₁ j hj x hx).2.1⟩
  have hlt₁ := trK_lt hm₁ (fun j hj x hx => (hs₁ j hj x hx).2.1)
  have hlt₂ := trK_lt hm₂ (fun j hj x hx => (hs₂ j hj x hx).2)
  unfold commCount
  rw [hL₁, hL₂, Array.size_ofFn, Array.size_ofFn, sum_map_range]
  refine Finset.sum_congr rfl fun k₁ hk₁ => ?_
  have hk₁ : k₁ < m₁ := Finset.mem_range.1 hk₁
  have hT : ∀ k₂ < m₂, ∀ p < n, tr2App levels stepsAll i₁ i₂ k₁ k₂ p =
      trK STEP₁ PAR₁ LAB₁ m₁ k₁ (trK STEP₂ PAR₂ LAB₂ m₂ k₂ p) := by
    intro k₂ hk₂ p hp
    unfold tr2App
    rw [hL₁, hL₂, Array.size_ofFn, Array.size_ofFn, trApp_eqK hm₂ hs₂ _ _ _ hk₂ hp,
      trApp_eqK hm₁ hs₁' _ _ _ hk₁ (hlt₂ _ _ _ hk₂ hp)]
  have hbl : Nat.blt k₁ m₁ = true := Nat.blt_eq ▸ hk₁
  have eF : ccF Z A STEP₁ INV₁ PAR₁ LAB₁ m₁ STEP₂ PAR₂ LAB₂ m₂ b₁ b₂ k₁ =
      cntK m₂ (ccQ Z A STEP₁ PAR₁ LAB₁ m₁ STEP₂ PAR₂ LAB₂ m₂ b₂ k₁
        (trInvK PAR₁ LAB₁ INV₁ m₁ k₁ (Z (trK STEP₁ PAR₁ LAB₁ m₁ k₁ b₁)))) := by
    unfold ccF
    rw [hbl]
    exact strictN_app _ _
  rw [eF, cntK_eq]
  congr 1
  refine List.filter_congr fun k₂ hk₂ => ?_
  have hk₂ : k₂ < m₂ := List.mem_range.1 hk₂
  have f₀ : trK STEP₂ PAR₂ LAB₂ m₂ k₂ b₀ = b₀ := trK_fix hm₂ (fun j hj => (hf₂ j hj).1) _ _ hk₂
  have f₁ : trK STEP₂ PAR₂ LAB₂ m₂ k₂ b₁ = b₁ := trK_fix hm₂ (fun j hj => (hf₂ j hj).2) _ _ hk₂
  have g₀ : trK STEP₁ PAR₁ LAB₁ m₁ k₁ b₀ = b₀ := trK_fix hm₁ hf₁ _ _ hk₁
  have zb₁ := (hz b₁ hb₁).2
  have hv := hz _ (hlt₁ m₁ k₁ b₁ hk₁ hb₁)
  have hw := hz _ (hlt₁ m₁ k₁ _ hk₁ (hlt₂ m₂ k₂ b₂ hk₂ hb₂))
  have e₀ : tr2App levels stepsAll i₁ i₂ k₁ k₂ z[b₀]! = b₀ := by
    rw [(hz b₀ hb₀).1, hz₀, hT k₂ hk₂ _ hb₀, f₀, g₀]
  have e₀' : z[tr2App levels stepsAll i₁ i₂ k₁ k₂ b₀]! = b₀ := by
    rw [hT k₂ hk₂ _ hb₀, f₀, g₀, (hz b₀ hb₀).1, hz₀]
  have e₁ : tr2App levels stepsAll i₁ i₂ k₁ k₂ z[b₁]! = trK STEP₁ PAR₁ LAB₁ m₁ k₁ (A k₂) := by
    rw [(hz b₁ hb₁).1, hT k₂ hk₂ _ zb₁, hA k₂ hk₂]
  have e₁' : z[tr2App levels stepsAll i₁ i₂ k₁ k₂ b₁]! = Z (trK STEP₁ PAR₁ LAB₁ m₁ k₁ b₁) := by
    rw [hT k₂ hk₂ _ hb₁, f₁, hv.1]
  have e₂ : tr2App levels stepsAll i₁ i₂ k₁ k₂ z[b₂]! =
      trK STEP₁ PAR₁ LAB₁ m₁ k₁ (trK STEP₂ PAR₂ LAB₂ m₂ k₂ (Z b₂)) := by
    rw [(hz b₂ hb₂).1, hT k₂ hk₂ _ (hz b₂ hb₂).2]
  have e₂' : z[tr2App levels stepsAll i₁ i₂ k₁ k₂ b₂]! =
      Z (trK STEP₁ PAR₁ LAB₁ m₁ k₁ (trK STEP₂ PAR₂ LAB₂ m₂ k₂ b₂)) := by
    rw [hT k₂ hk₂ _ hb₂, hw.1]
  rw [Bool.eq_iff_iff]
  simp only [List.all_toArray, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    beq_iff_eq]
  rw [e₀, e₀', e₁, e₁', e₂, e₂']
  unfold ccQ
  rw [bAnd_iff, nbeq_iff, nbeq_iff]
  have hAlt : A k₂ < n := by
    rw [hA k₂ hk₂]
    exact hlt₂ _ _ _ hk₂ zb₁
  have hinv₁ := trInvK_trK (n := n) hm₁ (fun j hj x hx => ⟨(hs₁ j hj x hx).2.1, (hs₁ j hj x hx).2.2.2.1⟩)
  have hinv₂ := trK_trInvK (n := n) hm₁ (fun j hj x hx => ⟨(hs₁ j hj x hx).2.2.1, (hs₁ j hj x hx).2.2.2.2⟩)
  constructor
  · rintro ⟨-, h₁, h₂⟩
    refine ⟨?_, h₂⟩
    rw [← h₁, hinv₁ m₁ k₁ _ hk₁ hAlt]
  · rintro ⟨h₁, h₂⟩
    refine ⟨rfl, ?_, h₂⟩
    rw [h₁, hinv₂ m₁ k₁ _ hk₁ hv.2]

end CFSG.KS.CB

end
