module

public import CFSG.Monster.B.TwoA.Sp8.P0RankWalk
public import Certificates.Data.Kernel.P0Vis
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.SuccPred

public section

namespace CFSG.KC.P0Vis

open CFSG.KC.P0Orb CFSG.Monster.B.TwoA.Sp8.P0Rank Finset

@[expose] def IdxTwo (M' W : Finset ℕ) : Prop := ∀ a ∈ M', ∀ b ∈ M', a ∉ W → b ∉ W → a ^^^ b ∈ W

@[expose] def phiW (W : Finset ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: g => (if x ∈ W then 0 else 1) + 2 * phiW W g

@[expose] def pbT (x : ℕ) : ℕ → Bool
  | 0 => false
  | n + 1 => pbT x n ^^ x.testBit n

theorem phiW_lt (W : Finset ℕ) : ∀ g : List ℕ, phiW W g < 2 ^ g.length
  | [] => by simp [phiW]
  | x :: g => by
    have := phiW_lt W g
    rw [phiW, List.length_cons, pow_succ]
    split_ifs <;> omega

theorem pbT_succ_bot (x : ℕ) : ∀ n, pbT x (n + 1) = (x.testBit 0 ^^ pbT (x / 2) n)
  | 0 => by simp [pbT]
  | n + 1 => by
    rw [pbT, pbT_succ_bot x n, pbT, Nat.testBit_succ, Bool.xor_assoc]

theorem pbT_of_lt {x n : ℕ} (hx : x < 2 ^ n) : ∀ m, n ≤ m → pbT x m = pbT x n
  | 0, h => by rw [Nat.le_zero.1 h]
  | m + 1, h => by
    rcases Nat.eq_or_lt_of_le h with rfl | h'
    · rfl
    · rw [pbT, pbT_of_lt hx m (by omega),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right Nat.two_pos (by omega))),
        Bool.xor_false]

theorem testBit_pf (y s i : ℕ) : (pf y s).testBit i = (y.testBit i ^^ y.testBit (s + i)) := by
  simp only [pf]
  change (y ^^^ y >>> s).testBit i = _
  rw [Nat.testBit_xor, Nat.testBit_shiftRight]

theorem pbT_add (x a : ℕ) : ∀ b, pbT x (a + b) = (pbT x a ^^ pbT (x >>> a) b)
  | 0 => by simp [pbT]
  | b + 1 => by
    rw [← Nat.add_assoc, pbT, pbT_add x a b, pbT, Nat.testBit_shiftRight, Bool.xor_assoc]

theorem pbT_xor (a b : ℕ) : ∀ n, pbT (a ^^^ b) n = (pbT a n ^^ pbT b n)
  | 0 => rfl
  | n + 1 => by
    rw [pbT, pbT, pbT, pbT_xor a b n, Nat.testBit_xor]
    cases pbT a n <;> cases pbT b n <;> cases a.testBit n <;> cases b.testBit n <;> rfl

theorem pbT_pf (y s t : ℕ) (ht : t = s + s) : pbT (pf y s) s = pbT y t := by
  change pbT (y ^^^ y >>> s) s = _
  rw [pbT_xor, ht, pbT_add]

theorem par16_eq_pbT (x : ℕ) : par16 x = (pbT x 16).toNat := by
  have h1 : (pf (pf (pf (pf x 8) 4) 2) 1).testBit 0 = pbT x 16 := by
    have e1 : ∀ z : ℕ, z.testBit 0 = pbT z 1 := fun z => by simp [pbT]
    rw [e1, pbT_pf _ 1 2 rfl, pbT_pf _ 2 4 rfl, pbT_pf _ 4 8 rfl, pbT_pf _ 8 16 rfl]
  change pf (pf (pf (pf x 8) 4) 2) 1 &&& 1 = _
  rw [← h1, Nat.and_one_is_mod, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one (pf (pf (pf (pf x 8) 4) 2) 1) with h | h <;> simp [h]

theorem beq_land_one (c : ℕ) : Nat.beq (Nat.land c 1) 1 = c.testBit 0 := by
  rw [Nat.testBit_zero]
  change Nat.beq (c &&& 1) 1 = _
  rw [Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one c with h | h <;> rw [h] <;> rfl

theorem notMem_xor {M' W : Finset ℕ} (hW : XorClosed W) (hidx : IdxTwo M' W) {a b : ℕ}
    (ha : a ∈ M') (hb : b ∈ M') :
    decide (a ^^^ b ∉ W) = (decide (a ∉ W) ^^ decide (b ∉ W)) := by
  by_cases haW : a ∈ W <;> by_cases hbW : b ∈ W
  · simp [haW, hbW, hW.2 a haW b hbW]
  · have : a ^^^ b ∉ W := fun h => hbW (by
      have := hW.2 a haW _ h
      rwa [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at this)
    simp [haW, hbW, this]
  · have : a ^^^ b ∉ W := fun h => haW (by
      have := hW.2 _ h b hbW
      rwa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at this)
    simp [haW, hbW, this]
  · simp [haW, hbW, hidx a ha b hb haW hbW]

theorem and_div_two (a b : ℕ) : (a &&& b) / 2 = (a / 2) &&& (b / 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [← Nat.testBit_succ, Nat.testBit_and, Nat.testBit_and, ← Nat.testBit_succ, ← Nat.testBit_succ]

theorem lAct_notMem {M' W : Finset ℕ} (hM : XorClosed M') (hW : XorClosed W)
    (hidx : IdxTwo M' W) : ∀ g : List ℕ, (∀ x ∈ g, x ∈ M') → ∀ c,
      lAct g c ∈ M' ∧ decide (lAct g c ∉ W) = pbT (phiW W g &&& c) g.length
  | [], _, c => by
    refine ⟨hM.1, ?_⟩
    change decide ((0 : ℕ) ∉ W) = false
    simp [hW.1]
  | x :: g, hg, c => by
    obtain ⟨ht, hχ⟩ := lAct_notMem hM hW hidx g (fun y hy => hg y (List.mem_cons_of_mem _ hy))
      (Nat.shiftRight c 1)
    have hx : x ∈ M' := hg x (List.mem_cons_self ..)
    have hdef : lAct (x :: g) c = (if c.testBit 0 then x else 0) ^^^ lAct g (Nat.shiftRight c 1) := by
      change Nat.xor (bif Nat.beq (Nat.land c 1) 1 then x else 0) (lAct g (Nat.shiftRight c 1)) = _
      rw [beq_land_one]
      cases c.testBit 0 <;> rfl
    have hu : (if c.testBit 0 then x else 0) ∈ M' := by
      split_ifs
      · exact hx
      · exact hM.1
    have hχu : decide ((if c.testBit 0 then x else 0) ∉ W) = (c.testBit 0 && decide (x ∉ W)) := by
      cases c.testBit 0
      · simp [hW.1]
      · simp
    have hsh : Nat.shiftRight c 1 = c / 2 := by
      change c >>> 1 = c / 2
      rw [Nat.shiftRight_eq_div_pow, pow_one]
    have hφ0 : (phiW W (x :: g)).testBit 0 = decide (x ∉ W) := by
      rw [phiW, Nat.testBit_zero]
      split_ifs with h <;> simp [h] <;> omega
    have hφ2 : phiW W (x :: g) / 2 = phiW W g := by
      rw [phiW]
      split_ifs <;> omega
    refine ⟨by rw [hdef]; exact hM.2 _ hu _ ht, ?_⟩
    rw [hdef, notMem_xor hW hidx hu ht, hχu, hχ, List.length_cons, pbT_succ_bot, Nat.testBit_and,
      hφ0, and_div_two, hφ2, hsh, Bool.and_comm]

theorem lAct_mem_of_par16 {M' W : Finset ℕ} (hM : XorClosed M') (hW : XorClosed W)
    (hidx : IdxTwo M' W) {g : List ℕ} (hg : ∀ x ∈ g, x ∈ M') (hlen : g.length ≤ 16) {c : ℕ}
    (hc : par16 (phiW W g &&& c) = 0) : lAct g c ∈ W := by
  have hlt : phiW W g &&& c < 2 ^ g.length := by
    rw [Nat.land_comm]
    exact Nat.and_lt_two_pow _ (phiW_lt W g)
  rw [par16_eq_pbT, pbT_of_lt hlt 16 hlen, ← (lAct_notMem hM hW hidx g hg c).2] at hc
  by_contra h
  simp [h] at hc

theorem card_image_xor (W : Finset ℕ) (x : ℕ) : (W.image (x ^^^ ·)).card = W.card :=
  card_image_of_injective _ fun u v h => by
    have := congrArg (x ^^^ ·) h
    simpa [← Nat.xor_assoc] using this

theorem image_xor_subset {M' W : Finset ℕ} (hM : XorClosed M') (hWM : W ⊆ M') {x : ℕ}
    (hx : x ∈ M') : W.image (x ^^^ ·) ⊆ M' := by
  intro y hy
  obtain ⟨w, hw, rfl⟩ := mem_image.1 hy
  exact hM.2 x hx w (hWM hw)

theorem disjoint_image_xor {W : Finset ℕ} (hW : XorClosed W) {x y : ℕ} (hxy : x ^^^ y ∉ W) :
    Disjoint (W.image (x ^^^ ·)) (W.image (y ^^^ ·)) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  obtain ⟨w, hw, rfl⟩ := mem_image.1 hz
  obtain ⟨w', hw', hzw⟩ := mem_image.1 hz'
  have hy : y = x ^^^ w ^^^ w' := by
    rw [← hzw, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  have : x ^^^ y = w ^^^ w' := by
    rw [hy, ← Nat.xor_assoc, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  exact hxy (by rw [this]; exact hW.2 w hw w' hw')

theorem idxTwo_of_card {M' W : Finset ℕ} (hM : XorClosed M') (hW : XorClosed W) (hWM : W ⊆ M')
    (hcard : M'.card < 4 * W.card) : IdxTwo M' W := by
  intro a ha b hb haW hbW
  by_contra hab
  have hba : b ^^^ (a ^^^ b) = a := by
    rw [Nat.xor_comm a b, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  have hab' : a ^^^ (a ^^^ b) = b := by rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  have d01 := disjoint_image_xor hW (x := 0) (y := a) (by rwa [Nat.zero_xor])
  have d02 := disjoint_image_xor hW (x := 0) (y := b) (by rwa [Nat.zero_xor])
  have d03 := disjoint_image_xor hW (x := 0) (y := a ^^^ b) (by rwa [Nat.zero_xor])
  have d12 := disjoint_image_xor hW (x := a) (y := b) hab
  have d13 := disjoint_image_xor hW (x := a) (y := a ^^^ b) (by rwa [hab'])
  have d23 := disjoint_image_xor hW (x := b) (y := a ^^^ b) (by rwa [hba])
  have hsub : W.image (0 ^^^ ·) ∪ W.image (a ^^^ ·) ∪ W.image (b ^^^ ·) ∪
      W.image ((a ^^^ b) ^^^ ·) ⊆ M' :=
    union_subset (union_subset (union_subset (image_xor_subset hM hWM hM.1)
      (image_xor_subset hM hWM ha)) (image_xor_subset hM hWM hb))
      (image_xor_subset hM hWM (hM.2 a ha b hb))
  have hc := card_le_card hsub
  rw [card_union_of_disjoint (disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨d03, d13⟩, d23⟩),
    card_union_of_disjoint (disjoint_union_left.2 ⟨d02, d12⟩), card_union_of_disjoint d01,
    card_image_xor, card_image_xor, card_image_xor, card_image_xor] at hc
  omega

end CFSG.KC.P0Vis

end
