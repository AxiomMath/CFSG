module

public import CFSG.CGT.T75JM.N6Cols
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.CGT.T75JM

@[expose] def codeV (v : Fin 4 → ZMod 2) : ℕ :=
  (v 0).val + 2 * (v 1).val + 4 * (v 2).val + 8 * (v 3).val

@[expose] def decodeV (n : ℕ) : Fin 4 → ZMod 2 := fun i => if n.testBit i.val then 1 else 0

theorem codeV_lt (v : Fin 4 → ZMod 2) : codeV v < 16 := by
  revert v; decide

theorem decodeV_codeV (v : Fin 4 → ZMod 2) : decodeV (codeV v) = v := by
  revert v; decide

theorem codeV_decodeV {n : ℕ} (hn : n < 16) : codeV (decodeV n) = n := by
  interval_cases n <;> decide

theorem codeV_add (u w : Fin 4 → ZMod 2) : codeV (u + w) = codeV u ^^^ codeV w := by
  revert u w; decide

theorem codeV_zero : codeV 0 = 0 := by decide

variable {G : Type*} [Group G]

structure Coords (T : Subgroup G) where
  coord : T → ℕ
  lt : ∀ t, coord t < 16
  mul : ∀ a b, coord (a * b) = coord a ^^^ coord b
  inj : ∀ a b, coord a = coord b → a = b
  surj : ∀ n, n < 16 → ∃ t, coord t = n

namespace Coords

variable {T : Subgroup G}

def ofEquiv (e : T ≃* Multiplicative (Fin 4 → ZMod 2)) : Coords T where
  coord t := codeV (Multiplicative.toAdd (e t))
  lt t := codeV_lt _
  mul a b := by simp [codeV_add]
  inj a b h := by
    apply e.injective
    have := congrArg decodeV h
    rw [decodeV_codeV, decodeV_codeV] at this
    exact Multiplicative.toAdd.injective this
  surj n hn := ⟨e.symm (Multiplicative.ofAdd (decodeV n)), by simp [codeV_decodeV hn]⟩

def change (c : Coords T) (Q Qi : Cols) (hQ : ∀ i, Q.col i < 16) (hQi : ∀ i, Qi.col i < 16)
    (h1 : ∀ v, v < 16 → applyC Qi (applyC Q v) = v)
    (h2 : ∀ v, v < 16 → applyC Q (applyC Qi v) = v) : Coords T where
  coord t := applyC Qi (c.coord t)
  lt t := applyC_lt hQi _
  mul a b := by rw [c.mul, applyC_xor]
  inj a b h := by
    apply c.inj
    have := congrArg (applyC Q) h
    rwa [h2 _ (c.lt a), h2 _ (c.lt b)] at this
  surj n hn := by
    obtain ⟨t, ht⟩ := c.surj (applyC Q n) (applyC_lt hQ n)
    exact ⟨t, by simp only [ht, h1 n hn]⟩

end Coords

section Basic

variable {T : Subgroup G} (c : Coords T)

include c

@[expose] noncomputable def tOf (n : ℕ) : T :=
  if h : n < 16 then Classical.choose (c.surj n h) else 1

theorem coord_tOf {n : ℕ} (hn : n < 16) : c.coord (tOf c n) = n := by
  simp only [tOf, hn, dite_true]
  exact Classical.choose_spec (c.surj n hn)

theorem tOf_coord (t : T) : tOf c (c.coord t) = t :=
  c.inj _ _ (coord_tOf c (c.lt t))

theorem coord_one : c.coord (1 : T) = 0 := by
  have h := c.mul 1 1
  rw [one_mul, Nat.xor_self] at h
  exact h

theorem tOf_zero : tOf c 0 = 1 := by
  apply c.inj
  rw [coord_tOf c (by norm_num), coord_one]

theorem coord_sq (a : T) : a * a = 1 := by
  apply c.inj
  rw [c.mul, coord_one, Nat.xor_self]

theorem mul_comm_T (a b : T) : a * b = b * a := by
  apply c.inj
  rw [c.mul, c.mul, Nat.xor_comm]

theorem decomp (t : T) :
    t = (tOf c (if (c.coord t).testBit 0 then 1 else 0) *
        tOf c (if (c.coord t).testBit 1 then 2 else 0)) *
      (tOf c (if (c.coord t).testBit 2 then 4 else 0) *
        tOf c (if (c.coord t).testBit 3 then 8 else 0)) := by
  apply c.inj
  have h1 : ∀ b : Bool, ∀ n : ℕ, n < 16 →
      c.coord (tOf c (if b then n else 0)) = if b then n else 0 :=
    fun b n hn => by cases b <;> simp [coord_tOf c hn, tOf_zero c, coord_one c]
  rw [c.mul, c.mul, c.mul, h1 _ _ (by norm_num), h1 _ _ (by norm_num),
    h1 _ _ (by norm_num), h1 _ _ (by norm_num)]
  exact vec_eq (c.lt t)

end Basic

section Action

variable {T : Subgroup G}

@[expose] def ctr (g : Subgroup.normalizer (T : Set G)) (t : T) : T :=
  ⟨(g : G) * t * (g : G)⁻¹, (Subgroup.mem_set_normalizer_iff.1 g.2 t).1 t.2⟩

theorem ctr_mul_apply (g : Subgroup.normalizer (T : Set G)) (a b : T) :
    ctr g (a * b) = ctr g a * ctr g b := by
  apply Subtype.ext
  simp [ctr, mul_assoc]

theorem ctr_mul (g h : Subgroup.normalizer (T : Set G)) (t : T) :
    ctr (g * h) t = ctr g (ctr h t) := by
  apply Subtype.ext
  simp [ctr, mul_assoc]

theorem ctr_one (t : T) : ctr (1 : Subgroup.normalizer (T : Set G)) t = t := by
  apply Subtype.ext
  simp [ctr]

theorem ctr_one_elem (g : Subgroup.normalizer (T : Set G)) : ctr g (1 : T) = 1 := by
  apply Subtype.ext
  simp [ctr]

end Action

section Cols

variable {T : Subgroup G} (c : Coords T)

@[expose] noncomputable def colsOf (g : Subgroup.normalizer (T : Set G)) : Cols :=
  ⟨c.coord (ctr g (tOf c 1)), c.coord (ctr g (tOf c 2)), c.coord (ctr g (tOf c 4)),
    c.coord (ctr g (tOf c 8))⟩

theorem coord_ctr (g : Subgroup.normalizer (T : Set G)) (t : T) :
    c.coord (ctr g t) = applyC (colsOf c g) (c.coord t) := by
  have key : ∀ (b : Bool) (n : ℕ), c.coord (ctr g (tOf c (if b then n else 0))) =
      if b then c.coord (ctr g (tOf c n)) else 0 := by
    intro b n; cases b <;> simp [tOf_zero c, ctr_one_elem, coord_one c]
  conv_lhs => rw [decomp c t]
  rw [ctr_mul_apply, ctr_mul_apply, ctr_mul_apply, c.mul, c.mul, c.mul, key, key, key, key]
  unfold applyC colsOf
  simp only [Nat.xor_assoc]

theorem colsOf_mul (g h : Subgroup.normalizer (T : Set G)) :
    colsOf c (g * h) = compC (colsOf c g) (colsOf c h) := by
  have h1 : ∀ n, c.coord (ctr (g * h) (tOf c n)) =
      applyC (colsOf c g) (c.coord (ctr h (tOf c n))) := by
    intro n; rw [ctr_mul, coord_ctr]
  show Cols.mk _ _ _ _ = Cols.mk _ _ _ _
  rw [h1 1, h1 2, h1 4, h1 8]
  rfl

theorem colsOf_one : colsOf c (1 : Subgroup.normalizer (T : Set G)) = idC := by
  show Cols.mk _ _ _ _ = Cols.mk _ _ _ _
  simp only [ctr_one, coord_tOf c (show 1 < 16 by norm_num), coord_tOf c (show 2 < 16 by norm_num),
    coord_tOf c (show 4 < 16 by norm_num), coord_tOf c (show 8 < 16 by norm_num)]

theorem colsOf_pow (g : Subgroup.normalizer (T : Set G)) (n : ℕ) :
    colsOf c (g ^ n) = powC (colsOf c g) n := by
  induction n with
  | zero => simpa [powC] using colsOf_one c
  | succ n ih => rw [pow_succ', colsOf_mul, ih]; rfl

theorem colsOf_of_mem (g : Subgroup.normalizer (T : Set G)) (hg : (g : G) ∈ T) :
    colsOf c g = idC := by
  have h : ∀ t : T, ctr g t = t := by
    intro t
    apply Subtype.ext
    have := mul_comm_T c ⟨(g : G), hg⟩ t
    have h2 : (g : G) * t = t * g := congrArg Subtype.val this
    simp [ctr, h2]
  show Cols.mk _ _ _ _ = Cols.mk _ _ _ _
  simp only [h, coord_tOf c (show 1 < 16 by norm_num), coord_tOf c (show 2 < 16 by norm_num),
    coord_tOf c (show 4 < 16 by norm_num), coord_tOf c (show 8 < 16 by norm_num)]

theorem commute_of_colsOf (g : Subgroup.normalizer (T : Set G)) (h : colsOf c g = idC) (t : T) :
    (g : G) * t = t * g := by
  have : ctr g t = t := by
    apply c.inj
    rw [coord_ctr, h, applyC_idC (c.lt t)]
  have h2 : (g : G) * t * (g : G)⁻¹ = t := congrArg Subtype.val this
  calc (g : G) * t = ((g : G) * t * (g : G)⁻¹) * g := by group
    _ = t * g := by rw [h2]

theorem colsOf_change (Q Qi : Cols) (hQ : ∀ i, Q.col i < 16) (hQi : ∀ i, Qi.col i < 16)
    (h1 : ∀ v, v < 16 → applyC Qi (applyC Q v) = v)
    (h2 : ∀ v, v < 16 → applyC Q (applyC Qi v) = v) (g : Subgroup.normalizer (T : Set G))
    (v : ℕ) (hv : v < 16) :
    applyC (colsOf (c.change Q Qi hQ hQi h1 h2) g) v =
      applyC Qi (applyC (colsOf c g) (applyC Q v)) := by
  set c' := c.change Q Qi hQ hQi h1 h2 with hc'
  have e1 : c'.coord (tOf c' v) = v := coord_tOf c' hv
  have e1' : applyC Qi (c.coord (tOf c' v)) = v := e1
  have e2 : c.coord (tOf c' v) = applyC Q v := by
    have := congrArg (applyC Q) e1'
    rwa [h2 _ (c.lt _)] at this
  have e3 : applyC (colsOf c' g) v = c'.coord (ctr g (tOf c' v)) := by
    rw [coord_ctr c', e1]
  rw [e3]
  show applyC Qi (c.coord (ctr g (tOf c' v))) = _
  rw [coord_ctr c, e2]

end Cols

end CFSG.CGT.T75JM
