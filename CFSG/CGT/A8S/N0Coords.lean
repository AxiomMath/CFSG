module

public import CFSG.CGT.A8S.N0Aff
public import CFSG.CGT.T75JM.N6Basic

public section

namespace CFSG.CGT.A8S.N0

open CFSG.CGT.T75JM

@[expose] def codeV3 (v : Fin 3 → ZMod 2) : ℕ := (v 0).val + 2 * (v 1).val + 4 * (v 2).val

@[expose] def decodeV3 (n : ℕ) : Fin 3 → ZMod 2 := fun i => if n.testBit i.val then 1 else 0

theorem codeV3_lt (v : Fin 3 → ZMod 2) : codeV3 v < 8 := by
  revert v; decide

theorem decodeV3_codeV3 (v : Fin 3 → ZMod 2) : decodeV3 (codeV3 v) = v := by
  revert v; decide

theorem codeV3_decodeV3 {n : ℕ} (hn : n < 8) : codeV3 (decodeV3 n) = n := by
  interval_cases n <;> decide

theorem codeV3_add (u w : Fin 3 → ZMod 2) : codeV3 (u + w) = codeV3 u ^^^ codeV3 w := by
  revert u w; decide

variable {G : Type*} [Group G]

structure Coords3 (T : Subgroup G) where
  coord : T → ℕ
  lt : ∀ t, coord t < 8
  mul : ∀ a b, coord (a * b) = coord a ^^^ coord b
  inj : ∀ a b, coord a = coord b → a = b
  surj : ∀ n, n < 8 → ∃ t, coord t = n

def Coords3.ofEquiv {T : Subgroup G} (e : T ≃* Multiplicative (Fin 3 → ZMod 2)) :
    Coords3 T where
  coord t := codeV3 (Multiplicative.toAdd (e t))
  lt t := codeV3_lt _
  mul a b := by simp [codeV3_add]
  inj a b h := by
    apply e.injective
    have := congrArg decodeV3 h
    rw [decodeV3_codeV3, decodeV3_codeV3] at this
    exact Multiplicative.toAdd.injective this
  surj n hn := ⟨e.symm (Multiplicative.ofAdd (decodeV3 n)), by simp [codeV3_decodeV3 hn]⟩

theorem nonempty_coords3 {T : Subgroup G}
    (φ : T ≃* Multiplicative (Fin 3 → GaloisField 2 1)) : Nonempty (Coords3 T) := by
  let e0 : GaloisField 2 1 ≃+ ZMod 2 := (GaloisField.equivZmodP 2).toRingEquiv.toAddEquiv
  let e1 : (Fin 3 → GaloisField 2 1) ≃+ (Fin 3 → ZMod 2) := AddEquiv.piCongrRight fun _ => e0
  exact ⟨Coords3.ofEquiv (φ.trans (AddEquiv.toMultiplicative e1))⟩

section Basic

variable {T : Subgroup G} (c : Coords3 T)

include c

@[expose] noncomputable def tOf3 (n : ℕ) : T :=
  if h : n < 8 then Classical.choose (c.surj n h) else 1

theorem coord_tOf3 {n : ℕ} (hn : n < 8) : c.coord (tOf3 c n) = n := by
  simp only [tOf3, hn, dite_true]
  exact Classical.choose_spec (c.surj n hn)

theorem coord_one3 : c.coord (1 : T) = 0 := by
  have h := c.mul 1 1
  rw [one_mul, Nat.xor_self] at h
  exact h

theorem tOf3_zero : tOf3 c 0 = 1 := by
  apply c.inj
  rw [coord_tOf3 c (by norm_num), coord_one3]

theorem coord_sq3 (a : T) : a * a = 1 := by
  apply c.inj
  rw [c.mul, coord_one3, Nat.xor_self]

theorem decomp3 (t : T) :
    t = (tOf3 c (if (c.coord t).testBit 0 then 1 else 0) *
        tOf3 c (if (c.coord t).testBit 1 then 2 else 0)) *
      tOf3 c (if (c.coord t).testBit 2 then 4 else 0) := by
  apply c.inj
  have h1 : ∀ b : Bool, ∀ n : ℕ, n < 8 →
      c.coord (tOf3 c (if b then n else 0)) = if b then n else 0 :=
    fun b n hn => by cases b <;> simp [coord_tOf3 c hn, tOf3_zero c, coord_one3 c]
  rw [c.mul, c.mul, h1 _ _ (by norm_num), h1 _ _ (by norm_num), h1 _ _ (by norm_num)]
  exact vec_eq3 (c.lt t)

end Basic

section Cols

variable {T : Subgroup G} (c : Coords3 T)

@[expose] noncomputable def colsOf3 (g : Subgroup.normalizer (T : Set G)) : Cols3 :=
  ⟨c.coord (ctr g (tOf3 c 1)), c.coord (ctr g (tOf3 c 2)), c.coord (ctr g (tOf3 c 4))⟩

theorem coord_ctr3 (g : Subgroup.normalizer (T : Set G)) (t : T) :
    c.coord (ctr g t) = applyC3 (colsOf3 c g) (c.coord t) := by
  have key : ∀ (b : Bool) (n : ℕ), c.coord (ctr g (tOf3 c (if b then n else 0))) =
      if b then c.coord (ctr g (tOf3 c n)) else 0 := by
    intro b n; cases b <;> simp [tOf3_zero c, ctr_one_elem, coord_one3 c]
  conv_lhs => rw [decomp3 c t]
  rw [ctr_mul_apply, ctr_mul_apply, c.mul, c.mul, key, key, key, applyC3_eq_ite]
  rfl

theorem colsOf3_mul (g h : Subgroup.normalizer (T : Set G)) :
    colsOf3 c (g * h) = compC3 (colsOf3 c g) (colsOf3 c h) := by
  have h1 : ∀ n, c.coord (ctr (g * h) (tOf3 c n)) =
      applyC3 (colsOf3 c g) (c.coord (ctr h (tOf3 c n))) := by
    intro n; rw [ctr_mul, coord_ctr3]
  show Cols3.mk _ _ _ = Cols3.mk _ _ _
  rw [h1 1, h1 2, h1 4]
  rfl

theorem colsOf3_one : colsOf3 c (1 : Subgroup.normalizer (T : Set G)) = idC3 := by
  show Cols3.mk _ _ _ = Cols3.mk _ _ _
  simp only [ctr_one, coord_tOf3 c (show 1 < 8 by norm_num),
    coord_tOf3 c (show 2 < 8 by norm_num), coord_tOf3 c (show 4 < 8 by norm_num)]

theorem commute_of_colsOf3 (g : Subgroup.normalizer (T : Set G)) (h : colsOf3 c g = idC3)
    (t : T) : (g : G) * t = t * g := by
  have : ctr g t = t := by
    apply c.inj
    rw [coord_ctr3, h, applyC3_idC3 (c.lt t)]
  have h2 : (g : G) * t * (g : G)⁻¹ = t := congrArg Subtype.val this
  calc (g : G) * t = ((g : G) * t * (g : G)⁻¹) * g := by group
    _ = t * g := by rw [h2]

theorem colsOf3_lt (g : Subgroup.normalizer (T : Set G)) (j : Fin 3) :
    (colsOf3 c g).col j < 8 := by
  fin_cases j <;> exact c.lt _

end Cols

end CFSG.CGT.A8S.N0
