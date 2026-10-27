module

public import CFSG.LieType.Universal.Unitary.Basic
public import Mathlib.Algebra.Group.Pi.Units

public section

namespace CFSG.ClassicalGroups.SUnThreeLocal

open Matrix CFSG.LieType.Universal.Unitary

variable {L : Type} [Field L] {n : ℕ}

structure FixedCubeRoot (σ : L ≃+* L) where
  ω : Lˣ
  pow_three : ω ^ 3 = 1
  ne_one : ω ≠ 1
  map_eq : σ (ω : L) = ω

namespace FixedCubeRoot

variable {σ : L ≃+* L} (ζ : FixedCubeRoot σ)

@[expose] def pow (k : ZMod 3) : Lˣ := ζ.ω ^ k.val

theorem pow_add (a b : ZMod 3) : ζ.pow (a + b) = ζ.pow a * ζ.pow b := by
  unfold pow
  rw [← _root_.pow_add, ZMod.val_add]
  exact (_root_.pow_eq_pow_mod _ ζ.pow_three).symm

theorem pow_zero : ζ.pow 0 = 1 := by simp [pow]

theorem pow_eq_one_iff (k : ZMod 3) : ζ.pow k = 1 ↔ k = 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have horder : orderOf ζ.ω = 3 := orderOf_eq_prime ζ.pow_three ζ.ne_one
  rw [pow, ← orderOf_dvd_iff_pow_eq_one, horder]
  exact ⟨fun h => (ZMod.val_eq_zero k).mp (Nat.eq_zero_of_dvd_of_lt h (ZMod.val_lt k)),
    fun h => by subst h; simp⟩

@[expose] def powHom : Multiplicative (ZMod 3) →* Lˣ where
  toFun k := ζ.pow (Multiplicative.toAdd k)
  map_one' := ζ.pow_zero
  map_mul' a b := ζ.pow_add _ _

theorem map_pow_eq (k : ZMod 3) : σ ((ζ.pow k : Lˣ) : L) = (ζ.pow k : Lˣ) := by
  rw [pow, Units.val_pow_eq_pow_val, map_pow, ζ.map_eq]

theorem exists_of_card [Finite L] {q : ℕ} (hq : q % 3 = 1) (hL : Nat.card L = q ^ 2)
    (hσ : ∀ c, σ c = c ^ q) : Nonempty (FixedCubeRoot σ) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq1 : 1 ≤ q := by omega
  have h3 : 3 ∣ Nat.card Lˣ := by
    rw [Nat.card_units, hL]
    obtain ⟨m, hm⟩ : 3 ∣ q - 1 := by omega
    obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    subst hk
    refine ⟨m * (k + 1 + 1), ?_⟩
    simp only [Nat.add_sub_cancel] at hm
    have : (k + 1) ^ 2 - 1 = k * (k + 2) := by
      rw [show (k + 1) ^ 2 = k * (k + 2) + 1 by ring, Nat.add_sub_cancel]
    rw [this, hm]
    ring
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Lˣ) 3 h3
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  refine ⟨⟨ω, hω3, ?_, ?_⟩⟩
  · intro h1
    rw [h1, orderOf_one] at hω
    exact absurd hω (by norm_num)
  · rw [hσ, ← Units.val_pow_eq_pow_val, _root_.pow_eq_pow_mod _ hω3, hq, pow_one]

end FixedCubeRoot

@[expose] def wt (n : ℕ) (v : Fin 3 → ZMod 3) (a : Fin n) : ZMod 3 :=
  if h : a.val < 3 then v ⟨a.val, h⟩
  else if h' : n ≤ a.val + 3 then -v ⟨n - 1 - a.val, by have := a.isLt; omega⟩ else 0

theorem wt_add (v w : Fin 3 → ZMod 3) (a : Fin n) : wt n (v + w) a = wt n v a + wt n w a := by
  unfold wt
  split_ifs <;> simp [neg_add] <;> abel

theorem wt_zero (a : Fin n) : wt n (0 : Fin 3 → ZMod 3) a = 0 := by
  unfold wt
  split_ifs <;> simp

theorem wt_rev (h6 : 6 ≤ n) (v : Fin 3 → ZMod 3) (a : Fin n) :
    wt n v (Fin.rev a) = - wt n v a := by
  have ha := a.isLt
  unfold wt
  simp only [Fin.val_rev]
  by_cases h1 : a.val < 3
  · have h2 : ¬ n - (a.val + 1) < 3 := by omega
    have h3 : n ≤ n - (a.val + 1) + 3 := by omega
    rw [dif_neg h2, dif_pos h3, dif_pos h1]
    exact congrArg (fun x : Fin 3 => -v x) (Fin.ext (by simp only; omega))
  · by_cases h2 : n ≤ a.val + 3
    · have h3 : n - (a.val + 1) < 3 := by omega
      rw [dif_pos h3, dif_neg h1, dif_pos h2, neg_neg]
      exact congrArg v (Fin.ext (by simp only; omega))
    · have h3 : ¬ n - (a.val + 1) < 3 := by omega
      have h4 : ¬ n ≤ n - (a.val + 1) + 3 := by omega
      rw [dif_neg h3, dif_neg h4, dif_neg h1, dif_neg h2, neg_zero]

theorem sum_wt (h6 : 6 ≤ n) (v : Fin 3 → ZMod 3) : ∑ a, wt n v a = 0 := by
  have h1 : ∑ a, wt n v a = ∑ a, wt n v (Fin.rev a) :=
    (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin n)) (fun a => wt n v a)).symm
  simp only [wt_rev h6, Finset.sum_neg_distrib] at h1
  revert h1
  generalize ∑ a, wt n v a = S
  revert S
  decide

@[expose] def pos (hn : n = 6 ∨ n = 7) (i : Fin 3) : Fin n := ⟨i.val, by omega⟩

theorem wt_pos (hn : n = 6 ∨ n = 7) (v : Fin 3 → ZMod 3) (i : Fin 3) :
    wt n v (pos hn i) = v i := by
  simp [wt, pos]

theorem wt_neg (hn : n = 6 ∨ n = 7) (v : Fin 3 → ZMod 3) (i : Fin 3) :
    wt n v (Fin.rev (pos hn i)) = - v i := by
  rw [wt_rev (by omega), wt_pos]

theorem pos_injective (hn : n = 6 ∨ n = 7) : Function.Injective (pos hn) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simpa [pos] using this

theorem rev_pos_injective (hn : n = 6 ∨ n = 7) :
    Function.Injective (fun i => Fin.rev (pos hn i)) := fun _ _ h =>
  pos_injective hn (Fin.rev_injective h)

theorem pos_ne_rev_pos (hn : n = 6 ∨ n = 7) (i j : Fin 3) : pos hn i ≠ Fin.rev (pos hn j) := by
  intro h
  have := congrArg Fin.val h
  have hi := i.isLt
  have hj := j.isLt
  simp only [pos, Fin.val_rev] at this
  omega

theorem rev_pos_ne_pos (hn : n = 6 ∨ n = 7) (i j : Fin 3) : Fin.rev (pos hn i) ≠ pos hn j :=
  (pos_ne_rev_pos hn j i).symm

theorem pos_cases (hn : n = 6 ∨ n = 7) (a : Fin n) :
    (∃ i, a = pos hn i) ∨ (∃ i, a = Fin.rev (pos hn i)) ∨ (3 ≤ a.val ∧ a.val + 3 < n) := by
  have ha := a.isLt
  by_cases h1 : a.val < 3
  · exact Or.inl ⟨⟨a.val, h1⟩, Fin.ext rfl⟩
  · by_cases h2 : n ≤ a.val + 3
    · refine Or.inr (Or.inl ⟨⟨n - 1 - a.val, by omega⟩, Fin.ext ?_⟩)
      simp only [pos, Fin.val_rev]
      omega
    · exact Or.inr (Or.inr ⟨by omega, by omega⟩)

theorem wt_eq_zero_of_mid (v : Fin 3 → ZMod 3) {a : Fin n} (h1 : 3 ≤ a.val)
    (h2 : a.val + 3 < n) : wt n v a = 0 := by
  unfold wt
  rw [dif_neg (by omega), dif_neg (by omega)]

theorem wt_ne_zero_of {v v' : Fin 3 → ZMod 3} (hv : ∀ i, v i ≠ 0) {a : Fin n}
    (h : wt n v' a ≠ 0) : wt n v a ≠ 0 := by
  unfold wt at h ⊢
  split_ifs at h ⊢ with h1 h2
  · exact hv _
  · exact neg_ne_zero.mpr (hv _)
  · exact absurd rfl h

variable (L n) in
@[expose] def diagGL : (Fin n → Lˣ) →* GL (Fin n) L :=
  (Units.map (Matrix.diagonalRingHom (Fin n) L).toMonoidHom).comp
    (MulEquiv.piUnits (M := fun _ : Fin n => L)).symm.toMonoidHom

theorem coe_diagGL (d : Fin n → Lˣ) :
    ((diagGL L n d : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal fun a => (d a : L) :=
  rfl

theorem diagGL_injective : Function.Injective (diagGL L n) := by
  intro d d' h
  funext a
  apply Units.ext
  have h1 := congrArg (fun g : GL (Fin n) L => (g : Matrix (Fin n) (Fin n) L) a a) h
  simpa [coe_diagGL] using h1

theorem det_diagGL (d : Fin n → Lˣ) :
    ((diagGL L n d : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).det = ∏ a, (d a : L) := by
  rw [coe_diagGL, Matrix.det_diagonal]

theorem conjTr_diagGL_mul_antidiag_mul {σ : L ≃+* L} (d : Fin n → Lˣ)
    (h1 : ∀ a, σ (d a : L) * (d (Fin.rev a) : L) = 1) :
    conjTr σ ((diagGL L n d : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * antidiag n *
      ((diagGL L n d : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = antidiag n := by
  rw [coe_diagGL, conjTr, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hb : b = Fin.rev a
  · subst hb
    simp only [antidiag, Matrix.of_apply, if_true, mul_one]
    exact h1 a
  · simp [antidiag, hb]

theorem diagGL_mem_SU {σ : L ≃+* L} (d : Fin n → Lˣ)
    (h1 : ∀ a, σ (d a : L) * (d (Fin.rev a) : L) = 1) (h2 : ∏ a, d a = 1) :
    diagGL L n d ∈ SU σ n := by
  refine ⟨?_, conjTr_diagGL_mul_antidiag_mul d h1⟩
  rw [det_diagGL, ← Units.coe_prod, h2]
  rfl

variable {σ : L ≃+* L} (ζ : FixedCubeRoot σ)

theorem diagGL_pow_wt_mem (hn : n = 6 ∨ n = 7) (v : Fin 3 → ZMod 3) :
    diagGL L n (fun a => ζ.pow (wt n v a)) ∈ SU σ n := by
  apply diagGL_mem_SU
  · intro a
    rw [ζ.map_pow_eq, ← Units.val_mul, ← ζ.pow_add, wt_rev (by omega), add_neg_cancel,
      ζ.pow_zero]
    rfl
  · calc ∏ a, ζ.pow (wt n v a) = ∏ a, ζ.powHom (Multiplicative.ofAdd (wt n v a)) := rfl
      _ = ζ.powHom (∏ a, Multiplicative.ofAdd (wt n v a)) := (map_prod _ _ _).symm
      _ = ζ.powHom (Multiplicative.ofAdd (∑ a, wt n v a)) := by rw [ofAdd_sum]
      _ = 1 := by rw [sum_wt (by omega)]; exact ζ.pow_zero

@[expose] def c₀ (hn : n = 6 ∨ n = 7) : Multiplicative (Fin 3 → ZMod 3) →* SU σ n where
  toFun v := ⟨diagGL L n fun a => ζ.pow (wt n (Multiplicative.toAdd v) a),
    diagGL_pow_wt_mem ζ hn _⟩
  map_one' := Subtype.ext (by
    show diagGL L n _ = 1
    rw [← map_one (diagGL L n)]
    congr 1
    funext a
    simp [wt_zero, ζ.pow_zero])
  map_mul' v w := Subtype.ext (by
    show diagGL L n _ = diagGL L n _ * diagGL L n _
    rw [← map_mul]
    congr 1
    funext a
    simp [toAdd_mul, wt_add, ζ.pow_add])

theorem coe_c₀ (hn : n = 6 ∨ n = 7) (v : Multiplicative (Fin 3 → ZMod 3)) :
    ((c₀ ζ hn v : SU σ n) : GL (Fin n) L) =
      diagGL L n fun a => ζ.pow (wt n (Multiplicative.toAdd v) a) :=
  rfl

theorem FixedCubeRoot.pow_injective : Function.Injective ζ.pow := by
  intro x y h
  have h1 : ζ.pow y * ζ.pow (x - y) = ζ.pow y * 1 := by
    rw [← ζ.pow_add, mul_one, ← h]
    congr 1
    ring
  exact sub_eq_zero.mp ((ζ.pow_eq_one_iff _).mp (mul_left_cancel h1))

theorem c₀_injective (hn : n = 6 ∨ n = 7) : Function.Injective (c₀ ζ hn) := by
  intro v w h
  have h1 := congrArg (fun g : SU σ n => (g : GL (Fin n) L)) h
  simp only [coe_c₀] at h1
  have h2 := diagGL_injective h1
  apply Multiplicative.toAdd.injective
  funext i
  have h3 := congrFun h2 (pos hn i)
  simp only [wt_pos] at h3
  exact ζ.pow_injective h3

theorem c₀_mulVec_eq_self_iff (hn : n = 6 ∨ n = 7) (v : Multiplicative (Fin 3 → ZMod 3))
    (w : Fin n → L) :
    ((c₀ ζ hn v : SU σ n) : GL (Fin n) L).val *ᵥ w = w ↔
      ∀ a, wt n (Multiplicative.toAdd v) a = 0 ∨ w a = 0 := by
  change Matrix.diagonal (fun a => ((ζ.pow (wt n (Multiplicative.toAdd v) a) : Lˣ) : L)) *ᵥ w = w
    ↔ _
  constructor
  · intro h a
    have h1 := congrFun h a
    rw [Matrix.mulVec_diagonal] at h1
    by_cases hw : w a = 0
    · exact Or.inr hw
    · left
      have h2 : ((ζ.pow (wt n (Multiplicative.toAdd v) a) : Lˣ) : L) = 1 :=
        mul_right_cancel₀ hw (h1.trans (one_mul _).symm)
      exact (ζ.pow_eq_one_iff _).mp (Units.val_eq_one.mp h2)
  · intro h
    funext a
    rw [Matrix.mulVec_diagonal]
    rcases h a with h0 | h0
    · rw [h0, ζ.pow_zero]
      simp
    · rw [h0, mul_zero]

theorem fix_iff (hn : n = 6 ∨ n = 7) (v : Multiplicative (Fin 3 → ZMod 3)) :
    {w : Fin n → L | ((c₀ ζ hn v : SU σ n) : GL (Fin n) L).val *ᵥ w = w} =
        {w : Fin n → L | ∀ v' : Multiplicative (Fin 3 → ZMod 3),
          ((c₀ ζ hn v' : SU σ n) : GL (Fin n) L).val *ᵥ w = w} ↔
      ∀ i, Multiplicative.toAdd v i ≠ 0 := by
  constructor
  · intro h i hi
    have hw1 : (Pi.single (pos hn i) 1 : Fin n → L) ∈
        {w : Fin n → L | ((c₀ ζ hn v : SU σ n) : GL (Fin n) L).val *ᵥ w = w} := by
      rw [Set.mem_setOf_eq, c₀_mulVec_eq_self_iff]
      intro a
      by_cases ha : a = pos hn i
      · subst ha
        left
        rw [wt_pos]
        exact hi
      · right
        simp [Pi.single_apply, ha]
    rw [h] at hw1
    have h2 := hw1 (Multiplicative.ofAdd (Pi.single i 1))
    rw [c₀_mulVec_eq_self_iff] at h2
    rcases h2 (pos hn i) with h3 | h3
    · rw [toAdd_ofAdd, wt_pos] at h3
      simp at h3
    · simp at h3
  · intro h
    ext w
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hw v'
      rw [c₀_mulVec_eq_self_iff] at hw ⊢
      intro a
      rcases eq_or_ne (wt n (Multiplicative.toAdd v') a) 0 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ((hw a).resolve_left (wt_ne_zero_of h h0))
    · intro hw
      exact hw v

end CFSG.ClassicalGroups.SUnThreeLocal
