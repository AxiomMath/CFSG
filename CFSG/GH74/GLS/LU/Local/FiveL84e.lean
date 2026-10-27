module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.GH74.GLS.LU.Local.Five

namespace WeightsCore

structure Mat where
  a : ZMod 4
  b : ZMod 4
  c : ZMod 4
  d : ZMod 4
  deriving DecidableEq

def Mat.mul (M N : Mat) : Mat :=
  ⟨M.a * N.a + M.b * N.c, M.a * N.b + M.b * N.d, M.c * N.a + M.d * N.c, M.c * N.b + M.d * N.d⟩

def Mat.one : Mat := ⟨1, 0, 0, 1⟩

def Mat.apply (M : Mat) (v : ZMod 4 × ZMod 4) : ZMod 4 × ZMod 4 :=
  (M.a * v.1 + M.b * v.2, M.c * v.1 + M.d * v.2)

def Mat.rowmul (r : ZMod 4 × ZMod 4) (M : Mat) : ZMod 4 × ZMod 4 :=
  (r.1 * M.a + r.2 * M.c, r.1 * M.b + r.2 * M.d)

def dot (r v : ZMod 4 × ZMod 4) : ZMod 4 := r.1 * v.1 + r.2 * v.2

theorem fin_core_aux : ∀ a b c d : ZMod 4, Mat.mul ⟨a, b, c, d⟩ ⟨a, b, c, d⟩ = Mat.one →
    ∀ a' b' c' d' : ZMod 4,
      Mat.mul (Mat.mul ⟨a', b', c', d'⟩ ⟨a, b, c, d⟩)
        (Mat.mul (Mat.mul ⟨a', b', c', d'⟩ ⟨a, b, c, d⟩) (Mat.mul ⟨a', b', c', d'⟩ ⟨a, b, c, d⟩))
        = Mat.one →
      ∀ r1 r2 : ZMod 4,
        Mat.rowmul (Mat.rowmul (r1, r2) ⟨a', b', c', d'⟩) ⟨a, b, c, d⟩ + (r1, r2)
            = Mat.rowmul (r1, r2) ⟨a', b', c', d'⟩ →
        Mat.rowmul (Mat.rowmul (r1, r2) ⟨a', b', c', d'⟩) ⟨a', b', c', d'⟩ = (r1, r2) := by
  decide +kernel

theorem fin_core (A B : Mat) (r : ZMod 4 × ZMod 4) (hB : B.mul B = Mat.one)
    (hA : (A.mul B).mul ((A.mul B).mul (A.mul B)) = Mat.one)
    (hK : Mat.rowmul (Mat.rowmul r A) B + r = Mat.rowmul r A) :
    Mat.rowmul (Mat.rowmul r A) A = r := by
  obtain ⟨a, b, c, d⟩ := B
  obtain ⟨a', b', c', d'⟩ := A
  obtain ⟨r1, r2⟩ := r
  exact fin_core_aux a b c d hB a' b' c' d' hA r1 r2 hK

abbrev H0 : Type := Multiplicative (ZMod 4) × Multiplicative (ZMod 4)

@[expose] def toH (v : ZMod 4 × ZMod 4) : H0 :=
  (Multiplicative.ofAdd v.1, Multiplicative.ofAdd v.2)

@[expose] def coord (h : H0) : ZMod 4 × ZMod 4 :=
  (Multiplicative.toAdd h.1, Multiplicative.toAdd h.2)

@[simp] theorem coord_toH (v : ZMod 4 × ZMod 4) : coord (toH v) = v := rfl

@[simp] theorem toH_coord (h : H0) : toH (coord h) = h := rfl

theorem toH_add (v w : ZMod 4 × ZMod 4) : toH (v + w) = toH v * toH w := rfl

theorem coord_mul (h h' : H0) : coord (h * h') = coord h + coord h' := rfl

def lin (f : H0 →* H0) : (ZMod 4 × ZMod 4) →+ (ZMod 4 × ZMod 4) :=
  AddMonoidHom.mk' (fun v => coord (f (toH v)))
    (fun v w => by simp only [toH_add, map_mul, coord_mul])

def toM (f : H0 →* H0) : Mat :=
  ⟨(lin f (1, 0)).1, (lin f (0, 1)).1, (lin f (1, 0)).2, (lin f (0, 1)).2⟩

theorem vec_decomp (v : ZMod 4 × ZMod 4) :
    v = v.1.val • ((1 : ZMod 4), (0 : ZMod 4)) + v.2.val • ((0 : ZMod 4), (1 : ZMod 4)) := by
  ext <;> simp

theorem lin_eq (f : H0 →* H0) (v : ZMod 4 × ZMod 4) : lin f v = (toM f).apply v := by
  conv_lhs => rw [vec_decomp v, map_add, map_nsmul, map_nsmul]
  ext <;> simp [Mat.apply, toM, nsmul_eq_mul, mul_comm]

theorem toH_inj {v w : ZMod 4 × ZMod 4} (h : toH v = toH w) : v = w := by
  simpa using congrArg coord h

theorem toH_nsmul (n : ℕ) (w : ZMod 4 × ZMod 4) : toH (n • w) = toH w ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero]; rfl
  | succ n ih => rw [succ_nsmul, toH_add, ih, pow_succ]

theorem toH_decomp (v : ZMod 4 × ZMod 4) :
    toH v = toH (1, 0) ^ v.1.val * toH (0, 1) ^ v.2.val := by
  rw [← toH_nsmul, ← toH_nsmul, ← toH_add, ← vec_decomp]

def gU : (ZMod 5)ˣ := ⟨2, 3, by decide, by decide⟩

theorem gU_pow_add : ∀ a b : ZMod 4, gU ^ (a + b).val = gU ^ a.val * gU ^ b.val := by decide

theorem gU_pow_zero : gU ^ (0 : ZMod 4).val = 1 := by decide

theorem gU_pow_inj : ∀ a b : ZMod 4, gU ^ a.val = gU ^ b.val → a = b := by decide

theorem gU_pow_surj : ∀ u : (ZMod 5)ˣ, ∃ k : ZMod 4, gU ^ k.val = u := by decide

def expU : Multiplicative (ZMod 4) →* (ZMod 5)ˣ where
  toFun k := gU ^ (Multiplicative.toAdd k).val
  map_one' := gU_pow_zero
  map_mul' a b := gU_pow_add (Multiplicative.toAdd a) (Multiplicative.toAdd b)

theorem expU_inj : Function.Injective expU :=
  fun a b h => gU_pow_inj (Multiplicative.toAdd a) (Multiplicative.toAdd b) h

theorem expU_surj : Function.Surjective expU := fun u => by
  obtain ⟨k, hk⟩ := gU_pow_surj u
  exact ⟨Multiplicative.ofAdd k, hk⟩

theorem char_eq (χ : H0 →* (ZMod 5)ˣ) :
    ∃ r : ZMod 4 × ZMod 4, ∀ v, χ (toH v) = expU (Multiplicative.ofAdd (dot r v)) := by
  obtain ⟨r1, h1⟩ := expU_surj (χ (toH (1, 0)))
  obtain ⟨r2, h2⟩ := expU_surj (χ (toH (0, 1)))
  refine ⟨(Multiplicative.toAdd r1, Multiplicative.toAdd r2), fun v => ?_⟩
  rw [toH_decomp v, map_mul, map_pow, map_pow, ← h1, ← h2, ← map_pow, ← map_pow, ← map_mul]
  congr 1
  apply Multiplicative.toAdd.injective
  simp [dot, nsmul_eq_mul, mul_comm]

theorem hom_toH (f : H0 →* H0) (v : ZMod 4 × ZMod 4) : f (toH v) = toH ((toM f).apply v) := by
  rw [← lin_eq]
  exact (toH_coord _).symm

theorem Mat.apply_mul (M N : Mat) (v : ZMod 4 × ZMod 4) :
    (M.mul N).apply v = M.apply (N.apply v) := by
  simp only [Mat.mul, Mat.apply]
  ext <;> ring

theorem Mat.apply_one (v : ZMod 4 × ZMod 4) : Mat.one.apply v = v := by
  simp [Mat.one, Mat.apply]

theorem Mat.ext_apply {M N : Mat} (h : ∀ v, M.apply v = N.apply v) : M = N := by
  have h1 := h (1, 0)
  have h2 := h (0, 1)
  obtain ⟨a, b, c, d⟩ := M
  obtain ⟨a', b', c', d'⟩ := N
  simp [Mat.apply, Prod.ext_iff] at h1 h2
  simp [h1, h2]

theorem dot_apply (r : ZMod 4 × ZMod 4) (M : Mat) (v : ZMod 4 × ZMod 4) :
    dot r (M.apply v) = dot (Mat.rowmul r M) v := by
  simp only [dot, Mat.apply, Mat.rowmul]
  ring

theorem dot_ext {s t : ZMod 4 × ZMod 4} (h : ∀ v, dot s v = dot t v) : s = t := by
  have h1 := h (1, 0)
  have h2 := h (0, 1)
  simp only [dot] at h1 h2
  exact Prod.ext (by simpa using h1) (by simpa using h2)

end WeightsCore

section Core

open WeightsCore

theorem weights_core0 (σ τ : H0 ≃* H0) (χ : H0 →* (ZMod 5)ˣ)
    (hσ : ∀ h, σ (σ h) = h)
    (h3 : ∀ h, σ (τ (σ (τ (σ (τ h))))) = h)
    (hK : ∀ h, χ (τ.symm h) = χ h * χ (τ.symm (σ.symm h))) :
    ∀ h, χ (τ.symm (τ.symm h)) = χ h := by
  obtain ⟨r, hr⟩ := char_eq χ
  have eσ : ∀ v, σ (toH v) = toH ((toM σ.toMonoidHom).apply v) :=
    fun v => hom_toH σ.toMonoidHom v
  have eτ : ∀ v, τ.symm (toH v) = toH ((toM τ.symm.toMonoidHom).apply v) :=
    fun v => hom_toH τ.symm.toMonoidHom v
  set B := toM σ.toMonoidHom
  set A := toM τ.symm.toMonoidHom
  have hσs : ∀ h, σ.symm h = σ h := fun h => by
    rw [MulEquiv.symm_apply_eq]
    exact (hσ h).symm
  have h3' : ∀ h, τ.symm (σ (τ.symm (σ (τ.symm (σ h))))) = h := fun h => by
    have := h3 (τ.symm (σ (τ.symm (σ (τ.symm (σ h))))))
    simpa [hσ] using this.symm
  have hB : B.mul B = Mat.one := by
    apply Mat.ext_apply
    intro v
    rw [Mat.apply_mul, Mat.apply_one]
    apply toH_inj
    rw [← eσ, ← eσ, hσ]
  have hA : (A.mul B).mul ((A.mul B).mul (A.mul B)) = Mat.one := by
    apply Mat.ext_apply
    intro v
    simp only [Mat.apply_mul, Mat.apply_one]
    apply toH_inj
    have := h3' (toH v)
    simp only [eσ, eτ] at this
    exact this
  have hK' : ∀ v, dot r (A.apply v) = dot r v + dot r (A.apply (B.apply v)) := fun v => by
    have := hK (toH v)
    simp only [hσs, eσ, eτ, hr] at this
    rw [← map_mul, ← ofAdd_add] at this
    exact Multiplicative.ofAdd.injective (expU_inj this)
  have hK'' : Mat.rowmul (Mat.rowmul r A) B + r = Mat.rowmul r A := by
    apply dot_ext
    intro v
    have := hK' v
    simp only [dot, Mat.apply, Mat.rowmul, Prod.fst_add, Prod.snd_add] at this ⊢
    linear_combination (-1 : ZMod 4) * this
  have hfin := fin_core A B r hB hA hK''
  intro h
  obtain ⟨v, rfl⟩ : ∃ v, h = toH v := ⟨coord h, (toH_coord h).symm⟩
  have hv : dot r (A.apply (A.apply v)) = dot r v := by
    rw [dot_apply, dot_apply, hfin]
  rw [eτ, eτ, hr, hr, hv]

theorem weights_core {H : Type} [CommGroup H]
    (e : H ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
    (σ τ : H ≃* H) (χ : H →* (ZMod 5)ˣ)
    (hσ : ∀ h, σ (σ h) = h)
    (h3 : ∀ h, σ (τ (σ (τ (σ (τ h))))) = h)
    (hK : ∀ h, χ (τ.symm h) = χ h * χ (τ.symm (σ.symm h))) :
    ∀ h, χ (τ.symm (τ.symm h)) = χ h := by
  intro h
  have key := weights_core0 (e.symm.trans (σ.trans e)) (e.symm.trans (τ.trans e))
    (χ.comp e.symm.toMonoidHom) (fun x => by simp [hσ]) (fun x => by simp [h3])
    (fun y => by simpa using hK (e.symm y)) (e h)
  simpa using key

end Core

end CFSG.GH74.GLS.LU.Local.Five
