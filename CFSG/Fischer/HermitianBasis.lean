module

public import CFSG.Fischer.Unitary
import all CFSG.Fischer.F4
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic

public section

namespace CFSG.Fischer

open Matrix

structure HForm (h : W → W → F4) : Prop where
  add_left : ∀ x x' y, h (x + x') y = h x y + h x' y
  smul_left : ∀ (c : F4) x y, h (c • x) y = c * h x y
  swap : ∀ x y, h y x = (h x y) ^ 2
  nondeg : ∀ x, (∀ y, h x y = 0) → x = 0

private theorem sq_sq' : ∀ c : F4, (c ^ 2) ^ 2 = c := by decide

private theorem sq_add' : ∀ a b : F4, (a + b) ^ 2 = a ^ 2 + b ^ 2 := by decide

private theorem norm_eq : ∀ c : F4, c ^ 2 = c → c ≠ 1 → c = 0 := by decide

private theorem polar_key : ∀ a : F4, a + a ^ 2 = 0 → F4.ω ^ 2 * a + F4.ω * a ^ 2 = 0 → a = 0 := by
  decide

namespace HForm

variable {h : W → W → F4} (hh : HForm h)
include hh

theorem add_right (x y y' : W) : h x (y + y') = h x y + h x y' := by
  rw [hh.swap (y + y') x, hh.add_left, sq_add', ← hh.swap y x, ← hh.swap y' x]

theorem smul_right (c : F4) (x y : W) : h x (c • y) = c ^ 2 * h x y := by
  rw [hh.swap (c • y) x, hh.smul_left, mul_pow, ← hh.swap y x]

theorem zero_left (y : W) : h 0 y = 0 := by
  have := hh.smul_left 0 0 y
  rwa [zero_smul, zero_mul] at this

theorem zero_right (x : W) : h x 0 = 0 := by
  rw [hh.swap 0 x, hh.zero_left]
  decide

theorem self_sq (x : W) : (h x x) ^ 2 = h x x := (hh.swap x x).symm

theorem sum_right {k : ℕ} (x : W) (c : Fin k → F4) (b : Fin k → W) :
    h x (∑ i, c i • b i) = ∑ i, (c i) ^ 2 * h x (b i) := by
  induction k with
  | zero => simp only [Finset.univ_eq_empty, Finset.sum_empty, hh.zero_right]
  | succ k ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, hh.add_right, hh.smul_right,
      ih (fun i => c i.succ) (fun i => b i.succ)]

theorem polar {x w : W} (hx : h x x = 0) (hw : h w w = 0) (h1 : h (x + w) (x + w) = 0)
    (h2 : h (x + F4.ω • w) (x + F4.ω • w) = 0) : h x w = 0 := by
  have e1 : h (x + w) (x + w) = h x w + (h x w) ^ 2 := by
    rw [hh.add_left, hh.add_right, hh.add_right, hx, hw, hh.swap x w]; ring
  have e2 : h (x + F4.ω • w) (x + F4.ω • w) = F4.ω ^ 2 * h x w + F4.ω * (h x w) ^ 2 := by
    rw [hh.add_left, hh.add_right, hh.add_right, hx, hh.smul_left, hh.smul_left, hh.smul_right,
      hh.smul_right, hw, hh.swap x w]; ring
  rw [e1] at h1
  rw [e2] at h2
  exact polar_key _ h1 h2

theorem sum_left {k : ℕ} (c : Fin k → F4) (b : Fin k → W) (z : W) :
    h (∑ i, c i • b i) z = ∑ i, c i * h (b i) z := by
  induction k with
  | zero => simp only [Finset.univ_eq_empty, Finset.sum_empty, hh.zero_left]
  | succ k ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, hh.add_left, hh.smul_left,
      ih (fun i => c i.succ) (fun i => b i.succ)]

theorem sub_left (x x' y : W) : h (x - x') y = h x y - h x' y := by
  have := hh.add_left (x - x') x' y
  rw [sub_add_cancel] at this
  rw [this, add_sub_cancel_right]

noncomputable def toLin {k : ℕ} (b : Fin k → W) : W →ₗ[F4] (Fin k → F4) where
  toFun x i := h x (b i)
  map_add' x y := by funext i; exact hh.add_left x y (b i)
  map_smul' c x := by funext i; exact hh.smul_left c x (b i)

theorem exists_perp_ne_zero {k : ℕ} (hk : k < 6) (b : Fin k → W) :
    ∃ x ≠ 0, ∀ i, h x (b i) = 0 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (hh.toLin b)
  have h2 : Module.finrank F4 (LinearMap.range (hh.toLin b)) ≤ k := by
    have := Submodule.finrank_le (LinearMap.range (hh.toLin b))
    rwa [Module.finrank_fin_fun] at this
  rw [Module.finrank_fin_fun] at h1
  have h3 : LinearMap.ker (hh.toLin b) ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at h1
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h3
  exact ⟨x, hx0, fun i => congrFun (LinearMap.mem_ker.1 hx) i⟩

theorem exists_unit_perp {k : ℕ} (hk : k < 6) (b : Fin k → W)
    (hb : ∀ i j, h (b i) (b j) = if i = j then 1 else 0) :
    ∃ x, (∀ i, h x (b i) = 0) ∧ h x x = 1 := by
  by_contra hne
  simp only [not_exists, not_and] at hne
  have hiso : ∀ x, (∀ i, h x (b i) = 0) → h x x = 0 :=
    fun x hx => norm_eq _ (hh.self_sq x) (hne x hx)
  obtain ⟨x0, hx00, hx0⟩ := hh.exists_perp_ne_zero hk b
  apply hx00
  apply hh.nondeg
  intro y
  set w := y - ∑ i, h y (b i) • b i with hw
  have hwp : ∀ j, h w (b j) = 0 := by
    intro j
    rw [hw, hh.sub_left, hh.sum_left]
    simp only [hb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      sub_self]
  have hadd : ∀ c : F4, ∀ j, h (x0 + c • w) (b j) = 0 := by
    intro c j
    rw [hh.add_left, hh.smul_left, hx0 j, hwp j, mul_zero, add_zero]
  have hxw : h x0 w = 0 := by
    refine hh.polar (hiso _ hx0) (hiso _ hwp) ?_ (hiso _ (hadd F4.ω))
    have := hiso _ (hadd 1)
    rwa [one_smul] at this
  have hy : y = w + ∑ i, h y (b i) • b i := by rw [hw, sub_add_cancel]
  rw [hy, hh.add_right, hxw, hh.sum_right]
  simp only [hx0, mul_zero, Finset.sum_const_zero, add_zero]

theorem exists_orthonormal_family : ∀ k ≤ 6, ∃ b : Fin k → W,
    ∀ i j, h (b i) (b j) = if i = j then 1 else 0 := by
  intro k
  induction k with
  | zero => intro _; exact ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  | succ k ih =>
    intro hk
    obtain ⟨b, hb⟩ := ih (by omega)
    obtain ⟨x, hxb, hxx⟩ := hh.exists_unit_perp (by omega) b hb
    refine ⟨Fin.snoc b x, fun i j => ?_⟩
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp [hxx]
      | cast j =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc, hxb j]
        rw [ite_eq_right (Fin.castSucc_lt_last j).ne']
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [hh.swap, hxb i, ite_eq_right (Fin.castSucc_lt_last i).ne]
        decide
      | cast j =>
        simp only [Fin.snoc_castSucc, hb i j, Fin.castSucc_inj]

theorem exists_orthonormal : ∃ b : Fin 6 → W, ∀ i j, h (b i) (b j) = if i = j then 1 else 0 :=
  hh.exists_orthonormal_family 6 le_rfl

end HForm

end CFSG.Fischer
