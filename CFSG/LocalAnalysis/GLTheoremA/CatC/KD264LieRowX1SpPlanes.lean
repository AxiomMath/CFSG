module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCorePlanes

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp

open CFSG.Open Module CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore

structure PlaneData {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (E : Subgroup (W ≃ₗ[ZMod 2] W)) (n : ℕ) where
  X : Fin n → Submodule (ZMod 2) W
  ρ : Fin n → (W ≃ₗ[ZMod 2] W)
  e : Fin n → (W ≃ₗ[ZMod 2] W)
  dim2 : ∀ i, Module.finrank (ZMod 2) (X i) = 2
  indep : iSupIndep X
  sup_eq : iSup X = ⊤
  inv : ∀ i, ∀ g ∈ E, ∀ x ∈ X i, g x ∈ X i
  memE : ∀ i, ρ i ∈ E
  cyc : ∀ i, ∀ x ∈ X i, ρ i (ρ i x) + ρ i x + x = 0
  fixfree : ∀ i, ∀ x ∈ X i, ρ i x = x → x = 0
  pow : ∀ i, ∀ g ∈ E, ∃ k : Fin 3, ∀ x ∈ X i, g x = (ρ i ^ (k : ℕ)) x
  emem : ∀ p, e p ∈ E
  eact : ∀ p q, ∀ x ∈ X q, e p x = if q = p then ρ q x else x

namespace PlaneData

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
variable {E : Subgroup (W ≃ₗ[ZMod 2] W)} {n : ℕ} (D : PlaneData E n)

theorem rho_mem (i : Fin n) : ∀ x ∈ D.X i, D.ρ i x ∈ D.X i :=
  fun x hx => D.inv i _ (D.memE i) x hx

theorem rho_pow_mem (i : Fin n) (s : ℕ) : ∀ x ∈ D.X i, (D.ρ i ^ s) x ∈ D.X i := by
  induction s with
  | zero => intro x hx; simpa using hx
  | succ s ih =>
    intro x hx
    rw [pow_succ', LinearEquiv.mul_apply]
    exact D.rho_mem i _ (ih x hx)

theorem rho_pow_three (hE : IsElemAbelian 3 E) (i : Fin n) : D.ρ i ^ 3 = 1 :=
  hE.2 _ (D.memE i)

theorem sum_pow_eq_zero (i : Fin n) (x : W) (hx : x ∈ D.X i) :
    x + D.ρ i x + D.ρ i (D.ρ i x) = 0 := by
  have h := D.cyc i x hx
  rw [← h]
  abel

theorem sum_fin3_pow (i : Fin n) (x : W) (hx : x ∈ D.X i) :
    ∑ s : Fin 3, (D.ρ i ^ (s : ℕ)) x = 0 := by
  rw [Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, LinearEquiv.coe_one, id]
  have h2 : (D.ρ i ^ 2) x = D.ρ i (D.ρ i x) := by
    rw [pow_two, LinearEquiv.mul_apply]
  rw [h2]
  exact D.sum_pow_eq_zero i x hx

theorem ea_trivial (a b : Fin n) (hab : a ≠ b) (t : ℕ) : ∀ u ∈ D.X a, (D.e b ^ t) u = u := by
  induction t with
  | zero => intro u _; simp
  | succ t ih =>
    intro u hu
    rw [pow_succ, LinearEquiv.mul_apply, D.eact b a u hu, if_neg hab]
    exact ih u hu

theorem ea_pow_plane (a : Fin n) (s : ℕ) : ∀ u ∈ D.X a, (D.e a ^ s) u = (D.ρ a ^ s) u := by
  induction s with
  | zero => intro u _; simp
  | succ s ih =>
    intro u hu
    rw [pow_succ, LinearEquiv.mul_apply, D.eact a a u hu, if_pos rfl, pow_succ,
      LinearEquiv.mul_apply]
    exact ih _ (D.rho_mem a u hu)

theorem orth_of_ne (f : LinearMap.BilinForm (ZMod 2) W)
    (hf : ∀ g ∈ E, ∀ x y, f (g x) (g y) = f x y) {p q : Fin n} (hpq : p ≠ q)
    {x y : W} (hx : x ∈ D.X p) (hy : y ∈ D.X q) : f x y = 0 := by
  have key : ∀ s t : ℕ, f x y = f ((D.ρ p ^ s) x) ((D.ρ q ^ t) y) := by
    intro s t
    have hmem : D.e p ^ s * D.e q ^ t ∈ E :=
      E.mul_mem (E.pow_mem (D.emem p) s) (E.pow_mem (D.emem q) t)
    have h1 := hf _ hmem x y
    have hx' : (D.e p ^ s * D.e q ^ t) x = (D.ρ p ^ s) x := by
      rw [LinearEquiv.mul_apply, D.ea_trivial p q hpq t x hx, D.ea_pow_plane p s x hx]
    have hy' : (D.e p ^ s * D.e q ^ t) y = (D.ρ q ^ t) y := by
      rw [LinearEquiv.mul_apply, D.ea_pow_plane q t y hy]
      exact D.ea_trivial q p hpq.symm s _ (D.rho_pow_mem q t y hy)
    rw [hx', hy'] at h1
    exact h1.symm
  have hsum : ∑ s : Fin 3, ∑ t : Fin 3, f ((D.ρ p ^ (s : ℕ)) x) ((D.ρ q ^ (t : ℕ)) y) = 0 := by
    have h0 : f (∑ s : Fin 3, (D.ρ p ^ (s : ℕ)) x) (∑ t : Fin 3, (D.ρ q ^ (t : ℕ)) y) = 0 := by
      rw [D.sum_fin3_pow p x hx, map_zero, LinearMap.zero_apply]
    rw [← h0, map_sum]
    simp only [map_sum]
    exact Finset.sum_comm
  have h9 : ∑ s : Fin 3, ∑ t : Fin 3, f x y = f x y := by
    simp only [Fin.sum_univ_three]
    generalize f x y = c
    revert c
    decide
  have hall : ∑ s : Fin 3, ∑ t : Fin 3, f x y =
      ∑ s : Fin 3, ∑ t : Fin 3, f ((D.ρ p ^ (s : ℕ)) x) ((D.ρ q ^ (t : ℕ)) y) := by
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    exact key s t
  rw [← h9, hall, hsum]

theorem range_sub (i : Fin n) (v : W) : D.e i v - v ∈ D.X i := by
  refine CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Planes.sub_mem_of_pieces D.sup_eq
    (D.e i) (D.X i) ?_ v
  intro j x hx
  by_cases hji : j = i
  · subst hji
    rw [D.eact j j x hx, if_pos rfl]
    exact Submodule.sub_mem _ (D.rho_mem j x hx) hx
  · rw [D.eact i j x hx, if_neg hji, sub_self]
    exact Submodule.zero_mem _

theorem two_smul_eq_zero' (z : W) : z + z = 0 := by
  have h : ((1 : ZMod 2) + 1) • z = 0 := by
    rw [show ((1 : ZMod 2) + 1) = 0 from rfl, zero_smul]
  rwa [add_smul, one_smul] at h

theorem exists_pre (hE : IsElemAbelian 3 E) (i : Fin n) (x : W) (hx : x ∈ D.X i) :
    ∃ y ∈ D.X i, D.e i y - y = x := by
  set ρ := D.ρ i with hρ
  have hcube : ρ (ρ (ρ x)) = x := by
    have h3 := D.rho_pow_three hE i
    have : (ρ ^ 3) x = x := by rw [h3, LinearEquiv.coe_one, id]
    rwa [show (ρ ^ 3) x = ρ (ρ (ρ x)) by simp [pow_succ, LinearEquiv.mul_apply]] at this
  have hρx : ρ x ∈ D.X i := D.rho_mem i x hx
  have hρρx : ρ (ρ x) ∈ D.X i := D.rho_mem i _ hρx
  refine ⟨x + ρ (ρ x), Submodule.add_mem _ hx hρρx, ?_⟩
  have hy : D.e i (x + ρ (ρ x)) = ρ (x + ρ (ρ x)) := by
    rw [D.eact i i _ (Submodule.add_mem _ hx hρρx), if_pos rfl]
  rw [hy, map_add, hcube]
  have hc := D.cyc i x hx
  have h4 := two_smul_eq_zero' (ρ (ρ x))
  have h5 := two_smul_eq_zero' x
  linear_combination (norm := module) hc - h4 - h5

end PlaneData

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp

end
