module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4QClass

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Subgroup Matrix
open scoped MatrixGroups

open GenLocU4Basic GenLocU4QLift GenLocU4QClass

namespace GenLocU4QHyp

variable {K : Type} [Field K] [Finite K] {A : Type} [Group A]

@[expose] def HypPlanes {q : ℕ} (Γ : Subgroup ↥(StatedSU 4 q K)) (x y z : GL (Fin 4) K) : Prop :=
  (∀ g : ↥(StatedSU 4 q K), (g : GL (Fin 4) K) * x = x * g → (g : GL (Fin 4) K) * y = y * g → g ∈ Γ) ∧
  (∀ g : ↥(StatedSU 4 q K), (g : GL (Fin 4) K) * x = x * g → (g : GL (Fin 4) K) * z = z * g → g ∈ Γ) ∧
  (∀ g : ↥(StatedSU 4 q K), (g : GL (Fin 4) K) * y = y * g → (g : GL (Fin 4) K) * z = z * g → g ∈ Γ) ∧
  (∀ g : ↥(StatedSU 4 q K), (g : GL (Fin 4) K) * x = x * g → (g : GL (Fin 4) K) * (y * z) = (y * z) * g → g ∈ Γ) ∧
  (∀ g : ↥(StatedSU 4 q K), (g : GL (Fin 4) K) * y = y * g → (g : GL (Fin 4) K) * (x * z) = (x * z) * g → g ∈ Γ) ∧
  (∀ g : ↥(StatedSU 4 q K), (g : GL (Fin 4) K) * z = z * g → (g : GL (Fin 4) K) * (x * y) = (x * y) * g → g ∈ Γ) ∧
  (∀ g : ↥(StatedSU 4 q K), (g : GL (Fin 4) K) * (x * y) = (x * y) * g → (g : GL (Fin 4) K) * (x * z) = (x * z) * g →
    g ∈ Γ)

omit [Finite K] in
theorem comm_iff {q : ℕ} (g : ↥(StatedSU 4 q K)) (u : GL (Fin 4) K) :
    (g : GL (Fin 4) K) * u = u * g ↔ ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (u : Matrix (Fin 4) (Fin 4) K) =
      (u : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
  constructor
  · intro h
    simpa [Units.val_mul] using congrArg (fun w : GL (Fin 4) K => (w : Matrix (Fin 4) (Fin 4) K)) h
  · intro h
    exact Units.ext (by simpa [Units.val_mul] using h)

variable {p f : ℕ}

theorem hypPlanes_of_data (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) [Finite A]
    (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) (hA : IsRank23 A) (hr : pRank 2 A = 3) {a b c : A}
    {x y z : GL (Fin 4) K} (hax : IsLiftU α a x) (hby : IsLiftU α b y) (hcz : IsLiftU α c z) {sx sy sz : K}
    (hx : (x : Matrix (Fin 4) (Fin 4) K) * x = sx • 1) (hy : (y : Matrix (Fin 4) (Fin 4) K) * y = sy • 1)
    (hz : (z : Matrix (Fin 4) (Fin 4) K) * z = sz • 1)
    (hxy : (x : Matrix (Fin 4) (Fin 4) K) * y = -((y : Matrix (Fin 4) (Fin 4) K) * x))
    (hxz : (x : Matrix (Fin 4) (Fin 4) K) * z = (z : Matrix (Fin 4) (Fin 4) K) * x)
    (hyz : (y : Matrix (Fin 4) (Fin 4) K) * z = (z : Matrix (Fin 4) (Fin 4) K) * y) (hzn : NonScalar z) :
    HypPlanes (gammaAct α) x y z := by
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have h2 : (2 : K) ≠ 0 := GenLocU4ExtFrame.two_ne_zero_of_card hp hp2 hK
  have hyx : (y : Matrix (Fin 4) (Fin 4) K) * x = -((x : Matrix (Fin 4) (Fin 4) K) * y) := by rw [hxy]; simp
  have nx := GenLocL4Q.not_scalar_of_anticomm h2 hxy
  have ny := GenLocL4Q.not_scalar_of_anticomm h2 hyx
  have nxy := GenLocL4Q.not_scalar_of_anticomm h2 (u := x * y) (v := x)
    (by rw [Units.val_mul]; exact GenLocL4Q.W_xy_x hx hy hz hxy hxz hyz)
  have nyz := GenLocL4Q.not_scalar_of_anticomm h2 (u := y * z) (v := x)
    (by rw [Units.val_mul]; exact GenLocL4Q.W_yz_x hx hy hz hxy hxz hyz)
  have nxz := GenLocL4Q.not_scalar_of_anticomm h2 (u := x * z) (v := y)
    (by rw [Units.val_mul]; exact GenLocL4Q.W_xz_y hx hy hz hxy hxz hyz)
  have nxyz := GenLocL4Q.not_scalar_of_anticomm h2 (u := x * (y * z)) (v := x)
    (by rw [Units.val_mul, Units.val_mul]; exact GenLocL4Q.W_xyz_x hx hy hz hxy hxz hyz)
  have nyxz := GenLocL4Q.not_scalar_of_anticomm h2 (u := y * (x * z)) (v := y)
    (by rw [Units.val_mul, Units.val_mul]; exact GenLocL4Q.W_yxz_y hx hy hz hxy hxz hyz)
  have nxyxz := GenLocL4Q.not_scalar_of_anticomm h2 (u := (x * y) * (x * z)) (v := x)
    (by rw [Units.val_mul, Units.val_mul, Units.val_mul]; exact GenLocL4Q.W_xyxz_x hx hy hz hxy hxz hyz)
  have nzxy := GenLocL4Q.not_scalar_of_anticomm h2 (u := z * (x * y)) (v := x) (by
    rw [Units.val_mul, Units.val_mul]
    have hxy_x := GenLocL4Q.W_xy_x hx hy hz hxy hxz hyz
    calc (z : Matrix (Fin 4) (Fin 4) K) * ((x : Matrix (Fin 4) (Fin 4) K) * y) * x
        = z * ((x * y) * x) := by rw [Matrix.mul_assoc]
      _ = z * (-(x * (x * y))) := by rw [hxy_x]
      _ = -((z * x) * (x * y)) := by rw [Matrix.mul_neg, ← Matrix.mul_assoc]
      _ = -((x * z) * (x * y)) := by rw [← hxz]
      _ = -(x * (z * (x * y))) := by rw [Matrix.mul_assoc])
  have hyz' : IsLiftU α (b * c) (y * z) := hby.mul h hcz
  have hxz' : IsLiftU α (a * c) (x * z) := hax.mul h hcz
  have hxy' : IsLiftU α (a * b) (x * y) := hax.mul h hby
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hgx hgy
    exact mem_gammaAct_of_pairU hp hp2 hK α hA hr hax hby nx ny nxy g ((comm_iff g x).1 hgx) ((comm_iff g y).1 hgy)
  · intro g hgx hgz
    exact mem_gammaAct_of_pairU hp hp2 hK α hA hr hax hcz nx hzn nxz g ((comm_iff g x).1 hgx) ((comm_iff g z).1 hgz)
  · intro g hgy hgz
    exact mem_gammaAct_of_pairU hp hp2 hK α hA hr hby hcz ny hzn nyz g ((comm_iff g y).1 hgy) ((comm_iff g z).1 hgz)
  · intro g hgx hgyz
    exact mem_gammaAct_of_pairU hp hp2 hK α hA hr hax hyz' nx nyz nxyz g ((comm_iff g x).1 hgx) ((comm_iff g _).1 hgyz)
  · intro g hgy hgxz
    exact mem_gammaAct_of_pairU hp hp2 hK α hA hr hby hxz' ny nxz nyxz g ((comm_iff g y).1 hgy) ((comm_iff g _).1 hgxz)
  · intro g hgz hgxy
    exact mem_gammaAct_of_pairU hp hp2 hK α hA hr hcz hxy' hzn nxy nzxy g ((comm_iff g z).1 hgz) ((comm_iff g _).1 hgxy)
  · intro g hgxy hgxz
    exact mem_gammaAct_of_pairU hp hp2 hK α hA hr hxy' hxz' nxy nxz nxyxz g ((comm_iff g _).1 hgxy) ((comm_iff g _).1 hgxz)

theorem hypPlanes_of_triple (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) [Finite A]
    (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) (hA : IsRank23 A) (hr : pRank 2 A = 3) {sx sy sz : K}
    (T : Triple α sx sy sz) :
    ∃ x y z : GL (Fin 4) K, IsUnitaryU (p ^ f) (x : Matrix (Fin 4) (Fin 4) K) ∧
      IsUnitaryU (p ^ f) (y : Matrix (Fin 4) (Fin 4) K) ∧ IsUnitaryU (p ^ f) (z : Matrix (Fin 4) (Fin 4) K) ∧
      (x : Matrix (Fin 4) (Fin 4) K) * x = sx • 1 ∧ (y : Matrix (Fin 4) (Fin 4) K) * y = sy • 1 ∧
      (z : Matrix (Fin 4) (Fin 4) K) * z = sz • 1 ∧
      (x : Matrix (Fin 4) (Fin 4) K) * y = -((y : Matrix (Fin 4) (Fin 4) K) * x) ∧
      (x : Matrix (Fin 4) (Fin 4) K) * z = (z : Matrix (Fin 4) (Fin 4) K) * x ∧
      (y : Matrix (Fin 4) (Fin 4) K) * z = (z : Matrix (Fin 4) (Fin 4) K) * y ∧ NonScalar z ∧
      HypPlanes (gammaAct α) x y z := by
  obtain ⟨a, b, c, x, y, z, hax, hby, hcz, hx, hy, hz, hxy, hxz, hyz, hn⟩ := T
  exact ⟨x, y, z, hax.1, hby.1, hcz.1, hx, hy, hz, hxy, hxz, hyz, hn,
    hypPlanes_of_data hp hp2 hK α hA hr hax hby hcz hx hy hz hxy hxz hyz hn⟩

end GenLocU4QHyp

end CFSG.GH74.Generic.BProg.B2
