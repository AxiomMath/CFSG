module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4QLift
public import CFSG.GH74.Generic.BProg.B2.GenLocL4QRank3

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Subgroup Matrix
open scoped MatrixGroups

open GenLocU4Basic GenLocU4QLift

namespace GenLocU4QClass

variable {K : Type} [Field K] [Finite K] {A : Type} [Group A]

@[expose] def NonScalar (u : GL (Fin 4) K) : Prop := ¬ ∃ l : K, (u : Matrix (Fin 4) (Fin 4) K) = l • 1

@[expose] def Triple {p f : ℕ} (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) (sx sy sz : K) : Prop :=
  ∃ (a b c : A) (x y z : GL (Fin 4) K), IsLiftU α a x ∧ IsLiftU α b y ∧ IsLiftU α c z ∧
    (x : Matrix (Fin 4) (Fin 4) K) * x = sx • 1 ∧ (y : Matrix (Fin 4) (Fin 4) K) * y = sy • 1 ∧
    (z : Matrix (Fin 4) (Fin 4) K) * z = sz • 1 ∧
    (x : Matrix (Fin 4) (Fin 4) K) * y = -((y : Matrix (Fin 4) (Fin 4) K) * x) ∧
    (x : Matrix (Fin 4) (Fin 4) K) * z = (z : Matrix (Fin 4) (Fin 4) K) * x ∧
    (y : Matrix (Fin 4) (Fin 4) K) * z = (z : Matrix (Fin 4) (Fin 4) K) * y ∧ NonScalar z

variable {p f : ℕ} {α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)}

omit [Finite K] in
theorem Triple.rel1 (h : UnitaryFieldData p f K) {sx sy sz : K} (T : Triple α sx sy sz) :
    Triple α sx (-(sx * sy)) sz := by
  obtain ⟨a, b, c, x, y, z, hax, hby, hcz, hx, hy, hz, hxy, hxz, hyz, hn⟩ := T
  have hyx : (y : Matrix (Fin 4) (Fin 4) K) * x = -((x : Matrix (Fin 4) (Fin 4) K) * y) := by rw [hxy]; simp
  refine ⟨a, a * b, c, x, x * y, z, hax, hax.mul h hby, hcz, hx, ?_, hz, ?_, hxz, ?_, hn⟩
  · rw [Units.val_mul]
    calc (x : Matrix (Fin 4) (Fin 4) K) * y * ((x : Matrix (Fin 4) (Fin 4) K) * y)
        = (x : Matrix (Fin 4) (Fin 4) K) * ((y : Matrix (Fin 4) (Fin 4) K) * x) * y := by simp only [Matrix.mul_assoc]
      _ = -((x * x) * (y * y)) := by rw [hyx]; simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = (-(sx * sy)) • 1 := by
          rw [hx, hy, Matrix.smul_mul, Matrix.one_mul, smul_smul, neg_smul, mul_comm]
  · rw [Units.val_mul]
    have e : (x : Matrix (Fin 4) (Fin 4) K) * y * x =
        -((x : Matrix (Fin 4) (Fin 4) K) * ((x : Matrix (Fin 4) (Fin 4) K) * y)) := by
      rw [Matrix.mul_assoc, hyx, Matrix.mul_neg]
    rw [e, neg_neg]
  · rw [Units.val_mul]
    calc (x : Matrix (Fin 4) (Fin 4) K) * y * z = x * (y * z) := by rw [Matrix.mul_assoc]
      _ = x * (z * y) := by rw [hyz]
      _ = (x * z) * y := by rw [Matrix.mul_assoc]
      _ = z * x * y := by rw [hxz]
      _ = z * (x * y) := by rw [Matrix.mul_assoc]

omit [Finite K] in
theorem Triple.rel2 (h : UnitaryFieldData p f K) {sx sy sz : K} (T : Triple α sx sy sz) :
    Triple α sy (-(sx * sy)) sz := by
  obtain ⟨a, b, c, x, y, z, hax, hby, hcz, hx, hy, hz, hxy, hxz, hyz, hn⟩ := T
  have hyx : (y : Matrix (Fin 4) (Fin 4) K) * x = -((x : Matrix (Fin 4) (Fin 4) K) * y) := by rw [hxy]; simp
  refine ⟨b, a * b, c, y, x * y, z, hby, hax.mul h hby, hcz, hy, ?_, hz, ?_, hyz, ?_, hn⟩
  · rw [Units.val_mul]
    calc (x : Matrix (Fin 4) (Fin 4) K) * y * ((x : Matrix (Fin 4) (Fin 4) K) * y)
        = (x : Matrix (Fin 4) (Fin 4) K) * ((y : Matrix (Fin 4) (Fin 4) K) * x) * y := by simp only [Matrix.mul_assoc]
      _ = -((x * x) * (y * y)) := by rw [hyx]; simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = (-(sx * sy)) • 1 := by
          rw [hx, hy, Matrix.smul_mul, Matrix.one_mul, smul_smul, neg_smul, mul_comm]
  · rw [Units.val_mul, ← Matrix.mul_assoc, hyx, Matrix.neg_mul]
  · rw [Units.val_mul]
    calc (x : Matrix (Fin 4) (Fin 4) K) * y * z = x * (y * z) := by rw [Matrix.mul_assoc]
      _ = x * (z * y) := by rw [hyz]
      _ = (x * z) * y := by rw [Matrix.mul_assoc]
      _ = z * x * y := by rw [hxz]
      _ = z * (x * y) := by rw [Matrix.mul_assoc]

omit [Finite K] in
theorem zuz {z u : Matrix (Fin 4) (Fin 4) K} (h : z * u = u * z) : z * (u * z) = u * (z * z) := by
  rw [← Matrix.mul_assoc, h, Matrix.mul_assoc]

omit [Finite K] in
theorem Triple.rel3 (h : UnitaryFieldData p f K) {sx sy sz : K} (T : Triple α sx sy sz) :
    Triple α (sx * sz) (sy * sz) sz := by
  obtain ⟨a, b, c, x, y, z, hax, hby, hcz, hx, hy, hz, hxy, hxz, hyz, hn⟩ := T
  have hyx : (y : Matrix (Fin 4) (Fin 4) K) * x = -((x : Matrix (Fin 4) (Fin 4) K) * y) := by rw [hxy]; simp
  have hzx : (z : Matrix (Fin 4) (Fin 4) K) * x = (x : Matrix (Fin 4) (Fin 4) K) * z := hxz.symm
  have hzy : (z : Matrix (Fin 4) (Fin 4) K) * y = (y : Matrix (Fin 4) (Fin 4) K) * z := hyz.symm
  refine ⟨a * c, b * c, c, x * z, y * z, z, hax.mul h hcz, hby.mul h hcz, hcz, ?_, ?_, hz, ?_, ?_, ?_, hn⟩
  · rw [Units.val_mul]
    calc (x : Matrix (Fin 4) (Fin 4) K) * z * ((x : Matrix (Fin 4) (Fin 4) K) * z)
        = x * (z * (x * z)) := by rw [Matrix.mul_assoc]
      _ = x * (x * (z * z)) := by rw [zuz hzx]
      _ = (x * x) * (z * z) := by rw [Matrix.mul_assoc]
      _ = (sx * sz) • 1 := by rw [hx, hz, Matrix.smul_mul, Matrix.one_mul, smul_smul]
  · rw [Units.val_mul]
    calc (y : Matrix (Fin 4) (Fin 4) K) * z * ((y : Matrix (Fin 4) (Fin 4) K) * z)
        = y * (z * (y * z)) := by rw [Matrix.mul_assoc]
      _ = y * (y * (z * z)) := by rw [zuz hzy]
      _ = (y * y) * (z * z) := by rw [Matrix.mul_assoc]
      _ = (sy * sz) • 1 := by rw [hy, hz, Matrix.smul_mul, Matrix.one_mul, smul_smul]
  · rw [Units.val_mul, Units.val_mul]
    have hL : (x : Matrix (Fin 4) (Fin 4) K) * z * ((y : Matrix (Fin 4) (Fin 4) K) * z) = (x * y) * (z * z) := by
      rw [Matrix.mul_assoc, zuz hzy, ← Matrix.mul_assoc]
    have hR : (y : Matrix (Fin 4) (Fin 4) K) * z * ((x : Matrix (Fin 4) (Fin 4) K) * z) = (y * x) * (z * z) := by
      rw [Matrix.mul_assoc, zuz hzx, ← Matrix.mul_assoc]
    rw [hL, hR, hyx, Matrix.neg_mul, neg_neg]
  · rw [Units.val_mul]
    calc (x : Matrix (Fin 4) (Fin 4) K) * z * z = (z * x) * z := by rw [hzx]
      _ = z * (x * z) := Matrix.mul_assoc _ _ _
  · rw [Units.val_mul]
    calc (y : Matrix (Fin 4) (Fin 4) K) * z * z = (z * y) * z := by rw [hzy]
      _ = z * (y * z) := Matrix.mul_assoc _ _ _

omit [Finite K] in
theorem Triple.scale {sx sy sz : K} (T : Triple α sx sy sz) {l1 l2 l3 : K} (h1 : l1 ≠ 0) (h2 : l2 ≠ 0) (h3 : l3 ≠ 0)
    (n1 : l1 ^ (p ^ f + 1) = 1) (n2 : l2 ^ (p ^ f + 1) = 1) (n3 : l3 ^ (p ^ f + 1) = 1) :
    Triple α (l1 * l1 * sx) (l2 * l2 * sy) (l3 * l3 * sz) := by
  obtain ⟨a, b, c, x, y, z, hax, hby, hcz, hx, hy, hz, hxy, hxz, hyz, hn⟩ := T
  refine ⟨a, b, c, GenLocU4ExtMain.smulGL l1 h1 x, GenLocU4ExtMain.smulGL l2 h2 y, GenLocU4ExtMain.smulGL l3 h3 z,
    hax.smul h1 n1, hby.smul h2 n2, hcz.smul h3 n3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [GenLocU4ExtMain.coe_smulGL, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hx]
    rw [mul_assoc]
  · simp only [GenLocU4ExtMain.coe_smulGL, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hy]
    rw [mul_assoc]
  · simp only [GenLocU4ExtMain.coe_smulGL, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hz]
    rw [mul_assoc]
  · simp only [GenLocU4ExtMain.coe_smulGL, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hxy, smul_neg]
    rw [mul_comm l1 l2]
  · simp only [GenLocU4ExtMain.coe_smulGL, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hxz]
    rw [mul_comm l1 l3]
  · simp only [GenLocU4ExtMain.coe_smulGL, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hyz]
    rw [mul_comm l2 l3]
  · rintro ⟨m, hm⟩
    apply hn
    refine ⟨l3⁻¹ * m, ?_⟩
    rw [GenLocU4ExtMain.coe_smulGL] at hm
    rw [mul_smul, ← hm, smul_smul, inv_mul_cancel₀ h3, one_smul]

theorem exists_scalar_pm (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    {s : K} (hs : s ^ (p ^ f + 1) = 1) :
    ∃ l : K, l ≠ 0 ∧ l ^ (p ^ f + 1) = 1 ∧ (l * l * s = 1 ∨ l * l * s = -1) := by
  by_cases hsq : GenLocU4ExtMu.IsSqM (p ^ f) s
  · obtain ⟨μ, hμ, hμs⟩ := hsq
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      simp at hμ
    refine ⟨μ⁻¹, inv_ne_zero hμ0, by rw [inv_pow, hμ, inv_one], Or.inl ?_⟩
    rw [← hμs]
    field_simp
  · obtain ⟨ω, hω, hωs⟩ := GenLocU4ExtMu.exists_omega hp hp2 hK hq hs hsq
    have hω0 : ω ≠ 0 := by
      rintro rfl
      simp at hω
    exact ⟨ω, hω0, hω, Or.inr hωs⟩

theorem Triple.pm (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    {sx sy sz : K} (T : Triple α sx sy sz) (nx : sx ^ (p ^ f + 1) = 1) (ny : sy ^ (p ^ f + 1) = 1)
    (nz : sz ^ (p ^ f + 1) = 1) :
    ∃ ex ey ez : K, (ex = 1 ∨ ex = -1) ∧ (ey = 1 ∨ ey = -1) ∧ (ez = 1 ∨ ez = -1) ∧ Triple α ex ey ez := by
  obtain ⟨l1, h1, n1, e1⟩ := exists_scalar_pm hp hp2 hK hq nx
  obtain ⟨l2, h2, n2, e2⟩ := exists_scalar_pm hp hp2 hK hq ny
  obtain ⟨l3, h3, n3, e3⟩ := exists_scalar_pm hp hp2 hK hq nz
  exact ⟨_, _, _, e1, e2, e3, T.scale h1 h2 h3 n1 n2 n3⟩

omit [Finite K] in
theorem Triple.cases (h : UnitaryFieldData p f K) {ex ey ez : K} (hx : ex = 1 ∨ ex = -1) (hy : ey = 1 ∨ ey = -1)
    (hz : ez = 1 ∨ ez = -1) (T : Triple α ex ey ez) :
    Triple α 1 1 1 ∨ Triple α 1 1 (-1) ∨ Triple α (-1) (-1) 1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl
  · exact Or.inl T
  · exact Or.inr (Or.inl T)
  · left; simpa using T.rel1 h
  · right; left; simpa using T.rel1 h
  · left; simpa using T.rel2 h
  · right; left; simpa using T.rel2 h
  · exact Or.inr (Or.inr T)
  · right; left; simpa using T.rel3 h

@[expose] def Pair (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) (sx sy : K) : Prop :=
  ∃ (a b : A) (x y : GL (Fin 4) K), IsLiftU α a x ∧ IsLiftU α b y ∧
    (x : Matrix (Fin 4) (Fin 4) K) * x = sx • 1 ∧ (y : Matrix (Fin 4) (Fin 4) K) * y = sy • 1 ∧
    (x : Matrix (Fin 4) (Fin 4) K) * y = -((y : Matrix (Fin 4) (Fin 4) K) * x)

omit [Finite K] in
theorem Pair.rel1 (h : UnitaryFieldData p f K) {sx sy : K} (T : Pair α sx sy) : Pair α sx (-(sx * sy)) := by
  obtain ⟨a, b, x, y, hax, hby, hx, hy, hxy⟩ := T
  have hyx : (y : Matrix (Fin 4) (Fin 4) K) * x = -((x : Matrix (Fin 4) (Fin 4) K) * y) := by rw [hxy]; simp
  refine ⟨a, a * b, x, x * y, hax, hax.mul h hby, hx, ?_, ?_⟩
  · rw [Units.val_mul]
    calc (x : Matrix (Fin 4) (Fin 4) K) * y * ((x : Matrix (Fin 4) (Fin 4) K) * y)
        = (x : Matrix (Fin 4) (Fin 4) K) * ((y : Matrix (Fin 4) (Fin 4) K) * x) * y := by simp only [Matrix.mul_assoc]
      _ = -((x * x) * (y * y)) := by rw [hyx]; simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = (-(sx * sy)) • 1 := by
          rw [hx, hy, Matrix.smul_mul, Matrix.one_mul, smul_smul, neg_smul, mul_comm]
  · rw [Units.val_mul]
    have e : (x : Matrix (Fin 4) (Fin 4) K) * y * x =
        -((x : Matrix (Fin 4) (Fin 4) K) * ((x : Matrix (Fin 4) (Fin 4) K) * y)) := by
      rw [Matrix.mul_assoc, hyx, Matrix.mul_neg]
    rw [e, neg_neg]

omit [Finite K] in
theorem Pair.rel2 (h : UnitaryFieldData p f K) {sx sy : K} (T : Pair α sx sy) : Pair α sy (-(sx * sy)) := by
  obtain ⟨a, b, x, y, hax, hby, hx, hy, hxy⟩ := T
  have hyx : (y : Matrix (Fin 4) (Fin 4) K) * x = -((x : Matrix (Fin 4) (Fin 4) K) * y) := by rw [hxy]; simp
  refine ⟨b, a * b, y, x * y, hby, hax.mul h hby, hy, ?_, ?_⟩
  · rw [Units.val_mul]
    calc (x : Matrix (Fin 4) (Fin 4) K) * y * ((x : Matrix (Fin 4) (Fin 4) K) * y)
        = (x : Matrix (Fin 4) (Fin 4) K) * ((y : Matrix (Fin 4) (Fin 4) K) * x) * y := by simp only [Matrix.mul_assoc]
      _ = -((x * x) * (y * y)) := by rw [hyx]; simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = (-(sx * sy)) • 1 := by
          rw [hx, hy, Matrix.smul_mul, Matrix.one_mul, smul_smul, neg_smul, mul_comm]
  · rw [Units.val_mul, ← Matrix.mul_assoc, hyx, Matrix.neg_mul]

omit [Finite K] in
theorem Pair.scale {sx sy : K} (T : Pair α sx sy) {l1 l2 : K} (h1 : l1 ≠ 0) (h2 : l2 ≠ 0)
    (n1 : l1 ^ (p ^ f + 1) = 1) (n2 : l2 ^ (p ^ f + 1) = 1) : Pair α (l1 * l1 * sx) (l2 * l2 * sy) := by
  obtain ⟨a, b, x, y, hax, hby, hx, hy, hxy⟩ := T
  refine ⟨a, b, GenLocU4ExtMain.smulGL l1 h1 x, GenLocU4ExtMain.smulGL l2 h2 y,
    hax.smul h1 n1, hby.smul h2 n2, ?_, ?_, ?_⟩
  · simp only [GenLocU4ExtMain.coe_smulGL, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hx]
    rw [mul_assoc]
  · simp only [GenLocU4ExtMain.coe_smulGL, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hy]
    rw [mul_assoc]
  · simp only [GenLocU4ExtMain.coe_smulGL, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hxy, smul_neg]
    rw [mul_comm l1 l2]

theorem Pair.pm (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    {sx sy : K} (T : Pair α sx sy) (nx : sx ^ (p ^ f + 1) = 1) (ny : sy ^ (p ^ f + 1) = 1) :
    ∃ ex ey : K, (ex = 1 ∨ ex = -1) ∧ (ey = 1 ∨ ey = -1) ∧ Pair α ex ey := by
  obtain ⟨l1, h1, n1, e1⟩ := exists_scalar_pm hp hp2 hK hq nx
  obtain ⟨l2, h2, n2, e2⟩ := exists_scalar_pm hp hp2 hK hq ny
  exact ⟨_, _, e1, e2, T.scale h1 h2 n1 n2⟩

omit [Finite K] in
theorem Pair.cases (h : UnitaryFieldData p f K) {ex ey : K} (hx : ex = 1 ∨ ex = -1) (hy : ey = 1 ∨ ey = -1)
    (T : Pair α ex ey) : Pair α 1 1 ∨ Pair α (-1) (-1) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact Or.inl T
  · left; simpa using T.rel1 h
  · left; simpa using T.rel2 h
  · exact Or.inr T

theorem lift_sq (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) {e : A} (hee : α e * α e = 1)
    {u : GL (Fin 4) K} (hu : IsLiftU α e u) :
    ∃ s : K, (u : Matrix (Fin 4) (Fin 4) K) * u = s • 1 ∧ s ^ (p ^ f + 1) = 1 := by
  obtain ⟨l, -, hl⟩ := GenLocU4ExtMain.rho_sq_scalar_U hp hp2 hK (α e) u hee hu.2
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have := GenLocU4ExtMain.norm_one_of_sq h u l hu.1 hl
  exact ⟨l, hl, by rw [pow_succ]; exact this⟩

theorem exists_pair (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    (hA : IsRank23 A) (ρ : A → GL (Fin 4) K)
    (hU : ∀ a, IsUnitaryU (p ^ f) (ρ a : Matrix (Fin 4) (Fin 4) K))
    (hρ : ∀ (a : A) (g : ↥(StatedSU 4 (p ^ f) K)),
      (((α a g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (ρ a : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((ρ a)⁻¹ : GL (Fin 4) K))
    {a b : A} (hanti : (ρ a : Matrix (Fin 4) (Fin 4) K) * (ρ b : Matrix (Fin 4) (Fin 4) K) =
      -((ρ b : Matrix (Fin 4) (Fin 4) K) * (ρ a : Matrix (Fin 4) (Fin 4) K))) :
    Pair α 1 1 ∨ Pair α (-1) (-1) := by
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have hsq_aut : ∀ e : A, α e * α e = 1 := fun e => by
    rw [← map_mul, WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 e, map_one]
  obtain ⟨sx, hsx, nx⟩ := lift_sq hp hp2 hK (hsq_aut a) (show IsLiftU α a (ρ a) from ⟨hU a, hρ a⟩)
  obtain ⟨sy, hsy, ny⟩ := lift_sq hp hp2 hK (hsq_aut b) (show IsLiftU α b (ρ b) from ⟨hU b, hρ b⟩)
  have T : Pair α sx sy := ⟨a, b, ρ a, ρ b, ⟨hU a, hρ a⟩, ⟨hU b, hρ b⟩, hsx, hsy, hanti⟩
  obtain ⟨ex, ey, hex, hey, T'⟩ := T.pm hp hp2 hK hq nx ny
  exact T'.cases h hex hey

theorem exists_comm_liftU (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) [Finite A]
    (hA : IsRank23 A) (ρ : A → GL (Fin 4) K)
    (hU : ∀ a, IsUnitaryU (p ^ f) (ρ a : Matrix (Fin 4) (Fin 4) K))
    (hρ : ∀ (a : A) (g : ↥(StatedSU 4 (p ^ f) K)),
      (((α a g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (ρ a : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((ρ a)⁻¹ : GL (Fin 4) K))
    {a b : A} (hxy : (ρ a : Matrix (Fin 4) (Fin 4) K) * (ρ b : Matrix (Fin 4) (Fin 4) K) =
      -((ρ b : Matrix (Fin 4) (Fin 4) K) * (ρ a : Matrix (Fin 4) (Fin 4) K))) (c₀ : A) :
    ∃ (c : A) (z : GL (Fin 4) K), (c = c₀ ∨ c = c₀ * a ∨ c = c₀ * b ∨ c = c₀ * (a * b)) ∧ IsLiftU α c z ∧
      (ρ a : Matrix (Fin 4) (Fin 4) K) * z = (z : Matrix (Fin 4) (Fin 4) K) * ρ a ∧
      (ρ b : Matrix (Fin 4) (Fin 4) K) * z = (z : Matrix (Fin 4) (Fin 4) K) * ρ b := by
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have := hA.1
  have hsq_aut : ∀ e : A, α e * α e = 1 := fun e => by
    rw [← map_mul, WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 e, map_one]
  have hcomm_aut : ∀ e g : A, α e * α g = α g * α e := fun e g => by
    rw [← map_mul, ← map_mul, mul_comm' e g]
  have hlift : ∀ e, IsLiftU α e (ρ e) := fun e => ⟨hU e, hρ e⟩
  have sgn : ∀ d : A, ∃ ε : K, (ε = 1 ∨ ε = -1) ∧
      (ρ c₀ : Matrix (Fin 4) (Fin 4) K) * (ρ d : Matrix (Fin 4) (Fin 4) K) =
        ε • ((ρ d : Matrix (Fin 4) (Fin 4) K) * (ρ c₀ : Matrix (Fin 4) (Fin 4) K)) := by
    intro d
    rcases GenLocU4Basic.comm_or_anticomm_U4_of_card hp hp2 hK α ρ hρ hsq_aut c₀ d (hcomm_aut c₀ d) with h1 | h1
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [one_smul]
      simpa [Units.val_mul] using congrArg (fun u : GL (Fin 4) K => (u : Matrix (Fin 4) (Fin 4) K)) h1
    · exact ⟨-1, Or.inr rfl, by rw [h1, neg_smul, one_smul]⟩
  obtain ⟨ε1, h1, hε1⟩ := sgn a
  obtain ⟨ε2, h2, hε2⟩ := sgn b
  rcases GenLocL4Q.adjust_signs hxy h1 h2 hε1 hε2 with ⟨-, -, e1, e2⟩ | ⟨-, -, e1, e2⟩ | ⟨-, -, e1, e2⟩ | ⟨-, -, e1, e2⟩
  · exact ⟨c₀, ρ c₀, Or.inl rfl, hlift c₀, e1, e2⟩
  · refine ⟨c₀ * a, ρ c₀ * ρ a, Or.inr (Or.inl rfl), (hlift c₀).mul h (hlift a), ?_, ?_⟩
    · rw [Units.val_mul]; exact e1
    · rw [Units.val_mul]; exact e2
  · refine ⟨c₀ * b, ρ c₀ * ρ b, Or.inr (Or.inr (Or.inl rfl)), (hlift c₀).mul h (hlift b), ?_, ?_⟩
    · rw [Units.val_mul]; exact e1
    · rw [Units.val_mul]; exact e2
  · refine ⟨c₀ * (a * b), ρ c₀ * (ρ a * ρ b), Or.inr (Or.inr (Or.inr rfl)),
      (hlift c₀).mul h ((hlift a).mul h (hlift b)), ?_, ?_⟩
    · rw [Units.val_mul, Units.val_mul]; exact e1
    · rw [Units.val_mul, Units.val_mul]; exact e2

theorem exists_triple (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) [Finite A]
    (hA : IsRank23 A) (hr : pRank 2 A = 3) (hinj : Function.Injective α) (ρ : A → GL (Fin 4) K)
    (hU : ∀ a, IsUnitaryU (p ^ f) (ρ a : Matrix (Fin 4) (Fin 4) K))
    (hρ : ∀ (a : A) (g : ↥(StatedSU 4 (p ^ f) K)),
      (((α a g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (ρ a : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((ρ a)⁻¹ : GL (Fin 4) K))
    {a b : A} (hanti : (ρ a : Matrix (Fin 4) (Fin 4) K) * (ρ b : Matrix (Fin 4) (Fin 4) K) =
      -((ρ b : Matrix (Fin 4) (Fin 4) K) * (ρ a : Matrix (Fin 4) (Fin 4) K))) :
    ∃ sx sy sz : K, sx ^ (p ^ f + 1) = 1 ∧ sy ^ (p ^ f + 1) = 1 ∧ sz ^ (p ^ f + 1) = 1 ∧ Triple α sx sy sz := by
  classical
  have := hA.1
  have hsq_aut : ∀ e : A, α e * α e = 1 := fun e => by
    rw [← map_mul, WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 e, map_one]
  have hlift : ∀ e, IsLiftU α e (ρ e) := fun e => ⟨hU e, hρ e⟩
  have haa : a * a = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 a
  have hbb : b * b = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 b
  have hab : (a * b) * (a * b) = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 (a * b)
  have hcard : Nat.card A = 8 := by
    rw [GenLocBasic.card_eq_two_pow_pRank_type hA.1, hr]; norm_num
  have := Fintype.ofFinite A
  obtain ⟨c₀, -, hc₀⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := ({1, a, b, a * b} : Finset A))
    (t := Finset.univ) (by
      have h1 : ({1, a, b, a * b} : Finset A).card ≤ 4 := Finset.card_le_four
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]; omega)
  obtain ⟨c, z, hc, hcz, hxz, hyz⟩ := exists_comm_liftU hp hp2 hK hA ρ hU hρ hanti c₀
  have hc1 : c ≠ 1 := by
    rcases hc with rfl | rfl | rfl | rfl
    · intro h; exact hc₀ (by simp [h])
    · intro h
      apply hc₀
      have : c₀ = a := by
        have := inv_eq_of_mul_eq_one_left h
        rw [← this]; exact (inv_eq_of_mul_eq_one_right haa)
      simp [this]
    · intro h
      apply hc₀
      have : c₀ = b := by
        have := inv_eq_of_mul_eq_one_left h
        rw [← this]; exact (inv_eq_of_mul_eq_one_right hbb)
      simp [this]
    · intro h
      apply hc₀
      have : c₀ = a * b := by
        have := inv_eq_of_mul_eq_one_left h
        rw [← this]; exact (inv_eq_of_mul_eq_one_right hab)
      simp [this]
  have hzn : NonScalar z := by
    rintro ⟨l, hl⟩
    apply hc1
    apply hinj
    rw [map_one]
    ext g : 1
    apply hcz.fix g
    rw [hl]
    simp
  obtain ⟨sx, hsx, nx⟩ := lift_sq hp hp2 hK (hsq_aut a) (hlift a)
  obtain ⟨sy, hsy, ny⟩ := lift_sq hp hp2 hK (hsq_aut b) (hlift b)
  obtain ⟨sz, hsz, nz⟩ := lift_sq hp hp2 hK (hsq_aut c) hcz
  exact ⟨sx, sy, sz, nx, ny, nz, a, b, c, ρ a, ρ b, z, hlift a, hlift b, hcz, hsx, hsy, hsz, hanti, hxz, hyz, hzn⟩

theorem classify_rank3 (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    [Finite A] (hA : IsRank23 A) (hr : pRank 2 A = 3) (hinj : Function.Injective α) (ρ : A → GL (Fin 4) K)
    (hU : ∀ a, IsUnitaryU (p ^ f) (ρ a : Matrix (Fin 4) (Fin 4) K))
    (hρ : ∀ (a : A) (g : ↥(StatedSU 4 (p ^ f) K)),
      (((α a g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (ρ a : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((ρ a)⁻¹ : GL (Fin 4) K))
    {a b : A} (hanti : (ρ a : Matrix (Fin 4) (Fin 4) K) * (ρ b : Matrix (Fin 4) (Fin 4) K) =
      -((ρ b : Matrix (Fin 4) (Fin 4) K) * (ρ a : Matrix (Fin 4) (Fin 4) K))) :
    Triple α 1 1 1 ∨ Triple α 1 1 (-1) ∨ Triple α (-1) (-1) 1 := by
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  obtain ⟨sx, sy, sz, nx, ny, nz, T⟩ := exists_triple hp hp2 hK hA hr hinj ρ hU hρ hanti
  obtain ⟨ex, ey, ez, hex, hey, hez, T'⟩ := T.pm hp hp2 hK hq nx ny nz
  exact T'.cases h hex hey hez

end GenLocU4QClass

end CFSG.GH74.Generic.BProg.B2
