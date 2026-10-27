module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4QHyp
public import CFSG.GH74.Generic.BProg.B2.GenLocU4Q1

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Subgroup Matrix
open scoped MatrixGroups

open GenLocU4Basic GenLocU4QLift GenLocU4QClass GenLocU4QHyp

namespace GenLocU4Q

variable {K : Type} [Field K] [Finite K]

@[expose] def Su4Q2Stmt (K : Type) [Field K] [Finite K] (p f : ℕ) : Prop :=
  p.Prime → p ≠ 2 → Nat.card K = (p ^ f) ^ 2 → p ^ f % 4 = 1 →
    ∀ (Γ : Subgroup ↥(StatedSU 4 (p ^ f) K)) (x y : GL (Fin 4) K),
      (x * x : GL (Fin 4) K) = -1 → (y * y : GL (Fin 4) K) = -1 →
      (x : Matrix (Fin 4) (Fin 4) K) * y = -((y : Matrix (Fin 4) (Fin 4) K) * x) →
      IsUnitaryU (p ^ f) (x : Matrix (Fin 4) (Fin 4) K) → IsUnitaryU (p ^ f) (y : Matrix (Fin 4) (Fin 4) K) →
      (∀ g : ↥(StatedSU 4 (p ^ f) K), (g : GL (Fin 4) K) * x = x * g → g ∈ Γ) →
      (∀ g : ↥(StatedSU 4 (p ^ f) K), (g : GL (Fin 4) K) * y = y * g → g ∈ Γ) → Γ = ⊤

@[expose] def Su4Q2SplitStmt (K : Type) [Field K] [Finite K] (p f : ℕ) : Prop :=
  p.Prime → p ≠ 2 → Nat.card K = (p ^ f) ^ 2 → p ^ f % 4 = 1 →
    ∀ (Γ : Subgroup ↥(StatedSU 4 (p ^ f) K)) (x y z : GL (Fin 4) K),
      IsUnitaryU (p ^ f) (x : Matrix (Fin 4) (Fin 4) K) → IsUnitaryU (p ^ f) (y : Matrix (Fin 4) (Fin 4) K) →
      IsUnitaryU (p ^ f) (z : Matrix (Fin 4) (Fin 4) K) →
      (x * x : GL (Fin 4) K) = -1 → (y * y : GL (Fin 4) K) = -1 → (z * z : GL (Fin 4) K) = 1 →
      (x : Matrix (Fin 4) (Fin 4) K) * y = -((y : Matrix (Fin 4) (Fin 4) K) * x) →
      (x : Matrix (Fin 4) (Fin 4) K) * z = (z : Matrix (Fin 4) (Fin 4) K) * x →
      (y : Matrix (Fin 4) (Fin 4) K) * z = (z : Matrix (Fin 4) (Fin 4) K) * y → NonScalar z →
      HypPlanes Γ x y z → Γ = ⊤

@[expose] def Su4Q10Stmt (K : Type) [Field K] [Finite K] (p f : ℕ) : Prop :=
  p.Prime → p ≠ 2 → Nat.card K = (p ^ f) ^ 2 → p ^ f % 4 = 1 →
    ∀ {A : Type} [Group A] [Finite A] (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)), IsRank23 A → pRank 2 A = 3 →
      Triple α 1 1 1 → gammaAct α = ⊤

@[expose] def Su4Q11Stmt (K : Type) [Field K] [Finite K] (p f : ℕ) : Prop :=
  p.Prime → p ≠ 2 → Nat.card K = (p ^ f) ^ 2 → p ^ f % 4 = 1 →
    ∀ {A : Type} [Group A] [Finite A] (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)), IsRank23 A → pRank 2 A = 3 →
      Triple α 1 1 (-1) → gammaAct α = ⊤

variable {p f : ℕ}

omit [Finite K] in
theorem gl_sq_eq {x : GL (Fin 4) K} {s : K} (h : (x : Matrix (Fin 4) (Fin 4) K) * x = s • 1) :
    ((x * x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = s • 1 := by
  rw [Units.val_mul]; exact h

omit [Finite K] in
theorem gl_sq_one {x : GL (Fin 4) K} (h : (x : Matrix (Fin 4) (Fin 4) K) * x = (1 : K) • 1) : x * x = 1 :=
  Units.ext (by rw [gl_sq_eq h, one_smul]; rfl)

omit [Finite K] in
theorem gl_sq_neg_one {x : GL (Fin 4) K} (h : (x : Matrix (Fin 4) (Fin 4) K) * x = (-1 : K) • 1) :
    (x * x : GL (Fin 4) K) = -1 :=
  Units.ext (by rw [gl_sq_eq h, neg_smul, one_smul]; simp)

theorem gammaAct_quat_rank2 (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    (hQ2 : Su4Q2Stmt K p f) {A : Type} [Group A] [Finite A] (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K))
    (hA : IsRank23 A) (hr : pRank 2 A = 2) (ρ : A → GL (Fin 4) K)
    (hU : ∀ a, IsUnitaryU (p ^ f) (ρ a : Matrix (Fin 4) (Fin 4) K))
    (hρ : ∀ (a : A) (g : ↥(StatedSU 4 (p ^ f) K)),
      (((α a g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (ρ a : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((ρ a)⁻¹ : GL (Fin 4) K))
    {a b : A} (hanti : (ρ a : Matrix (Fin 4) (Fin 4) K) * (ρ b : Matrix (Fin 4) (Fin 4) K) =
      -((ρ b : Matrix (Fin 4) (Fin 4) K) * (ρ a : Matrix (Fin 4) (Fin 4) K))) :
    gammaAct α = ⊤ := by
  have h2 : (2 : K) ≠ 0 := GenLocU4ExtFrame.two_ne_zero_of_card hp hp2 hK
  rcases exists_pair hp hp2 hK hq hA ρ hU hρ hanti with P | P
  · obtain ⟨a', b', x, y, hax, hby, hx, hy, hxy⟩ := P
    have hyx : (y : Matrix (Fin 4) (Fin 4) K) * x = -((x : Matrix (Fin 4) (Fin 4) K) * y) := by rw [hxy]; simp
    have nx := GenLocL4Q.not_scalar_of_anticomm h2 hxy
    have ny := GenLocL4Q.not_scalar_of_anticomm h2 hyx
    exact eq_top_of_centralizers_q1 hp hp2 hK hq (gammaAct α) x y (gl_sq_one hx) (gl_sq_one hy) hxy hax.1 hby.1
      (fun g hg => mem_gammaAct_of_oneU hp hp2 hK α hA hr hax nx g ((comm_iff g x).1 hg))
      (fun g hg => mem_gammaAct_of_oneU hp hp2 hK α hA hr hby ny g ((comm_iff g y).1 hg))
  · obtain ⟨a', b', x, y, hax, hby, hx, hy, hxy⟩ := P
    have hyx : (y : Matrix (Fin 4) (Fin 4) K) * x = -((x : Matrix (Fin 4) (Fin 4) K) * y) := by rw [hxy]; simp
    have nx := GenLocL4Q.not_scalar_of_anticomm h2 hxy
    have ny := GenLocL4Q.not_scalar_of_anticomm h2 hyx
    exact hQ2 hp hp2 hK hq (gammaAct α) x y (gl_sq_neg_one hx) (gl_sq_neg_one hy) hxy hax.1 hby.1
      (fun g hg => mem_gammaAct_of_oneU hp hp2 hK α hA hr hax nx g ((comm_iff g x).1 hg))
      (fun g hg => mem_gammaAct_of_oneU hp hp2 hK α hA hr hby ny g ((comm_iff g y).1 hg))

theorem gammaAct_quat_rank3 (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    (hQ2s : Su4Q2SplitStmt K p f) (hQ10 : Su4Q10Stmt K p f) (hQ11 : Su4Q11Stmt K p f)
    {A : Type} [Group A] [Finite A] (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K))
    (hA : IsRank23 A) (hr : pRank 2 A = 3) (hinj : Function.Injective α) (ρ : A → GL (Fin 4) K)
    (hU : ∀ a, IsUnitaryU (p ^ f) (ρ a : Matrix (Fin 4) (Fin 4) K))
    (hρ : ∀ (a : A) (g : ↥(StatedSU 4 (p ^ f) K)),
      (((α a g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (ρ a : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((ρ a)⁻¹ : GL (Fin 4) K))
    {a b : A} (hanti : (ρ a : Matrix (Fin 4) (Fin 4) K) * (ρ b : Matrix (Fin 4) (Fin 4) K) =
      -((ρ b : Matrix (Fin 4) (Fin 4) K) * (ρ a : Matrix (Fin 4) (Fin 4) K))) :
    gammaAct α = ⊤ := by
  rcases classify_rank3 hp hp2 hK hq hA hr hinj ρ hU hρ hanti with T | T | T
  · exact hQ10 hp hp2 hK hq α hA hr T
  · exact hQ11 hp hp2 hK hq α hA hr T
  · obtain ⟨x, y, z, hxU, hyU, hzU, hx, hy, hz, hxy, hxz, hyz, hzn, hH⟩ := hypPlanes_of_triple hp hp2 hK α hA hr T
    exact hQ2s hp hp2 hK hq (gammaAct α) x y z hxU hyU hzU (gl_sq_neg_one hx) (gl_sq_neg_one hy) (gl_sq_one hz)
      hxy hxz hyz hzn hH

theorem lifts_proportional (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) {A : Type} [Group A]
    (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) (ρ : A → GL (Fin 4) K)
    (hρ : ∀ (a : A) (g : ↥(StatedSU 4 (p ^ f) K)),
      (((α a g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (ρ a : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((ρ a)⁻¹ : GL (Fin 4) K))
    {e e' : A} (hee : α e = α e') :
    ∃ l : K, l ≠ 0 ∧ (ρ e : Matrix (Fin 4) (Fin 4) K) = l • (ρ e' : Matrix (Fin 4) (Fin 4) K) := by
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  refine GenLocU4Basic.proportional_of_conj_eq h hp2 (fun g hg => ?_)
  have h1 := hρ e ⟨g, hg⟩
  have h2 := hρ e' ⟨g, hg⟩
  rw [hee] at h1
  apply Units.ext
  simp only [Units.val_mul]
  rw [← h1, h2]

theorem gammaAct_su4_quat_of (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    (hQ2 : Su4Q2Stmt K p f) (hQ2s : Su4Q2SplitStmt K p f) (hQ10 : Su4Q10Stmt K p f) (hQ11 : Su4Q11Stmt K p f)
    {A : Type} [Group A] [Finite A] (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) (hA : IsRank23 A)
    (ρ : A → GL (Fin 4) K) (hU : ∀ a, IsUnitaryU (p ^ f) (ρ a : Matrix (Fin 4) (Fin 4) K))
    (hρ : ∀ (a : A) (g : ↥(StatedSU 4 (p ^ f) K)),
      (((α a g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (ρ a : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((ρ a)⁻¹ : GL (Fin 4) K))
    (a b : A) (hanti : (ρ a : Matrix (Fin 4) (Fin 4) K) * (ρ b : Matrix (Fin 4) (Fin 4) K) =
      -((ρ b : Matrix (Fin 4) (Fin 4) K) * (ρ a : Matrix (Fin 4) (Fin 4) K))) :
    gammaAct α = ⊤ := by
  rcases hA.2 with hr | hr
  · exact gammaAct_quat_rank2 hp hp2 hK hq hQ2 α hA hr ρ hU hρ hanti
  · by_cases hker : ∃ E : Subgroup A, pRank 2 A - 1 ≤ pRank 2 ↥E ∧ E ≤ α.ker
    · obtain ⟨E, hE, hEk⟩ := hker
      exact gammaAct_eq_top_of_le_ker α hE hEk
    · have hker' : ∀ E : Subgroup A, pRank 2 A - 1 ≤ pRank 2 ↥E → ¬ E ≤ α.ker :=
        fun E hE hEk => hker ⟨E, hE, hEk⟩
      obtain ⟨hr23, hgam, -⟩ := range_reduction α hA hker'
      rw [hgam]
      have : Finite ↥α.range := Finite.of_surjective _ α.rangeRestrict_surjective
      have hspec : ∀ t : ↥α.range, α (Classical.choose t.2) = t.1 := fun t => Classical.choose_spec t.2
      let ρ' : ↥α.range → GL (Fin 4) K := fun t => ρ (Classical.choose t.2)
      have hU' : ∀ t, IsUnitaryU (p ^ f) (ρ' t : Matrix (Fin 4) (Fin 4) K) := fun t => hU _
      have hρ' : ∀ (t : ↥α.range) (g : ↥(StatedSU 4 (p ^ f) K)),
          (((α.range.subtype t g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
            (ρ' t : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
              ((ρ' t)⁻¹ : GL (Fin 4) K) := by
        intro t g
        have := hρ (Classical.choose t.2) g
        rw [hspec t] at this
        exact this
      let a' : ↥α.range := ⟨α a, a, rfl⟩
      let b' : ↥α.range := ⟨α b, b, rfl⟩
      obtain ⟨l1, hl1, e1⟩ := lifts_proportional hp hp2 hK α ρ hρ (e := Classical.choose a'.2) (e' := a) (hspec a')
      obtain ⟨l2, hl2, e2⟩ := lifts_proportional hp hp2 hK α ρ hρ (e := Classical.choose b'.2) (e' := b) (hspec b')
      have hanti' : (ρ' a' : Matrix (Fin 4) (Fin 4) K) * (ρ' b' : Matrix (Fin 4) (Fin 4) K) =
          -((ρ' b' : Matrix (Fin 4) (Fin 4) K) * (ρ' a' : Matrix (Fin 4) (Fin 4) K)) := by
        show (ρ (Classical.choose a'.2) : Matrix (Fin 4) (Fin 4) K) * (ρ (Classical.choose b'.2) : Matrix (Fin 4) (Fin 4) K) =
          -((ρ (Classical.choose b'.2) : Matrix (Fin 4) (Fin 4) K) * (ρ (Classical.choose a'.2) : Matrix (Fin 4) (Fin 4) K))
        rw [e1, e2, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul, hanti,
          smul_neg, mul_comm l1 l2]
      rcases hr23.2 with hr2 | hr3
      · exact gammaAct_quat_rank2 hp hp2 hK hq hQ2 α.range.subtype hr23 hr2 ρ' hU' hρ' hanti'
      · exact gammaAct_quat_rank3 hp hp2 hK hq hQ2s hQ10 hQ11 α.range.subtype hr23 hr3 Subtype.val_injective ρ'
          hU' hρ' hanti'

end GenLocU4Q

end CFSG.GH74.Generic.BProg.B2
