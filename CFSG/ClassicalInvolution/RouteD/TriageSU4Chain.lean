module

public import CFSG.ClassicalInvolution.RouteD.TypeARecognition

public section

namespace CFSG.ClassicalInvolution.RouteD.SU4Pattern

open CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
open scoped MatrixGroups

theorem eq_blockSL_neg_one {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {m : ℕ} (hm : 2 < m) {X : Type}
    [Group X] {θ : SL(m, F) →* X} (hker : θ.ker ≤ Subgroup.center SL(m, F)) {j : ℕ}
    (hj : j + 2 ≤ m) {a : X} (ha : a ∈ (blockSL F m 2 j hj).range.map θ) (ha2 : orderOf a = 2) :
    a = θ (blockSL F m 2 j hj (-1)) := by
  obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := ha
  have hinj := comp_blockSL_injective hker hj hm
  have haa : θ (blockSL F m 2 j hj A) * θ (blockSL F m 2 j hj A) = 1 := by
    rw [← pow_two]
    have := pow_orderOf_eq_one (θ (blockSL F m 2 j hj A))
    rwa [ha2] at this
  have hAA : A * A = 1 := by
    apply hinj
    simp only [MonoidHom.comp_apply, map_mul, map_one]
    exact haa
  rcases sl2_sq_eq_one h2 hAA with h | h
  · exfalso
    subst h
    rw [map_one, map_one, orderOf_one] at ha2
    omega
  · rw [h]

theorem blockSL_neg_one_mul_mem_center (F : Type) [Field F] :
    blockSL F 4 2 0 (by omega) (-1) * blockSL F 4 2 2 (by omega) (-1) ∈
      Subgroup.center SL(4, F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, by norm_num, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL_neg_one, coe_blockSL_neg_one,
    negBlock_eq_diagonal, negBlock_eq_diagonal, Matrix.diagonal_mul_diagonal]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.scalar_apply]

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem chain_le_centralizer_mul (hq : 4 ≤ p ^ f) (h2 : (2 : GaloisField p f) ≠ 0)
    {K K₁ K₂ : Subgroup G} {z w : G} (hz : IsClassicalMember p f K z)
    (hw : IsClassicalMember p f K₂ w) (c02 : Commutes K K₂)
    (p01 : ∃ W, LinearBlockStandardPair (GaloisField p f) W K K₁)
    (p12 : ∃ W, LinearBlockStandardPair (GaloisField p f) W K₁ K₂) :
    K₁ ≤ Subgroup.centralizer ({z * w} : Set G) := by
  obtain ⟨ψ, hker, -, hblk⟩ := exists_psi_of_chain (p := p) (f := f) hq (m := 1) le_rfl
    (U := ![K, K₁, K₂])
    (fun i j hij => by
      have hi := i.isLt
      have hj := j.isLt
      have : (i : ℕ) = 0 ∧ (j : ℕ) = 2 := by omega
      have e1 : i = 0 := Fin.ext this.1
      have e2 : j = 2 := Fin.ext this.2
      subst e1 e2
      exact c02)
    (fun i j hij => by
      have hi := i.isLt
      have hj := j.isLt
      have : ((i : ℕ) = 0 ∧ (j : ℕ) = 1) ∨ ((i : ℕ) = 1 ∧ (j : ℕ) = 2) := by omega
      rcases this with ⟨h1, h3⟩ | ⟨h1, h3⟩
      · have e1 : i = 0 := Fin.ext h1
        have e2 : j = 1 := Fin.ext h3
        subst e1 e2
        exact p01
      · have e1 : i = 1 := Fin.ext h1
        have e2 : j = 2 := Fin.ext h3
        subst e1 e2
        exact p12)
  have hK : (blockSL (GaloisField p f) 4 2 0 (by omega)).range.map ψ = K := hblk 0
  have hK₁ : (blockSL (GaloisField p f) 4 2 1 (by omega)).range.map ψ = K₁ := hblk 1
  have hK₂ : (blockSL (GaloisField p f) 4 2 2 (by omega)).range.map ψ = K₂ := hblk 2
  have hzmem : z ∈ (blockSL (GaloisField p f) 4 2 0 (by omega)).range.map ψ := by
    rw [hK]; exact hz.mem
  have hwmem : w ∈ (blockSL (GaloisField p f) 4 2 2 (by omega)).range.map ψ := by
    rw [hK₂]; exact hw.mem
  have hz' : z = ψ (blockSL (GaloisField p f) 4 2 0 (by omega) (-1)) :=
    eq_blockSL_neg_one (m := 4) h2 (by omega) hker (by omega) hzmem hz.orderOf_eq_two
  have hw' : w = ψ (blockSL (GaloisField p f) 4 2 2 (by omega) (-1)) :=
    eq_blockSL_neg_one (m := 4) h2 (by omega) hker (by omega) hwmem hw.orderOf_eq_two
  have hzw : z * w = ψ (blockSL (GaloisField p f) 4 2 0 (by omega) (-1) *
      blockSL (GaloisField p f) 4 2 2 (by omega) (-1)) := by
    rw [map_mul, ← hz', ← hw']
  intro k hk
  rw [← hK₁] at hk
  obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hk
  have hc := Subgroup.mem_center_iff.mp (blockSL_neg_one_mul_mem_center (GaloisField p f))
    (blockSL (GaloisField p f) 4 2 1 (by omega) A)
  rw [Subgroup.mem_centralizer_singleton_iff, hzw, ← map_mul, ← map_mul, hc]

end CFSG.ClassicalInvolution.RouteD.SU4Pattern
