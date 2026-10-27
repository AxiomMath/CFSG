module

public import CFSG.ClassicalInvolution.Asc77.AscIH8Std

public section


namespace CFSG.ClassicalInvolution.Asc77.T3Typed

open CFSG.LieType.Steinberg CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

section MatrixFacts

variable {F : Type*} [Field F]

theorem entries_of_commute_rot (h2 : (2 : F) ≠ 0) {g : Matrix (Fin 3) (Fin 3) F}
    (hg : g * embPair 2 (Phan.rotMat : Matrix (Fin 2) (Fin 2) F) =
      embPair 2 Phan.rotMat * g) :
    g 0 2 = 0 ∧ g 1 2 = 0 ∧ g 2 0 = 0 ∧ g 2 1 = 0 ∧ g 1 1 = g 0 0 ∧ g 1 0 = - g 0 1 := by
  have h00 := congrFun (congrFun hg 0) 0
  have h01 := congrFun (congrFun hg 0) 1
  have h02 := congrFun (congrFun hg 0) 2
  have h10 := congrFun (congrFun hg 1) 0
  have h11 := congrFun (congrFun hg 1) 1
  have h12 := congrFun (congrFun hg 1) 2
  have h20 := congrFun (congrFun hg 2) 0
  have h21 := congrFun (congrFun hg 2) 1
  have h22 := congrFun (congrFun hg 2) 2
  simp [embPair, Phan.rotMat, Matrix.mul_apply, Fin.sum_univ_three] at h00 h01 h02 h10 h11 h12
  simp [embPair, Phan.rotMat, Matrix.mul_apply, Fin.sum_univ_three] at h20 h21 h22
  have hneg : ∀ x : F, x = -x → x = 0 := fun x hx => by
    have h : (2 : F) * x = 0 := by linear_combination hx
    exact (mul_eq_zero.mp h).resolve_left h2
  have e02 : g 0 2 = 0 := hneg _ (by rw [h12] at h02; exact h02)
  have e12 : g 1 2 = 0 := by rw [h12, e02]
  have e20 : g 2 0 = 0 := hneg _ (by rw [h20] at h21; exact h21.symm)
  have e21 : g 2 1 = 0 := by rw [h20, e20]
  exact ⟨e02, e12, e20, e21, h10, by linear_combination (-1 : F) * h11⟩

theorem commute_of_commute_embPair_rot (h2 : (2 : F) ≠ 0) {g g' : Matrix (Fin 3) (Fin 3) F}
    (hg : g * embPair 2 (Phan.rotMat : Matrix (Fin 2) (Fin 2) F) = embPair 2 Phan.rotMat * g)
    (hg' : g' * embPair 2 (Phan.rotMat : Matrix (Fin 2) (Fin 2) F) =
      embPair 2 Phan.rotMat * g') : g * g' = g' * g := by
  obtain ⟨a02, a12, a20, a21, a11, a10⟩ := entries_of_commute_rot h2 hg
  obtain ⟨b02, b12, b20, b21, b11, b10⟩ := entries_of_commute_rot h2 hg'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, a02, a12, a20, a21, a11, a10, b02, b12, b20, b21,
      b11, b10] <;> ring

end MatrixFacts

section Linear

variable {F : Type} [Field F] [Finite F] {X : Type} [Group X]

theorem LinearBlockStandardPair.centralizer_comm (h4 : 4 ≤ Nat.card F) (h2 : (2 : F) ≠ 0)
    {W U V : Subgroup X} (h : WeakCT.LinearBlockStandardPair F W U V) {x y : X}
    (hxW : x ∈ W) (hyW : y ∈ W) (hxc : ∀ u ∈ U, x * u = u * x) (hyc : ∀ u ∈ U, y * u = u * y) :
    x * y = y * x := by
  obtain ⟨θ, hrange, hker, hU, hV⟩ := WeakCT.pair_normalize h
  rw [← hrange] at hxW hyW
  obtain ⟨g, rfl⟩ := hxW
  obtain ⟨g', rfl⟩ := hyW
  have key : ∀ g₀ : SL(3, F), (∀ u ∈ U, θ g₀ * u = u * θ g₀) →
      (g₀ : Matrix (Fin 3) (Fin 3) F) * embPair 2 (Phan.rotMat : Matrix (Fin 2) (Fin 2) F) =
        embPair 2 Phan.rotMat * (g₀ : Matrix (Fin 3) (Fin 3) F) := by
    intro g₀ hc
    have hcomm :=
      CFSG.ClassicalInvolution.Balance.StrongBalance.commute_of_perfect_of_commutator_mem_center
      (B12_perfect h4) (r := g₀) (fun s hs => by
        apply hker
        rw [MonoidHom.mem_ker]
        have := hc (θ s) (hU ▸ Subgroup.mem_map_of_mem θ hs)
        simp only [map_mul, map_inv]
        rw [this]
        group)
    have e := hcomm (WeakCT.blockSL F 3 2 0 (by omega) WeakCT.rotSL) ⟨WeakCT.rotSL, rfl⟩
    have e2 := congrArg (fun z : SL(3, F) => (z : Matrix (Fin 3) (Fin 3) F)) e
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL_zero] at e2
    exact e2
  have hmat := commute_of_commute_embPair_rot h2 (key g hxc) (key g' hyc)
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (by simpa using hmat)

omit [Finite F] in
theorem LinearBlockStandardPair.le_group {W U V : Subgroup X}
    (h : WeakCT.LinearBlockStandardPair F W U V) : U ≤ W ∧ V ≤ W := by
  obtain ⟨θ, hrange, -, hU, hV⟩ := WeakCT.pair_normalize h
  rw [← hrange, ← hU, ← hV]
  exact ⟨Subgroup.map_le_range _ _, Subgroup.map_le_range _ _⟩

end Linear

section Unitary

open CFSG.ClassicalInvolution.Models (suMat)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {X : Type} [Group X]

theorem UnitaryBlockStandardPair.centralizer_comm (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : 5 ≤ p ^ f) (h2 : (2 : K) ≠ 0) {W U V : Subgroup X}
    (h : Phan.UnitaryBlockStandardPair K p f W U V) {x y : X} (hxW : x ∈ W) (hyW : y ∈ W)
    (hxc : ∀ u ∈ U, x * u = u * x) (hyc : ∀ u ∈ U, y * u = u * y) : x * y = y * x := by
  obtain ⟨θ, hrange, hker, hU, hV⟩ := Phan.pair_normalize h
  rw [← hrange] at hxW hyW
  obtain ⟨g, rfl⟩ := hxW
  obtain ⟨g', rfl⟩ := hyW
  have key : ∀ g₀ : Phan.Su K p f 3, (∀ u ∈ U, θ g₀ * u = u * θ g₀) →
      suMat g₀ * embPair 2 (Phan.rotMat : Matrix (Fin 2) (Fin 2) K) =
        embPair 2 Phan.rotMat * suMat g₀ := by
    intro g₀ hc
    have hcomm :=
      CFSG.ClassicalInvolution.Balance.StrongBalance.commute_of_perfect_of_commutator_mem_center
      (unitaryB12_perfect hK hq) (r := g₀) (fun s hs => by
        apply hker
        rw [MonoidHom.mem_ker]
        have := hc (θ s) (hU ▸ Subgroup.mem_map_of_mem θ hs)
        simp only [map_mul, map_inv]
        rw [this]
        group)
    have e := hcomm (embSUid (unitaryInvolution K p f) 2 (Phan.rotSU (unitaryInvolution K p f)))
      ⟨_, rfl⟩
    have e2 := congrArg suMat e
    simp only [Models.suMat_mul] at e2
    exact e2
  have hmat := commute_of_commute_embPair_rot h2 (key g hxc) (key g' hyc)
  rw [← map_mul, ← map_mul]
  congr 1
  exact Models.suMat_injective (by rw [Models.suMat_mul, Models.suMat_mul]; exact hmat)

theorem UnitaryBlockStandardPair.le_group {W U V : Subgroup X}
    (h : Phan.UnitaryBlockStandardPair K p f W U V) : U ≤ W ∧ V ≤ W := by
  obtain ⟨θ, hrange, -, hU, hV⟩ := Phan.pair_normalize h
  rw [← hrange, ← hU, ← hV]
  exact ⟨Subgroup.map_le_range _ _, Subgroup.map_le_range _ _⟩

end Unitary

end CFSG.ClassicalInvolution.Asc77.T3Typed
