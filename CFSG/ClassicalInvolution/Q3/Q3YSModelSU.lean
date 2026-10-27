module

public import CFSG.ClassicalInvolution.Q3.Q3YSInputs

public section

namespace CFSG.ClassicalInvolution.Q3.Q3YS

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models

theorem fourGroup_transport {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : ∃ F : Subgroup B, IsElemAbelian 2 F ∧ Nat.card F = 4 ∧ F ⊓ Subgroup.center B = ⊥) :
    ∃ F : Subgroup A, IsElemAbelian 2 F ∧ Nat.card F = 4 ∧ F ⊓ Subgroup.center A = ⊥ := by
  obtain ⟨F, hF, hcard, hz⟩ := h
  refine ⟨F.map e.symm.toMonoidHom, Q3Y.isElemAbelian_map e.symm.toMonoidHom hF, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.symm.injective, hcard]
  · rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨⟨x, hxF, rfl⟩, hgZ⟩ := hg
    have hx : x ∈ F ⊓ Subgroup.center B := by
      refine Subgroup.mem_inf.mpr ⟨hxF, ?_⟩
      rw [Subgroup.mem_center_iff]
      intro b
      have h1 := Subgroup.mem_center_iff.mp hgZ (e.symm b)
      have h2 := congrArg e h1
      simpa using h2
    rw [hz, Subgroup.mem_bot] at hx
    rw [Subgroup.mem_bot]
    simp [hx]

section SU

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem fourGroup_su (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {n : ℕ} (hn : 3 ≤ n) :
    ∃ F : Subgroup (Su K p f n), IsElemAbelian 2 F ∧ Nat.card F = 4 ∧
      F ⊓ Subgroup.center (Su K p f n) = ⊥ := by
  have h2 : (2 : K) ≠ 0 := Models.two_ne_zero_of_charP_ne_two hp
  have hneg : (-1 : K) ≠ 1 := by
    intro h
    apply h2
    linear_combination -h
  let T₁ : Pair n := ⟨{⟨0, by omega⟩, ⟨1, by omega⟩}, Finset.card_pair (by simp [Fin.ext_iff])⟩
  let T₂ : Pair n := ⟨{⟨1, by omega⟩, ⟨2, by omega⟩}, Finset.card_pair (by simp [Fin.ext_iff])⟩
  have hnc : ∀ g : Su K p f n, (∃ i j : Fin n, suMat g i i ≠ suMat g j j) →
      g ∉ Subgroup.center (Su K p f n) := by
    rintro g ⟨i, j, hij⟩ hz
    obtain ⟨u, hu⟩ := exists_scalar_of_mem_center
      (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK) hn hz
    apply hij
    have key : ∀ c : Fin n, suMat g c c = (u : K) := fun c => by
      have := congrFun (congrFun hu c) c
      simpa [suMat, Matrix.scalar_apply, Matrix.diagonal_apply_eq] using this
    rw [key i, key j]
  have ha : zEltU K p f T₁ ∉ Subgroup.center (Su K p f n) := by
    refine hnc _ ⟨⟨0, by omega⟩, ⟨2, by omega⟩, ?_⟩
    simp [suMat_zEltU, zMat_apply_self, T₁, Fin.ext_iff, hneg]
  have hb : zEltU K p f T₂ ∉ Subgroup.center (Su K p f n) := by
    refine hnc _ ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩
    simp [suMat_zEltU, zMat_apply_self, T₂, Fin.ext_iff, Ne.symm hneg]
  have hab : zEltU K p f T₁ * zEltU K p f T₂ ∉ Subgroup.center (Su K p f n) := by
    refine hnc _ ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩
    simp [suMat_mul, suMat_zEltU, zMat, T₁, T₂, Fin.ext_iff, hneg]
  have hcomm : zEltU K p f T₁ * zEltU K p f T₂ = zEltU K p f T₂ * zEltU K p f T₁ :=
    suMat_injective (by simp only [suMat_mul, suMat_zEltU]; exact zMat_mul_comm _ _)
  exact exists_fourGroup_of_noncentral (zEltU_mul_self T₁) (zEltU_mul_self T₂) hcomm ha hb hab

end SU

theorem modelFourGroup3On_psu : ModelFourGroup3On fun t => t = .PSU := by
  intro t n ht _ hadm _ _
  subst ht
  have hn : 3 ≤ n := hadm.2.2.1
  have hF9 : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  let e : CFSG.LieType.Universal.Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 3 (2 * 1)) 3 1) n ≃*
      Su (GaloisField 3 (2 * 1)) 3 1 n :=
    (CFSG.LieType.Universal.Unitary.equivStatedSU hF9 n).trans
      (MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF9 n)).symm
  exact fourGroup_transport e (fourGroup_su hF9 (by norm_num) hn)

end CFSG.ClassicalInvolution.Q3.Q3YS
