module

public import CFSG.LieType.SeitzGeneration.SubfieldPairSLBlock
public import CFSG.LieType.SeitzGeneration.SubfieldPairSLEntry

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.RankThree.PartOne.CTP
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)

variable {n : ℕ} {K : Type} [Field K] [Finite K] {k : Subfield K} {p : ℕ}

theorem subfieldPairSL_odd (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = Nat.card k ^ p) (hk3 : 3 ≤ Nat.card k) (hn3 : 3 ≤ n) (A : GL (Fin n) K)
    (hne : (slSub n k).map (slConjugation n K A).toMonoidHom ≠ slSub n k) :
    Subgroup.closure ((slSub n k : Set (SpecialLinearGroup (Fin n) K)) ∪
      ((slSub n k).map (slConjugation n K A).toMonoidHom :
        Set (SpecialLinearGroup (Fin n) K))) = ⊤ := by
  obtain ⟨c, d, hcd, r, s, hrs, hirr⟩ := exists_offDiag_not_mem hp hp2 hK A hne
  have hab : s ≠ r := hrs.symm
  have hα : colVec A c r ≠ 0 := fun h => hirr (by rw [h, zero_mul]; exact k.zero_mem)
  have hβ : rowVec A d s ≠ 0 := fun h => hirr (by rw [h, mul_zero]; exact k.zero_mem)
  have hφu := rowVec_dotProduct_colVec A hcd
  set G₀ := slSub n k with hG₀
  set G₁ := G₀.map (slConjugation n K A).toMonoidHom with hG₁
  set H := Subgroup.closure ((G₀ : Set (SpecialLinearGroup (Fin n) K)) ∪
    (G₁ : Set (SpecialLinearGroup (Fin n) K))) with hH
  have hk : G₀ ≤ H := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hk1 : G₁ ≤ H := fun x hx => Subgroup.subset_closure (Or.inr hx)
  set Φ := blockHom (colPair s (colVec A c)) (rowsF s r (colVec A c) (rowVec A d))
    (rowsF_mul_colPair hab hφu hα hβ) with hΦ
  have hu : ∀ t ∈ k, u2 (t * colVec A c r) ∈ H.comap Φ := by
    intro t ht
    show Φ (u2 (t * colVec A c r)) ∈ H
    rw [hΦ, blockHom_u2 hab hφu hα hβ, mul_assoc, mul_inv_cancel₀ hα, mul_one]
    exact hk (transvection_mem_slSub hab ht)
  have hl : ∀ t ∈ k, l2 (t * rowVec A d s) ∈ H.comap Φ := by
    intro t ht
    show Φ (l2 (t * rowVec A d s)) ∈ H
    rw [hΦ, blockHom_l2 hab hφu hα hβ]
    have h1 : tv (colVec A c) ((t * rowVec A d s * (rowVec A d s)⁻¹) • rowVec A d)
        (by rw [smul_dotProduct, hφu, smul_zero]) =
        slConjugation n K A (SpecialLinearGroup.transvection hcd t) := by
      rw [slConjugation_transvection A hcd t]
      exact tv_eq_of_eq rfl (by rw [mul_assoc, mul_inv_cancel₀ hβ, mul_one]) _ _
    rw [h1]
    exact hk1 (Subgroup.mem_map_of_mem _ (transvection_mem_slSub hcd ht))
  have hM : H.comap Φ = ⊤ := sl2_eq_top_of_root_pair hp hp2 hK hk3 hirr hu hl
  obtain ⟨μ, hμ⟩ : ∃ μ : K, μ ∉ k := by
    by_contra h
    push Not at h
    have hsurj : Function.Surjective (fun x : k => (x : K)) := fun y => ⟨⟨y, h y⟩, rfl⟩
    have h1 := Nat.card_le_card_of_surjective _ hsurj
    rw [hK] at h1
    have h2 : 2 ≤ Nat.card k := Finite.one_lt_card
    exact absurd h1 (not_le.mpr (by
      calc Nat.card k < Nat.card k ^ 2 := by nlinarith
        _ ≤ Nat.card k ^ p := Nat.pow_le_pow_right (by omega) hp.two_le))
  have hmem : u2 (μ * colVec A c r) ∈ H.comap Φ := hM ▸ Subgroup.mem_top _
  have hmem' : SpecialLinearGroup.transvection hab μ ∈ H := by
    have h2 : Φ (u2 (μ * colVec A c r)) ∈ H := hmem
    rwa [hΦ, blockHom_u2 hab hφu hα hβ, mul_assoc, mul_inv_cancel₀ hα, mul_one] at h2
  exact eq_top_of_root_not_mem hk hn3 hp hK hμ hab hmem'

end CFSG.LieType.SeitzGeneration
