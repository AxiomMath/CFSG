module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04D3
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04I117Rank

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.DFour
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

theorem d3_card_le_nine_inner {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 3 ^ n)
    (X : Subgroup (MulAut (D4Model K))) (hX : IsElemAbelian 3 X) :
    Nat.card X ≤ 9 * Nat.card (X ⊓ Inn (D4Model K) : Subgroup (MulAut (D4Model K))) ∧
      (¬ 3 ∣ n → Nat.card X ≤ 3 * Nat.card (X ⊓ Inn (D4Model K) : Subgroup (MulAut (D4Model K)))) := by
  have hf : 1 ≤ n := one_le_of_card_field hK
  obtain ⟨hQ0, hab2, hcen⟩ := d4Facts2 Nat.prime_three (by norm_num) hf hK
  obtain ⟨-, -, -, -, hidx⟩ := d4Facts Nat.prime_three (by norm_num) hf hK
  set Q := coordinateQuadPlus 4 K with hQdef
  have hQv :=
    CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration.exists_nonzero_value Q hQ0
  obtain ⟨g, hgE, hg⟩ := exists_gen_image Q
  obtain ⟨hEX, hXI⟩ := card_le_of_tower Nat.prime_three le_rfl (linearRange_normal Q) hidx g hgE hg
    (fun δ hδ hδp => mem_inner_of_mem_linearRange Q hQv hab2 Nat.prime_three (by norm_num) hδ hδp)
    hX.2
  refine ⟨by simpa [mul_assoc] using hXI, fun h3 => ?_⟩
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have hle : (D4Img K ⊓ X : Subgroup (MulAut (D4Model K))) ≤ X ⊓ Inn (D4Model K) := by
    intro y hy
    refine ⟨hy.2, ?_⟩
    have hy3 : y ^ 3 = 1 := hX.2 y hy.2
    have hyD := mem_linearRange_of_pow_eq_one Q Nat.prime_three hK hcop hy.1 hy3
    exact mem_inner_of_mem_linearRange Q hQv hab2 Nat.prime_three (by norm_num) hyD hy3
  have hrel : (D4Img K).relIndex X * Nat.card (D4Img K ⊓ X : Subgroup (MulAut (D4Model K)))
      = Nat.card X := Subgroup.relIndex_mul_card _ _
  have hrel3 := relIndex_le_three hidx X
  calc Nat.card X = (D4Img K).relIndex X *
        Nat.card (D4Img K ⊓ X : Subgroup (MulAut (D4Model K))) := hrel.symm
    _ ≤ 3 * Nat.card (X ⊓ Inn (D4Model K) : Subgroup (MulAut (D4Model K))) :=
        Nat.mul_le_mul hrel3 (Subgroup.card_le_of_le hle)

theorem d3_card_le_of_triality {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 3 ^ n)
    (hC : D3TrialityCentRank) (X : Subgroup (MulAut (D4Model K))) (hX : IsElemAbelian 3 X)
    (hXE : ¬ X ≤ D4Img K) :
    Nat.card X ≤ 3 ^ (4 * n + 2) ∧ (¬ 3 ∣ n → Nat.card X ≤ 3 ^ (4 * n + 1)) := by
  have hf : 1 ≤ n := one_le_of_card_field hK
  obtain ⟨-, -, hcen⟩ := d4Facts2 Nat.prime_three (by norm_num) hf hK
  obtain ⟨h9, h3⟩ := d3_card_le_nine_inner hK X hX
  obtain ⟨t, htX, htE⟩ := Set.not_subset.mp hXE
  obtain ⟨A, hA, hfix, hcardA⟩ := exists_fixed_of_mem hcen hX htX
  have hA4 : Nat.card (X ⊓ Inn (D4Model K) : Subgroup (MulAut (D4Model K))) ≤ 3 ^ (4 * n) := by
    rw [← hcardA]
    exact hC K n hK t (hX.2 t htX) htE A hA hfix
  refine ⟨?_, fun h => ?_⟩
  · calc Nat.card X ≤ 9 * 3 ^ (4 * n) := h9.trans (Nat.mul_le_mul_left _ hA4)
      _ = 3 ^ (4 * n + 2) := by rw [pow_add]; ring
  · calc Nat.card X ≤ 3 * 3 ^ (4 * n) := (h3 h).trans (Nat.mul_le_mul_left _ hA4)
      _ = 3 ^ (4 * n + 1) := by rw [pow_succ]; ring

end CFSG.LocalAnalysis.GLTheoremA
