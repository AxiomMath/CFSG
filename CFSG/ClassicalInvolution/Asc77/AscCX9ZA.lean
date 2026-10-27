module

public import CFSG.ClassicalInvolution.Asc77.AscCX9Z9
public import CFSG.ClassicalInvolution.Asc77.AscCX9Z6

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX.MF2U

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77.CX.MF2L (spForm)
open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4 (suMat_rootInvSU_four
  suMat_rootInvSU_inv_four)
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem spForm_z (m n : K) : spForm m n * diagonal ![-1, -1, 1, 1] = spForm (-m) n := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [MF2L.spForm, Matrix.mul_diagonal]

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem z_spFormInv (m n : K) :
    diagonal ![-1, -1, 1, 1] * spFormInv m n = spFormInv (-m) n := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spFormInv, Matrix.diagonal_mul]

theorem twisted_z (α : Su K p f 4 →* Su K p f 4) {m n : K}
    (hα : ∀ x, suMat (α x) = spForm m n * (suMat x).map (unitaryInvolution K p f) *
      spFormInv m n) (x : Su K p f 4) :
    suMat ((α.comp (MulAut.conj (rootInvSU K p f (show 2 ≤ 4 by norm_num))).toMonoidHom) x) =
      spForm (-m) n * (suMat x).map (unitaryInvolution K p f) * spFormInv (-m) n := by
  have hZ : (!![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] :
      Matrix (Fin 4) (Fin 4) K) = diagonal ![-1, -1, 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hZσ : (diagonal ![-1, -1, 1, 1] : Matrix (Fin 4) (Fin 4) K).map
      (unitaryInvolution K p f) = diagonal ![-1, -1, 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  rw [hα, suMat_mul, suMat_mul, suMat_rootInvSU_four, suMat_rootInvSU_inv_four, hZ,
    Matrix.map_mul, Matrix.map_mul, hZσ, ← spForm_z, ← z_spFormInv]
  simp only [Matrix.mul_assoc]

section Std


theorem reflWit_std_U (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hq1 : p ^ f % 4 = 1) {Y : Type} [Group Y] [Finite Y] (θ : Su K p f 4 →* Y)
    (hθ : Function.Surjective θ) (hker : θ.ker = Subgroup.center (Su K p f 4))
    {Φ : Set (Subgroup Y)} {a₀ b₀ : Y}
    (htw : TwinSect0 Φ ((blockEmb K p f 4 2 0 (by norm_num)).range.map θ)
      ((blockEmb K p f 4 2 2 (by norm_num)).range.map θ)
      (θ (rootInvSU K p f (show 2 ≤ 4 by norm_num))) a₀ b₀)
    (hconj : ∀ J ∈ Φ, ∀ y : Y, conjSub y J ∈ Φ) (β : MulAut Y)
    (hβA : ∀ y ∈ (blockEmb K p f 4 2 0 (by norm_num)).range.map θ, β y = y)
    (hβA' : ∀ y ∈ (blockEmb K p f 4 2 2 (by norm_num)).range.map θ, β y = y)
    (hβ2 : β * β = 1) (hβ1 : β ≠ 1)
    (hβz : β ≠ MulAut.conj (θ (rootInvSU K p f (show 2 ≤ 4 by norm_num)))) :
    ∃ (hA : (blockEmb K p f 4 2 0 (by norm_num)).range.map θ ≤
        Goldschmidt75.perfRes (fixSubgroup β))
      (hA' : (blockEmb K p f 4 2 2 (by norm_num)).range.map θ ≤
        Goldschmidt75.perfRes (fixSubgroup β))
      (hB : (blockEmb K p f 4 2 0 (by norm_num)).range.map θ ≤
        Goldschmidt75.perfRes (fixSubgroup
          (β * MulAut.conj (θ (rootInvSU K p f (show 2 ≤ 4 by norm_num))))))
      (hB' : (blockEmb K p f 4 2 2 (by norm_num)).range.map θ ≤
        Goldschmidt75.perfRes (fixSubgroup
          (β * MulAut.conj (θ (rootInvSU K p f (show 2 ≤ 4 by norm_num)))))),
      IsOm5 p f (centTG _ _ β hA hA') ∧ IsOm5 p f (centTG _ _ _ hB hB') ∧
        DiagWit p (centTG _ _ β hA hA') (centTG _ _ _ hB hB') := by
  classical
  set σ := unitaryInvolution K p f with hσdef
  set z := rootInvSU K p f (show 2 ≤ 4 by norm_num) with hz
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  have hσσ := unitaryInvolution_involutive hK
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · rw [h, pow_zero] at hq
      omega
    · exact h
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [GaloisField.card p f (by omega)]
    omega
  have hsq : IsSquare (-1 : GaloisField p f) := by
    have : Fintype (GaloisField p f) := Fintype.ofFinite _
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card,
      GaloisField.card p f (by omega)]
    omega
  obtain ⟨ε⟩ : Nonempty (GaloisField p f ≃+* fixedSubfield K p f) := by
    have := Fintype.ofFinite (GaloisField p f)
    have := Fintype.ofFinite (fixedSubfield K p f)
    exact ⟨FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, GaloisField.card p f (by omega),
        card_fixedSubfield hK])⟩
  have hfix0 : ∀ A : Su K p f 2, β (θ (blockEmb K p f 4 2 0 (by norm_num) A)) =
      θ (blockEmb K p f 4 2 0 (by norm_num) A) := fun A => hβA _ ⟨_, ⟨A, rfl⟩, rfl⟩
  have hfix2 : ∀ A : Su K p f 2, β (θ (blockEmb K p f 4 2 2 (by norm_num) A)) =
      θ (blockEmb K p f 4 2 2 (by norm_num) A) := fun A => hβA' _ ⟨_, ⟨A, rfl⟩, rfl⟩
  have hk : β ^ (2 ^ 1) = 1 := by rw [pow_one, sq, hβ2]
  rcases CX4.U4.two_elem_cases hK hp2 hq hq1 θ hθ hker.le β hfix0 hfix2 hk with
    (h | h) | ⟨α, hα, m, n, hm, hn, hNm, hNn, hαM⟩
  · exact absurd h hβ1
  · exact absurd h hβz
  obtain ⟨c, hc⟩ := hσ.exists_norm_neg_one
  obtain ⟨t, ht0, hσt⟩ := exists_unitaryInvolution_eq_neg hK
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp2
  have ht : t - σ t ≠ 0 := by
    rw [hσt, sub_neg_eq_add, ← two_mul]
    exact mul_ne_zero h2 ht0
  set ι : GaloisField p f →+* K := (fixedSubfield K p f).subtype.comp ε.toRingHom with hι
  have hfixι : ∀ a, σ (ι a) = ι a := fun a => mem_fixedSubfield.mp (ε a).2
  have hontoι : ∀ b, σ b = b → ∃ a, ι a = b := fun b hb =>
    ⟨ε.symm ⟨b, mem_fixedSubfield.mpr hb⟩, by simp [hι]⟩
  have hNm' : σ (-m) * -m = 1 := by rw [map_neg, neg_mul_neg, hNm]
  let D : DescData σ (GaloisField p f) := ⟨c, t, m, n, ι, hσσ, hc, hNm, hNn, ht, hfixι, hontoι⟩
  let D' : DescData σ (GaloisField p f) :=
    ⟨c, t, -m, n, ι, hσσ, hc, hNm', hNn, ht, hfixι, hontoι⟩
  have hβθ : ∀ x, β (θ x) = θ (α x) := fun x => (hα x).symm
  have hX₁ := D.perfRes_fix_eq h4 hK θ hθ hker.le α hαM β hβθ
  have hα'M : ∀ x, suMat ((α.comp (MulAut.conj z).toMonoidHom) x) =
      spForm D'.m D'.n * (suMat x).map σ * spFormInv D'.m D'.n := twisted_z α hαM
  have hβθ' : ∀ x, (β * MulAut.conj (θ z)) (θ x) = θ ((α.comp (MulAut.conj z).toMonoidHom) x) := by
    intro x
    rw [MulAut.mul_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, hβθ]
    rfl
  have hX₂ := D'.perfRes_fix_eq h4 hK θ hθ hker.le _ hα'M _ hβθ'
  have hA : (blockEmb K p f 4 2 0 (by norm_num)).range.map θ ≤
      Goldschmidt75.perfRes (fixSubgroup β) := by
    rw [hX₁]
    exact Subgroup.map_mono (D.block0_le hK)
  have hA' : (blockEmb K p f 4 2 2 (by norm_num)).range.map θ ≤
      Goldschmidt75.perfRes (fixSubgroup β) := by
    rw [hX₁]
    exact Subgroup.map_mono (D.block2_le hK)
  have hB : (blockEmb K p f 4 2 0 (by norm_num)).range.map θ ≤
      Goldschmidt75.perfRes (fixSubgroup (β * MulAut.conj (θ z))) := by
    rw [hX₂]
    exact Subgroup.map_mono (D'.block0_le hK)
  have hB' : (blockEmb K p f 4 2 2 (by norm_num)).range.map θ ≤
      Goldschmidt75.perfRes (fixSubgroup (β * MulAut.conj (θ z))) := by
    rw [hX₂]
    exact Subgroup.map_mono (D'.block2_le hK)
  exact ⟨hA, hA', hB, hB', ⟨_, _, _, _, D.om5Data_T hK hp2 hq θ hker.le _ hX₁ htw hconj⟩,
    ⟨_, _, _, _, D'.om5Data_T hK hp2 hq θ hker.le _ hX₂ htw hconj⟩,
    diagWit_U hK hp2 hsq D hσt θ hθ hker β _ hX₁ hX₂ hA hA' hB hB'⟩

end Std

end CFSG.ClassicalInvolution.Asc77.CX.MF2U
