module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycNodes
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycL3
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycAut

public section

namespace CFSG.AGLEmbedding.BlockCyc

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabAutIrr
  CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem hasE9_psl_of_three_le {m : ℕ} (hm : 3 ≤ m) {F : Type} [Field F] [Finite F] [CharP F 2]
    {Y : Type} [Group Y] (e : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F ≃* Y) :
    HasE9 Y := by
  have h2 : 2 < (rootDatum m F).rank := hm
  have h0 : 0 < (rootDatum m F).rank := by omega
  refine (borelQuotient_sl e).hasE9_of_nodes (i := ⟨2, h2⟩) (j := ⟨0, h0⟩) ?_ ?_
    (hasSL2Node_sl (m := m) (F := F) ⟨2, h2⟩).hasOrderThree
    (hasSL2Node_sl (m := m) (F := F) ⟨0, h0⟩).hasOrderThreeNC
  · simp [rootDatum, CartanMatrix.A, Fin.ext_iff]
  · simp [Fin.ext_iff]

theorem hasE9_or_aut5Le_psl_three {Y : Type} [Group Y] [Finite Y] {f : ℕ}
    (h : StatedClassicalModel Y .PSL 3 2 f) : HasE9 Y ∨ Aut5Le Y := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_equiv_projectiveSL h
  by_cases hf : Even f
  · left
    have h3 : 3 ∣ Nat.card Kˣ := by
      obtain ⟨k, hk⟩ := hf
      rw [Nat.card_units, hK, hk, ← two_mul, pow_mul]
      simpa using Nat.sub_dvd_pow_sub_pow 4 1 k
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hω : (g : K) ^ 3 = 1 := by
      have := pow_orderOf_eq_one g
      rw [hg] at this
      rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
    have hω1 : (g : K) ≠ 1 := by
      intro h1
      have : g = 1 := Units.ext h1
      rw [this, orderOf_one] at hg
      omega
    exact hasE9_of_mulEquiv e.symm (hasE9_projectiveSL_three hω hω1)
  · right
    have hodd : Odd f := Nat.not_even_iff_odd.1 hf
    refine aut5Le_of_mulEquiv e.symm (aut5Le_projectiveSL_three ?_)
    intro h5
    have hdvd : Nat.card (projectiveSL 3 K) ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) :=
      Subgroup.index_dvd_card (scalars 3 K)
    exact not_five_dvd_card_SL_three hK hodd (h5.trans hdvd)

theorem lieCyclic_of_model_psl {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSL n 2 f) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) (hJtop : J ≠ ⊤) :
    HasE9 Y ∨ Aut5Le Y := by
  have h' := h
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have ePSL := (projectiveSpecialLinearGroupEquivStatedProj (m + 1) F).trans e.symm
  rcases (show m = 1 ∨ m = 2 ∨ 3 ≤ m by omega) with rfl | rfl | hm
  · exfalso
    obtain ⟨i, j, hij⟩ := (borelQuotient_sl ePSL).exists_two_nodes T J hNJ hJ hJtop
    have hi : i.val < 1 := i.isLt
    have hj : j.val < 1 := j.isLt
    exact hij (Fin.ext (by omega))
  · exact hasE9_or_aut5Le_psl_three h'
  · exact Or.inl (hasE9_psl_of_three_le hm ePSL)

end CFSG.AGLEmbedding.BlockCyc
