module

public import CFSG.LocalAnalysis.RankThreeUC.K518HAFam

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K518H

open CFSG.Open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits CFSG.AGLEmbedding.ParabHub CFSG.LieType.BorelTits
  CFSG.AGLEmbeddingD2.Tits.GN516 CFSG.LieType.Universal.Unitary.SUExtras

section SU

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {n : ℕ}

include hF in
private theorem su_center_scalar (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2))
    {z : SU (unitaryInvolution F 2 f) n}
    (hz : z ∈ Subgroup.center (SU (unitaryInvolution F 2 f) n)) :
    ∃ u : F, mat (unitaryInvolution F 2 f) n z = Matrix.scalar (Fin n) u := by
  obtain ⟨P, hP⟩ := exists_wittMatrix hF n
  set ψ : SU (unitaryInvolution F 2 f) n ≃* StatedSU n (2 ^ f) F :=
    (conjEquiv P hP).trans (MulEquiv.subgroupCongr (SUid_eq_statedSU hF n)) with hψ
  have h1 : ψ z ∈ Subgroup.center ↥(StatedSU n (2 ^ f) F) := by
    rw [← CFSG.LieType.Universal.Unitary.map_center_mulEquiv ψ]
    exact ⟨z, hz, rfl⟩
  rw [(isQuasisimple_statedSU_of_card hF hn hnq).2, Subgroup.mem_subgroupOf] at h1
  obtain ⟨u, hu⟩ := h1
  have hcoe : ((ψ z : StatedSU n (2 ^ f) F) : GL (Fin n) F) = P * (z : GL (Fin n) F) * P⁻¹ := rfl
  have hz' : (z : GL (Fin n) F) = P⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin n) u * P := by
    rw [hu, hcoe]
    group
  refine ⟨(u : F), ?_⟩
  rw [mat_apply, hz', Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
    ← (Matrix.scalar_commute (u : F) (fun r => mul_comm _ r) _).eq, Matrix.mul_assoc,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]

include hF in
private theorem su_center_inf_rankOne_last (hn5 : 5 ≤ n) (hn : ¬Even n) {k : Fin (n / 2)}
    (hk : ¬k.val + 1 < n / 2) {z : SU (unitaryInvolution F 2 f) n}
    (hz : z ∈ Subgroup.center (SU (unitaryInvolution F 2 f) n))
    (hzL : z ∈ rankOne (rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) n)
      k) :
    z = 1 := by
  obtain ⟨u, hu⟩ := su_center_scalar hF (by omega) (fun h => by
    have := (Prod.mk.inj h).1
    omega) hz
  have hblk := isBlkOn_lastIdxOdd hn hk hzL
  set s₀ : Fin n := ⟨0, by omega⟩
  have hk1 : 1 ≤ k.val := by
    have := k.isLt
    obtain ⟨r, hr⟩ := Nat.not_even_iff_odd.mp hn
    omega
  have hs₀ : s₀ ∉ Set.range (lastIdxOdd k hn) := by
    rintro ⟨i, hi⟩
    have := congrArg Fin.val hi
    fin_cases i <;> simp [lastIdxOdd, s₀, val_lowIdx, midIdx, Fin.val_rev] at this <;> omega
  have h1 := hblk s₀ s₀ (Or.inl hs₀)
  rw [hu, Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h1
  apply Subtype.ext
  apply Units.ext
  change mat (unitaryInvolution F 2 f) n z = mat (unitaryInvolution F 2 f) n 1
  rw [hu, map_one, h1, map_one]


include hF in
private theorem hasRkModel_su (hf : 1 ≤ f) (hn : 4 ≤ n) {Y : Type} [Group Y]
    (e : Y ≃* StatedProj (StatedSU n (2 ^ f) F)) : HasRkModel Y := by
  classical
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have h := borelQuotient_su hF (by omega) ζ hζ e
  have key : ∀ i : Fin (n / 2),
      (RkKind ↥(rankOne (rootDatum hF n).rootGroup i) ∧
        Subgroup.center (SU (unitaryInvolution F 2 f) n) ⊓ rankOne (rootDatum hF n).rootGroup i = ⊥ ∧
        Nat.card F - 1 ∣ Nat.card ↥(rankOne (rootDatum hF n).rootGroup i)) ∧
      (Subgroup.center ↥(rankOne (rootDatum hF n).rootGroup i) = ⊥ ∨
        (¬ i.val + 1 < n / 2 ∧ ¬ Even n)) := by
    intro i
    by_cases hk : i.val + 1 < n / 2
    · have e1 : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥(rankOne (rootDatum hF n).rootGroup i) :=
        (rankOneShortEquiv (hσ := unitaryInvolution_involutive hF) hk).symm
      obtain ⟨h1, h2, h3, h4⟩ := nodeData_of_sl2 h e1 (sub_one_dvd_sq_sub_one _)
      exact ⟨⟨h1, center_inf_eq_bot_of_center_eq_bot h4, h3⟩, Or.inl h4⟩
    · by_cases he : Even n
      · obtain ⟨z, hz0, hz⟩ := exists_unitaryInvolution_eq_neg hF
        have e1 : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield F 2 f) ≃*
            ↥(rankOne (rootDatum hF n).rootGroup i) :=
          (hypEquiv (p := 2) (f := f) hz0 (by simpa using hz)).trans
            (rankOneLastEvenEquiv hF he hk).symm
        have hM : Nat.card F - 1 ∣ Nat.card (fixedSubfield F 2 f) ^ 2 - 1 := by
          rw [card_fixedSubfield hF, hF]
        obtain ⟨h1, h2, h3, h4⟩ := nodeData_of_sl2 h e1 hM
        exact ⟨⟨h1, center_inf_eq_bot_of_center_eq_bot h4, h3⟩, Or.inl h4⟩
      · have hn5 : 5 ≤ n := by
          obtain ⟨r, hr⟩ := Nat.not_even_iff_odd.mp he
          omega
        have e1 := rankOneLastOddEquiv (p := 2) (f := f) hF he hk
        refine ⟨⟨Or.inr ⟨F, inferInstance, inferInstance, inferInstance, f, hf, hF, ⟨e1⟩⟩, ?_, ?_⟩,
          Or.inr ⟨hk, he⟩⟩
        · refine eq_bot_iff.2 fun z hz => ?_
          rw [Subgroup.mem_bot]
          exact su_center_inf_rankOne_last hF hn5 he hk hz.1 hz.2
        · have hc1 : Nat.card ↥(rankOne (rootDatum hF n).rootGroup i) =
              Nat.card (SU (unitaryInvolution F 2 f) 3) := Nat.card_congr e1.toEquiv
          rw [hc1, card_SU_three (p := 2) (f := f) hF, hF]
          exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  refine hasRkModel_of_nodes h (fun i => ⟨(key i).1.1,
    ker_inf_eq_bot_of_center_inf h (key i).1.2.1, (key i).1.2.2⟩) fun i j hij => ?_
  rcases (key i).2 with hi | ⟨hi1, hi2⟩
  · exact Or.inl hi
  · rcases (key j).2 with hj | ⟨hj1, hj2⟩
    · exact Or.inr hj
    · exfalso
      apply hij
      apply Fin.ext
      have := i.isLt
      have := j.isLt
      omega

end SU

theorem hasRkModel_of_model_psu {Y : Type} [Group Y] {n f : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel Y .PSU n 2 f) (hn4 : 4 ≤ n) :
    HasRkModel Y := by
  obtain ⟨⟨-, hf, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  exact hasRkModel_su hcard hf hn4 e

end CFSG.LocalAnalysis.RankThreeUC.S15.K518H

end
