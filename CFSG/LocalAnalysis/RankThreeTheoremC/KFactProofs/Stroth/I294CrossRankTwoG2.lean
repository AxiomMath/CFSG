module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossFamilies
import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousG2

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

private theorem mem_conj_range_of_congr {L H : Type} [Group L] [Group H] (ψ : L ≃* H)
    (α : MulAut L) (h : MulAut.congr ψ α ∈ (MulAut.conj : H →* MulAut H).range) :
    α ∈ (MulAut.conj : L →* MulAut L).range := by
  obtain ⟨g, hg⟩ := h
  refine ⟨ψ.symm g, ?_⟩
  ext y
  apply ψ.injective
  have hy : g * ψ y * g⁻¹ = ψ (α y) := by
    have h' := congrArg (fun φ : MulAut H => φ (ψ y)) hg
    simpa [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply] using h'
  simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact hy

theorem i294CrossThreeRankTwoOn_G2 :
    I294CrossThreeRankTwoOn I294CrossIsG2 := by
  intro L _ _ _ _ d hG hc3 hLe _ _ hr h81 α hα
  obtain ⟨idx, hv⟩ := d
  obtain ⟨q, rfl⟩ : ∃ q : TauCeti.PrimePower, idx = .G2 q := by
    cases idx
    case G2 q => exact ⟨q, rfl⟩
    all_goals simp [I294CrossIsG2] at hG
  obtain ⟨eL⟩ := hLe
  have hp3 : q.p ≠ 3 := by simpa [TauCeti.LieTypeIndex.characteristic_G2] using hc3
  have hord : Nat.card L = CFSG.Open.ordG2 q.card := by
    rw [Nat.card_congr eL.toEquiv,
      CFSG.RankThree.PartTwo.Sec11.KSListsProof.card_G2_carrier q hv]
  have hf3 : ¬ 3 ∣ q.exponent := by
    rintro ⟨m, hm⟩
    have hcard : q.card = (q.p ^ m) ^ 3 := by
      rw [TauCeti.PrimePower.card_def, hm, mul_comm, pow_mul]
    have hQ3 : ¬ 3 ∣ q.p ^ m := fun h =>
      hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three q.prime_p).1
        (Nat.prime_three.dvd_of_dvd_pow h)).symm
    have hcop : Nat.Coprime (q.p ^ m) 9 := by
      have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
      rw [h9]
      exact Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hQ3).symm
    have h6 : Nat.totient 9 = 6 := by decide
    have hE : (q.p ^ m) ^ 6 ≡ 1 [MOD 9] := by
      have := Nat.ModEq.pow_totient hcop
      rwa [h6] at this
    have hZ : 9 ∣ (q.p ^ m) ^ 6 - 1 := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hE)
    have hodd : ∀ Y : ℕ, CFSG.Open.ordG2 (Y ^ 3) =
        (Y ^ 6) ^ 3 * ((Y ^ 6) ^ 3 - 1) * (Y ^ 6 - 1) := by
      intro Y
      have h1 : (Y ^ 3) ^ 6 = (Y ^ 6) ^ 3 := by ring
      have h2 : (Y ^ 3) ^ 2 = Y ^ 6 := by ring
      unfold CFSG.Open.ordG2
      rw [h1, h2]
    have key : ∀ Z : ℕ, 9 ∣ Z - 1 → 81 ∣ Z ^ 3 * (Z ^ 3 - 1) * (Z - 1) := by
      intro Z hZ'
      have h9 : 9 ∣ Z ^ 3 - 1 := dvd_trans hZ' (Nat.sub_one_dvd_pow_sub_one Z 3)
      have h81' : 81 ∣ (Z ^ 3 - 1) * (Z - 1) := by
        rw [show (81 : ℕ) = 9 * 9 by norm_num]
        exact mul_dvd_mul h9 hZ'
      rw [mul_assoc]
      exact Dvd.dvd.mul_left h81' _
    apply h81
    rw [hord, hcard, hodd]
    have h81eq : (3 : ℕ) ^ 4 = 81 := by norm_num
    rw [h81eq]
    exact key _ hZ
  obtain ⟨K, _, _, hK, hKc, ⟨e⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
  have hq3 : 3 ≤ q.card :=
    (TauCeti.LieTypeIndex.inStandardRange_iff (.G2 q)).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  obtain ⟨Q, _, _, Θ, hQ, hker⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_hom_cyclic_G2 q hq3 K hK
  have hcop2 : Nat.Coprime (2 * q.exponent) 3 :=
    Nat.Coprime.mul_left (by norm_num) ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hf3).symm
  have hQ3 : Nat.Coprime (Nat.card Q) 3 := Nat.Coprime.coprime_dvd_left hQ hcop2
  obtain ⟨k, hk⟩ := hα
  let ψ := eL.trans e
  have hinner : MulAut.congr ψ α ∈ Θ.ker := by
    rw [MonoidHom.mem_ker]
    have h1 : (MulAut.congr ψ α) ^ 3 ^ k = 1 := by
      rw [← map_pow, hk, map_one]
    have h2 : Θ (MulAut.congr ψ α) ^ 3 ^ k = 1 := by
      rw [← map_pow, h1, map_one]
    have h3 : Θ (MulAut.congr ψ α) ^ Nat.card Q = 1 := pow_card_eq_one'
    have h4 := pow_gcd_eq_one.mpr ⟨h2, h3⟩
    have hg : Nat.gcd (3 ^ k) (Nat.card Q) = 1 := Nat.Coprime.pow_left k hQ3.symm
    rw [hg, pow_one] at h4
    exact h4
  rw [hker] at hinner
  exact mem_conj_range_of_congr ψ α hinner

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
