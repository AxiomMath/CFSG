module

public import CFSG.CGT.Timmesfeld75.ListWCBender
public import CFSG.LargeExtraspecial.Bender
public import CFSG.StronglyEmbedded.BenderUnitaryBorel

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open CFSG.BenderSuzuki CFSG.Assembly.LowTwoRank

theorem exists_sz_of_lieModel {G : Type} [Group G] {s : ℕ}
    (hG : CFSG.Blueprint.LieModel G .twistedB2 0 2 s) :
    ∃ a : ℕ, 1 ≤ a ∧ s = 2 * a + 1 ∧ Nonempty (G ≃* CFSG.Open.Sz a) := by
  have hS : CFSG.Blueprint.SuzukiModel G 2 s := by
    rcases hG with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact h
  obtain ⟨-, a, ha, K, _, _, hs, hcard, ⟨e⟩⟩ := hS
  subst hs
  exact ⟨a, ha, rfl, ⟨e.trans ((MulEquiv.subgroupCongr
    (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
    (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard))⟩⟩

theorem sz_wc {G : Type} [Group G] [Finite G] {s : ℕ}
    (hG : CFSG.Blueprint.LieModel G .twistedB2 0 2 s) {T : Subgroup G} (hT : IsWC T)
    (hT1 : T ≠ ⊥) :
    (Nat.card T = 2 ^ s ∧
      (∃ S : Sylow 2 G, T = (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype) ∧
      BorelTwoTransitive G T) ∧
    ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer (T : Set G), g * x * g⁻¹ = y := by
  have hsyl := CFSG.LargeExtraspecial.Bender.card_sylow_of_suzuki G s hG
  obtain ⟨a, ha, rfl, ⟨e⟩⟩ := exists_sz_of_lieModel hG
  have hK : IsBenderGroup G := isBenderGroup_of_mulEquiv_sz ha e
  have : Finite (CFSG.Open.Sz a) := Finite.of_equiv G e.toEquiv
  have hB : fusionBenderBorel G (2 ^ (2 * a + 1)) 2 :=
    (bender_suzuki_borel_full a ha).map_mulEquiv e.symm
  exact bender_wc hK hB (by rw [hsyl, ← pow_mul, mul_comm]) hT hT1

theorem exists_psu3_of_statedClassicalModel {G : Type} [Group G] {s : ℕ} (hs : 2 ≤ s)
    (hG : StatedClassicalModel G .PSU 3 2 s) : Nonempty (G ≃* CFSG.Open.PSU3 2 s) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hG
  have hcard : Nat.card K = 2 ^ (2 * s) := by rw [hK, ← pow_mul, mul_comm]
  let e' : G ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) K (2 ^ s)) := e
  exact ⟨e'.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative s hs hcard)⟩

theorem card_sylow_le_of_borel {G₀ : Type} [Group G₀] [Finite G₀] {q k : ℕ}
    (hB : fusionBenderBorel G₀ q k) {U R : Subgroup G₀} (hR2 : IsPGroup 2 R)
    (hRcard : Nat.card R = q ^ k) (hUN : U ≤ Subgroup.normalizer (R : Set G₀)) {N : ℕ}
    (hG : Nat.card G₀ = N * Nat.card U) : Nat.card (Sylow 2 G₀) ≤ N := by
  obtain ⟨P, hRP⟩ := hR2.exists_le_sylow
  have hRP' : R = P := Subgroup.eq_of_le_of_card_ge hRP (by rw [(hB P).2.2.2.2, hRcard])
  have hU0 : 0 < Nat.card U := Nat.card_pos
  have hidx : U.index = N := by
    have h := U.card_mul_index
    rw [hG, mul_comm N] at h
    exact Nat.eq_of_mul_eq_mul_left hU0 h
  rw [Sylow.card_eq_index_normalizer P]
  have hUN' : U ≤ Subgroup.normalizer ((P : Subgroup G₀) : Set G₀) := hRP' ▸ hUN
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h, zero_mul] at hG
      exact absurd hG Nat.card_pos.ne'
    · exact h
  exact Nat.le_of_dvd (hidx ▸ hN0) (hidx ▸ Subgroup.index_dvd_of_le hUN')

open CFSG.BenderSuzuki.MatrixGroups in
theorem card_sylow_psu3 {G : Type} [Group G] [Finite G] {s : ℕ}
    (hG : StatedClassicalModel G .PSU 3 2 s) : Nat.card (Sylow 2 G) = 2 ^ (3 * s) + 1 := by
  apply le_antisymm _ (CFSG.LargeExtraspecial.Bender.le_card_sylow_of_psu3 G s hG)
  obtain ⟨⟨-, hs1, -, hs⟩, K, _, _, hK, ⟨e⟩⟩ := hG
  have hs2 : 2 ≤ s := by
    by_contra h
    exact hs (by rw [show s = 1 by omega, pow_one])
  have hK' : Nat.card K = 2 ^ (2 * s) := by rw [hK, ← pow_mul, mul_comm]
  let J := binaryQuadraticHermitian s (by omega)
  have hEcard : Nat.card (FiniteField.Extension (GaloisField 2 s) 2 2) = (2 ^ s) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 s (by omega)]
  have hfixed : Nat.card {x : FiniteField.Extension (GaloisField 2 s) 2 2 // J.conj x = x} =
      2 ^ s :=
    quadraticBinaryFrobenius_fixed_card s (by omega)
  obtain ⟨eJ⟩ := projectiveSpecialUnitary_equiv_PSU3Model J s hs2 rfl hEcard hfixed
  let e₀ : G ≃* CFSG.Open.PSU3 2 s :=
    e.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative s hs2 hK')
  let e₁ : G ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
    (e₀.trans (MulEquiv.subgroupCongr (show CFSG.Open.PSU3 2 s = PSU3Model s from rfl))).trans
      eJ.symm
  rw [CFSG.LargeExtraspecial.Bender.card_sylow_congr e₁]
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv G e₁.toEquiv
  have : Finite (CFSG.Open.PSU3 2 s) := Finite.of_equiv G e₀.toEquiv
  have hB : fusionBenderBorel (ProjectiveSpecialUnitaryMatrixGroup J) (2 ^ s) 3 :=
    (bender_psu3_borel_full s hs2).map_mulEquiv (e₀.symm.trans e₁)
  rcases CFSG.BenderSuzuki.External.huppert_II_10_12 J (2 ^ s) hEcard hfixed rfl with
    ⟨-, rho, pinf, -, -, hUcard, ⟨R, -, -, -, hUN, -, -, -, hRcard, -⟩, -, hGcard, -⟩
  have hR2 : IsPGroup 2 R := IsPGroup.of_card (n := s * 3) (by rw [hRcard, ← pow_mul])
  have hq1 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
  have hdvd : Nat.gcd 3 (2 ^ s + 1) ∣ (2 ^ s) ^ 3 * ((2 ^ s) ^ 2 - 1) := by
    refine dvd_mul_of_dvd_right ((Nat.gcd_dvd_right _ _).trans ⟨2 ^ s - 1, ?_⟩) _
    rw [show (2 ^ s) ^ 2 - 1 = (2 ^ s) ^ 2 - 1 ^ 2 by rw [one_pow], Nat.sq_sub_sq]
  have hle := card_sylow_le_of_borel hB hR2 hRcard hUN (N := (2 ^ s) ^ 3 + 1) (by
    rw [hGcard, hUcard, Nat.gcd_comm (2 ^ s + 1) 3, mul_assoc, Nat.mul_div_assoc _ hdvd])
  rwa [← pow_mul, mul_comm] at hle

theorem psu3_wc {G : Type} [Group G] [Finite G] {s : ℕ}
    (hs : 2 ≤ s) (hG : StatedClassicalModel G .PSU 3 2 s) {T : Subgroup G} (hT : IsWC T)
    (hT1 : T ≠ ⊥) :
    (Nat.card T = 2 ^ s ∧
      (∃ S : Sylow 2 G, T = (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype) ∧
      BorelTwoTransitive G T) ∧
    ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer (T : Set G), g * x * g⁻¹ = y := by
  have hsyl := card_sylow_psu3 hG
  obtain ⟨e⟩ := exists_psu3_of_statedClassicalModel hs hG
  have hK : IsBenderGroup G :=
    .isPSU3 s hs (e.trans (MulEquiv.subgroupCongr
      (show CFSG.Open.PSU3 2 s = PSU3Model s from rfl)))
  have : Finite (CFSG.Open.PSU3 2 s) := Finite.of_equiv G e.toEquiv
  have hB : fusionBenderBorel G (2 ^ s) 3 := (bender_psu3_borel_full s hs).map_mulEquiv e.symm
  exact bender_wc hK hB (by rw [hsyl, ← pow_mul, mul_comm]) hT hT1

end CFSG.CGT.Timmesfeld75
