module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.L44AtlasBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.ElimFacts

public noncomputable section

namespace CFSG.EvenSporadicStandard.M24Std

namespace L44Atlas

open Matrix
open CFSG.RankThree.PartTwo.KFacts.KS21.L44 (F4 M card_F4 units_pow_three)

theorem card_le_of_exponent_three {G : Type*} [Group G] [Finite G] {m : ℕ} (hm : ¬ 3 ∣ m)
    (hcard : Nat.card G = 3 ^ 4 * m) {g : G} (hg9 : g ^ 9 = 1) (hg3 : g ^ 3 ≠ 1)
    (S : Subgroup G) (hS : ∀ s ∈ S, s ^ 3 = 1) : Nat.card S ≤ 27 := by
  by_contra hlt
  have hlt : 27 < Nat.card S := not_le.mp hlt
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSp : IsPGroup 3 S := fun s => ⟨1, Subtype.ext (by simpa using hS s s.2)⟩
  obtain ⟨k, hk⟩ := hSp.exists_card_eq
  have hdvd : 3 ^ k ∣ 3 ^ 4 * m := hk ▸ hcard ▸ Subgroup.card_subgroup_dvd_card S
  have hcop : Nat.Coprime (3 ^ k) m :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm)
  have hk4 : k ≤ 4 :=
    (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right hdvd)
  have hk3 : 3 < k := by
    by_contra hk3
    have : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hfac : (Nat.card G).factorization 3 = 4 := by
    rw [hcard, Nat.factorization_mul (by positivity) (by rintro rfl; exact hm (dvd_zero 3)),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three]
    simp [Nat.factorization_eq_zero_of_not_dvd hm]
  have hS81 : Nat.card S = 3 ^ (Nat.card G).factorization 3 := by
    rw [hfac, hk]
    congr 1
    omega
  let P : Sylow 3 G := Sylow.ofCard S hS81
  have hgp : IsPGroup 3 (Subgroup.zpowers g) := by
    intro x
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp x.2
    refine ⟨2, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hn, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul]
    simp [hg9]
  obtain ⟨Q, hQ⟩ := hgp.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G P Q
  have hgQ : g ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers g)
  rw [← hh, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hgQ
  obtain ⟨s, hs, hsg⟩ := Subgroup.mem_map.mp hgQ
  apply hg3
  have : g = h * s * h⁻¹ := by simpa [MulAut.conj_apply] using hsg.symm
  rw [this, conj_pow, hS s hs]
  simp

theorem exists_ne_zero_ne_one : ∃ r : F4, r ≠ 0 ∧ r ≠ 1 := by
  classical
  have := Fintype.ofFinite F4
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hsub : (Finset.univ : Finset F4) ⊆ {0, 1} := fun a _ => by
    by_cases ha : a = 0
    · simp [ha]
    · simp [h a ha]
  have hle := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, card_F4] at hle
  have := Finset.card_le_two (a := (0 : F4)) (b := 1)
  omega

theorem pow_three_eq_one {ω : F4} (h0 : ω ≠ 0) : ω ^ 3 = 1 := by
  have := congrArg Units.val (units_pow_three (Units.mk0 ω h0))
  simpa using this

@[expose] def gMat (ω : F4) : Matrix (Fin 4) (Fin 4) F4 :=
  !![0, 0, ω, 0; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, ω * ω]

theorem gMat_mul_self_mul_self (ω : F4) :
    gMat ω * gMat ω * gMat ω = diagonal ![ω, ω, ω, ω * ω * ω * ω * ω * ω] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gMat, Matrix.mul_apply, Fin.sum_univ_four]
  ring

theorem det_gMat {ω : F4} (h : ω ^ 3 = 1) : (gMat ω).det = 1 := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp [gMat, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix]
  rw [← h]
  ring

theorem gMat_pow_three {ω : F4} (h : ω ^ 3 = 1) : gMat ω ^ 3 = diagonal ![ω, ω, ω, 1] := by
  rw [pow_three', gMat_mul_self_mul_self]
  congr 1
  ext i
  fin_cases i <;> simp
  calc ω * ω * ω * ω * ω * ω = (ω ^ 3) ^ 2 := by ring
    _ = 1 := by rw [h]; norm_num

theorem gMat_pow_nine {ω : F4} (h : ω ^ 3 = 1) : gMat ω ^ 9 = 1 := by
  rw [show 9 = 3 * 3 by norm_num, pow_mul, gMat_pow_three h, Matrix.diagonal_pow,
    ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp [h]

@[expose] def gSL {ω : F4} (h : ω ^ 3 = 1) : M := ⟨gMat ω, det_gMat h⟩

theorem gSL_pow_nine {ω : F4} (h : ω ^ 3 = 1) : gSL h ^ 9 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  exact gMat_pow_nine h

theorem gSL_pow_three_ne_one {ω : F4} (h : ω ^ 3 = 1) (h1 : ω ≠ 1) : gSL h ^ 3 ≠ 1 := by
  intro h3
  have := congrArg (fun g : M => (g : Matrix (Fin 4) (Fin 4) F4) 0 0) h3
  simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] at this
  change (gMat ω ^ 3) 0 0 = (1 : Matrix (Fin 4) (Fin 4) F4) 0 0 at this
  rw [gMat_pow_three h] at this
  simp at this
  exact h1 this

theorem card_SL_four : Nat.card M = 3 ^ 4 * 12185600 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), card_F4]
  decide

end L44Atlas

theorem atlasL44ThreeRank : AtlasL44ThreeRank := by
  intro E _ ⟨e⟩ S _ hS3
  let e' : E ≃* CFSG.RankThree.PartTwo.KFacts.KS21.L44.M := e.trans L44Atlas.pslFourEquivSL
  have : Finite E := Finite.of_equiv _ e'.symm.toEquiv
  obtain ⟨ω, h0, h1⟩ := L44Atlas.exists_ne_zero_ne_one
  have h3 := L44Atlas.pow_three_eq_one h0
  have key := L44Atlas.card_le_of_exponent_three (G := CFSG.RankThree.PartTwo.KFacts.KS21.L44.M)
    (m := 12185600) (by norm_num) L44Atlas.card_SL_four (L44Atlas.gSL_pow_nine h3)
    (L44Atlas.gSL_pow_three_ne_one h3 h1) (S.map e'.toMonoidHom) (by
      rintro _ ⟨s, hs, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, ← map_pow, hS3 s hs, map_one])
  rwa [Subgroup.card_map_of_injective e'.injective] at key

end CFSG.EvenSporadicStandard.M24Std
