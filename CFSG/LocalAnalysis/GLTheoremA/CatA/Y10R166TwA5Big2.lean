module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Big
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPart
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Mult
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166SUBlocks

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ClassicalGroups.UnitaryFlag CFSG.SeitzReduction.UnitaryPilot
open CFSG.LocalAnalysis.ComponentInitial
open Matrix

namespace TwA5Big

section Certs


variable {n : ℕ} {F : Type} [Field F] [Finite F]

theorem exists_twA5_prime {n : ℕ} (hn : 4 ≤ n) :
    ∃ q : ℕ, q.Prime ∧ q ∣ 2 ^ n + 1 ∧ ¬ q ∣ 30 := by
  obtain ⟨q, hq, hdvd, hprim⟩ :=
    CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one (2 * n) (by omega) (by omega)
  have h2n : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by
    rw [show 2 * n = n * 2 by omega, pow_mul]
  have hfac : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
    simpa using Nat.sq_sub_sq (2 ^ n) 1
  have hqfac : q ∣ 2 ^ n + 1 := by
    rcases (Nat.Prime.dvd_mul hq).1 (hfac ▸ h2n ▸ hdvd) with h | h
    · exact h
    · exact absurd h (hprim n (by omega) (by omega))
  refine ⟨q, hq, hqfac, ?_⟩
  intro h30
  have h5 : q ∣ 5 := by
    have h30' : q ∣ 6 * 5 := by simpa using h30
    rcases (Nat.Prime.dvd_mul hq).1 h30' with h | h
    · exact absurd h (by
        intro h6
        have h23 : q ∣ 2 * 3 := by simpa using h6
        rcases (Nat.Prime.dvd_mul hq).1 h23 with h2 | h3
        · have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h2
          subst hq2
          have h2dvd : 2 ∣ 2 ^ (2 * n) := dvd_pow_self 2 (by omega)
          have hp : 1 ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
          have h1 : 2 ∣ 1 := by
            have h := Nat.dvd_sub h2dvd hdvd
            rwa [show 2 ^ (2 * n) - (2 ^ (2 * n) - 1) = 1 by omega] at h
          omega
        · have hq3 : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 h3
          subst hq3
          exact hprim 2 (by norm_num) (by omega) (by norm_num))
    · exact h
  have hq5 : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).1 h5
  subst hq5
  exact hprim 4 (by norm_num) (by omega) (by norm_num)

theorem exists_twA5_zeta (h : UnitaryFieldData 2 n F) {q : ℕ} (hq : q.Prime)
    (hqdvd : q ∣ 2 ^ n + 1) :
    ∃ ζu : Fˣ, h.norm (ζu : F) = 1 ∧ orderOf ζu = q := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact q.Prime := ⟨hq⟩
  have hcard : Fintype.card (Units.map h.normHom).ker = 2 ^ n + 1 := by
    rw [← Nat.card_eq_fintype_card, h.card_ker_normUnits_and_surjective.1]
  obtain ⟨ζu, hζo⟩ :=
    exists_prime_orderOf_dvd_card (G := (Units.map h.normHom).ker) q (by rw [hcard]; exact hqdvd)
  refine ⟨ζu, h.mem_ker_normUnits.1 ζu.2, ?_⟩
  rw [← hζo, Subgroup.orderOf_mk]

theorem diagFiveLast_not_scalar (h : UnitaryFieldData 2 n F) {q : ℕ} (hq : q.Prime)
    (hq6 : ¬ q ∣ 6) {ζu : Fˣ} (hζ : h.norm (ζu : F) = 1) (hζo : orderOf ζu = q) :
    diagFiveLast h (ζu : F) hζ ∉ unitaryScalars h 6 := by
  intro hmem
  rw [mem_unitaryScalars] at hmem
  obtain ⟨c, -, -, hEq⟩ := hmem
  have hmat : ((diagFiveLast h (ζu : F) hζ : unitarySU 2 n F 6) : GL (Fin 6) F) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) c := hEq
  have h00 := congrFun (congrFun (congrArg (fun g : GL (Fin 6) F =>
    ((g : Matrix (Fin 6) (Fin 6) F))) hmat) 0) 0
  have h55 := congrFun (congrFun (congrArg (fun g : GL (Fin 6) F =>
    ((g : Matrix (Fin 6) (Fin 6) F))) hmat) 5) 5
  simp only [coe_diagFiveLast, Matrix.diagonal_apply_eq, Fin.isValue, Fin.reduceEq,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h00 h55
  have h1 : (ζu : F) = (c : F) := h00
  have h2 : ((ζu : F) ^ 5)⁻¹ = (c : F) := h55
  have h3 : ((ζu : F) ^ 5)⁻¹ = (ζu : F) := by rw [h2, h1]
  have h6 : (ζu : F) ^ 6 = 1 := by
    have h4 : (ζu : F) ^ 5 * ((ζu : F) ^ 5)⁻¹ = (ζu : F) ^ 6 := by
      rw [h3, ← pow_succ]
    rw [mul_inv_cancel₀ (pow_ne_zero 5 (Units.ne_zero ζu))] at h4
    exact h4.symm
  have h6u : ζu ^ 6 = 1 := by
    ext
    push_cast
    exact h6
  have hdvd : q ∣ 6 := by
    rw [← hζo]
    exact orderOf_dvd_iff_pow_eq_one.2 h6u
  exact hq6 hdvd

theorem blockSU_suFiveIndex_clauses (h : UnitaryFieldData 2 n F) (hn : 2 ≤ n) :
    ((Subgroup.center ↥(blockSU h suFiveIndex) = ⊥ ∧
        TrivialMultiplierT ↥(blockSU h suFiveIndex)) ∨ Even n) ∧
      Odd (Nat.card (Subgroup.center ↥(blockSU h suFiveIndex))) ∧
      4 * n ≤ twoRank ↥(blockSU h suFiveIndex) ∧
      (∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ 2 ^ (2 * n) - 1 →
        r ∣ Nat.card (↥(blockSU h suFiveIndex) ⧸
          Subgroup.center ↥(blockSU h suFiveIndex))) :=
  unitaryFive_mult (J := ↥(blockSU h suFiveIndex)) (n := n) hn
    (hasLabel_blockSU_suFiveIndex h (by omega))
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds

theorem centralizes_of_unitaryProj_centralizes (h : UnitaryFieldData 2 n F)
    {S : Subgroup (unitarySU 2 n F 6)} (hS : IsPGroup 2 S) {A : unitarySU 2 n F 6}
    (hA : ∀ s ∈ S, unitaryProj h 6 A * unitaryProj h 6 s =
      unitaryProj h 6 s * unitaryProj h 6 A) :
    A ∈ Subgroup.centralizer (S : Set (unitarySU 2 n F 6)) := by
  have hodd : Odd (Nat.card (unitaryScalars h 6)) :=
    CFSG.SeitzReduction.UnitaryPilot.odd_card_unitaryScalars h (by norm_num)
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  have hsk : s ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  set c : unitarySU 2 n F 6 := A * s * A⁻¹ * s⁻¹ with hc
  have hcS : c ∈ unitaryScalars h 6 := by
    rw [← ker_unitaryProj h 6, MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hc]
    rw [hA s hs]
    group
  have hcen : c * s = s * c :=
    (Subgroup.mem_center_iff.1 (unitaryScalars_le_center h 6 hcS) s).symm
  have hcs : c * s = A * s * A⁻¹ := by
    rw [hc]
    group
  have h2 : (A * s * A⁻¹) ^ 2 ^ k = 1 := by
    rw [← MulAut.conj_apply A s, ← map_pow, hsk, map_one]
  have h3 : (c * s) ^ 2 ^ k = c ^ 2 ^ k * s ^ 2 ^ k := Commute.mul_pow hcen _
  rw [hcs, h2, hsk, mul_one] at h3
  have hpow : c ^ 2 ^ k = 1 := h3.symm
  have hdvd : orderOf c ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.2 hpow
  have hdvd2 : orderOf c ∣ Nat.card (unitaryScalars h 6) := by
    have h1 := orderOf_dvd_natCard (⟨c, hcS⟩ : unitaryScalars h 6)
    rwa [Subgroup.orderOf_mk] at h1
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (unitaryScalars h 6)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  have hone : orderOf c = 1 := Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hdvd hdvd2)
  have h1 : A * s * A⁻¹ = s := by rw [← hcs, orderOf_eq_one_iff.1 hone, one_mul]
  have h2 : A * s = s * A := by
    have h3 := congrArg (fun x => x * A) h1
    simpa [mul_assoc] using h3
  exact h2.symm

end Certs

end TwA5Big

end CFSG.LocalAnalysis.GLTheoremA.Y10F
