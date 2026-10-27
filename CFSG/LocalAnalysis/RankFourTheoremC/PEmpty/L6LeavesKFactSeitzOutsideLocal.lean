module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactSeitzOutsideBase
public import CFSG.Quasithin.Recognition.CertTitsTwoLocal
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels
public import CFSG.Quasithin.H13.U3U33Fixed
public import CFSG.Quasithin.EmptyFaithful.SBc17Ent3

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KSeitz

open CFSG.Open Subgroup
open CFSG.LieType.SeitzGeneration (Cat)
open CFSG.Sporadic.Schreier.Tits (titsD titsModelEquiv)
open CFSG.Quasithin (titsSD titsHD titsND)

section Tits


theorem false_of_tits {K : Type} [Group K] [Finite K] {hv : TauCeti.LieTypeIndex.tits.Valid}
    (e : K ≃* Cat ⟨.tits, hv⟩) {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) {E P : Subgroup K}
    (hE : Nat.card E = f ^ 2) (S : Sylow 2 K) (hP : P ≠ ⊤) (hEP : E ≤ P)
    (hSP : (S : Subgroup K) ≤ P) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ⟩ := titsModelEquiv K 2 1 (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨e⟩⟩)
  have hSp : IsPGroup 2 titsSD :=
    IsPGroup.of_card (n := 11) (by rw [CFSG.Quasithin.card_titsSD]; norm_num)
  have hSi : ¬ 2 ∣ titsSD.index := by
    have h := Subgroup.card_mul_index titsSD
    rw [CFSG.Quasithin.card_titsSD, CFSG.Sporadic.Schreier.Tits.card_titsD] at h
    have : titsSD.index = 8775 := by omega
    rw [this]
    decide
  have hmem := card_mem_of_overgroups φ (hSp.toSylow hSi) {2048, 10240, 6144}
    (fun X hX => by
      rw [IsPGroup.toSylow_coe] at hX
      rcases CFSG.Quasithin.titsD_overgroups X hX with h | h | h | h
      · right
        rw [h, CFSG.Quasithin.card_titsSD]
        simp
      · right
        rw [h, CFSG.Quasithin.card_titsHD]
        simp
      · right
        rw [h, CFSG.Quasithin.card_titsND]
        simp
      · left
        exact h) S hP hSP
  have hdvd : f ^ 2 ∣ Nat.card P := hE ▸ Subgroup.card_dvd_of_le hEP
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h
  · rw [h, show (2048 : ℕ) = 2 ^ 11 * 1 by norm_num] at hdvd
    exact not_sq_dvd_two_pow_mul hf hf2 (Or.inl rfl) hdvd
  · rw [h, show (10240 : ℕ) = 2 ^ 11 * 5 by norm_num] at hdvd
    exact not_sq_dvd_two_pow_mul hf hf2 (Or.inr Nat.prime_five) hdvd
  · rw [h, show (6144 : ℕ) = 2 ^ 11 * 3 by norm_num] at hdvd
    exact not_sq_dvd_two_pow_mul hf hf2 (Or.inr Nat.prime_three) hdvd

end Tits

section U33


theorem false_of_u33 {K : Type} [Group K] [Finite K] (h : CFSG.Quasithin.IsPSU 3 3 1 K) {f : ℕ}
    (hf : f.Prime) (hf2 : f ≠ 2) {E P : Subgroup K} (hE : Nat.card E = f ^ 2) (S : Sylow 2 K)
    (hP : P ≠ ⊤) (hEP : E ≤ P) (hSP : (S : Subgroup K) ≤ P) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eK⟩ := CFSG.Quasithin.SBc17.nonempty_mulEquiv_PSU3_of_isPSU h
  obtain ⟨eU⟩ := CFSG.Quasithin.u33Pres_mulEquiv_PSU3
  have hmem := card_mem_of_overgroups (eK.trans eU.symm) CFSG.Quasithin.u33SylowT {32, 96}
    (fun X hX => by
      rw [CFSG.Quasithin.coe_u33SylowT] at hX
      rcases CFSG.Quasithin.u33Data.lattice X hX with h | h | h | h
      · right
        rw [h, CFSG.Quasithin.u33_card_T]
        simp
      · right
        rw [h, CFSG.Quasithin.H13.U3.card_u33_A]
        simp
      · right
        rw [h, CFSG.Quasithin.H13.U3.card_u33_B]
        simp
      · left
        exact h) S hP hSP
  have hdvd : f ^ 2 ∣ Nat.card P := hE ▸ Subgroup.card_dvd_of_le hEP
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h
  · rw [h, show (32 : ℕ) = 2 ^ 5 * 1 by norm_num] at hdvd
    exact not_sq_dvd_two_pow_mul hf hf2 (Or.inl rfl) hdvd
  · rw [h, show (96 : ℕ) = 2 ^ 5 * 3 by norm_num] at hdvd
    exact not_sq_dvd_two_pow_mul hf hf2 (Or.inr Nat.prime_three) hdvd

end U33

end KSeitz

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
