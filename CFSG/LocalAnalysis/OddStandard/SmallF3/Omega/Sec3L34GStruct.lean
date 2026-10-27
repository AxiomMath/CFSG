module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GOdd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GFacts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2G2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34G2Q8

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private theorem l34g_card_sl23 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) = 24 := by
  rw [Matrix.card_SL_field (𝔽 := ZMod 3) 2, ZMod.card, Fin.prod_univ_two]
  norm_num

theorem l34g_pocket_oddCore_isPGroup (hM3 : Asc82SchurOdd3) [Finite G] {x y : G}
    {X K : Subgroup G} (hD : Sec3PocketData x X y K) : IsPGroup 3 ↥(oddCore ↥K) := by
  have hOK := l34g_oddCore_le_oddCore_of_pocketData asc82NoQ8InL2_holds
    asc82OddCoreCentralizerQ8_holds hD
  have hX3 : IsPGroup 3 ↥(oddCore ↥X) := hM3 G X hD.inFStar
  intro k
  obtain ⟨z, hz, hzk⟩ := hOK (Subgroup.mem_map_of_mem K.subtype k.2)
  obtain ⟨n, hn⟩ := hX3 ⟨z, hz⟩
  refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
  have h1 : (z : G) ^ 3 ^ n = 1 := by
    have := congrArg (fun w : ↥(oddCore ↥X) => ((w : ↥X) : G)) hn
    simpa using this
  have h2 : ((k : ↥K) : G) = (z : G) := hzk.symm
  simp [h2, h1]

theorem l34g_pocket_card (hM3 : Asc82SchurOdd3) [Finite G] {x y : G} {X K : Subgroup G}
    (hD : Sec3PocketData x X y K) :
    ∃ m : ℕ, Nat.card ↥K = 24 * 3 ^ m ∧ Nat.card ↥(oddCore ↥K) = 3 ^ m := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp (l34g_pocket_oddCore_isPGroup hM3 hD)
  obtain ⟨e⟩ := hD.pocket.2.2.2
  refine ⟨m, ?_, hm⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (oddCore ↥K)
  rw [Nat.card_congr e.toEquiv, l34g_card_sl23, hm] at h1
  exact h1

theorem sec3_pocket_structure (hM3 : Asc82SchurOdd3) [Finite G] {x y : G} {X K : Subgroup G}
    (hD : Sec3PocketData x X y K) :
    Nat.card ↥(CFSG.inSubgroup (CFSG.pCore 2) K) = 8 ∧
      ∀ g ∈ K, ∃ n : ℕ, g ^ (3 ^ n) ∈ CFSG.inSubgroup (CFSG.pCore 2) K := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hcardK, -⟩ := l34g_pocket_card hM3 hD
  obtain ⟨f, hf, -, hfQ⟩ := exists_quaternion_of_pocketData_q8 asc82NoQ8InL2_holds
    asc82OddCoreCentralizerQ8_holds hD
  let Qg : Subgroup ↥K := CFSG.pCore 2 ↥K
  have hcardQ : Nat.card ↥(CFSG.inSubgroup (CFSG.pCore 2) K) = Nat.card ↥Qg :=
    Subgroup.card_map_of_injective K.subtype_injective
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (CFSG.pCore_isPGroup (p := 2) (G := ↥K))
  have hQ8 : Nat.card ↥Qg ∣ 8 := by
    have h1 : 2 ^ k ∣ 8 * 3 ^ (m + 1) := by
      have h := Subgroup.card_subgroup_dvd_card Qg
      rw [hk, hcardK] at h
      have h' : 24 * 3 ^ m = 8 * 3 ^ (m + 1) := by ring
      rwa [h'] at h
    have hcop : Nat.Coprime (2 ^ k) (3 ^ (m + 1)) := Nat.Coprime.pow _ _ (by norm_num)
    rw [hk]
    exact hcop.dvd_of_dvd_mul_right h1
  have h8 : 8 ∣ Nat.card ↥(CFSG.inSubgroup (CFSG.pCore 2) K) := by
    rw [← natCard_range_quaternion hf]
    exact Subgroup.card_dvd_of_le hfQ
  have hQ : Nat.card ↥Qg = 8 := Nat.dvd_antisymm hQ8 (hcardQ ▸ h8)
  refine ⟨hcardQ.trans hQ, fun g hg => ⟨m + 1, ?_⟩⟩
  have hquot : Nat.card (↥K ⧸ Qg) = 3 ^ (m + 1) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Qg
    rw [hcardK, hQ] at h1
    have h2 : 3 ^ (m + 1) * 8 = Nat.card (↥K ⧸ Qg) * 8 := by rw [← h1]; ring
    exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h2).symm
  have hpow : (QuotientGroup.mk (⟨g, hg⟩ : ↥K) : ↥K ⧸ Qg) ^ (3 ^ (m + 1)) = 1 := by
    rw [← hquot]
    exact pow_card_eq_one'
  have hmem : (⟨g, hg⟩ : ↥K) ^ (3 ^ (m + 1)) ∈ Qg := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hpow
  exact ⟨_, hmem, rfl⟩

end CFSG.OddStandard.SmallF3.Omega
