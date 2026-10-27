module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamDefs

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank

section Orders

variable {G : Type} [Group G] {K B B' P R : Subgroup G} {m : ℕ}

theorem ExamConfig.R_le_K (h : ExamConfig K B B' P R m) : R ≤ K := h.R_le_P.trans h.sylowP.1

theorem ExamConfig.pow_dvd_card (h : ExamConfig K B B' P R m) :
    2 ^ (4 * m) ∣ Nat.card ↥K := by
  have := Subgroup.card_dvd_of_le h.R_le_K
  rwa [h.card_R] at this

theorem ExamConfig.isElemAbelian_blockU (h : ExamConfig K B B' P R m) :
    IsElemAbelian 2 (blockU B) := by
  obtain ⟨hle, hsq⟩ := h.short.2.2.1
  refine ⟨⟨⟨fun u v => Subtype.ext ?_⟩⟩, hsq⟩
  have hu : (u : G) ∈ Subgroup.centralizer (blockQ B : Set G) := (Subgroup.mem_inf.mp (hle u.2)).2
  have hv : (v : G) ∈ blockQ B := (Subgroup.mem_inf.mp (hle v.2)).1
  exact (Subgroup.mem_centralizer_iff.mp hu (v : G) hv).symm

theorem ExamConfig.isElemAbelian_blockU' (h : ExamConfig K B B' P R m) :
    IsElemAbelian 2 (blockU B') := by
  obtain ⟨hle, hsq⟩ := h.short'.2.2.1
  refine ⟨⟨⟨fun u v => Subtype.ext ?_⟩⟩, hsq⟩
  have hu : (u : G) ∈ Subgroup.centralizer (blockQ B' : Set G) := (Subgroup.mem_inf.mp (hle u.2)).2
  have hv : (v : G) ∈ blockQ B' := (Subgroup.mem_inf.mp (hle v.2)).1
  exact (Subgroup.mem_centralizer_iff.mp hu (v : G) hv).symm

end Orders

section Center

variable {X : Type} [Group X] [Finite X]

theorem card_le_pCore_of_central {Y : Subgroup X} (hY : Y ≤ Subgroup.center X)
    (hY4 : Nat.card Y = 4) : 4 ≤ Nat.card (CFSG.Open.pCore 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : Y.Normal := ⟨fun n hn g => by
    have h1 := Subgroup.mem_center_iff.mp (hY hn) g
    have h2 : g * n * g⁻¹ = n := by rw [h1, mul_inv_cancel_right]
    rw [h2]
    exact hn⟩
  have hp : IsPGroup 2 Y := IsPGroup.of_card (n := 2) (by rw [hY4]; norm_num)
  have hle : Y ≤ CFSG.Open.pCore 2 X := CFSG.LieType.BorelTits.le_pCore 2 hnorm hp
  have := Subgroup.card_le_of_le hle
  rwa [hY4] at this

theorem not_four_dvd_card_center (h : Nat.card (CFSG.Open.pCore 2 X) ≤ 2) :
    ¬ 4 ∣ Nat.card (Subgroup.center X) := by
  intro hdvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Y, hY⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(Subgroup.center X)) 2 (n := 2)
    (by simpa using hdvd)
  have hY4 : Nat.card (Y.map (Subgroup.center X).subtype) = 4 := by
    rw [Subgroup.card_map_of_injective (Subgroup.center X).subtype_injective, hY]
    norm_num
  have hle : Y.map (Subgroup.center X).subtype ≤ Subgroup.center X := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have := card_le_pCore_of_central hle hY4
  omega

theorem pow_seven_dvd_card_quotient_of_pCore (h : Nat.card (CFSG.Open.pCore 2 X) ≤ 2)
    (h8 : 2 ^ 8 ∣ Nat.card X) :
    2 ^ 7 ∣ Nat.card (X ⧸ Subgroup.center X) := by
  have hZ := not_four_dvd_card_center h
  have hmul : Nat.card X = Nat.card (X ⧸ Subgroup.center X) * Nat.card (Subgroup.center X) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  obtain ⟨s, z, hzodd, hz⟩ := Nat.exists_eq_two_pow_mul_odd (n := Nat.card (Subgroup.center X))
    Nat.card_pos.ne'
  have hs : s ≤ 1 := by
    by_contra hs
    apply hZ
    rw [hz]
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4]
    exact dvd_mul_of_dvd_left (pow_dvd_pow 2 (by omega : 2 ≤ s)) _
  rw [hmul, hz] at h8
  have h8' : 2 ^ 8 ∣ Nat.card (X ⧸ Subgroup.center X) * 2 ^ s * z := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using h8
  have h7 : 2 ^ 7 ∣ Nat.card (X ⧸ Subgroup.center X) * z := by
    have h2s : 2 ^ s ∣ 2 := by
      interval_cases s <;> norm_num
    have : 2 ^ 8 ∣ (Nat.card (X ⧸ Subgroup.center X) * z) * 2 := by
      have h3 : 2 ^ 8 ∣ (Nat.card (X ⧸ Subgroup.center X) * z) * 2 ^ s := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using h8'
      exact h3.trans (Nat.mul_dvd_mul_left _ h2s)
    have h8'' : 2 * 2 ^ 7 ∣ 2 * (Nat.card (X ⧸ Subgroup.center X) * z) := by
      simpa [pow_succ, mul_comm] using this
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h8''
  have hcop : Nat.Coprime (2 ^ 7) z :=
    Nat.Coprime.pow_left _ ((Nat.coprime_two_left).mpr hzodd)
  exact hcop.dvd_of_dvd_mul_right h7

end Center

section Quotient

variable {G : Type} [Group G] {K B B' P R : Subgroup G} {m : ℕ}

theorem ExamConfig.card_pCore_group (h : ExamConfig K B B' P R m) :
    Nat.card (CFSG.Open.pCore 2 ↥K) ≤ 2 := by
  have := h.card_pCore
  unfold pCoreOf at this
  rwa [Subgroup.card_map_of_injective K.subtype_injective] at this

theorem ExamConfig.pow_seven_dvd_card_quotient [Finite G] (h : ExamConfig K B B' P R m) :
    2 ^ 7 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := by
  refine pow_seven_dvd_card_quotient_of_pCore h.card_pCore_group ?_
  exact (pow_dvd_pow 2 (by have := h.two_le; omega : 8 ≤ 4 * m)).trans h.pow_dvd_card

end Quotient

end CFSG.QuasithinUnique.Lin2
