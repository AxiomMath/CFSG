module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AQ15E
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AQ15F
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise commutatorElement

section Q15G

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem q15_cent_Q1_Y (h : L41GPh10 t L S x₁ x₂ lam rho) (ht : t ∉ l41Q1 t x₁ x₂ rho)
    (hcard : Nat.card (l41Q1 t x₁ x₂ rho) = 2 ^ 8) :
    l41Q1 t x₁ x₂ rho ⊓ centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) =
        l41R t x₁ x₂ rho ∨
      l41Q1 t x₁ x₂ rho ⊓ centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) =
        l41Q1 t x₁ x₂ rho := by
  have hρM : rho ∈ l41M t x₁ x₂ rho := q14_rho_mem_M h.toL41GPh8
  have hρ3 : rho ^ 3 = 1 := q15_rho_cube h.toL41GPh1
  have hρY : rho ∈ normalizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) :=
    q14_mem_normalizer_Y h hρM
  have hRC : l41R t x₁ x₂ rho ≤
      l41Q1 t x₁ x₂ rho ⊓ centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) := by
    refine le_inf (q15_R_le h.toL41GPh8) ?_
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact m13_comm_R h (m13_Y_le_R t x₁ x₂ rho hy) hr
  have hCQ : l41Q1 t x₁ x₂ rho ⊓ centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) ≤
      l41Q1 t x₁ x₂ rho := inf_le_left
  have hdvdC : Nat.card ↥(l41Q1 t x₁ x₂ rho ⊓
      centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G)) ∣ 2 ^ 8 :=
    hcard ▸ Subgroup.card_dvd_of_le hCQ
  have hdvdR : 2 ^ 6 ∣ Nat.card ↥(l41Q1 t x₁ x₂ rho ⊓
      centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G)) :=
    h.rfacts.card_R ▸ Subgroup.card_dvd_of_le hRC
  obtain ⟨k, hk, hkC⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvdC
  have hk6 : 6 ≤ k := by
    rw [hkC] at hdvdR
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvdR
  have hmod : Nat.card ↥(l41Q1 t x₁ x₂ rho ⊓
      centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G)) % 3 = 1 := by
    refine q14_card_mod_three hρ3 ?_ ?_
    · intro d hd
      obtain ⟨hdQ, hdC⟩ := Subgroup.mem_inf.mp hd
      refine Subgroup.mem_inf.mpr ⟨(q15_normal_Q1 h).2 rho hρM d hdQ, ?_⟩
      rw [Subgroup.mem_centralizer_iff] at hdC ⊢
      intro y hy
      have hy' : rho⁻¹ * y * rho ∈ l41Y t x₁ x₂ rho :=
        (Subgroup.mem_normalizer_iff''.mp hρY y).mp hy
      have hcomm := hdC _ hy'
      calc y * (rho * d * rho⁻¹) = rho * ((rho⁻¹ * y * rho) * d) * rho⁻¹ := by group
        _ = rho * (d * (rho⁻¹ * y * rho)) * rho⁻¹ := by rw [hcomm]
        _ = (rho * d * rho⁻¹) * y := by group
    · intro d hd hfix
      obtain ⟨hdQ₁, -⟩ := Subgroup.mem_inf.mp hd
      have hdQ : d ∈ l41Q t x₁ x₂ rho := q15_Q1_le_Q h.toL41GPh8 hdQ₁
      have hdcent : d ∈ centralizer ({rho} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc d * rho = (rho * d * rho⁻¹) * rho := by rw [hfix]
          _ = rho * d := by group
      have hdt : d ∈ zpowers t := by
        rw [← q14_cent_Q_rho h]
        exact Subgroup.mem_inf.mpr ⟨hdQ, hdcent⟩
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hdt
      rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
      · rw [zpow_mul, zpow_two, t_mul_self h.hyp, one_zpow]
      · exfalso
        apply ht
        have hodd : t ^ (2 * m + 1 : ℤ) = t := by
          rw [zpow_add_one, zpow_mul, zpow_two, t_mul_self h.hyp, one_zpow, one_mul]
        rw [hodd] at hdQ₁
        exact hdQ₁
  have hk' : k = 6 ∨ k = 8 := by
    rw [hkC] at hmod
    interval_cases k
    · left; rfl
    · norm_num at hmod
    · right; rfl
  rcases hk' with rfl | rfl
  · left
    exact (Subgroup.eq_of_le_of_card_ge hRC
      (le_of_eq (by rw [hkC, h.rfacts.card_R]))).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge hCQ (le_of_eq (by rw [hcard, hkC]))

theorem l41_q1_of (h : L41GPh14 t L S x₁ x₂ lam rho) (hV1 : 2 ∣ (l41V1 t x₁ x₂ rho lam).index) :
    L41Q1Facts t x₁ x₂ lam rho := by
  obtain ⟨ht, hQ, hcard, hquot⟩ := q15_hs27 h.toL41GPh10
  refine
    { t_not_mem := ht
      Q_eq := hQ
      R_le := q15_R_le h.toL41GPh8
      normal_Q1 := q15_normal_Q1 h.toL41GPh10
      card_Q1 := hcard
      Y_le := q15_Y_le h.toL41GPh10
      comm_le := ?_
      quot_Q1 := hquot
      V1_pGroup := q15_V1_pGroup h.toL41GPh10 hQ
      V1_sylow := q15_V1_sylow h.toL41GPh10 hQ
      card_V1 := q15_card_V1 h.toL41GPh10 hQ
      V1_not_sylow := hV1
      cent_Q1_Y := q15_cent_Q1_Y h.toL41GPh10 ht hcard }
  rcases hquot with e | e
  · exact q15_comm_le_of_sectionIso e
  · exact q15_comm_le_of_sectionIso e

end Q15G

end CFSG.OddStandard.SmallF3.HarrisU33.S4A

namespace CFSG.OddStandard.SmallF3.HarrisU33

theorem l41_q1_holds : L41Q1Stmt :=
  fun h => S4A.l41_q1_of h.toG
    (S4A.q15_V1_not_sylow h.toL41Ph10 (S4A.q15_hs27 h.toL41Ph10.toG).2.1)

end CFSG.OddStandard.SmallF3.HarrisU33
