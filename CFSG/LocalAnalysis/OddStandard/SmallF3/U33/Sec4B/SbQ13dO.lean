module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13c0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b1

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private theorem q13dO_y_ne_z (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    x₁ ^ 2 ≠ (x₁ * x₂) ^ 2 := by
  intro hEq
  have hy_ne_one : x₁ ^ 2 ≠ 1 := (q13a_x₁_facts h).2.2.2.2.2
  have h4 : x₁ ^ 4 = 1 := by
    rw [← (q13a_x₁_facts h).2.2.1]
    exact pow_orderOf_eq_one x₁
  have hsq : x₁ ^ 2 * x₁ ^ 2 = 1 := by
    calc x₁ ^ 2 * x₁ ^ 2 = x₁ ^ (2 + 2) := by rw [← pow_add]
      _ = x₁ ^ 4 := by norm_num
      _ = 1 := h4
  have h1 : lam * x₁ ^ 2 * lam⁻¹ = 1 := by
    rw [q13c_lam_y h, ← hEq, hsq]
  have h2 : x₁ ^ 2 = 1 := by
    calc x₁ ^ 2 = lam⁻¹ * (lam * x₁ ^ 2 * lam⁻¹) * lam := by group
      _ = lam⁻¹ * 1 * lam := by rw [h1]
      _ = 1 := by group
  exact hy_ne_one h2

private theorem q13dO_conjIn_y_ncard_le (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hB : Q13Bs t x₁ x₂ lam tau) {𝒮 : Subgroup G} (h𝒮 : IsPGroup 2 𝒮)
    (hU : ctxU t tau x₁ x₂ lam ≤ 𝒮) :
    (conjIn 𝒮 (x₁ ^ 2)).ncard ≤ 2 := by
  have hsubset : conjIn 𝒮 (x₁ ^ 2) ⊆ ({x₁ ^ 2, x₁ ^ 2 * (x₁ * x₂) ^ 2} : Set G) := by
    rintro u ⟨s, hs, rfl⟩
    have hB𝒮 := hB 𝒮 h𝒮 hU
    have hyV : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
    have hzV : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
    have hconjV : s * x₁ ^ 2 * s⁻¹ ∈ fourGrp x₁ x₂ := (hB𝒮.V_normal).2 s hs (x₁ ^ 2) hyV
    have hz_cent : s * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * s := q13b_z_central h h𝒮 hU s hs
    have hcomm_yz : x₁ ^ 2 * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * x₁ ^ 2 := by
      haveI : IsMulCommutative ↥(fourGrp x₁ x₂) := (h.c11.wreath.fourGrp_eq_omega).2.1.1
      exact congrArg Subtype.val (mul_comm' ⟨x₁ ^ 2, hyV⟩ ⟨(x₁ * x₂) ^ 2, hzV⟩)
    have hy2 : x₁ ^ 2 * x₁ ^ 2 = 1 := by
      have h4 : x₁ ^ 4 = 1 := by
        rw [← (q13a_x₁_facts h).2.2.1]
        exact pow_orderOf_eq_one x₁
      calc x₁ ^ 2 * x₁ ^ 2 = x₁ ^ (2 + 2) := by rw [← pow_add]
        _ = x₁ ^ 4 := by norm_num
        _ = 1 := h4
    have hz2 : (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 := (q13b_z_facts h).2
    rcases q13b_mem_closure_pair hy2 hz2 hcomm_yz hconjV with h1 | h1 | h1 | h1
    · exfalso
      have hy1 : x₁ ^ 2 = 1 := by
        calc x₁ ^ 2 = s⁻¹ * (s * x₁ ^ 2 * s⁻¹) * s := by group
          _ = s⁻¹ * 1 * s := by rw [h1]
          _ = 1 := by group
      exact (q13a_x₁_facts h).2.2.2.2.2 hy1
    · rw [h1]
      simp
    · exfalso
      have hzy : x₁ ^ 2 = (x₁ * x₂) ^ 2 := by
        calc x₁ ^ 2 = s⁻¹ * (s * x₁ ^ 2 * s⁻¹) * s := by group
          _ = s⁻¹ * (x₁ * x₂) ^ 2 * s := by rw [h1]
          _ = s⁻¹ * ((x₁ * x₂) ^ 2 * s) := by rw [mul_assoc]
          _ = s⁻¹ * (s * (x₁ * x₂) ^ 2) := by rw [← hz_cent]
          _ = (x₁ * x₂) ^ 2 := by group
      exact q13dO_y_ne_z h hzy
    · rw [h1]
      simp
  calc (conjIn 𝒮 (x₁ ^ 2)).ncard ≤ ({x₁ ^ 2, x₁ ^ 2 * (x₁ * x₂) ^ 2} : Set G).ncard :=
        Set.ncard_le_ncard hsubset
    _ ≤ 2 := by
        rcases eq_or_ne (x₁ ^ 2) (x₁ ^ 2 * (x₁ * x₂) ^ 2) with h | h
        · rw [← h]
          calc _ ≤ ({x₁ ^ 2} : Set G).ncard + 1 := Set.ncard_insert_le _ _
            _ = 2 := by simp
        · rw [Set.ncard_pair h]

private theorem q13dO_conjIn_tau_ncard_le (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hB : Q13Bs t x₁ x₂ lam tau) {𝒮 : Subgroup G} (h𝒮 : IsPGroup 2 𝒮)
    (hU : ctxU t tau x₁ x₂ lam ≤ 𝒮) :
    (conjIn (𝒮 ⊓ centralizer ({x₁ ^ 2} : Set G)) tau).ncard ≤ 4 := by
  have hsubset : conjIn (𝒮 ⊓ centralizer ({x₁ ^ 2} : Set G)) tau ⊆
      tau • (fourGrp x₁ x₂ : Set G) := by
    rintro u ⟨d, hd, rfl⟩
    have hd𝒮 : d ∈ 𝒮 := (Subgroup.mem_inf.mp hd).1
    have hB𝒮 := hB 𝒮 h𝒮 hU
    have hdconjN : d * tau * d⁻¹ ∈ ctxN tau x₁ x₂ :=
      (hB𝒮.N_normal).2 d hd𝒮 tau (q13b_tau_mem_N h)
    have hdconjNotV : d * tau * d⁻¹ ∉ fourGrp x₁ x₂ := by
      intro hmem
      have htauV : tau ∈ fourGrp x₁ x₂ := by
        have hconj : d⁻¹ * (d * tau * d⁻¹) * d ∈ fourGrp x₁ x₂ := by
          simpa only [inv_inv] using
            (hB𝒮.V_normal).2 d⁻¹ (𝒮.inv_mem hd𝒮) (d * tau * d⁻¹) hmem
        rw [show d⁻¹ * (d * tau * d⁻¹) * d = tau by group] at hconj
        exact hconj
      exact l12_tau_not_mem_V h.c11.toCtx10.toCtx4 htauV
    rcases (q13d_mem_N h).mp hdconjN with hV | ⟨v, hvV, hveq⟩
    · exact absurd hV hdconjNotV
    · exact ⟨v, hvV, hveq.symm⟩
  calc (conjIn (𝒮 ⊓ centralizer ({x₁ ^ 2} : Set G)) tau).ncard
      ≤ (tau • (fourGrp x₁ x₂ : Set G)).ncard := Set.ncard_le_ncard hsubset
    _ = 4 := by
        rw [Set.ncard_smul_set, ← Nat.card_coe_set_eq]
        exact h.c11.wreath.fourGrp_eq_omega.2.2

private theorem q13dO_E_le_C (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hB : Q13Bs t x₁ x₂ lam tau) {𝒮 : Subgroup G} (h𝒮 : IsPGroup 2 𝒮)
    (hU : ctxU t tau x₁ x₂ lam ≤ 𝒮) :
    𝒮 ⊓ centralizer ({x₁ ^ 2} : Set G) ⊓ centralizer ({tau} : Set G) ≤
      𝒮 ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G) := by
  intro g hg
  have hgS : g ∈ 𝒮 := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg).1).1
  have hgy : x₁ ^ 2 * g = g * x₁ ^ 2 :=
    (Subgroup.mem_centralizer_singleton_iff.mp
      (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg).1).2).symm
  have hgtau : tau * g = g * tau :=
    (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hg).2).symm
  have hgz : (x₁ * x₂) ^ 2 * g = g * (x₁ * x₂) ^ 2 :=
    (q13b_z_central h h𝒮 hU g hgS).symm
  have hN_le : ctxN tau x₁ x₂ ≤ centralizer ({g} : Set G) := by
    rw [ctxN, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hgtau
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hgy
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hgz
  exact Subgroup.mem_inf.mpr ⟨hgS, Subgroup.mem_centralizer_iff.mpr fun n hn =>
    Subgroup.mem_centralizer_singleton_iff.mp (hN_le hn)⟩

theorem q13d_card_le_cent_N (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hB : Q13Bs t x₁ x₂ lam tau) {𝒮 : Subgroup G} (h𝒮 : IsPGroup 2 𝒮) (hU :
      ctxU t tau x₁ x₂ lam ≤ 𝒮) :
    Nat.card ↥𝒮 ≤ 8 * Nat.card ↥(𝒮 ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G)) := by
  let D : Subgroup G := 𝒮 ⊓ centralizer ({x₁ ^ 2} : Set G)
  let E : Subgroup G := D ⊓ centralizer ({tau} : Set G)
  have hcardS : Nat.card ↥𝒮 = (conjIn 𝒮 (x₁ ^ 2)).ncard * Nat.card ↥D :=
    card_eq_ncard_conjIn_mul 𝒮 (x₁ ^ 2)
  have hcardD : Nat.card ↥D = (conjIn D tau).ncard * Nat.card ↥E :=
    card_eq_ncard_conjIn_mul D tau
  have hy_le : (conjIn 𝒮 (x₁ ^ 2)).ncard ≤ 2 := q13dO_conjIn_y_ncard_le h hB h𝒮 hU
  have htau_le : (conjIn D tau).ncard ≤ 4 := q13dO_conjIn_tau_ncard_le h hB h𝒮 hU
  have hE_le_C : Nat.card ↥E ≤
      Nat.card ↥(𝒮 ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G)) :=
    card_le_of_le (q13dO_E_le_C h hB h𝒮 hU)
  calc Nat.card ↥𝒮
      = (conjIn 𝒮 (x₁ ^ 2)).ncard * Nat.card ↥D := hcardS
    _ = (conjIn 𝒮 (x₁ ^ 2)).ncard * ((conjIn D tau).ncard * Nat.card ↥E) := by rw [hcardD]
    _ ≤ 2 * (4 * Nat.card ↥(𝒮 ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G))) := by
        exact Nat.mul_le_mul hy_le (Nat.mul_le_mul htau_le hE_le_C)
    _ = 8 * Nat.card ↥(𝒮 ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G)) := by ring

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
