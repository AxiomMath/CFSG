module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b2a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b2b

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private theorem q13b_F_cent_V_aux_zconj (h : Q13Om t L S x₁ x₂ lam rho tau om) {x n : G}
    (hx : x ∈ zpowers ((x₁ * x₂) ^ 2)) (hn : n ∈ ctxU t tau x₁ x₂ lam) :
    n * x * n⁻¹ = x := by
  have hz : (x₁ * x₂) ^ 2 ∈ centralizer ({n} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact q13b_z_central h (q13b_isPGroup_U h) le_rfl n hn
  have hle : zpowers ((x₁ * x₂) ^ 2) ≤ centralizer ({n} : Set G) :=
    Subgroup.zpowers_le.mpr hz
  have hcomm : n * x = x * n := Subgroup.mem_centralizer_iff.mp (hle hx) n (by simp)
  calc n * x * n⁻¹ = x * n * n⁻¹ := by rw [hcomm]
    _ = x := by group

private theorem q13b_F_cent_V_aux_cases (h : Q13Om t L S x₁ x₂ lam rho tau om) {F : Subgroup G}
    (hF : NormalIn F (ctxU t tau x₁ x₂ lam)) (hFe : CFSG.Open.IsElemAbelian 2 F)
    (hFc : Nat.card F = 4) (hzF : (x₁ * x₂) ^ 2 ∈ F) {f : G} (hfF : f ∈ F) :
    ∀ n ∈ ctxU t tau x₁ x₂ lam,
      n * f * n⁻¹ = f ∨ n * f * n⁻¹ = f * (x₁ * x₂) ^ 2 := by
  intro n hn
  obtain ⟨hz1, hz2⟩ := q13b_z_facts h
  have hle : zpowers ((x₁ * x₂) ^ 2) ≤ F := Subgroup.zpowers_le.mpr hzF
  have hcard0 : Nat.card (zpowers ((x₁ * x₂) ^ 2)) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (p := 2) (by simpa [pow_two] using hz2) hz1
  have hcard : Nat.card F = 2 * Nat.card (zpowers ((x₁ * x₂) ^ 2)) := by
    rw [hFc, hcard0]
  have hgF : ∀ x ∈ F, n * x * n⁻¹ ∈ F := fun x hx => hF.2 n hn x hx
  have hgF₀ : ∀ x ∈ zpowers ((x₁ * x₂) ^ 2), n * x * n⁻¹ ∈ zpowers ((x₁ * x₂) ^ 2) := by
    intro x hx
    rw [q13b_F_cent_V_aux_zconj h hx hn]
    exact hx
  have hgF₀' : ∀ x ∈ zpowers ((x₁ * x₂) ^ 2), n⁻¹ * x * n ∈ zpowers ((x₁ * x₂) ^ 2) := by
    intro x hx
    have hx' : n⁻¹ * x * n = x := by
      simpa using q13b_F_cent_V_aux_zconj h hx (Subgroup.inv_mem (ctxU t tau x₁ x₂ lam) hn)
    rw [hx']
    exact hx
  have hmem := q13b_comm_mem_of_index_two hle hcard hgF hgF₀ hgF₀' f hfF
  rcases q13b_mem_zpowers_sq hz2 hmem with h1 | h1
  · left
    calc n * f * n⁻¹ = n * f * n⁻¹ * f⁻¹ * f := by group
      _ = 1 * f := by rw [h1]
      _ = f := by group
  · right
    calc n * f * n⁻¹ = n * f * n⁻¹ * f⁻¹ * f := by group
      _ = (x₁ * x₂) ^ 2 * f := by rw [h1]
      _ = f * (x₁ * x₂) ^ 2 := CFSG.Open.IsElemAbelian.comm hFe hzF hfF

private theorem q13b_F_cent_V_aux_inv (h : Q13Om t L S x₁ x₂ lam rho tau om) {f n : G}
    (hn : n ∈ ctxU t tau x₁ x₂ lam)
    (hc : n * f * n⁻¹ = f ∨ n * f * n⁻¹ = f * (x₁ * x₂) ^ 2) :
    n⁻¹ * f * n = f ∨ n⁻¹ * f * n = f * (x₁ * x₂) ^ 2 := by
  have hz2 := (q13b_z_facts h).2
  have hzn : n⁻¹ * (x₁ * x₂) ^ 2 * n = (x₁ * x₂) ^ 2 := by
    have hx' := q13b_F_cent_V_aux_zconj h (Subgroup.mem_zpowers ((x₁ * x₂) ^ 2))
      (Subgroup.inv_mem (ctxU t tau x₁ x₂ lam) hn)
    rwa [inv_inv] at hx'
  rcases hc with hc | hc
  · left
    calc n⁻¹ * f * n = n⁻¹ * (n * f * n⁻¹) * n := by rw [hc]
      _ = f := by group
  · right
    have h3 : (n⁻¹ * f * n) * (x₁ * x₂) ^ 2 = f := by
      calc (n⁻¹ * f * n) * (x₁ * x₂) ^ 2
          = n⁻¹ * f * n * (n⁻¹ * (x₁ * x₂) ^ 2 * n) := by rw [hzn]
        _ = n⁻¹ * (f * (x₁ * x₂) ^ 2) * n := by group
        _ = n⁻¹ * (n * f * n⁻¹) * n := by rw [hc]
        _ = f := by group
    calc n⁻¹ * f * n
        = (n⁻¹ * f * n) * ((x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2) := by rw [hz2, mul_one]
      _ = ((n⁻¹ * f * n) * (x₁ * x₂) ^ 2) * (x₁ * x₂) ^ 2 := by group
      _ = f * (x₁ * x₂) ^ 2 := by rw [h3]

private theorem q13b_F_cent_V_aux_Kinv (h : Q13Om t L S x₁ x₂ lam rho tau om) {F : Subgroup G}
    (hF : NormalIn F (ctxU t tau x₁ x₂ lam)) (hFe : CFSG.Open.IsElemAbelian 2 F)
    (hFc : Nat.card F = 4) (hzF : (x₁ * x₂) ^ 2 ∈ F) {f : G} (hfF : f ∈ F) :
    ∀ q ∈ ctxQ t tau x₁ x₂ rho,
      ∀ k ∈ ctxN tau x₁ x₂ ⊓ centralizer ({f} : Set G),
        q * k * q⁻¹ ∈ ctxN tau x₁ x₂ ⊓ centralizer ({f} : Set G) := by
  intro q hq k hk
  have hqU : q ∈ ctxU t tau x₁ x₂ lam := (q13b_Q_normal_U h).1 hq
  have hkN : k ∈ ctxN tau x₁ x₂ := hk.1
  have hkU : k ∈ ctxU t tau x₁ x₂ lam := q13b_O_le_U h (q13b_N_le_O h hkN)
  have hkf : k * f = f * k := Subgroup.mem_centralizer_singleton_iff.mp hk.2
  have hkz : k * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * k :=
    q13b_z_central h (q13b_isPGroup_U h) le_rfl k hkU
  have hqN : q * k * q⁻¹ ∈ ctxN tau x₁ x₂ := (q13b_N_normal_U h).2 q hqU k hkN
  have hc := q13b_F_cent_V_aux_cases h hF hFe hFc hzF hfF q hqU
  have hc' := q13b_F_cent_V_aux_inv h hqU hc
  have hkc : k * (q⁻¹ * f * q) = (q⁻¹ * f * q) * k := by
    rcases hc' with hc' | hc'
    · rw [hc']; exact hkf
    · rw [hc']
      calc k * (f * (x₁ * x₂) ^ 2) = (k * f) * (x₁ * x₂) ^ 2 := by group
        _ = (f * k) * (x₁ * x₂) ^ 2 := by rw [hkf]
        _ = f * (k * (x₁ * x₂) ^ 2) := by group
        _ = f * ((x₁ * x₂) ^ 2 * k) := by rw [hkz]
        _ = (f * (x₁ * x₂) ^ 2) * k := by group
  have hfeq : f = q * (q⁻¹ * f * q) * q⁻¹ := by group
  refine ⟨hqN, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have hstep1 : (q * k * q⁻¹) * (q * (q⁻¹ * f * q) * q⁻¹)
      = q * (k * (q⁻¹ * f * q)) * q⁻¹ := by group
  have hstep2 : q * (k * (q⁻¹ * f * q)) * q⁻¹
      = q * ((q⁻¹ * f * q) * k) * q⁻¹ := by rw [hkc]
  have hstep3 : q * ((q⁻¹ * f * q) * k) * q⁻¹
      = (q * (q⁻¹ * f * q) * q⁻¹) * (q * k * q⁻¹) := by group
  calc (q * k * q⁻¹) * f
      = (q * k * q⁻¹) * (q * (q⁻¹ * f * q) * q⁻¹) := by conv_lhs => rw [hfeq]
    _ = q * (k * (q⁻¹ * f * q)) * q⁻¹ := hstep1
    _ = q * ((q⁻¹ * f * q) * k) * q⁻¹ := hstep2
    _ = (q * (q⁻¹ * f * q) * q⁻¹) * (q * k * q⁻¹) := hstep3
    _ = f * (q * k * q⁻¹) := by conv_rhs => rw [hfeq]

theorem q13b_F_cent_V (h : Q13Om t L S x₁ x₂ lam rho tau om) {F : Subgroup G}
    (hF : NormalIn F (ctxU t tau x₁ x₂ lam)) (hFe : CFSG.Open.IsElemAbelian 2 F)
    (hFc : Nat.card F = 4) : ∀ f ∈ F, ∀ v ∈ fourGrp x₁ x₂, f * v = v * f := by
  intro f hfF v hv
  have hFne : F ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card F = 1 := by rw [hbot, Subgroup.card_bot]
    omega
  have hzF : (x₁ * x₂) ^ 2 ∈ F :=
    q13b_z_mem_of_normal h (q13b_isPGroup_U h) le_rfl hF hFne
  set K : Subgroup G := ctxN tau x₁ x₂ ⊓ centralizer ({f} : Set G) with hKdef
  have hcases := q13b_F_cent_V_aux_cases h hF hFe hFc hzF hfF
  have hNle : Nat.card (ctxN tau x₁ x₂) ≤ 2 * Nat.card K := by
    rw [hKdef]
    exact q13b_card_le_two_mul (H := ctxN tau x₁ x₂) (f := f) (z := (x₁ * x₂) ^ 2)
      (fun n hn => hcases n (q13b_O_le_U h (q13b_N_le_O h hn)))
  have hKcard : 4 ≤ Nat.card K := by
    rw [q13b_card_N h] at hNle
    omega
  have hKinv : ∀ q ∈ ctxQ t tau x₁ x₂ rho, ∀ k ∈ K, q * k * q⁻¹ ∈ K := by
    rw [hKdef]
    exact q13b_F_cent_V_aux_Kinv h hF hFe hFc hzF hfF
  have hVK : fourGrp x₁ x₂ ≤ K := by
    rcases q13b_inv_sub_N h (K := K) (by rw [hKdef]; exact inf_le_left) hKinv with hKV | hNK
    · have hV4 : Nat.card (fourGrp x₁ x₂) = 4 := (h.c11.wreath.fourGrp_eq_omega).2.2
      have hEq : K = fourGrp x₁ x₂ :=
        Subgroup.eq_of_le_of_card_ge hKV (by rw [hV4]; exact hKcard)
      rw [hEq]
    · exact (q13b_V_le_N h).trans (by rw [hKdef]; exact hNK)
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hVK hv).2).symm

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
