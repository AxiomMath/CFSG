module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b4a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b4b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b2c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private theorem q13b_aux_zconj (h : Q13Om t L S x₁ x₂ lam rho tau om) {x n : G}
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

theorem q13b_F_le_N (h : Q13Om t L S x₁ x₂ lam rho tau om) {F : Subgroup G}
    (hF : NormalIn F (ctxU t tau x₁ x₂ lam)) (hFe : CFSG.Open.IsElemAbelian 2 F)
    (hFc : Nat.card F = 4) : F ≤ ctxN tau x₁ x₂ := by
  classical
  have hFne : F ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card F = 1 := by rw [hbot, Subgroup.card_bot]
    omega
  obtain ⟨hz1, hz2⟩ := q13b_z_facts h
  have hzF : (x₁ * x₂) ^ 2 ∈ F :=
    q13b_z_mem_of_normal h (q13b_isPGroup_U h) le_rfl hF hFne
  have hle : zpowers ((x₁ * x₂) ^ 2) ≤ F := Subgroup.zpowers_le.mpr hzF
  have hcard0 : Nat.card (zpowers ((x₁ * x₂) ^ 2)) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (p := 2) (by simpa [pow_two] using hz2) hz1
  have hcard : Nat.card F = 2 * Nat.card (zpowers ((x₁ * x₂) ^ 2)) := by
    rw [hFc, hcard0]
  have hV : zpowers ((x₁ * x₂) ^ 2) ≤ fourGrp x₁ x₂ :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have htU : t ∈ ctxU t tau x₁ x₂ lam := q13b_O_le_U h (q13b_t_mem_O h)
  have homU : om ∈ ctxU t tau x₁ x₂ lam := q13b_O_le_U h (q13b_om_mem_O h)
  intro f hf
  have hfU : f ∈ ctxU t tau x₁ x₂ lam := hF.1 hf
  have hcent : ∀ v ∈ fourGrp x₁ x₂, f * v = v * f :=
    q13b_F_cent_V h hF hFe hFc f hf
  have hfO : f ∈ ctxO t tau x₁ x₂ := q13b_cent_V_le_O h hfU hcent
  have hf2 : f * f = 1 := CFSG.Open.IsElemAbelian.mul_self_eq_one hFe hf
  have ha : t * f * t⁻¹ * f⁻¹ ∈ fourGrp x₁ x₂ := by
    have hres := q13b_comm_mem_of_index_two (F := F)
      (F₀ := zpowers ((x₁ * x₂) ^ 2)) hle hcard
      (fun x hx => hF.2 t htU x hx)
      (fun x hx => by rw [q13b_aux_zconj h hx htU]; exact hx)
      (fun x hx => by
        have hx' : t⁻¹ * x * t = x := by
          have := q13b_aux_zconj h hx (Subgroup.inv_mem (ctxU t tau x₁ x₂ lam) htU)
          simpa using this
        rw [hx']; exact hx) f hf
    exact hV hres
  have hb : om * f * om⁻¹ * f⁻¹ ∈ fourGrp x₁ x₂ := by
    have hres := q13b_comm_mem_of_index_two (F := F)
      (F₀ := zpowers ((x₁ * x₂) ^ 2)) hle hcard
      (fun x hx => hF.2 om homU x hx)
      (fun x hx => by rw [q13b_aux_zconj h hx homU]; exact hx)
      (fun x hx => by
        have hx' : om⁻¹ * x * om = x := by
          have := q13b_aux_zconj h hx (Subgroup.inv_mem (ctxU t tau x₁ x₂ lam) homU)
          simpa using this
        rw [hx']; exact hx) f hf
    exact hV hres
  exact q13b_core h hfO hf2 ha hb

theorem q13b_V_unique (h : Q13Om t L S x₁ x₂ lam rho tau om) {𝒮 F : Subgroup G}
    (h𝒮 : IsPGroup 2 𝒮) (hU : ctxU t tau x₁ x₂ lam ≤ 𝒮) (hF : NormalIn F 𝒮)
    (hFe : CFSG.Open.IsElemAbelian 2 F) (hFc : Nat.card F = 4) :
    F = fourGrp x₁ x₂ := by
  classical
  have hFU : F ≤ ctxU t tau x₁ x₂ lam := q13b_F_le_U h h𝒮 hU hF hFe hFc
  have hFUn : NormalIn F (ctxU t tau x₁ x₂ lam) :=
    ⟨hFU, fun g hg k hk => hF.2 g (hU hg) k hk⟩
  have hFN : F ≤ ctxN tau x₁ x₂ := q13b_F_le_N h hFUn hFe hFc
  have hFinv : ∀ q ∈ ctxQ t tau x₁ x₂ rho, ∀ k ∈ F, q * k * q⁻¹ ∈ F := by
    intro q hq k hk
    exact hF.2 q (hU ((q13b_Q_normal_U h).1 hq)) k hk
  rcases q13b_inv_sub_N h hFN hFinv with hFV | hNF
  · have hV4 : Nat.card (fourGrp x₁ x₂) = 4 := (h.c11.wreath.fourGrp_eq_omega).2.2
    exact Subgroup.eq_of_le_of_card_ge hFV (by rw [hV4, hFc])
  · exfalso
    have h8 : Nat.card (ctxN tau x₁ x₂) ≤ Nat.card F := Subgroup.card_le_of_le hNF
    rw [q13b_card_N h, hFc] at h8
    omega

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
