module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13KQ16

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem c13K_O_le_U_le_M (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    ctxO t tau x₁ x₂ ≤ ctxU t tau x₁ x₂ lam ∧ ctxU t tau x₁ x₂ lam ≤ ctxM t tau x₁ x₂ :=
  ⟨le_sup_left, hc.U_sylow.1⟩

theorem c13K_Q_B_le_O (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    ctxQ t tau x₁ x₂ rho ≤ ctxO t tau x₁ x₂ ∧
      ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G) ≤ ctxO t tau x₁ x₂ := by
  have hQR : ctxQ t tau x₁ x₂ rho ≤ ctxR t tau x₁ x₂ := by
    rw [hc.R_eq]; exact le_sup_left
  have hQO : ctxQ t tau x₁ x₂ rho ≤ ctxO t tau x₁ x₂ := hQR.trans hc.R_le_O
  refine ⟨hQO, sup_le hQO ((Subgroup.closure_le _).mpr ?_)⟩
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with h | h
  · rw [h]
    refine hc.R_le_O ?_
    rw [(c13K_lemma4_12a hc).2.2.2.2.1]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  · rw [h]
    have hom : om ∈ ctxCO t tau x₁ x₂ rho := hc.om_mem
    exact hom.1

theorem c13K_card_U (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(ctxU t tau x₁ x₂ lam) = 2 ^ 10 := by
  rw [card_eq_of_isSylowIn hc.U_sylow, hc.card_M]
  have h2 : (3 * 2 ^ 10 : ℕ).factorization 2 = 10 := by
    rw [Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    simp
  rw [h2]

theorem c13K_card_B (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G)) = 2 ^ 8 := by
  obtain ⟨-, -, hom2, htau2, htau1, -, htauom, -⟩ := c13K_rel hc
  have hom2' : om * om = 1 := by rw [← pow_two]; exact hom2
  have htau2' : tau * tau = 1 := by rw [← pow_two]; exact htau2
  have hom1 : om ≠ 1 := by
    intro h
    exact hc.om_not_mem (by rw [h]; exact one_mem _)
  have hne : tau ≠ om := by
    intro h
    exact hc.om_not_mem (by
      rw [← h]
      exact Subgroup.subset_closure (by simp))
  have hK4 : Nat.card ↥(closure ({tau, om} : Set G)) = 4 :=
    c13K_card_closure_pair htau2' hom2' htauom htau1 hom1 hne
  have hnorm : ∀ k ∈ closure ({tau, om} : Set G), ∀ h ∈ ctxQ t tau x₁ x₂ rho,
      k * h * k⁻¹ ∈ ctxQ t tau x₁ x₂ rho := fun k hk h hh =>
    c13K_normal_Q_QQ hc k (Subgroup.mem_sup_right hk) h hh
  have hinf : ctxQ t tau x₁ x₂ rho ⊓ closure ({tau, om} : Set G) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hxQ, hxK⟩
    rcases c13K_mem_closure_pair htau2' hom2' htauom hxK with h | h | h | h
    · exact h
    · exact absurd (h ▸ hxQ) (c13K_not_mem_Q hc).2.1
    · exact absurd (h ▸ hxQ) (c13K_om_not_mem_Q hc)
    · rw [htauom] at h
      exact absurd (h ▸ hxQ) (c13K_omtau_not_mem_Q hc)
  rw [card_sup_eq_mul hnorm hinf, hK4, (c13K_lemma4_12a hc).2.2.2.1]
  norm_num

theorem c13K_B_eq_cent (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    ctxU t tau x₁ x₂ lam ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) =
      ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G) := by
  have hUM := (c13K_O_le_U_le_M hc).2
  have hBU : ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G) ≤ ctxU t tau x₁ x₂ lam :=
    (c13K_Q_B_le_O hc).2.trans (c13K_O_le_U_le_M hc).1
  apply le_antisymm
  · intro x hx
    have h2 : x ∈ ctxM t tau x₁ x₂ ⊓
        centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) := ⟨hUM hx.1, hx.2⟩
    rwa [hc.cent_M_Y] at h2
  · intro x hx
    have h2 : x ∈ ctxM t tau x₁ x₂ ⊓
        centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) := by
      rwa [hc.cent_M_Y]
    exact ⟨hBU hx, h2.2⟩

theorem c13K_B_normal_U (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    ∀ u ∈ ctxU t tau x₁ x₂ lam, ∀ b ∈ ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G),
      u * b * u⁻¹ ∈ ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G) := by
  intro u hu b hb
  have huM : u ∈ ctxM t tau x₁ x₂ := (c13K_O_le_U_le_M hc).2 hu
  have hb' : b ∈ ctxM t tau x₁ x₂ ⊓
      centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) := by
    rwa [hc.cent_M_Y]
  rw [← hc.cent_M_Y]
  refine ⟨(ctxM t tau x₁ x₂).mul_mem ((ctxM t tau x₁ x₂).mul_mem huM hb'.1)
    ((ctxM t tau x₁ x₂).inv_mem huM), Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  have hy' : u⁻¹ * y * u ∈ ctxYq t tau x₁ x₂ rho := by
    have h := hc.normal_Y.2 u⁻¹ ((ctxM t tau x₁ x₂).inv_mem huM) y hy
    simpa using h
  have hcomm : (u⁻¹ * y * u) * b = b * (u⁻¹ * y * u) :=
    Subgroup.mem_centralizer_iff.mp hb'.2 _ hy'
  calc y * (u * b * u⁻¹) = u * ((u⁻¹ * y * u) * b) * u⁻¹ := by group
    _ = u * (b * (u⁻¹ * y * u)) * u⁻¹ := by rw [hcomm]
    _ = u * b * u⁻¹ * y := by group

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
