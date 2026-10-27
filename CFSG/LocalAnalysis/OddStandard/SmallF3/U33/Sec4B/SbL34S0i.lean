module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0f2

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open scoped Pointwise
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem conj_mem_closure {S : Set G} {g : G} (h : ∀ s ∈ S, g * s * g⁻¹ ∈ closure S) :
    ∀ k ∈ closure S, g * k * g⁻¹ ∈ closure S := by
  intro k hk
  induction hk using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => simp
  | mul x y _ _ ihx ihy =>
      rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
      exact mul_mem ihx ihy
  | inv x _ ih =>
      rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
      exact inv_mem ih

section Base

variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau)
include hc

theorem V_le_base : fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := by
  have hx₁ : x₁ ∈ baseGrp x₁ x₂ := subset_closure (by simp)
  have hx₂ : x₂ ∈ baseGrp x₁ x₂ := subset_closure (by simp)
  rw [fourGrp, closure_le]
  rintro _ (rfl | rfl)
  · exact pow_mem hx₁ 2
  · exact pow_mem (mul_mem hx₁ hx₂) 2

theorem base_le_U : baseGrp x₁ x₂ ≤ ctxU t tau x₁ x₂ lam :=
  (hc.base_le_Q.trans hc.Q_le_O).trans (O_le_U hc)

theorem Q_norm_base {q k : G} (hq : q ∈ ctxQ t tau x₁ x₂ rho) (hk : k ∈ baseGrp x₁ x₂) :
    q * k * q⁻¹ ∈ baseGrp x₁ x₂ := by
  have hkQ : k ∈ ctxQ t tau x₁ x₂ rho := hc.base_le_Q hk
  have h := V_le_base hc (hc.Q_quot.2 q hq k hkQ)
  have : q * k * q⁻¹ = (q * k * q⁻¹ * k⁻¹) * k := by group
  rw [this]
  exact mul_mem h hk

theorem t_comm_base {k : G} (hk : k ∈ baseGrp x₁ x₂) : t * k * t⁻¹ = k := by
  have hx₁L : x₁ ∈ L := by
    have h : x₁ ∈ S ⊓ L := by rw [hc.inf_eq]; exact subset_closure (by simp)
    exact h.2
  have hx₂L : x₂ ∈ L := by
    have h : x₂ ∈ S ⊓ L := by rw [hc.inf_eq]; exact subset_closure (by simp)
    exact h.2
  have hle : baseGrp x₁ x₂ ≤ L := by
    rw [baseGrp, closure_le]
    rintro _ (rfl | rfl)
    · exact hx₁L
    · exact hx₂L
  have hcomm : t * k = k * t :=
    (mem_centralizer_iff.mp hc.hyp.mem_centralizer k (hle hk)).symm
  rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

theorem tau_norm_base {k : G} (hk : k ∈ baseGrp x₁ x₂) : tau * k * tau⁻¹ ∈ baseGrp x₁ x₂ := by
  refine conj_mem_closure (S := ({x₁, x₂} : Set G)) ?_ k hk
  rintro s (rfl | rfl)
  · rw [hc.tau_x₁]; exact inv_mem (subset_closure (by simp))
  · rw [hc.tau_x₂]; exact inv_mem (subset_closure (by simp))

theorem lam_norm_base {k : G} (hk : k ∈ baseGrp x₁ x₂) : lam * k * lam⁻¹ ∈ baseGrp x₁ x₂ := by
  have hlam : lam⁻¹ = lam := inv_eq_of_mul_eq_one_right (lam_mul_self hc)
  have h₂ : lam * x₂ * lam⁻¹ = x₁ := by
    have h := hc.wreath.conj_x₁
    calc lam * x₂ * lam⁻¹ = lam * (lam * x₁ * lam⁻¹) * lam⁻¹ := by rw [h]
      _ = (lam * lam) * x₁ * (lam⁻¹ * lam⁻¹) := by group
      _ = x₁ := by rw [lam_mul_self hc, hlam, lam_mul_self hc]; group
  refine conj_mem_closure (S := ({x₁, x₂} : Set G)) ?_ k hk
  rintro s (rfl | rfl)
  · rw [hc.wreath.conj_x₁]; exact subset_closure (by simp)
  · rw [h₂]; exact subset_closure (by simp)

theorem O_le_normalizer_base :
    ctxO t tau x₁ x₂ ≤ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
  rw [hc.O_eq_Q]
  refine sup_le ?_ ?_
  · intro q hq
    exact Subgroup.mem_normalizer_fintype (fun k hk => Q_norm_base hc hq hk)
  · rw [closure_le]
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · refine Subgroup.mem_normalizer_fintype (fun k hk => ?_)
      rw [t_comm_base hc hk]; exact hk
    · exact Subgroup.mem_normalizer_fintype (fun k hk => tau_norm_base hc hk)

theorem normal_base_U : NormalIn (baseGrp x₁ x₂) (ctxU t tau x₁ x₂ lam) := by
  refine ⟨base_le_U hc, fun g hg k hk => ?_⟩
  have hU : ctxU t tau x₁ x₂ lam ≤ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
    refine sup_le (O_le_normalizer_base hc) ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_normalizer_fintype (fun k hk => lam_norm_base hc hk)
  exact (Subgroup.mem_normalizer_iff.mp (hU hg) k).mp hk

end Base

section Sylow

variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau)
include hc

theorem U_not_sylow_top (hG : Sec4Glob G) :
    ¬ IsSylowIn 2 (ctxU t tau x₁ x₂ lam) (⊤ : Subgroup G) := by
  intro hsyl
  have h1 := S4B.card_eq_of_isSylowIn hsyl
  rw [card_U hc, Subgroup.card_top] at h1
  have h2 : 11 ≤ (Nat.card G).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hG.dvd
  have h3 : (Nat.card G).factorization 2 = 9 :=
    (Nat.pow_right_injective (le_refl 2) h1).symm
  omega

theorem O_eq_U_inf_centralizer : ctxO t tau x₁ x₂ =
    ctxU t tau x₁ x₂ lam ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
  apply le_antisymm
  · intro a ha
    refine ⟨O_le_U hc ha, ?_⟩
    have ha' : a ∈ ctxM t tau x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
      rw [← hc.O_eq_CV]; exact ha
    exact ha'.2
  · intro a ha
    rw [hc.O_eq_CV]
    exact ⟨U_le_M hc ha.1, ha.2⟩

end Sylow

section Char

variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau) (hs : IsSylSL34 (ctxQ t tau x₁ x₂ rho))
include hc hs

theorem char_O : CharIn (ctxO t tau x₁ x₂) (ctxU t tau x₁ x₂ lam) := by
  rw [O_eq_U_inf_centralizer hc]
  exact charIn_inf_centralizer (char_V hc hs)

end Char

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
