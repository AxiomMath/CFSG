module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43L3E8CaseC
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf46OneOne

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

@[expose] def L3E8TwoFactors {T : Type} [Group T] (K : Subgroup T) : Prop :=
  ∃ m₀ ∈ sigmaNorm K, conjSub m₀ (firstFactor K) ≠ firstFactor K ∧
    ∀ n ∈ sigmaNorm K, conjSub n (firstFactor K) = firstFactor K ∨
      conjSub n (firstFactor K) = conjSub m₀ (firstFactor K)

namespace L3E8Cfg

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {H Q E S : Subgroup T}

theorem mul_commutator_mem_of_other_factors (cfg : L3E8Cfg K z J zJ H Q E S) {m₁ m₂ n : T}
    (hm₁ : m₁ ∈ sigmaNorm K) (hm₂ : m₂ ∈ sigmaNorm K) (hn : n ∈ sigmaNorm K)
    (hne₁ : conjSub m₁ (firstFactor K) ≠ conjSub n (firstFactor K))
    (hne₂ : conjSub m₂ (firstFactor K) ≠ conjSub n (firstFactor K)) {x y : T}
    (hx : x ∈ conjSub m₁ (firstFactor K)) (hy : y ∈ conjSub m₂ (firstFactor K)) {w : T}
    (hw : w ∈ conjSub n (firstFactor K)) :
    x * y * w * (x * y)⁻¹ * w⁻¹ ∈ oddCoreOf (sigmaGen K) := by
  have h₁ := cfg.factor_comm hm₁ hn hne₁ hx hw
  have h₂ := Asc77.mem_normalizer_oddCoreOf_of_mem_normalizer
    (Subgroup.le_normalizer (cfg.conjSub_firstFactor_le hm₁ hx))
    (cfg.factor_comm hm₂ hn hne₂ hy hw)
  rw [show x * y * w * (x * y)⁻¹ * w⁻¹ =
    x * (y * w * y⁻¹ * w⁻¹) * x⁻¹ * (x * w * x⁻¹ * w⁻¹) by group]
  exact (oddCoreOf (sigmaGen K)).mul_mem h₂ h₁

theorem cent_le_of_third_factor [CaseIAmbient T] (cfg : L3E8Cfg K z J zJ H Q E S)
    {m₁ m₂ n : T} (hm₁ : m₁ ∈ sigmaNorm K) (hm₂ : m₂ ∈ sigmaNorm K) (hn : n ∈ sigmaNorm K)
    (hne₁ : conjSub m₁ (firstFactor K) ≠ conjSub n (firstFactor K))
    (hne₂ : conjSub m₂ (firstFactor K) ≠ conjSub n (firstFactor K)) {x y : T}
    (hx : x ∈ conjSub m₁ (firstFactor K)) (hy : y ∈ conjSub m₂ (firstFactor K))
    (h2 : IsPGroup 2 (Subgroup.zpowers (x * y))) (h1 : x * y ≠ 1) :
    Subgroup.centralizer ({x * y} : Set T) ≤ sigmaNorm K :=
  cfg.toFrameCfg.cent_le_of_factor hn h2 h1
    (cfg.sigmaGen_le_normalizer_conjSub_firstFactor hn ((sigmaGen K).mul_mem
      (cfg.conjSub_firstFactor_le hm₁ hx) (cfg.conjSub_firstFactor_le hm₂ hy)))
    fun _ hw => cfg.mul_commutator_mem_of_other_factors hm₁ hm₂ hn hne₁ hne₂ hx hy hw

theorem cent_le_of_not_twoFactors [CaseIAmbient T] (cfg : L3E8Cfg K z J zJ H Q E S)
    (h : ¬ L3E8TwoFactors K) : L3E8CentLe K z := by
  rintro _ ⟨g, hne, hc, hnot, rfl⟩
  have hz := cfg.datum.unique
  have hzHt : z ∈ firstFactor K := cfg.Q_le_ht (cfg.E_le_Q cfg.z_mem_E)
  have h1Ht : conjSub (1 : T) (firstFactor K) = firstFactor K :=
    conjSub_eq_self_of_mem (Subgroup.one_mem _)
  have hgM : g⁻¹ ∈ sigmaNorm K :=
    (sigmaNorm K).inv_mem (cfg.zconj_cent (Subgroup.mem_centralizer_singleton_iff.mpr hc.symm))
  have hw : g⁻¹ * z * g ∈ conjSub g⁻¹ (firstFactor K) := by
    simpa using conj_mem_conjSub (n := g⁻¹) hzHt
  have hF : conjSub g⁻¹ (firstFactor K) ≠ firstFactor K := fun e => hnot (e ▸ hw)
  obtain ⟨n, hn, hn₁, hn₂⟩ : ∃ n ∈ sigmaNorm K, conjSub n (firstFactor K) ≠ firstFactor K ∧
      conjSub n (firstFactor K) ≠ conjSub g⁻¹ (firstFactor K) := by
    by_contra hcon
    refine h ⟨g⁻¹, hgM, hF, fun n hn => ?_⟩
    by_contra hor
    exact hcon ⟨n, hn, fun e => hor (Or.inl e), fun e => hor (Or.inr e)⟩
  have hw2 : g⁻¹ * z * g * (g⁻¹ * z * g) = 1 := by
    calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hz.sq]; group
  have ha2 : z * (g⁻¹ * z * g) * (z * (g⁻¹ * z * g)) = 1 := by
    calc z * (g⁻¹ * z * g) * (z * (g⁻¹ * z * g)) =
          z * (g⁻¹ * z * g * z) * (g⁻¹ * z * g) := by group
      _ = z * (z * (g⁻¹ * z * g)) * (g⁻¹ * z * g) := by rw [hc]
      _ = z * z * (g⁻¹ * z * g * (g⁻¹ * z * g)) := by group
      _ = 1 := by rw [hz.sq, hw2, one_mul]
  have ha1 : z * (g⁻¹ * z * g) ≠ 1 := fun h1 =>
    hne ((eq_inv_of_mul_eq_one_right h1).trans (inv_eq_of_mul_eq_one_right hz.sq))
  have ha : IsPGroup 2 (Subgroup.zpowers (z * (g⁻¹ * z * g))) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1, pow_one])
  exact cfg.cent_le_of_third_factor (Subgroup.one_mem _) hgM hn (by rw [h1Ht]; exact hn₁.symm)
    hn₂.symm (by rw [h1Ht]; exact hzHt) hw ha ha1

theorem cent_le_of_twoFactors_case [CaseIAmbient T] (cfg : L3E8Cfg K z J zJ H Q E S)
    (h2 : L3E8TwoFactors K → L3E8CentLe K z) : L3E8CentLe K z := by
  by_cases h : L3E8TwoFactors K
  · exact h2 h
  · exact cfg.cent_le_of_not_twoFactors h

end L3E8Cfg

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
