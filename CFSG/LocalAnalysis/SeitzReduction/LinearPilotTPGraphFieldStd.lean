module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTPGraphFieldZT
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTPGraphFieldInner
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTPGraphFieldGraph
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTPGraphFieldOrder

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart linearFieldPart_eq
  exists_standard_form)
open CFSG.Quasithin (perfectCore)

variable {n : ℕ} {K : Type} [Field K] [Finite K]

variable (n K) in
@[expose] def TransvectionIntrinsicStdGraphField : Prop :=
  ∀ σ : K ≃+* K, σ ≠ 1 → (fieldAut n K σ * dualAut n K) ^ 2 = 1 →
    ∀ β : MulAut (projectiveSL n K), β ^ 2 = 1 → β ≠ 1 →
      ∀ (Γ : Type) [Group Γ] [Finite Γ] (φ₁ φ₂ : projectiveSL n K →* Γ),
        Function.Injective φ₁ → Function.Injective φ₂ →
          (perfectCore (autFixSubgroup (fieldAut n K σ * dualAut n K))).map φ₁ =
            (perfectCore (autFixSubgroup β)).map φ₂ →
          ∀ y ∈ perfectCore (autFixSubgroup (fieldAut n K σ * dualAut n K)),
            IsInvolutionClass 1 y →
              ∃ z : projectiveSL n K, IsInvolutionClass 1 z ∧ φ₂ z = φ₁ y

theorem transvectionIntrinsicStdGraphField {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n) :
    TransvectionIntrinsicStdGraphField n K := by
  intro σ hσ1 hσ2 β hβ2 hβ1 Γ _ _ φ₁ φ₂ hφ₁ hφ₂ hXY y hy hyt
  have hn3 : 3 ≤ n := by omega
  have : CharP K 2 := charP_two_of_card_eq_two_pow hK
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h1
    · have h1 := Finite.one_lt_card (α := K)
      rw [hK, h0, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact h1
  obtain ⟨e, h, hfe, hσbar⟩ := exists_unitaryFieldData_of_graphField hK hn3 hσ1 hσ2
  have he1 : 1 ≤ e := h.one_le
  have hnq : (n, 2 ^ e) ≠ (3, 2) := fun h0 => by
    have h1 := congrArg Prod.fst h0
    simp only at h1
    omega
  set X := perfectCore (autFixSubgroup (fieldAut n K σ * dualAut n K)) with hX
  have hXs : IsSimpleGroup X := isSimpleGroup_perfectCore_graphField h hn3 hnq σ hσbar
  have hXnc := not_forall_mul_comm_perfectCore_graphField h hn3 hnq σ hσbar
  have hXsyl : HasSylowCard n K X (2 ^ e) := fun S =>
    card_sylow_perfectCore_graphField h hn3 hnq σ hσbar S
  have hc2 : (2 ^ e) ^ 2 = Nat.card K := by rw [hK, hfe, ← pow_mul, mul_comm]
  have hc1 : 1 < 2 ^ e := Nat.one_lt_two_pow (by omega)
  have hq : 4 ≤ Nat.card K := by
    rw [← hc2]
    nlinarith
  obtain ⟨τ, A, η, hη, rfl⟩ := exists_standard_form K n hn3 β
  rcases (by omega : η = 0 ∨ η = 1) with rfl | rfl
  · rw [pow_zero, mul_one] at hβ2 hβ1 hXY
    by_cases hτ : τ = 1
    ·
      subst hτ
      rw [map_one, mul_one] at hβ2 hβ1 hXY
      exact absurd hXY (map_ne_perfectCore_conjAut_of_isSimpleGroup hq hn hXs A hβ2 hβ1 hφ₁ hφ₂)
    ·
      have hτ2 : τ ^ 2 = 1 := by
        have h1 := congrArg (linearFieldPart K hn3) hβ2
        rwa [map_pow, map_one, show conjAut n K A * fieldAut n K τ =
          conjAut n K A * fieldAut n K τ * dualAut n K ^ 0 by rw [pow_zero, mul_one],
          linearFieldPart_eq hn3 (Nat.zero_le 1)] at h1
      obtain ⟨-, -, H, hH⟩ := even_linear_field_involution_descent hf hK hn3 A τ hτ hβ2
      rw [hH, perfectCore_autFixSubgroup_conj, Subgroup.map_map] at hXY
      exact absurd hXY.symm (fieldCoreNeGraphFieldCore hK hn3 τ σ hτ hτ2 hσ1 hσ2 Γ
        (φ₂.comp (conjAut n K H).toMonoidHom) φ₁ (hφ₂.comp (conjAut n K H).injective) hφ₁)
  · rw [pow_one] at hβ2 hXY
    by_cases hτ : τ = 1
    ·
      subst hτ
      rw [map_one, mul_one] at hβ2 hXY
      exact absurd hXY
        (map_ne_perfectCore_graph_of_sylow hK hn hc2 hc1 hXsyl hXs hXnc A hβ2 hφ₁ hφ₂)
    ·
      obtain ⟨-, hτx, H, hH⟩ :=
        UnitaryHigher.linear_graph_field_involution_descent Nat.prime_two hf hK hn3 A τ hτ hβ2
      have hτσ : τ = σ := RingEquiv.ext fun x => by
        rw [hτx, hσbar, UnitaryFieldData.bar_apply, show f / 2 = e by omega]
      subst hτσ
      rw [hH, perfectCore_autFixSubgroup_conj] at hXY
      have hZT := (twoCentralTransvection_perfectCore_graphField h hn3 hnq τ hσbar).map_conjAut H
      exact exists_isInvolutionClass_one_of_map_eq hφ₁ hφ₂ hXY hZT hy (hyt.ne_one one_ne_zero)
        (centralizesSylow_perfectCore_graphField h hn3 hnq τ hσbar hy hyt)

theorem transvectionIntrinsicStd {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n) :
    TransvectionIntrinsicStd n K :=
  transvectionIntrinsicStd_of_field (transvectionIntrinsicStdField hK hn)
    (transvectionIntrinsicStdGraphField hK hn)

end CFSG.SeitzReduction.LinearPilot
