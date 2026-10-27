module

public import CFSG.ClassicalInvolution.Asc77.AscIH8Bridge
public import CFSG.ClassicalInvolution.SmallCases.NDB5Sec
public import CFSG.ClassicalInvolution.SmallCases.NDB5dAct

public section

namespace CFSG.ClassicalInvolution.NDB.Alpha

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.ExactLayer
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem lift_eq {s z : G} {Φ : Set (Subgroup G)} {hN : NormalizesLayer Φ s}
    {D : LocalLieSystemAt p f Φ s} {j₀ : Fin D.card}
    (hodd : Odd (Nat.card (GaloisField p (D.exp j₀))))
    (hA1 : ¬ (D.tag j₀ = .PSL ∧ D.rank j₀ = 2))
    (hker : (secComponentHom hN D j₀).ker ≤ Subgroup.center (compModel D j₀).K)
    {R : Subgroup (compModel D j₀).K}
    (hR : R ∈ fundamentalSubgroups (D.tag j₀) (compModel D j₀).D)
    (e : R ≃* SL(2, GaloisField p (D.exp j₀))) {L : Subgroup G}
    (himg : R.map (secComponentHom hN D j₀) = modOdd s L)
    (hzC : z ∈ Subgroup.centralizer ({s} : Set G))
    (hU : IsUniqueInvolution (modOdd s L) (oddQuotMk s ⟨z, hzC⟩)) :
    secComponentHom hN D j₀ (sl2Inv e) = oddQuotMk s ⟨z, hzC⟩ := by
  set ψ := secComponentHom hN D j₀ with hψ
  have hmem : ψ (sl2Inv e) ∈ modOdd s L := himg ▸ ⟨sl2Inv e, sl2Inv_mem e, rfl⟩
  have hsq : ψ (sl2Inv e) * ψ (sl2Inv e) = 1 := by
    rw [← map_mul, sl2Inv_mul_self hodd e, map_one]
  have hne : ψ (sl2Inv e) ≠ 1 := by
    intro h1
    have hc : sl2Inv e ∈ Subgroup.center (compModel D j₀).K := hker (MonoidHom.mem_ker.mpr h1)
    apply sl2Inv_ne_one hodd e
    refine RouteD.Gaps.fundNoncentral p (D.tag j₀) (D.rank j₀) (D.exp j₀) (D.isFundTag j₀)
      (D.admissible j₀) hA1 R hR (sl2Inv e) (sl2Inv_mem e) fun y => ?_
    rw [← Subgroup.mem_center_iff.mp hc y, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  exact (hU.unique _ hmem hsq).resolve_left hne

theorem exists_commuting_lifts (hp2 : p ≠ 2) {s z₁ z₂ : G} {Φ : Set (Subgroup G)}
    {hN : NormalizesLayer Φ s} {D : LocalLieSystemAt p f Φ s} {j₀ : Fin D.card}
    (h5 : 5 ≤ p ^ D.exp j₀) (hG2 : D.tag j₀ ≠ .G2) (hD4 : D.tag j₀ ≠ .trialityD4)
    (hA1 : ¬ (D.tag j₀ = .PSL ∧ D.rank j₀ = 2))
    (hker : (secComponentHom hN D j₀).ker ≤ Subgroup.center (compModel D j₀).K)
    {R₁ R₂ : Subgroup (compModel D j₀).K}
    (hR₁ : R₁ ∈ fundamentalSubgroups (D.tag j₀) (compModel D j₀).D)
    (hR₂ : R₂ ∈ fundamentalSubgroups (D.tag j₀) (compModel D j₀).D) {L₁ L₂ : Subgroup G}
    (himg₁ : R₁.map (secComponentHom hN D j₀) = modOdd s L₁)
    (himg₂ : R₂.map (secComponentHom hN D j₀) = modOdd s L₂)
    (hz₁C : z₁ ∈ Subgroup.centralizer ({s} : Set G))
    (hz₂C : z₂ ∈ Subgroup.centralizer ({s} : Set G))
    (hU₁ : IsUniqueInvolution (modOdd s L₁) (oddQuotMk s ⟨z₁, hz₁C⟩))
    (hU₂ : IsUniqueInvolution (modOdd s L₂) (oddQuotMk s ⟨z₂, hz₂C⟩))
    (hz₂L₁ : conjSub (oddQuotMk s ⟨z₂, hz₂C⟩) (modOdd s L₁) = modOdd s L₁) :
    ∃ x₁ x₂ : (compModel D j₀).K, x₁ * x₁ = 1 ∧ x₂ * x₂ = 1 ∧ x₁ * x₂ = x₂ * x₁ ∧
      secComponentHom hN D j₀ x₁ = oddQuotMk s ⟨z₁, hz₁C⟩ ∧
        secComponentHom hN D j₀ x₂ = oddQuotMk s ⟨z₂, hz₂C⟩ := by
  set ψ := secComponentHom hN D j₀ with hψ
  have hodd : Odd (Nat.card (GaloisField p (D.exp j₀))) := WC.odd_card_galoisField hp2 h5
  obtain ⟨e₁⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (D.isFundTag j₀)
    (D.admissible j₀) hG2 hD4 hR₁
  obtain ⟨e₂⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (D.isFundTag j₀)
    (D.admissible j₀) hG2 hD4 hR₂
  have hx₁ := lift_eq hodd hA1 hker hR₁ e₁ himg₁ hz₁C hU₁
  have hx₂ := lift_eq hodd hA1 hker hR₂ e₂ himg₂ hz₂C hU₂
  have h4 : 4 ≤ p ^ D.exp j₀ := by omega
  have hper : ∀ {R : Subgroup (compModel D j₀).K},
      R ∈ fundamentalSubgroups (D.tag j₀) (compModel D j₀).D → R ≤ ⁅R, R⁆ := fun hR =>
    ModelFacts.fundPerfect_core (D.tag j₀) (D.rank j₀) p (D.exp j₀) hp2 (D.isFundTag j₀)
      (D.admissible j₀) h4 _ hR
  have hconj : conjSub (sl2Inv e₂) R₁ = R₁ := by
    refine RouteD.eq_of_map_eq_of_perfect ψ hker (ih8_perfect_conjSub (hper hR₁) _) (hper hR₁) ?_
    rw [S.map_conjSub, himg₁, hx₂, hz₂L₁]
  have hmem : sl2Inv e₂ * sl2Inv e₁ * (sl2Inv e₂)⁻¹ ∈ R₁ := by
    have h0 : sl2Inv e₂ * sl2Inv e₁ * (sl2Inv e₂)⁻¹ ∈ conjSub (sl2Inv e₂) R₁ :=
      ⟨sl2Inv e₁, sl2Inv_mem e₁, rfl⟩
    rw [hconj] at h0
    exact h0
  have hord : orderOf (sl2Inv e₂ * sl2Inv e₁ * (sl2Inv e₂)⁻¹) = 2 := by
    apply orderOf_eq_prime
    · calc (sl2Inv e₂ * sl2Inv e₁ * (sl2Inv e₂)⁻¹) ^ 2
          = sl2Inv e₂ * (sl2Inv e₁ * sl2Inv e₁) * (sl2Inv e₂)⁻¹ := by rw [sq]; group
        _ = 1 := by rw [sl2Inv_mul_self hodd e₁]; group
    · intro h1
      apply sl2Inv_ne_one hodd e₁
      calc sl2Inv e₁ = (sl2Inv e₂)⁻¹ * (sl2Inv e₂ * sl2Inv e₁ * (sl2Inv e₂)⁻¹) * sl2Inv e₂ := by
            group
        _ = 1 := by rw [h1]; group
  have he := eq_sl2Inv_of_orderOf_eq_two hodd e₁ hmem hord
  refine ⟨sl2Inv e₁, sl2Inv e₂, sl2Inv_mul_self hodd e₁, sl2Inv_mul_self hodd e₂, ?_, hx₁, hx₂⟩
  calc sl2Inv e₁ * sl2Inv e₂ = (sl2Inv e₂ * sl2Inv e₁ * (sl2Inv e₂)⁻¹) * sl2Inv e₂ := by
        rw [he]
    _ = sl2Inv e₂ * sl2Inv e₁ := by group

end CFSG.ClassicalInvolution.NDB.Alpha
