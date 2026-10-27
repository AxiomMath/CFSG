module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S4a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S4b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S4c1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S2s

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem false_of_normal_Q (ha : Ctx4P t L S x₁ x₂ lam rho tau)
    (hQn : NormalIn (ctxQ t tau x₁ x₂ rho) (ctxLO t tau x₁ x₂)) : False := by
  have hA := ha.toCtx4A
  have hl := ha.toCtx4L
  have hc := hl.toCtx4Q
  have hs : IsSylSL34 (ctxQ t tau x₁ x₂ rho) := isSylSL34_of_Ctx4L hl
  have hPL : ctxPL t tau x₁ x₂ ≤ ctxLO t tau x₁ x₂ := inf_le_left
  have hPQ : ∀ p ∈ ctxPL t tau x₁ x₂, ∀ x ∈ ctxQ t tau x₁ x₂ rho,
      p * x * p⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    fun p hp x hx => hQn.2 p (hPL hp) x hx
  have hfix : ∀ p ∈ ctxPL t tau x₁ x₂,
      ∀ z ∈ ctxQ t tau x₁ x₂ rho ⊓
        centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G),
      p * z * p⁻¹ = z := by
    intro p hp z hz
    have hzV : z ∈ fourGrp x₁ x₂ := by
      rw [← hl.Z_Q]
      exact hz
    have hpC : p ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) :=
      (Subgroup.mem_inf.mp hp).2
    have hcomm : z * p = p * z := Subgroup.mem_centralizer_iff.mp hpC z hzV
    rw [← hcomm]
    group
  have hP : IsPGroup 2 ↥(ctxPL t tau x₁ x₂) := IsPGroup.of_card ha.card_P
  obtain ⟨R, hRP, hRidx, hR⟩ :=
    exists_stab_subgroup (ctxQ t tau x₁ x₂ rho) (ctxPL t tau x₁ x₂) hs hP hPQ hfix
  have hRO : R ≤ ctxO t tau x₁ x₂ := by
    intro r hr
    have hrP : r ∈ ctxPL t tau x₁ x₂ := hRP hr
    have hrL : r ∈ ctxLO t tau x₁ x₂ := hPL hrP
    apply hA.CL_Obar r hrL
    intro o ho
    have hoL : o ∈ ctxLO t tau x₁ x₂ := Subgroup.le_normalizer ho
    have hcommQ : ∀ q ∈ ctxQ t tau x₁ x₂ rho,
        (r * o * r⁻¹ * o⁻¹) * q = q * (r * o * r⁻¹ * o⁻¹) := by
      intro q hq
      have h := comm_cent_of_stab (ctxQ t tau x₁ x₂ rho) r⁻¹ o⁻¹
        (fun z hz => hfix r⁻¹ (hRP (R.inv_mem hr)) z hz)
        (fun z hz => by
          have hzV : z ∈ fourGrp x₁ x₂ := by
            rw [← hl.Z_Q]
            exact hz
          have hoz : o * z = z * o := V_comm_O hc ho hzV
          have hz' : o⁻¹ * z * o = z := by
            calc o⁻¹ * z * o = o⁻¹ * (z * o) := by group
              _ = o⁻¹ * (o * z) := by rw [← hoz]
              _ = z := by group
          simpa using hz')
        (fun x hx => hR r⁻¹ (R.inv_mem hr) x hx)
        (fun x hx => by
          have hmem : x⁻¹ * o⁻¹ * x * o ∈ fourGrp x₁ x₂ := by
            have hmem' := comm_Q_O_mem_V hc (b := x⁻¹) (s := o⁻¹)
              ((ctxQ t tau x₁ x₂ rho).inv_mem hx) ((ctxO t tau x₁ x₂).inv_mem ho)
            simpa using hmem'
          rw [hl.Z_Q]
          simpa only [inv_inv, mul_assoc] using hmem)
        q hq
      simpa using h
    have hdL : r * o * r⁻¹ * o⁻¹ ∈ ctxLO t tau x₁ x₂ :=
      mul_mem (mul_mem (mul_mem hrL hoL) (inv_mem hrL)) (inv_mem hoL)
    exact CLO_Q_le_V hA hQn hdL hcommQ
  have hcardR : Nat.card R ≤ 2 ^ 8 := by
    calc Nat.card R ≤ Nat.card (ctxO t tau x₁ x₂) := Subgroup.card_le_of_le hRO
      _ = 2 ^ 8 := hl.card_O
  have hrel := Subgroup.relIndex_mul_card R (ctxPL t tau x₁ x₂)
  rw [inf_eq_left.mpr hRP, ha.card_P] at hrel
  have hle : 2 ^ 10 ≤ 2 * 2 ^ 8 := by
    rw [← hrel]
    exact Nat.mul_le_mul hRidx hcardR
  exact absurd hle (by norm_num)

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
