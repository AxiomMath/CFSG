module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64OtherParabolic
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64MiddleSubgroup
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64NoncentralPoint

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise commutatorElement

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

section Aux

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)

variable {G : Type} [Group G] {L : Subgroup G} (φ : L ≃* bilinIsometryGroup b) {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)

local notation "𝒜₂" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℛ" => radSub φ z e

include hinf in
theorem center_eq_radA_of_kappa_zero {D₂ : Subgroup G} {κ₂ : ZMod 2}
    (hκ : ∀ d ∈ D₂, ∀ (C B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (C, 1)) →
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + κ₂ • symThreePolarSym
          (symThreeDiag (C : M₃)) (symThreeDiag (B : M₃)) + ε • C, ε)))
    (hκ0 : κ₂ = 0) {ν₂ : G → ↥(binarySymMatrices 3)}
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hν₂surj : ∀ C : ↥(binarySymMatrices 3), ∃ d ∈ D₂, ν₂ d = C)
    (hRD₂ : ℛ ≤ D₂) (hD₂H : D₂ ⊓ centralizer ({z} : Set G) = ℛ) :
    (center D₂).map D₂.subtype = 𝒜₂ ∧ ⁅𝒜₂, D₂⁆ = ⊥ ∧ ∀ d ∈ D₂, ∀ a ∈ 𝒜₂, d⁻¹ * a * d = a := by
  subst hκ0
  have hfix : ∀ d ∈ D₂, ∀ a ∈ 𝒜₂, d⁻¹ * a * d = a := by
    intro d hd a ha
    obtain ⟨B, rfl⟩ := (mem_pullSub_iff φ he).1 ha
    have h := hκ d hd (ν₂ d) (Multiplicative.toAdd B) 0 (hν₂z d hd)
    rw [zero_smul, add_zero, zero_smul, add_zero, radHom_tau, ofAdd_toAdd] at h
    exact h
  have hcomm : ∀ d ∈ D₂, ∀ a ∈ 𝒜₂, d * a = a * d := fun d hd a ha => by
    have h := hfix d hd a ha
    calc d * a = d * (d⁻¹ * a * d) := by rw [h]
      _ = a * d := by group
  refine ⟨?_, ?_, hfix⟩
  · ext x
    rw [mem_map_center_subtype_iff]
    constructor
    · rintro ⟨hxD, hc⟩
      have hzD : z ∈ D₂ := hRD₂ (mem_sup_right (mem_zpowers z))
      have hxR : x ∈ ℛ := by
        rw [← hD₂H]
        exact mem_inf.2 ⟨hxD, mem_centralizer_singleton_iff.2 (hc z hzD).symm⟩
      obtain ⟨B, ε, rfl⟩ := (mem_radSub_iff φ he hzC hz).1 hxR
      obtain ⟨d, hd, hdC⟩ := hν₂surj (jSym 0 1 0)
      have h1 := hκ d hd (jSym 0 1 0) B ε (by rw [hν₂z d hd, hdC])
      have h2 : d⁻¹ * (tauHom φ he (Multiplicative.ofAdd B) * zPow z ε) * d =
          tauHom φ he (Multiplicative.ofAdd B) * zPow z ε := by
        rw [mul_assoc, ← hc d hd]
        group
      rw [← radHom_apply φ he hzC hz] at h2
      rw [h2, zero_smul, add_zero] at h1
      have h3 := Multiplicative.ofAdd.injective (radHom_injective φ he hzC hz hinf h1)
      have h4 := congrArg (fun p => ((p.1 : ↥(binarySymMatrices 3)) : M₃) 0 1) h3
      simp only at h4
      have hε : ε = 0 := by
        change (B : M₃) 0 1 = (B : M₃) 0 1 + ε * 1 at h4
        rw [mul_one] at h4
        exact (add_eq_left.1 h4.symm)
      subst hε
      rw [← radHom_apply φ he hzC hz, radHom_tau]
      exact (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
    · intro hx
      exact ⟨hRD₂ (mem_sup_left hx), fun d hd => hcomm d hd x hx⟩
  · rw [commutator_eq_bot_iff_le_centralizer]
    intro a ha
    exact mem_centralizer_iff.2 fun d hd => hcomm d hd a ha

end Aux

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
