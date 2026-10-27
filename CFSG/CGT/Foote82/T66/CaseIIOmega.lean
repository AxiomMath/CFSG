module

import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusFacts
import CFSG.LocalAnalysis.GLTheoremB.I2810.AltDegree
import CFSG.CGT.Foote82.T66.Overgroup
public import CFSG.CGT.Foote82.T66.CaseIIRefl

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.PGLModel

namespace CaseII

section Dickson

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {Q : QuadraticForm (ZMod 2) W}

private theorem dickson_mul (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {g t : W ≃ₗ[ZMod 2] W}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    (Module.finrank (ZMod 2)
        ↥(LinearMap.range (((g * t : W ≃ₗ[ZMod 2] W) : Module.End (ZMod 2) W) - 1)) : ZMod 2) =
      Module.finrank (ZMod 2) ↥(LinearMap.range ((g : Module.End (ZMod 2) W) - 1)) +
        Module.finrank (ZMod 2) ↥(LinearMap.range ((t : Module.End (ZMod 2) W) - 1)) :=
  CFSG.RankThree.OrthogonalInvolutions.natCast_finrank_commSpace_mul hQ hg ht

private theorem mem_commutator_iff_even (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (h6 : 6 ≤ Module.finrank (ZMod 2) W) {g : W ≃ₗ[ZMod 2] W}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ↔
      Even (Module.finrank (ZMod 2) ↥(LinearMap.range ((g : Module.End (ZMod 2) W) - 1))) := by
  rw [CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup hQ h6,
    CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup]
  exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩

end Dickson

private theorem cdim6_eq_toLinEquiv (g : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
    cdim6 g = Module.finrank (ZMod 2) ↥(LinearMap.range
      (((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) g) :
        Module.End (ZMod 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2)) - 1)) := by
  have e : Matrix.mulVecLin
      ((g : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) - 1) =
      (((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) g) :
        Module.End (ZMod 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2)) - 1) := by
    refine LinearMap.ext fun x => ?_
    rw [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec, LinearMap.sub_apply,
      Module.End.one_apply, LinearEquiv.coe_coe,
      CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]
  show Module.finrank (ZMod 2) ↥(LinearMap.range (Matrix.mulVecLin
    ((g : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) - 1))) = _
  rw [e]

private theorem coe_quadMinus₆ :
    ⇑(CFSG.LieType.Universal.Spin.quadMinus (2 + 1) (ZMod 2) (1 : ZMod 2) 1) =
      CFSG.Open.StatedQuadMinus (2 + 1) (ZMod 2) 1 1 :=
  CFSG.LieType.Universal.Spin.coe_quadMinus (2 + 1) (ZMod 2) 1 1

private theorem nondeg₆ : (QuadraticMap.polarBilin
    (CFSG.LieType.Universal.Spin.quadMinus (2 + 1) (ZMod 2) (1 : ZMod 2) 1)).Nondegenerate :=
  CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (2 + 1) (ZMod 2)
    CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.irreducible_one_one

private theorem mem_O_iff {g : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)} :
    g ∈ orthogonalMinus 2 (ZMod 2) 1 1 ↔
      CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) g ∈
        TauCeti.QuadraticMap.orthogonalGroup
          (CFSG.LieType.Universal.Spin.quadMinus (2 + 1) (ZMod 2) (1 : ZMod 2) 1) := by
  have := CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap coe_quadMinus₆
  exact SetLike.ext_iff.1 this g

theorem mem_omega_iff_even {g : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)}
    (hg : g ∈ orthogonalMinus 2 (ZMod 2) 1 1) :
    g ∈ omegaMinusTwo 2 ↔ Even (cdim6 g) := by
  have h6 : 6 ≤ Module.finrank (ZMod 2) (Fin (2 + 1 - 1) ⊕ Fin (2 + 1 - 1) ⊕ Fin 2 → ZMod 2) := by
    rw [CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.finrank_minus]
  have hΩ : omegaMinusTwo 2 =
      ⁅TauCeti.QuadraticMap.orthogonalGroup
          (CFSG.LieType.Universal.Spin.quadMinus (2 + 1) (ZMod 2) (1 : ZMod 2) 1),
        TauCeti.QuadraticMap.orthogonalGroup
          (CFSG.LieType.Universal.Spin.quadMinus (2 + 1) (ZMod 2) (1 : ZMod 2) 1)⁆.comap
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2)
          (ZMod 2)).toMonoidHom := by
    rw [CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.omegaMinusTwo_eq_statedOmega,
      CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap coe_quadMinus₆]
  rw [hΩ, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
    mem_commutator_iff_even nondeg₆ h6 (mem_O_iff.1 hg), cdim6_eq_toLinEquiv]

theorem cdim6_mul_cast {g t : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)}
    (hg : g ∈ orthogonalMinus 2 (ZMod 2) 1 1) (ht : t ∈ orthogonalMinus 2 (ZMod 2) 1 1) :
    (cdim6 (g * t) : ZMod 2) = cdim6 g + cdim6 t := by
  have hadd := dickson_mul nondeg₆ (mem_O_iff.1 hg) (mem_O_iff.1 ht)
  rw [← map_mul (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) g t,
    ← cdim6_eq_toLinEquiv, ← cdim6_eq_toLinEquiv, ← cdim6_eq_toLinEquiv] at hadd
  exact hadd

theorem not_mem_omega_of_cdim6_one {t : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)}
    (ht : t ∈ orthogonalMinus 2 (ZMod 2) 1 1) (ht1 : cdim6 t = 1) : t ∉ omegaMinusTwo 2 := by
  rw [mem_omega_iff_even ht, ht1]
  decide

theorem mem_omega_or_mul_mem {g t : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)}
    (hg : g ∈ orthogonalMinus 2 (ZMod 2) 1 1) (ht : t ∈ orthogonalMinus 2 (ZMod 2) 1 1)
    (ht1 : cdim6 t = 1) : g ∈ omegaMinusTwo 2 ∨ g * t ∈ omegaMinusTwo 2 := by
  rw [mem_omega_iff_even hg, mem_omega_iff_even ((orthogonalMinus 2 (ZMod 2) 1 1).mul_mem hg ht)]
  have hadd := cdim6_mul_cast hg ht
  rw [ht1] at hadd
  rcases Nat.even_or_odd (cdim6 g) with he | ho
  · exact Or.inl he
  · right
    rw [← ZMod.natCast_eq_zero_iff_even, hadd]
    rw [← ZMod.natCast_eq_one_iff_odd] at ho
    rw [ho]
    decide

theorem isSimpleGroup_omega : IsSimpleGroup ↥(omegaMinusTwo 2) ∧
    commutator ↥(omegaMinusTwo 2) = ⊤ ∧ ¬ ∀ x y : ↥(omegaMinusTwo 2), x * y = y * x := by
  obtain ⟨hs, hc, hna⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.isSimpleGroup_statedOmega_quadMinus_small
      (K := ZMod 2) (n := 2 + 1) (Or.inr rfl)
      CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.irreducible_one_one
  exact ⟨hs, hc, hna⟩

theorem card_omega : Nat.card ↥(omegaMinusTwo 2) = 25920 :=
  CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.AltDegree.card_omegaMinusSix.2

theorem isQuasisimple_omega : CFSG.Open.IsQuasisimple ↥(omegaMinusTwo 2) := by
  obtain ⟨hs, hc, hna⟩ := isSimpleGroup_omega
  refine ⟨hc, ?_⟩
  have hZ : Subgroup.center ↥(omegaMinusTwo 2) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(omegaMinusTwo 2)) with
      h0 | h0
    · exact h0
    · exact absurd (fun x y => Subgroup.mem_center_iff.1 (h0 ▸ Subgroup.mem_top y) x) hna
  have e : ↥(omegaMinusTwo 2) ⧸ Subgroup.center ↥(omegaMinusTwo 2) ≃* ↥(omegaMinusTwo 2) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact e.isSimpleGroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {G L : Subgroup (GLV V)} {z : GLV V} {v : V} {H₁ : Subgroup (GLV V)}
  {ψ : ↥H₁ ≃* ↥(orthogonalMinus 2 (ZMod 2) 1 1)}

namespace Ctx

variable (c : Ctx G L z v H₁ ψ)
include c

theorem z_not_mem_H : z ∉ HH G L v := by
  rw [c.mem_H_iff c.z_mem]
  exact not_mem_omega_of_cdim6_one (ψ ⟨z, c.z_mem⟩).2 c.data.ψ_z

theorem psi_mul {a b : GLV V} (ha : a ∈ H₁) (hb : b ∈ H₁) :
    ((ψ ⟨a * b, H₁.mul_mem ha hb⟩ : ↥(orthogonalMinus 2 (ZMod 2) 1 1)) : GL I6 (ZMod 2)) =
      (ψ ⟨a, ha⟩ : GL I6 (ZMod 2)) * (ψ ⟨b, hb⟩ : GL I6 (ZMod 2)) := by
  rw [show (⟨a * b, H₁.mul_mem ha hb⟩ : ↥H₁) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl, map_mul]
  rfl

theorem mul_z_mem_H {a : GLV V} (ha : a ∈ H₁) (haH : a ∉ HH G L v) : a * z ∈ HH G L v := by
  rw [c.mem_H_iff (H₁.mul_mem ha c.z_mem), c.psi_mul ha c.z_mem]
  rw [c.mem_H_iff ha] at haH
  rcases mem_omega_or_mul_mem (ψ ⟨a, ha⟩).2 (ψ ⟨z, c.z_mem⟩).2 c.data.ψ_z with h | h
  · exact absurd h haH
  · exact h

theorem relIndex_H : (HH G L v).relIndex H₁ = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨z, c.z_mem, fun b hb => ?_⟩
  by_cases hbH : b ∈ HH G L v
  · refine Or.inr ⟨hbH, fun hbz => c.z_not_mem_H ?_⟩
    have : z = b⁻¹ * (b * z) := by group
    rw [this]
    exact (HH G L v).mul_mem ((HH G L v).inv_mem hbH) hbz
  · exact Or.inl ⟨c.mul_z_mem_H hb hbH, hbH⟩

theorem isSimpleGroup_H : IsSimpleGroup ↥(HH G L v) := by
  have := isSimpleGroup_omega.1
  exact c.phi.isSimpleGroup

theorem card_H : Nat.card ↥(HH G L v) = 25920 := by
  rw [Nat.card_congr c.phi.toEquiv, card_omega]

theorem card_H₁ : Nat.card ↥H₁ = 51840 := by
  have h := ((HH G L v).subgroupOf H₁).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.H_le).toEquiv, c.card_H] at h
  have h2 : ((HH G L v).subgroupOf H₁).index = 2 := c.relIndex_H
  rw [h2] at h
  omega

theorem isQuasisimple_H : CFSG.Open.IsQuasisimple ↥(HH G L v) :=
  CFSG.Open.IsQuasisimple.of_mulEquiv c.phi isQuasisimple_omega

theorem H_perfect : ⁅HH G L v, HH G L v⁆ = HH G L v :=
  commutator_eq_self_of_isQuasisimple c.isQuasisimple_H

end Ctx

end CaseII

end CFSG.CGT.Foote82
