module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDisc15Clique
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDisc15Red

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Disc15

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc


@[expose] def TwoGroupR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    SettingR r n R S t₀ K K' z u J t W →
      alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥ →
        ¬ rLayer (CoreAssembly.conjClass (tightCore R)) (t * z) ≤
            sigmaGen (CoreAssembly.conjClass (tightCore R)) K →
          ∀ J₂ ∈ omegaOfSet (CoreAssembly.conjClass (tightCore R))
              (twinSet (CoreAssembly.conjClass (tightCore R)) K),
            ∀ t₂ : Y, IsUniqueInvolution J₂ t₂ → t₂ ≠ t →
              ∃ B M₁ M₂ M₃ M₄ : Subgroup Y, IsPGroup 2 B ∧
                M₁ ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K ∧
                M₂ ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K ∧ M₂ ≠ M₁ ∧
                M₃ ∈ omegaOfSet (CoreAssembly.conjClass (tightCore R))
                  (twinSet (CoreAssembly.conjClass (tightCore R)) K) ∧
                IsUniqueInvolution M₃ t ∧
                M₄ ∈ omegaOfSet (CoreAssembly.conjClass (tightCore R))
                  (twinSet (CoreAssembly.conjClass (tightCore R)) K) ∧
                IsUniqueInvolution M₄ t₂ ∧
                2 < Nat.card ↥(M₁ ⊓ B) ∧ 2 < Nat.card ↥(M₂ ⊓ B) ∧
                2 < Nat.card ↥(M₃ ⊓ B) ∧ 2 < Nat.card ↥(M₄ ⊓ B)

theorem normCentR_of_twoGroup {r n : ℕ} (hTq : DiscTqTzR r n) (hG : TwoGroupR r n) :
    NormCentR r n := by
  intro Y _ _ R S t₀ K K' z u J t W s hα hD
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hP : Q3CL.PartIHypG Ω := partIHypGR s.core
  have hΩ : HypOmegaGen Ω := hP.hyp
  have hf := s.data.frame
  have hK : K ∈ Ω := hf.mem
  have hz : IsUniqueInvolution K z := hf.hz
  have hne : dComp Ω K ≠ dstarComp Ω K := fun heq =>
    hD (rLayer_tz_le_sigmaGen_of_eqR hTq s hα heq)
  refine normalizer_le_centralizer_tz_of_conj hz fun m hm => ?_
  have hmK : conjSub m K = K := mem_normalizer_iff_conjSub_eq.mp hm
  have hJ₂ := conjSub_mem_omegaOfSet_twin hΩ.conjInvariant hf.hJ hmK
  have ht₂ : IsUniqueInvolution (conjSub m J) (m * t * m⁻¹) := hf.ht.conj m
  by_cases h : m * t * m⁻¹ = t
  · exact h
  obtain ⟨B, M₁, M₂, M₃, M₄, hB, hM₁, hM₂, h₂₁, hM₃, hz₃, hM₄, hz₄, c₁, c₂, c₃, c₄⟩ :=
    hG Y R S t₀ K K' z u J t W s hα hD _ hJ₂ _ ht₂ h
  have h₃₄ : M₄ ≠ M₃ := by
    intro h'
    subst h'
    exact h (hz₄.eq hz₃)
  have hz₁ : IsUniqueInvolution M₁ z := isUniqueInvolution_of_mem_twinSet hz hM₁
  have hz₂ : IsUniqueInvolution M₂ z := isUniqueInvolution_of_mem_twinSet hz hM₂
  have h₂₄ : M₄ ≠ M₂ := fun h' =>
    not_mem_twinSet_of_mem_omegaOfSet hK hz hM₄ (h' ▸ hM₂)
  have h4 := mul_four_eq_one_of_twoGroup hP hK hne hM₁.1 hM₂.1 hM₃.1 hM₄.1 hz₁ hz₂ hz₃ hz₄
    (Q3CL.T3.twin_mem_omegaNbr hΩ hM₁.1 hM₂.1 h₂₁ hz₁ hz₂) (hM₃.2 M₁ hM₁) (hM₃.2 M₂ hM₂)
    (hM₄.2 M₁ hM₁) h₂₄ h₃₄ hB c₁ c₂ c₃ c₄
  rw [hz.sq, one_mul] at h4
  have h5 : m * t * m⁻¹ = t⁻¹ := eq_inv_of_mul_eq_one_right h4
  rw [h5]
  exact inv_eq_of_mul_eq_one_right hf.ht.sq

theorem disc15R_of_twoGroup {r n : ℕ} (hTq : DiscTqTzR r n) (hG : TwoGroupR r n) : Disc15R r n :=
  disc15R_of_normCent hTq (normCentR_of_twoGroup hTq hG)

end CFSG.CGT.PushingUpLit.SolKNA.R4.Disc15
