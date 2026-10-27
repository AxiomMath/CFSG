module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf40Layer
public import CFSG.ClassicalInvolution.Asc77.AscT7V1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf16Thm3
public import CFSG.ClassicalInvolution.Q3.Q3T6DCaseIC

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Asc77.T3Core CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Uniform CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3T6D

section U3

variable {T : Type} [Group T] [Finite T]

@[expose] def layerU3 (H : Subgroup T) : Subgroup T := ⁅H, H⁆ ⊔ oddCoreOf H

theorem layerU3_normalizer {H : Subgroup T} {g : T} (hg : g ∈ Subgroup.normalizer (H : Set T)) :
    g ∈ Subgroup.normalizer (layerU3 H : Set T) := by
  have key : conjSub g (layerU3 H) ≤ layerU3 H := by
    unfold layerU3
    rw [conjSub_sup g, Asc77.T7V.conjSub_oddCoreOf_eq_of_mem_normalizer hg]
    refine sup_le_sup_right ?_ _
    have hH : conjSub g H = H := mem_normalizer_iff_conjSub_eq.mp hg
    have : conjSub g ⁅H, H⁆ = ⁅conjSub g H, conjSub g H⁆ := Subgroup.map_commutator _ _ _
    rw [this, hH]
  exact Asc77.Thompson.mem_normalizer_of_conjSub_le key

theorem layerU3_le (H : Subgroup T) : layerU3 H ≤ H :=
  sup_le (Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem h₁ h₂) (H.inv_mem h₁)) (H.inv_mem h₂))
    (oddCoreOf_le_self H)

structure U3LayerFacts (H : Subgroup T) : Prop where
  quasi : CFSG.IsQuasisimple (↥(layerU3 H) ⧸ classicalInvolutionOddCore ↥(layerU3 H))
  sq : ∀ x ∈ H, x * x ∈ layerU3 H
  conj : ∀ x ∈ layerU3 H, x * x = 1 → x ≠ 1 → ∀ y ∈ layerU3 H, y * y = 1 → y ≠ 1 →
    ∃ h ∈ layerU3 H, h * x * h⁻¹ = y
  sqrt : ∀ x ∈ layerU3 H, x * x = 1 → x ≠ 1 → ∃ k ∈ layerU3 H, k * k = x ∧ k ^ 4 = 1
  model : ∃ (N : Type) (_ : Group N), CFSG.Blueprint.LieModel N .PSU 3 3 1 ∧
    Nonempty ((↥(layerU3 H) ⧸ classicalInvolutionOddCore ↥(layerU3 H)) ≃* N) ∧
    2 * Nat.card N ≤ Nat.card H

@[expose] def FrameC201U3Section : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (H : Subgroup T),
    Thm3RowU3 (⊤ : Subgroup ↥H) → U3LayerFacts H

theorem frame_false_of_u3LayerFacts (h4 : Asc75Theorem4) {T : Type} [Group T] [Finite T]
    [CaseIAmbient T] {R : Subgroup T} {t : T} {J : Subgroup T} {zK zJ : T}
    (hh : FrameCaseIHyps T R t J zK zJ) {H : Subgroup T}
    (hH : omegaGen (aStar (CoreAssembly.conjClass R) R) = H) (hf : U3LayerFacts H)
    (hn : H ≠ ⊤ → layerU3 H ≠ ⊥ → ¬ (layerU3 H).Normal) : False := by
  have hΩg : HypOmegaGen (CoreAssembly.conjClass R) := hh.datum.hyp
  have hK : R ∈ CoreAssembly.conjClass R := CoreAssembly.mem_conjClass_self R
  have hv := hh.viol
  have htrans : ∀ M ∈ CoreAssembly.conjClass R, ∃ g : T, conjSub g R = M := by
    intro M hM
    obtain ⟨g, rfl⟩ := hM
    exact ⟨g, rfl⟩
  have hKS : R ∈ aStar (CoreAssembly.conjClass R) R := Relation.ReflTransGen.refl
  have hJS : J ∈ aStar (CoreAssembly.conjClass R) R :=
    Relation.ReflTransGen.single ⟨hv.mem, Or.inl ⟨zK, zJ, hv⟩⟩
  have hKH : R ≤ H := hH ▸ le_omegaGen hKS
  have hJH : J ≤ H := hH ▸ le_omegaGen hJS
  have hHtop : H ≠ ⊤ := fun h =>
    hh.ne (aStar_eq_of_omegaGen_eq_top hΩg.conjInvariant hK htrans (hH.trans h))
  have hz : IsUniqueInvolution R zK := hv.hzK
  have ht : IsUniqueInvolution J zJ := hv.hzJ
  obtain ⟨k₀, hk₀K, hkk₀, -⟩ := Q3T6D.exists_sq_eq_involution3 hΩg hK hz
  obtain ⟨j₀, hj₀J, hjj₀, -⟩ := Q3T6D.exists_sq_eq_involution3 hΩg hv.mem ht
  have hzΛ : zK ∈ layerU3 H := hkk₀ ▸ hf.sq k₀ (hKH hk₀K)
  have htΛ : zJ ∈ layerU3 H := hjj₀ ▸ hf.sq j₀ (hJH hj₀J)
  have hΛ1 : layerU3 H ≠ ⊥ := fun h => hz.ne_one (by rwa [h, Subgroup.mem_bot] at hzΛ)
  exact frame_false_of_layerSection h4 hh hH (layerU3_le H) (fun g hg => layerU3_normalizer hg)
    hf.quasi hzΛ htΛ (fun x hx hx2 hx1 => hf.conj zK hzΛ hz.sq hz.ne_one x hx hx2 hx1)
    (hf.sqrt zK hzΛ hz.sq hz.ne_one) (hn hHtop hΛ1)

end U3

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
