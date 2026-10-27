module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptFrame
public import CFSG.ClassicalInvolution.Q3.Q3URTransfer

public section

namespace CFSG.ClassicalInvolution.Q3.Q3E6T

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.Steinberg CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.NonClassical
  CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.Models
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive
  exists_unitaryInvolution_eq_neg)
open CFSG.LieType.Steinberg.Exceptional (frobQ frobQ_apply frobQ_frobQ)
open scoped MatrixGroups

set_option linter.unusedSectionVars false

theorem exists_su6Frame_of_witt3 (P : GL (Fin 6) (GaloisField 3 (2 * 1)))
    (hP : conjTr (unitaryInvolution (GaloisField 3 (2 * 1)) 3 1)
      (P : Matrix (Fin 6) (Fin 6) (GaloisField 3 (2 * 1))) *
        (P : Matrix (Fin 6) (Fin 6) (GaloisField 3 (2 * 1))) = antidiag 6) :
    ∃ F : SU6Frame 3 1 le_rfl,
      F.R₁ = (nodeSU (unitaryInvolution_involutive (K := GaloisField 3 (2 * 1)) (p := 3) (f := 1)
        (CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl)) 2).map
          (conjEquiv P hP).toMonoidHom ∧
      F.S₂ = (nodeSU (unitaryInvolution_involutive (K := GaloisField 3 (2 * 1)) (p := 3) (f := 1)
        (CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl)) 1).map
          (conjEquiv P hP).toMonoidHom ∧
      F.S₃ = (nodeSU (unitaryInvolution_involutive (K := GaloisField 3 (2 * 1)) (p := 3) (f := 1)
        (CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl)) 0).map
          (conjEquiv P hP).toMonoidHom := by
  classical
  have : NeZero (2 * 1) := ⟨by norm_num⟩
  have hF : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl
  have hσ := unitaryInvolution_involutive (K := GaloisField 3 (2 * 1)) (p := 3) (f := 1) hF
  obtain ⟨μ, hμ0, hμ⟩ := exists_unitaryInvolution_eq_neg (K := GaloisField 3 (2 * 1)) (p := 3)
    (f := 1) hF
  have hσθ : ∀ c, unitaryInvolution (GaloisField 3 (2 * 1)) 3 1 c = frobQ 3 1 c := fun c => by
    rw [unitaryInvolution_apply, frobQ_apply]
  have hθ := frobQ_frobQ 3 1 le_rfl
  let φ := conjEquiv P hP
  obtain ⟨i₀, hi₀⟩ : ∃ i, IsLongRootSU2 (GaloisField 3 (2 * 1)) 3 1 (by norm_num : 2 ≤ 6)
      ((nodeSU hσ 2).map φ.toMonoidHom) i :=
    CFSG.ClassicalInvolution.ModelFacts.exists_isLongRootSU2_map_rankOne hF
      (by norm_num : (3 : ℕ) ≠ 2) (by norm_num)
      (k := ⟨2, by norm_num⟩) (γ := Pi.single 2 1) (by decide +kernel) (by decide +kernel) P hP
  have hB23 : nodeSU hσ 1 = (WeakCT.B23 (GaloisField 3 (2 * 1))).map (iota3 hσ) :=
    le_antisymm (iota3_B23_ge hσ) (iota3_B23_le hσ)
  have hB12 : nodeSU hσ 0 = (WeakCT.B12 (GaloisField 3 (2 * 1))).map (iota3 hσ) :=
    le_antisymm (iota3_B12_ge hσ) (iota3_B12_le hσ)
  have hlb : nodeSU hσ 2 = ((ulb (frobQ 3 1) hθ).range).map (iota4 hθ hμ0 hμ hσθ) :=
    le_antisymm (iota4_ulb_ge hσ hθ hμ0 hμ hσθ) (iota4_ulb_le hσ hθ hμ0 hμ hσθ)
  have hker : (QuotientGroup.mk' (Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 6))).ker ≤
      Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 6) := by
    rw [QuotientGroup.ker_mk']
  refine ⟨{
    R₁ := (nodeSU hσ 2).map φ.toMonoidHom
    S₂ := (nodeSU hσ 1).map φ.toMonoidHom
    S₃ := (nodeSU hσ 0).map φ.toMonoidHom
    R₁_mem := ⟨i₀, hi₀⟩
    commutes_R₁_S₃ := ?_
    gen := ?_
    ι₄ := φ.toMonoidHom.comp (iota4 hθ hμ0 hμ hσθ)
    ι₄_injective := φ.injective.comp (iota4_injective hθ hμ0 hμ hσθ)
    ι₄_long := ?_
    ι₄_short := ?_
    ι₃ := φ.toMonoidHom.comp (iota3 hσ)
    ι₃_injective := φ.injective.comp (iota3_injective hσ)
    ι₃_B23 := ?_
    ι₃_B12 := ?_
    R₁_center := ?_
    S₂_center := ?_ }, rfl, rfl, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show φ x * φ y = φ y * φ x
    rw [← map_mul, ← map_mul, commutes_node2_node0 hσ hθ hμ0 hμ hσθ x hx y hy]
  · rw [← Subgroup.map_sup, ← Subgroup.map_sup, nodes_generate hF]
    exact Subgroup.map_top_of_surjective _ φ.surjective
  · rw [← Subgroup.map_map]
    exact congrArg (Subgroup.map φ.toMonoidHom) hlb.symm
  · rw [← Subgroup.map_map]
    exact congrArg (Subgroup.map φ.toMonoidHom)
      ((iota4_usb_range hσ hθ hμ0 hμ hσθ).trans hB23.symm)
  · rw [← Subgroup.map_map, ← hB23]
  · rw [← Subgroup.map_map, ← hB12]
  · exact fun r hr hc => eq_one_of_mem_ker_of_isLongRootSU2_3 (by norm_num) hi₀ hker r hr
      (by rw [QuotientGroup.ker_mk']; exact hc)
  · rintro _ ⟨x, hx, rfl⟩ hc
    rw [hB23] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    have hcx : ∀ y : SU (unitaryInvolution (GaloisField 3 (2 * 1)) 3 1) 6,
        iota3 hσ b * y = y * iota3 hσ b := fun y =>
      φ.injective (by rw [map_mul, map_mul]; exact ((Subgroup.mem_center_iff.mp hc) (φ y)).symm)
    have hb1 : b = 1 := by
      refine eq_one_of_mem_B23_commute_B12 hb (fun c => ?_) (fun c => ?_)
      · exact iota3_injective hσ (by rw [map_mul, map_mul]; exact hcx _)
      · exact iota3_injective hσ (by rw [map_mul, map_mul]; exact hcx _)
    rw [hb1, map_one, map_one]

variable {g : GL (Fin 6) (GaloisField 3 (2 * 1))} {P : GL (Fin 6) (GaloisField 3 (2 * 1))}

theorem adaptedFrame_of_adaptedBasis3
    {α : Su (GaloisField 3 (2 * 1)) 3 1 6 →* Su (GaloisField 3 (2 * 1)) 3 1 6}
    (hα : ∀ x : Su (GaloisField 3 (2 * 1)) 3 1 6,
      ((α x : GL (Fin 6) (GaloisField 3 (2 * 1))) :
        Matrix (Fin 6) (Fin 6) (GaloisField 3 (2 * 1))) =
        (g : Matrix (Fin 6) (Fin 6) (GaloisField 3 (2 * 1))) *
          ((x : GL (Fin 6) (GaloisField 3 (2 * 1))) :
            Matrix (Fin 6) (Fin 6) (GaloisField 3 (2 * 1))) *
          ((g⁻¹ : GL (Fin 6) (GaloisField 3 (2 * 1))) :
            Matrix (Fin 6) (Fin 6) (GaloisField 3 (2 * 1))))
    {d₀ d₁ : GaloisField 3 (2 * 1)}
    (hAB : AdaptedBasis 3 1 (g : Matrix (Fin 6) (Fin 6) (GaloisField 3 (2 * 1))) P d₀ d₁) :
    AdaptedFrame 3 1 le_rfl α := by
  classical
  have : NeZero (2 * 1) := ⟨by norm_num⟩
  have hF : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl
  have hσ := unitaryInvolution_involutive (K := GaloisField 3 (2 * 1)) (p := 3) (f := 1) hF
  obtain ⟨F, hR, hS2, hS3⟩ := exists_su6Frame_of_witt3 P hAB.gram
  have hB23 : nodeSU hσ 1 = (WeakCT.B23 (GaloisField 3 (2 * 1))).map (iota3 hσ) :=
    le_antisymm (iota3_B23_ge hσ) (iota3_B23_le hσ)
  have hB12 : nodeSU hσ 0 = (WeakCT.B12 (GaloisField 3 (2 * 1))).map (iota3 hσ) :=
    le_antisymm (iota3_B12_ge hσ) (iota3_B12_le hσ)
  have hfixι : ∀ b : SL(3, GaloisField 3 (2 * 1)),
      α (conjEquiv P hAB.gram (iota3 hσ b)) = conjEquiv P hAB.gram (iota3 hσ b) := by
    intro b
    refine alpha_eq_of_commutes hα ?_
    show (g : Matrix (Fin 6) (Fin 6) (GaloisField 3 (2 * 1))) *
      ((P * ((iota3 hσ b : SU _ 6) : GL (Fin 6) (GaloisField 3 (2 * 1))) * P⁻¹ :
        GL (Fin 6) (GaloisField 3 (2 * 1))) : Matrix (Fin 6) (Fin 6) (GaloisField 3 (2 * 1))) = _
    rw [Units.val_mul, Units.val_mul]
    exact commutes_of_conj_diagonal hAB.eigen (diagonal_mul_iota3 hσ d₀ d₁ b)
  refine ⟨F, ?_, ?_, ?_⟩
  · rw [hR]
    refine map_node_two_eq le_rfl (by norm_num : (3 : ℕ) ≠ 2) hAB.gram ?_
    have hle : colPlane (P : Matrix (Fin 6) (Fin 6) (GaloisField 3 (2 * 1)))
        (lowIdx (⟨2, by norm_num⟩ : Fin (6 / 2))) ≤ te6Minus 3 1 := by
      refine Submodule.span_le.mpr ?_
      rintro _ (rfl | rfl)
      · rw [SetLike.mem_coe, mem_te6Minus_iff (by norm_num : (3 : ℕ) ≠ 2)]
        intro r hr
        rw [Matrix.mulVec_single_one]
        exact (hAB.plane r hr).1
      · rw [SetLike.mem_coe, mem_te6Minus_iff (by norm_num : (3 : ℕ) ≠ 2)]
        intro r hr
        rw [Matrix.mulVec_single_one]
        exact (hAB.plane r hr).2
    exact Submodule.eq_of_le_of_finrank_eq hle (by
      rw [finrank_colPlane hAB.gram (lowIdx_ne_rev _ _),
        finrank_te6Minus (by norm_num : (3 : ℕ) ≠ 2)])
  · intro x hx
    rw [hS2] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [hB23] at ha
    obtain ⟨_, ⟨b, -, rfl⟩, rfl⟩ := ha
    exact hfixι _
  · intro x hx
    rw [hS3] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [hB12] at ha
    obtain ⟨_, ⟨b, -, rfl⟩, rfl⟩ := ha
    exact hfixι _

end CFSG.ClassicalInvolution.Q3.Q3E6T
