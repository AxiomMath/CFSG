module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeGraphNormalUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryOdd

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup
  mem_matrixIsometryGroup det_eq_one_of_mem eq_one_of_mem_of_scalar)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (statedSpMap centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.QuasithinUnique.Lin2.Five (tauSp)

section Construct

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K₀ : Type} [Field K₀]

theorem exists_unitaryOddNeighbourParam_three {f : ℕ} [Finite K₀] [CharP K₀ 2]
    (hset : SeitzSetting G L) (hKc : Nat.card K₀ = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp 3 K₀)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin 3)
    (hk : RootKindSp e t f k .unitaryOdd) :
    ∃ (K' : Type) (_ : Field K') (h : UnitaryFieldData 2 f K') (_ : CharP h.fixedField 2)
      (C₀ : GL (Fin (2 * 2 + 1)) K') (hC : IsPrimeFormGram C₀)
      (hC₀ : ((C₀ : GL (Fin (2 * 2 + 1)) K') :
        Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) K') = 1),
      ∀ β : StatedSp 2 h.fixedField ≃*
          matrixIsometryGroup (1 : Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) h.fixedField),
        ∃ (ι : K₀ ≃+* h.fixedField) (κ : StatedSp 2 K₀ →* StatedSp 2 K₀)
          (Φ : gramSU h (C₀ : Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) K') →* G),
          (κ = MonoidHom.id _ ∨ κ = tauSp) ∧ Φ.range = neighbourCore e k ∧
          Φ.ker ≤ center (gramSU h (C₀ : Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) K')) ∧
          (∀ x : StatedSp 2 K₀,
            Φ (isoOneToSU h hC₀ (β (statedSpMap (ι : K₀ →+* h.fixedField) 2 (κ x)))) =
              ((e.symm ((complSpEquiv k x : complSp K₀ k) : StatedSp 3 K₀) : L) : G)) ∧
          ∀ x, t * Φ x * t⁻¹ = Φ (primeFormFieldSU h hC (UnitaryPilot.barRingEquiv h) x) := by

  have hN : t ∈ normalizer (centralizerPerfectCore (modelToG e (rootTorusSp K₀ k)) : Set G) :=
    le_normalizer_neighbourCore e htC k
  obtain ⟨r, K', _, h', C₀, hC, φ, ρ', hcase, hφ, hρs, hρker, -, hρt⟩ :=
    exists_surjective_primeFormP_neighbourCore_unitary' hset hKc hf (by omega : 2 ≤ 2) e htC ht
      k rfl rfl (Or.inr rfl) hk hN
  obtain ⟨-, rfl, h1⟩ : Sp2mKind.unitaryOdd = .unitaryOdd ∧ r = 2 * 2 + 1 ∧
      (C₀ : Matrix (Fin r) (Fin r) K') = 1 := by
    rcases hcase with ⟨h2, -⟩ | h1
    · exact absurd h2 (by decide)
    · exact h1
  have hφb : φ = UnitaryPilot.barRingEquiv h' := RingEquiv.ext fun x =>
    (hφ x).trans (UnitaryPilot.barRingEquiv_apply h' x).symm
  subst hφb
  have hk2 : CharP h'.fixedField 2 :=
    CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer.fixedField_charP h'
  have hq : ¬(2 * 2 + 1 = 3 ∧ 2 ^ f = 2) := fun h3 => by omega
  refine ⟨K', inferInstance, h', hk2, C₀, hC, h1, fun β => ?_⟩
  have hμ : Function.Injective ((QuotientGroup.mk' (normOneScalars h'
      (gramSU h' (C₀ : Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) K')) (2 * 2 + 1))).comp
        ((isoOneToSU h' h1).comp β.toMonoidHom)) :=
    (proj_isoOneToSU_injective (by omega) h1).comp β.injective
  have hμr : ((QuotientGroup.mk' (normOneScalars h'
      (gramSU h' (C₀ : Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) K')) (2 * 2 + 1))).comp
        ((isoOneToSU h' h1).comp β.toMonoidHom)).range =
      fixedSubgroup (primeFormFieldHom h' hC (UnitaryPilot.barRingEquiv h')) := by
    rw [← MonoidHom.comp_assoc, MonoidHom.range_comp, MonoidHom.range_eq_top.2 β.surjective,
      ← MonoidHom.range_eq_map]
    exact range_proj_isoOneToSU (by omega) hq hC h1
  obtain ⟨ι, κ, Φ, hκ, hrange, hker, hN1, hN3⟩ := exists_param_of_proj_two e hKc hf htC k h' hC
    (gramSU_one_exists_section_of_central h' h1 (by omega)
      (by rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one 2) hf)
    (isPerfect_gramSU_one h' h1 (by omega) (fun h3 => by
      have := (Prod.mk.inj h3).1
      omega))
    ((isoOneToSU h' h1).comp β.toMonoidHom) hμ hμr hN ρ' hρs hρker hρt
  exact ⟨ι, κ, Φ, hκ, hrange, hker, hN1, hN3⟩

end Construct

end CFSG.SeitzReduction.SymplecticPilot
