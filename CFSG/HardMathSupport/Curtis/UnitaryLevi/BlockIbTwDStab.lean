module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltPlusD.FlagLink
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualTwistedD.FlagSpinM

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.HardMathSupport.Curtis.NaturalModuleCensus
open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted Matrix

section Stab

variable {n : ℕ} {F : Type} [Field F] [Finite F] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

include hirr in
theorem stab_of_map_stabEM (hn : 4 ≤ n)
    (π' : spinGroup (quadMinus n F b c) →* StatedProj (StatedOmega (StatedQuadMinus n F b c)))
    (g : StatedProj (StatedOmega (StatedQuadMinus n F b c)))
    (hπ' : ∀ k, π' k = g * spinToStatedProj (quadMinus n F b c)
      (range_spinMatrix_quadMinus hn hirr) k * g⁻¹)
    {m : ℕ} {k : spinGroup (quadMinus n F b c)} (hk : k ∈ stabEM (n := n) (b := b) (c := c) m)
    (Ag : StatedOmega (StatedQuadMinus n F b c)) (hAg : (QuotientGroup.mk Ag :
      StatedProj (StatedOmega (StatedQuadMinus n F b c))) = g)
    (A : StatedOmega (StatedQuadMinus n F b c))
    (hA : (QuotientGroup.mk A : StatedProj (StatedOmega (StatedQuadMinus n F b c))) = π' k) :
    ∀ w ∈ (eSpanM n (K := F) m).map (Matrix.mulVecLin
      ((Ag : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
      Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)),
      ((A : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
        Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *ᵥ w ∈
      (eSpanM n (K := F) m).map (Matrix.mulVecLin
        ((Ag : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
        Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)) := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
  rw [Matrix.mulVecLin_apply]
  have hek : (QuotientGroup.mk A : StatedProj (StatedOmega (StatedQuadMinus n F b c))) =
      QuotientGroup.mk (Ag * ⟨spinMatrix (quadMinus n F b c) k,
        spinMatrix_mem_of_range_eq _ (range_spinMatrix_quadMinus hn hirr) k⟩ * Ag⁻¹) := by
    rw [hA, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hAg, hπ' k,
      spinToStatedProj_apply]
  obtain ⟨d, hd⟩ := exists_smul_mulVec_of_mk_eq hek
  rw [hd]
  refine Submodule.smul_mem _ _ ⟨spinMatrix (quadMinus n F b c) k *ᵥ v, ?_, ?_⟩
  · rw [spinMatrix_mulVec]
    exact hk v hv
  · simp only [Matrix.mulVecLin_apply]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]
    congr 2
    rw [Subgroup.coe_inv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]

theorem eSpanM_zero : eSpanM n (K := F) 0 = ⊥ := by
  rw [eSpanM]
  have : {v : Vm n F | ∃ j : Fin (n - 1), j.val < 0 ∧ v = eVec n (K := F) j} = ∅ := by
    ext v; simp
  rw [this, Submodule.span_empty]

theorem eSpanM_succ {j : ℕ} (hj : j < n - 1) :
    eSpanM n (K := F) (j + 1) =
      eSpanM n (K := F) j ⊔ Submodule.span F {eVec n (K := F) ⟨j, hj⟩} := by
  rw [eSpanM, eSpanM, ← Submodule.span_union]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j', hj', rfl⟩
    by_cases h : j'.val < j
    · exact Or.inl ⟨j', h, rfl⟩
    · right
      have : j' = ⟨j, hj⟩ := Fin.ext (by show j'.val = j; omega)
      rw [this]
  · rintro (⟨j', hj', rfl⟩ | rfl)
    · exact ⟨j', by omega, rfl⟩
    · exact ⟨⟨j, hj⟩, by simp, rfl⟩

theorem quad_of_mem_eSpanM {m : ℕ} {v : Vm n F} (hv : v ∈ eSpanM n (K := F) m) :
    StatedQuadMinus n F b c v = 0 := by
  rw [mem_eSpanM_iff] at hv
  have h1 : ∀ i, v (.inr (.inl i)) = 0 := fun i => hv _ (fun k _ => by simp)
  have h2 : ∀ t, v (.inr (.inr t)) = 0 := fun t => hv _ (fun k _ => by simp)
  simp [StatedQuadMinus, h1, h2]

theorem quad_map_eSpanM {m : ℕ} (Ag : StatedOmega (StatedQuadMinus n F b c)) :
    ∀ w ∈ (eSpanM n (K := F) m).map (Matrix.mulVecLin
      ((Ag : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
      Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)),
      StatedQuadMinus n F b c w = 0 := by
  rintro _ ⟨v, hv, rfl⟩
  rw [Matrix.mulVecLin_apply, preserves_of_mem_statedOmega Ag.2]
  exact quad_of_mem_eSpanM hv

theorem finrank_map_eSpanM {m : ℕ} (hm : m ≤ n - 1)
    (Ag : StatedOmega (StatedQuadMinus n F b c)) :
    Module.finrank F ↥((eSpanM n (K := F) m).map (Matrix.mulVecLin
      ((Ag : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
      Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F))) = m := by
  have hAgunit : IsUnit ((Ag : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
      Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :=
    (Ag : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F).isUnit
  have hAginj : Function.Injective (Matrix.mulVecLin
      ((Ag : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
      Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)) :=
    Matrix.mulVec_injective_iff_isUnit.mpr hAgunit
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hAginj _)).symm.trans
    (finrank_eSpanM hm)

end Stab

end CFSG.HardMathSupport.Curtis.UnitaryLevi
