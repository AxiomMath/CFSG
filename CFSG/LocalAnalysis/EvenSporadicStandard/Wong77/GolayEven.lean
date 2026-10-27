module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.Golay

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Wong77.Module

open CFSG.Blueprint

abbrev GolayEvenMod : Type := ↥golayEven

theorem natCard_golayEvenMod : Nat.card GolayEvenMod = 2 ^ 11 := natCard_golayEven

@[expose] def evenEquiv (g : NativeSporadic.Carrier .M23) : GolayEvenMod ≃ₗ[ZMod 2] GolayEvenMod :=
  LinearEquiv.ofSubmodules (wordRep g) golayEven golayEven
    (map_permLin_eq (golayEven_mem_permStab (toPerm_mem g)))

@[expose] def golayRep : NativeSporadic.Carrier .M23 →* (GolayEvenMod ≃ₗ[ZMod 2] GolayEvenMod) where
  toFun := evenEquiv
  map_one' := LinearEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => Subtype.ext rfl

theorem golayRep_apply (g : NativeSporadic.Carrier .M23) (v : GolayEvenMod) :
    ((golayRep g v : GolayEvenMod) : Word) = wordRep g v := rfl

@[expose] def sepMask : Fin 8 → ℕ :=
  ![4961400, 2534159, 1531270, 8012529, 2739884, 1438291, 8191385, 7419887]

theorem sepMask_mem (k : Fin 8) : wordOfNat (sepMask k) ∈ golayEven := by
  rw [mem_golayEven_iff, mem_golayCode_iff]
  revert k
  decide

theorem sepMask_separates : ∀ i j : Fin 23, i ≠ j →
    ∃ k, wordOfNat (sepMask k) i = 1 ∧ wordOfNat (sepMask k) j = 0 := by
  decide

theorem golayRep_injective : Function.Injective golayRep := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hfix : ∀ i, toPerm g i = i := by
    intro i
    by_contra hne
    obtain ⟨k, hk1, hk0⟩ := sepMask_separates i (toPerm g i) (Ne.symm hne)
    have h := congrArg (fun f => ((f ⟨wordOfNat (sepMask k), sepMask_mem k⟩ : GolayEvenMod) : Word)
      (toPerm g i)) hg
    simp only [golayRep_apply, wordRep_apply] at h
    change wordOfNat (sepMask k) ((toPerm g).symm (toPerm g i)) = wordOfNat (sepMask k) (toPerm g i)
      at h
    rw [Equiv.symm_apply_apply, hk1, hk0] at h
    exact one_ne_zero h
  exact toPerm_injective (Equiv.ext hfix)

end CFSG.EvenSporadicStandard.Wong77.Module
