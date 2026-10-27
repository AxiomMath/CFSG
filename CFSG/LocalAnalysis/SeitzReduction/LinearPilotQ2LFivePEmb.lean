module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFivePRad

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial

variable {n m : ℕ} {K : Type*} [Field K]

theorem reindexSpecialLinear_transvection {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) {i j : ι} (hij : i ≠ j) (c : K) :
    reindexSpecialLinear e (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection (e.injective.ne hij) c := by
  ext k l
  change reindex e e ((1 : Matrix ι ι K) + single i j c) k l =
    ((1 : Matrix κ κ K) + single (e i) (e j) c) k l
  simp [Matrix.one_apply, Matrix.single_apply, Equiv.eq_symm_apply]

variable [CharP K 2]

@[expose] noncomputable def embTwo (I : Finset (Fin n)) (σ : Fin m ≃ I) :
    SpecialLinearGroup (Fin m) (ZMod 2) →* LinearFlag.projectiveSL n K :=
  ((LinearFlag.proj n K).comp (blockEmbed I)).comp
    ((reindexSpecialLinear σ).toMonoidHom.comp
      (SpecialLinearGroup.map (ZMod.castHom (dvd_refl 2) K)))

theorem embTwo_injective {I : Finset (Fin n)} (σ : Fin m ≃ I) (hI : I.card < n) :
    Function.Injective (embTwo (K := K) I σ) :=
  (proj_comp_blockEmbed_injective hI).comp ((reindexSpecialLinear σ).injective.comp
    (specialLinearGroup_map_injective_of_injective (ZMod.castHom (dvd_refl 2) K).injective))

theorem embTwo_mem_blockSL {I : Finset (Fin n)} (σ : Fin m ≃ I)
    (g : SpecialLinearGroup (Fin m) (ZMod 2)) : embTwo (K := K) I σ g ∈ blockSL I := by
  rw [blockSL_eq_range]
  exact ⟨_, rfl⟩

theorem embTwo_transvection {I : Finset (Fin n)} (σ : Fin m ≃ I) {p q : Fin m} (hpq : p ≠ q) :
    embTwo (K := K) I σ (SpecialLinearGroup.transvection hpq 1) =
      xab (show (σ p : Fin n) ≠ σ q from fun h => hpq (σ.injective (Subtype.ext h))) 1 := by
  rw [embTwo, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
    Matrix.SpecialLinearGroup.map_transvection, map_one, MulEquiv.coe_toMonoidHom,
    reindexSpecialLinear_transvection, blockEmbed_transvection]
  rfl

theorem embTwo_uRoot {I : Finset (Fin n)} (σ : Fin 4 ≃ I) (k : Fin 6) :
    embTwo (K := K) I σ (uRoot k) =
      xab (show (σ (uRow k) : Fin n) ≠ σ (uCol k) from
        fun h => uRow_ne_uCol k (σ.injective (Subtype.ext h))) 1 := by
  rw [uRoot_eq_transvection, embTwo_transvection]

end CFSG.SeitzReduction.LinearPilot
