module

public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.CentralExt.FieldFour
  Matrix
open scoped Pointwise

theorem exists_conj_le_sylow {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    (A : Subgroup G) (hA : IsPGroup 2 A) : ∃ g : G, A.map (MulAut.conj g).toMonoidHom ≤ P := by
  obtain ⟨Q, hQ⟩ := hA.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨g, ?_⟩
  have h2 : ((g • Q : Sylow 2 G) : Subgroup G) =
      (Q : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  rw [hg] at h2
  rw [h2]
  exact Subgroup.map_mono hQ

variable (K : Type) [Field K] [Finite K] [CharP K 2]

abbrev Uad (τ : Tag) : Subgroup (adjointGroup τ K) := (posUnipotent τ K).subgroupOf (adjointGroup τ K)

theorem Uad_sylow (τ : Tag) : IsPGroup 2 (Uad K τ) ∧ ¬ 2 ∣ (Uad K τ).index :=
  CFSG.LieType.Chevalley.isPGroup_and_not_dvd_index 2 posUnipotent_le_adjointGroup card_posUnipotent

theorem adjoint_conj_into_U (τ : Tag) (A : Subgroup (adjointGroup τ K)) (hA : IsPGroup 2 A) :
    ∃ g : adjointGroup τ K, A.map (MulAut.conj g).toMonoidHom ≤ Uad K τ := by
  have : Finite (adjointGroup τ K) := by
    have := finite_modGL (τ := τ) (K := K)
    infer_instance
  obtain ⟨hp, hi⟩ := Uad_sylow K τ
  exact exists_conj_le_sylow (hp.toSylow hi) A hA

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
