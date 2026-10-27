module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.FrameIsometry
public import CFSG.RankThree.PartOne.S11d.OrthModels
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairSpinPlus
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairSpinMinus

public noncomputable section

open Module QuadraticMap Subgroup Matrix
open scoped MatrixGroups

namespace CFSG.ClassicalGroups.Orthogonal

open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.PartOne (orthDerivedEquiv linConj linConj_apply)

variable {K U V H : Type} [Field K] [CharP K 2] [Finite K]
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Group H]
  {Q : QuadraticForm K U} {Q' : QuadraticForm K V}

theorem exists_vector_cover_position
    (ρ : H →* (U ≃ₗ[K] U)) (hρinj : Function.Injective ρ)
    (hρrange : ρ.range = orthDerived Q)
    (R : Subgroup H) (F : Frame Q) (hR : R.map ρ = F.La.range)
    (e : Q.IsometryEquiv Q') (hQ' : (polarBilin Q').Nondegenerate) (F' : Frame Q') :
    ∃ lambda : H ≃* ↥(orthDerived Q'),
      R.map lambda.toMonoidHom = F'.La.range.subgroupOf (orthDerived Q') := by
  obtain ⟨e', _hincl, hLa⟩ := exists_matched_isometry e hQ' F F'
  let lambda : H ≃* ↥(orthDerived Q') :=
    (MonoidHom.ofInjective hρinj).trans
      ((MulEquiv.subgroupCongr hρrange).trans (orthDerivedEquiv e'))
  have hcoe (a : H) : (lambda a : V ≃ₗ[K] V) = linConj e'.toLinearEquiv (ρ a) := by
    let u : ↥(orthDerived Q) :=
      MulEquiv.subgroupCongr hρrange (MonoidHom.ofInjective hρinj a)
    have hu : (u : U ≃ₗ[K] U) = ρ a := by
      calc
        _ = (MonoidHom.ofInjective hρinj a : U ≃ₗ[K] U) :=
          MulEquiv.subgroupCongr_apply hρrange _
        _ = ρ a := MonoidHom.ofInjective_apply hρinj
    change (MulEquiv.subgroupCongr (CFSG.RankThree.PartOne.map_orthDerived_linConj e')
      ((linConj e'.toLinearEquiv).subgroupMap (orthDerived Q) u) : V ≃ₗ[K] V) = _
    calc
      _ = ((linConj e'.toLinearEquiv).subgroupMap (orthDerived Q) u : V ≃ₗ[K] V) :=
        MulEquiv.subgroupCongr_apply _ _
      _ = linConj e'.toLinearEquiv (u : U ≃ₗ[K] U) :=
        MulEquiv.coe_subgroupMap_apply _ _ _
      _ = _ := by rw [hu]
  have hact (A : SL(2, K)) : linConj e'.toLinearEquiv (F.La A) = F'.La A := by
    apply LinearEquiv.ext
    intro v
    rw [linConj_apply, ← LinearEquiv.autCongr_apply_apply]
    exact DFunLike.congr_fun (hLa A) v
  refine ⟨lambda, ?_⟩
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    have hmem : ρ a ∈ F.La.range := hR ▸ (mem_map_of_mem ρ ha)
    obtain ⟨A, hA⟩ := hmem
    change (lambda a : V ≃ₗ[K] V) ∈ F'.La.range
    refine ⟨A, ?_⟩
    rw [hcoe, ← hA, hact]
  · intro hz
    change (z : V ≃ₗ[K] V) ∈ F'.La.range at hz
    obtain ⟨A, hA⟩ := hz
    have hmem : F.La A ∈ R.map ρ := hR.symm ▸ MonoidHom.mem_range.mpr ⟨A, rfl⟩
    obtain ⟨a, ha, hρa⟩ := hmem
    refine ⟨a, ha, ?_⟩
    apply Subtype.ext
    change (lambda a : V ≃ₗ[K] V) = (z : V ≃ₗ[K] V)
    rw [hcoe, hρa, hact]
    exact hA

end CFSG.ClassicalGroups.Orthogonal

namespace CFSG.LieType.Universal.Spin

open CFSG.ClassicalGroups.Orthogonal

open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin
open CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.CurtisTits
open CFSG.GroupTheory.WeirSylow
open CFSG.RankThree.Classical2 (orthDerived)

variable {K V : Type} [Field K] [CharP K 2] [Finite K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {n : ℕ}

theorem exists_spinPlus_root_position (hn : 4 ≤ n)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank K V = 2 * n)
    (hplus : IsPlusType Q) (F : Frame Q) :
    ∃ lambda : spinGroup (quadPlus n K) ≃* ↥(orthDerived Q),
      (rankOne (plusDatum n K (le_trans (by decide) hn)).rootGroup
        (⟨0, by omega⟩ : Fin n)).map
        lambda.toMonoidHom = F.La.range.subgroupOf (orthDerived Q) := by
  let hn3 : 3 ≤ n := le_trans (by decide) hn
  let i : Fin n := ⟨0, by omega⟩
  have hinj : Function.Injective (spinAction (quadPlus n K)) := by
    let := isCentral_cliffordAlgebra_quadPlus K n
    exact (MonoidHom.ker_eq_bot_iff _).mp
      (ker_spinAction_eq_bot_of_isCentral (quadPlus n K) CharTwo.two_eq_zero)
  have hrange : (spinAction (quadPlus n K)).range = orthDerived (quadPlus n K) :=
    range_spinAction_quadPlus_eq_commutator hn3
  let F0 := (plusFrame n K hn3).toFrame (rootIdxD_ne n (by omega) i) true (rootSignD n i)
  have hR := map_rankOne_plus (K := K) hn3 i
  obtain ⟨e⟩ := nonempty_isometry_quadPlus hQ hdim hplus
  exact exists_vector_cover_position (spinAction (quadPlus n K)) hinj hrange
    (rankOne (plusDatum n K hn3).rootGroup i) F0 hR e.symm hQ F

theorem exists_spinMinus_root_position (hn : 4 ≤ n)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank K V = 2 * n)
    (hminus : ¬ IsPlusType Q) (F : Frame Q) :
    ∃ lambda : spinGroup (quadMinus n K b c) ≃* ↥(orthDerived Q),
      (rankOne (minusDatum n hirr).rootGroup (⟨0, by omega⟩ : Fin (n - 1))).map
        lambda.toMonoidHom = F.La.range.subgroupOf (orthDerived Q) := by
  let i : Fin (n - 1) := ⟨0, by omega⟩
  have hi : i.val + 1 < n - 1 := by dsimp [i]; omega
  have hinj : Function.Injective (spinAction (quadMinus n K b c)) := by
    let := isCentral_cliffordAlgebra_quadMinus n b c hirr
    exact (MonoidHom.ker_eq_bot_iff _).mp
      (ker_spinAction_eq_bot_of_isCentral (quadMinus n K b c) CharTwo.two_eq_zero)
  have hrange : (spinAction (quadMinus n K b c)).range = orthDerived (quadMinus n K b c) :=
    range_spinAction_quadMinus_eq_commutator hn hirr
  let F0 := (minusFrame n b c).toHypFrame.toFrame (succ_ne_of_lt n hi) true false
  have hR := map_rankOne_minus hirr hi
  obtain ⟨e⟩ := nonempty_isometry_of_not_isPlusType hQ (le_trans (by decide) hn) hdim hminus hirr
  exact exists_vector_cover_position (spinAction (quadMinus n K b c)) hinj hrange
    (rankOne (minusDatum n hirr).rootGroup i) F0 hR e.symm hQ F

end CFSG.LieType.Universal.Spin

end
