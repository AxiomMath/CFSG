module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryInvariant
public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData

public section

namespace CFSG.AGLEmbedding.ToralCensus

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary Matrix Polynomial
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem aeval_toLin_X_pow_sub_C {ι : Type} [Fintype ι] [DecidableEq ι] (t : GL ι K) {m : ℕ}
    {c : Kˣ} (ht : t ^ m = GeneralLinearGroup.scalar ι c) :
    aeval (GeneralLinearGroup.toLin t : Module.End K (ι → K)) (X ^ m - C (c : K)) = 0 := by
  have h1 : ((GeneralLinearGroup.toLin t : Module.End K (ι → K))) ^ m =
      algebraMap K (Module.End K (ι → K)) (c : K) := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ht]
    ext v i
    simp [GeneralLinearGroup.coe_toLin, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.mulVec_diagonal]
  rw [map_sub, map_pow, aeval_X, aeval_C, h1, sub_self]

theorem squarefree_minpoly_toLin_of_pow_eq_scalar {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : GL ι K) {m : ℕ} (hm : (m : K) ≠ 0) {c : Kˣ} (ht : t ^ m = GeneralLinearGroup.scalar ι c) :
    Squarefree (minpoly K (GeneralLinearGroup.toLin t : Module.End K (ι → K))) := by
  have hsep : (X ^ m - C (c : K)).Separable := separable_X_pow_sub_C _ hm c.ne_zero
  exact (hsep.squarefree).squarefree_of_dvd (minpoly.dvd K _ (aeval_toLin_X_pow_sub_C t ht))

theorem hypPrimaryData (h : UnitaryFieldData p f K) (t : hypSU h r ε)
    (hsq : Squarefree (minpoly K
      (GeneralLinearGroup.toLin (t : GL (HypIndex r ε) K) : Module.End K (HypIndex r ε → K)))) :
    UnitaryPrimaryData h.bar (hypForm h r ε) (GeneralLinearGroup.toLin (t : GL (HypIndex r ε) K)) :=
  ⟨fun c => h.bar_bar c, hypForm_isSymm h, hypForm_separatingLeft h,
    sesqSpecialUnitaryGroup_le _ ((toLin_mem_sesqSpecialUnitaryGroup_iff h _ _).mpr t.2), hsq⟩

theorem toLin_mem_sesqSpecialUnitaryGroup_hyp (h : UnitaryFieldData p f K) (t : hypSU h r ε) :
    GeneralLinearGroup.toLin (t : GL (HypIndex r ε) K) ∈
      sesqSpecialUnitaryGroup (hypForm h r ε) :=
  (toLin_mem_sesqSpecialUnitaryGroup_iff h _ _).mpr t.2

theorem forall_commute_of_hyp (h : UnitaryFieldData p f K) {t : hypSU h r ε}
    {W : Submodule K (HypIndex r ε → K)}
    (hC : ∀ y : hypSU h r ε, Commute y t → ∀ w ∈ W,
      ((y : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ w ∈ W) :
    ∀ g : LinearMap.GeneralLinearGroup K (HypIndex r ε → K),
      g ∈ sesqSpecialUnitaryGroup (hypForm h r ε) →
      Commute (g : Module.End K (HypIndex r ε → K))
        (GeneralLinearGroup.toLin (t : GL (HypIndex r ε) K) : Module.End K (HypIndex r ε → K)) →
      ∀ w ∈ W, (g : Module.End K (HypIndex r ε → K)) w ∈ W := by
  intro g hg hgx w hw
  set A := GeneralLinearGroup.toLin.symm g with hAdef
  have hgA : g = GeneralLinearGroup.toLin A := (MulEquiv.apply_symm_apply _ _).symm
  have hA : A ∈ hypSU h r ε := by
    rw [hgA] at hg
    exact (toLin_mem_sesqSpecialUnitaryGroup_iff h _ A).mp hg
  have hcomm : Commute (⟨A, hA⟩ : hypSU h r ε) t := by
    have h1 : GeneralLinearGroup.toLin (A * (t : GL (HypIndex r ε) K)) =
        GeneralLinearGroup.toLin ((t : GL (HypIndex r ε) K) * A) := by
      rw [map_mul, map_mul, ← hgA]
      exact Units.ext hgx.eq
    exact Subtype.ext (GeneralLinearGroup.toLin.injective h1)
  have := hC ⟨A, hA⟩ hcomm w hw
  rw [hgA, GeneralLinearGroup.coe_toLin]
  exact this

variable [Finite K]

theorem eq_bot_of_forall_dualPoly_eq (h : UnitaryFieldData p f K) {t : hypSU h r ε}
    (hsq : Squarefree (minpoly K
      (GeneralLinearGroup.toLin (t : GL (HypIndex r ε) K) : Module.End K (HypIndex r ε → K))))
    (hself : ∀ a ∈ primaryFactors
      (GeneralLinearGroup.toLin (t : GL (HypIndex r ε) K) : Module.End K (HypIndex r ε → K)),
      dualPoly h.bar a = a)
    {W : Submodule K (HypIndex r ε → K)} (hWt : ∀ v ∈ W, ∀ w ∈ W, hypForm h r ε v w = 0)
    (hC : ∀ y : hypSU h r ε, Commute y t → ∀ w ∈ W,
      ((y : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ w ∈ W) :
    W = ⊥ := by
  have H := hypPrimaryData h t hsq
  have hxS := toLin_mem_sesqSpecialUnitaryGroup_hyp h t
  have hC' := forall_commute_of_hyp h hC
  have hWx := hC' _ hxS (Commute.refl _)
  refine (ToralCensus.eq_iSup_primaryComponent_of_forall_commute h H
    (mem_sesqSpecialUnitaryGroup.mp hxS).2 hWt hC').trans
      (eq_bot_iff.mpr (iSup₂_le fun a ha => iSup_le fun hle => ?_))
  have hbot := ToralCensus.inf_primaryComponent_eq_bot_of_selfDual h H hWt hC' hWx ha
    (hself a ha)
  rw [inf_eq_right.mpr hle] at hbot
  exact hbot.le

end CFSG.AGLEmbedding.ToralCensus
