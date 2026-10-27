module

public import CFSG.FeitThompson.Representations.InductionIntegerIsometryTISupport
public import CFSG.FeitThompson.Representations.RectangleDifferencesGramMatrix
public import CFSG.FeitThompson.Representations.RealBridgeRemainderProjectionBound
public import CFSG.FeitThompson.Representations.RectangleDifferencesBasisSupportedFunctions
public import CFSG.FeitThompson.Representations.InducedIrreducibleNormOrbitFormula
public import CFSG.FeitThompson.Representations.CyclicTIIsometryMixedSetValues

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G] {W W1 W2 : Subgroup G}

theorem resClassFun_one (H : Subgroup G) : resClassFun H (1 : G → ℂ) = 1 :=
  funext fun x => resClassFun_apply H 1 x

namespace IsCyclicTIPair

theorem prodCharAlpha_mem_dadeZDomain (h : IsCyclicTIPair W W1 W2) {lam : ↥W1 → ℂ}
    {mu : ↥W2 → ℂ} (hlam : lam ∈ Irr ↥W1) (hmu : mu ∈ Irr ↥W2) :
    h.prodCharAlpha lam mu ∈ dadeZDomain W (cyclicTIDiff W W1 W2) :=
  mem_dadeZDomain.2 ⟨h.prodCharAlpha_mem_virtualChars hlam hmu,
    (mem_dadeDomain.1 (h.prodCharAlpha_mem_dadeDomain hlam hmu)).2⟩

noncomputable def prodCharBeta (h : IsCyclicTIPair W W1 W2) [Fintype G]
    (lam : ↥W1 → ℂ) (mu : ↥W2 → ℂ) : G → ℂ :=
  indClassFun W (h.prodCharAlpha lam mu) - 1

theorem prodCharBeta_eq (h : IsCyclicTIPair W W1 W2) [Fintype G]
    (lam : ↥W1 → ℂ) (mu : ↥W2 → ℂ) :
    h.prodCharBeta lam mu = indClassFun W (h.prodCharAlpha lam mu) - 1 := (rfl)

theorem prodCharBeta_mem_classFun [Fintype G] (h : IsCyclicTIPair W W1 W2)
    (lam : ↥W1 → ℂ) (mu : ↥W2 → ℂ) : h.prodCharBeta lam mu ∈ classFun G := by
  rw [prodCharBeta_eq]
  exact sub_mem (indClassFun_mem_classFun W _) (one_mem_classFun G)

theorem prodCharBeta_apply_one [Fintype G] (h : IsCyclicTIPair W W1 W2) {lam : ↥W1 → ℂ}
    {mu : ↥W2 → ℂ} (hlam : lam ∈ Irr ↥W1) (hmu : mu ∈ Irr ↥W2) :
    h.prodCharBeta lam mu 1 = -1 := by
  rw [prodCharBeta_eq, Pi.sub_apply, indClassFun_one, h.prodCharAlpha_one hlam hmu]
  simp

theorem prodCharBeta_mem_virtualChars [Fintype G] (h : IsCyclicTIPair W W1 W2) {lam : ↥W1 → ℂ}
    {mu : ↥W2 → ℂ} (hlam : lam ∈ Irr ↥W1) (hmu : mu ∈ Irr ↥W2) :
    h.prodCharBeta lam mu ∈ virtualChars G := by
  rw [prodCharBeta_eq]
  exact sub_mem
    (h.isTIWithNormalizer.indClassFun_mem_virtualChars (h.prodCharAlpha_mem_dadeZDomain hlam hmu))
    (Irr_subset_virtualChars one_mem_Irr)

theorem cfInner_indClassFun_prodCharAlpha_one [Fintype G]
    (h : IsCyclicTIPair W W1 W2) {i : Irr ↥W1} {j : Irr ↥W2}
    (hi : i ≠ principalIrr ↥W1) (hj : j ≠ principalIrr ↥W2) :
    cfInner (indClassFun W (h.prodCharAlpha (i : ↥W1 → ℂ) (j : ↥W2 → ℂ))) (1 : G → ℂ) = 1 := by
  have : Fintype ↥W := Fintype.ofFinite _
  rw [cfInner_indClassFun W _ (one_mem_classFun G), resClassFun_one]
  exact h.cfInner_prodCharAlpha_one hi hj

theorem cfInner_prodCharBeta_one [Fintype G]
    (h : IsCyclicTIPair W W1 W2) {i : Irr ↥W1} {j : Irr ↥W2}
    (hi : i ≠ principalIrr ↥W1) (hj : j ≠ principalIrr ↥W2) :
    cfInner (h.prodCharBeta (i : ↥W1 → ℂ) (j : ↥W2 → ℂ)) (1 : G → ℂ) = 0 := by
  rw [prodCharBeta_eq, cfInner_sub_left, h.cfInner_indClassFun_prodCharAlpha_one hi hj,
    cfInner_one_one, sub_self]

theorem cfInner_prodCharBeta_eq_sub [Fintype G] [Fintype ↥W]
    (h : IsCyclicTIPair W W1 W2) {i k : Irr ↥W1} {j l : Irr ↥W2}
    (hi : i ≠ principalIrr ↥W1) (hk : k ≠ principalIrr ↥W1)
    (hj : j ≠ principalIrr ↥W2) (hl : l ≠ principalIrr ↥W2) :
    cfInner (h.prodCharBeta (i : ↥W1 → ℂ) (j : ↥W2 → ℂ))
        (h.prodCharBeta (k : ↥W1 → ℂ) (l : ↥W2 → ℂ)) =
      cfInner (h.prodCharAlpha (i : ↥W1 → ℂ) (j : ↥W2 → ℂ))
        (h.prodCharAlpha (k : ↥W1 → ℂ) (l : ↥W2 → ℂ)) - 1 := by
  have hiso := h.isTIWithNormalizer.cfInner_indClassFun
    (h.prodCharAlpha_mem_dadeDomain i.2 j.2) (h.prodCharAlpha_mem_dadeDomain k.2 l.2)
  have h1 : cfInner (1 : G → ℂ)
      (indClassFun W (h.prodCharAlpha (k : ↥W1 → ℂ) (l : ↥W2 → ℂ))) = 1 := by
    rw [← conj_cfInner, h.cfInner_indClassFun_prodCharAlpha_one hk hl, map_one]
  rw [prodCharBeta_eq, prodCharBeta_eq, cfInner_sub_left, cfInner_sub_right, cfInner_sub_right,
    hiso, h.cfInner_indClassFun_prodCharAlpha_one hi hj, h1, cfInner_one_one]
  ring

open scoped Classical in
theorem cfInner_prodCharBeta [Fintype G]
    (h : IsCyclicTIPair W W1 W2) {i k : Irr ↥W1} {j l : Irr ↥W2}
    (hi : i ≠ principalIrr ↥W1) (hk : k ≠ principalIrr ↥W1)
    (hj : j ≠ principalIrr ↥W2) (hl : l ≠ principalIrr ↥W2) :
    cfInner (h.prodCharBeta (i : ↥W1 → ℂ) (j : ↥W2 → ℂ))
        (h.prodCharBeta (k : ↥W1 → ℂ) (l : ↥W2 → ℂ)) =
      (if i = k then 1 else 0) + (if j = l then 1 else 0) +
        (if i = k then 1 else 0) * (if j = l then 1 else 0) := by
  have : Fintype ↥W := Fintype.ofFinite _
  rw [h.cfInner_prodCharBeta_eq_sub hi hk hj hl, h.cfInner_prodCharAlpha hi hk hj hl]
  split_ifs <;> ring

theorem cfInner_self_prodCharBeta [Fintype G]
    (h : IsCyclicTIPair W W1 W2) {i : Irr ↥W1} {j : Irr ↥W2}
    (hi : i ≠ principalIrr ↥W1) (hj : j ≠ principalIrr ↥W2) :
    cfInner (h.prodCharBeta (i : ↥W1 → ℂ) (j : ↥W2 → ℂ))
      (h.prodCharBeta (i : ↥W1 → ℂ) (j : ↥W2 → ℂ)) = 3 := by
  classical
  rw [h.cfInner_prodCharBeta hi hi hj hj]
  norm_num

end IsCyclicTIPair

end CFSG.FeitThompson
