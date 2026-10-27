module

public import CFSG.LieType.SeitzGeneration.OmegaF2.BridgeCore

public section

namespace CFSG.LieType.SeitzGeneration.OmegaF2

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.CTP
  CFSG.LieType.SeitzGeneration.RootPairOrth Matrix

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

variable {P P' : HypPair Q}

private theorem neg_eq_self_char2 [CharP K 2] (v : V) : -v = v := by
  rw [neg_eq_iff_add_eq_zero, ← two_smul K v, CharTwo.two_eq_zero, zero_smul]

theorem quadEmb_E00 : quadEmb P P' !![1, 0; 0, 0] = P.e := by
  simp [quadEmb]

theorem quadEmb_E01 [CharP K 2] : quadEmb P P' !![0, 1; 0, 0] = P'.e := by
  simp [quadEmb, neg_eq_self_char2 (K := K)]

theorem quadEmb_t_row [CharP K 2] (t a₁ a₂ : K) :
    quadEmb P P' !![t * a₁, t * a₂; 0, 0] = t • (a₁ • P.e + a₂ • P'.e) := by
  simp [quadEmb, smul_add, smul_smul, smul_neg, neg_eq_self_char2 (K := K)]

theorem theta_zero_u2 [CharP K 2] (h : P.Orth P') (r : V) (t : K) :
    eichler Q r (quadEmb P P' 0) * quadHom h (u2 t) = eichler Q P.e (t • P'.e) := by
  rw [map_zero, eichler_zero_right, one_mul, quadHom_u2, CharTwo.neg_eq]

theorem theta_zero_l2 (h : P.Orth P') (r : V) (s : K) :
    eichler Q r (quadEmb P P' 0) * quadHom h (l2 s) = eichler Q P.f (s • P'.f) := by
  rw [map_zero, eichler_zero_right, one_mul, quadHom_l2]

theorem eichler_e_eq_theta [CharP K 2] (h : P.Orth P') {r : V} (hr : PerpData P P' r) (α β : K) :
    eichler Q P.e (r + α • P.e + β • P'.e) =
      eichler Q r (quadEmb P P' !![1, 0; 0, 0]) * quadHom h (u2 β) := by
  have hxr : polar Q P.e r = 0 := by rw [polar_comm]; exact hr.e
  have hxα : polar Q P.e (α • P.e) = 0 := by rw [polar_smul_right_eq, P.polar_ee, mul_zero]
  have hxβ : polar Q P.e (β • P'.e) = 0 := by rw [polar_smul_right_eq, h.ee, mul_zero]
  have hxa : polar Q P.e (r + α • P.e) = 0 := by rw [polar_add_right, hxr, hxα, add_zero]
  have hα1 : eichler Q P.e (α • P.e) = 1 := by
    have h0 := eichler_add_smul_self P.Q_e (0 : V) α
    rwa [zero_add, eichler_zero_right] at h0
  rw [quadEmb_E00, quadHom_u2, CharTwo.neg_eq, ← eichler_mul hxa hxβ, ← eichler_mul hxr hxα, hα1,
    mul_one, ← eichler_swap_char2 P.Q_e hr.Q_r hxr]

theorem eichler_e'_eq_theta [CharP K 2] (h : P.Orth P') {r : V} (hr : PerpData P P' r) (α β : K) :
    eichler Q P'.e (r + α • P.e + β • P'.e) =
      eichler Q r (quadEmb P P' !![0, 1; 0, 0]) * quadHom h (u2 α) := by
  have hyr : polar Q P'.e r = 0 := by rw [polar_comm]; exact hr.e'
  have hyα : polar Q P'.e (α • P.e) = 0 := by
    rw [polar_smul_right_eq, polar_comm, h.ee, mul_zero]
  have hyβ : polar Q P'.e (β • P'.e) = 0 := by rw [polar_smul_right_eq, P'.polar_ee, mul_zero]
  have hya : polar Q P'.e (r + α • P.e) = 0 := by rw [polar_add_right, hyr, hyα, add_zero]
  have hβ1 : eichler Q P'.e (β • P'.e) = 1 := by
    have h0 := eichler_add_smul_self P'.Q_e (0 : V) β
    rwa [zero_add, eichler_zero_right] at h0
  have hQα : Q (α • P.e) = 0 := by rw [map_smul_eq_sq, P.Q_e, mul_zero]
  have hyαx : eichler Q P'.e (α • P.e) = eichler Q P.e (α • P'.e) :=
    (eichler_swap_char2 P'.Q_e hQα hyα).symm.trans (eichler_smul_left α P.e P'.e)
  rw [quadEmb_E01, quadHom_u2, CharTwo.neg_eq, ← eichler_mul hya hyβ, ← eichler_mul hyr hyα, hβ1,
    mul_one, hyαx, ← eichler_swap_char2 P'.Q_e hr.Q_r hyr]

end CFSG.LieType.SeitzGeneration.OmegaF2
