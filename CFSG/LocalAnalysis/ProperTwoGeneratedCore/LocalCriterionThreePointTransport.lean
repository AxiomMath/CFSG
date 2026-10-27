module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylowCounting

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]

theorem rightCosetStabilizer_right_translate (H : Subgroup G)
    (a : rightCosetSpace H) (g : G) :
    rightConjugate (rightCosetStabilizer H a) g =
      rightCosetStabilizer H (rightCosetTranslate H a g) := by
  ext x
  rw [mem_right_conjugate_iff, mem_rightCosetStabilizer_iff, mem_rightCosetStabilizer_iff]
  constructor
  · intro hx
    calc
      rightCosetTranslate H (rightCosetTranslate H a g) x =
          rightCosetTranslate H a (g * x) := rightCosetTranslate_mul H a g x
      _ = rightCosetTranslate H (rightCosetTranslate H a (g * x * g⁻¹)) g := by
        rw [rightCosetTranslate_mul]
        simp only [mul_assoc, inv_mul_cancel, mul_one]
      _ = rightCosetTranslate H a g := by rw [hx]
  · intro hx
    have hback := congrArg (fun b : rightCosetSpace H => rightCosetTranslate H b g⁻¹) hx
    calc
      rightCosetTranslate H a (g * x * g⁻¹) =
          rightCosetTranslate H (rightCosetTranslate H (rightCosetTranslate H a g) x) g⁻¹ := by
        rw [rightCosetTranslate_mul, rightCosetTranslate_mul, mul_assoc]
      _ = rightCosetTranslate H (rightCosetTranslate H a g) g⁻¹ := hback
      _ = a := by rw [rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one]

theorem right_pair_flip_returns
    {H : Subgroup G} {z t : G} (hz : orderOf z = 2)
    {beta : rightCosetSpace H} (ht : t ∈ rightPairFlipFiber H z beta) :
    rightCosetTranslate H beta t = rightCosetMk H 1 := by
  have htorder := order_two_of_mem_pointClass hz ht.1
  have htt : t * t = 1 := by
    have hpow := pow_orderOf_eq_one t
    rwa [htorder, pow_two] at hpow
  rw [← ht.2, rightCosetTranslate_mul, htt, rightCosetTranslate_one]

theorem opposite_pair_flip_transport
    {H : Subgroup G} {z t : G} (h : InvolutionPointLocalEmbedding H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    (ht : t ∈ rightPairFlipFiber H z beta) :
    let delta := rightCosetTranslate H (rightCosetTranslate H beta z) t
    delta ≠ rightCosetMk H 1 ∧
      rightConjugate (oppositePairStabilizer H z beta) t = pairPointStabilizer H delta := by
  dsimp only
  have htreturn := right_pair_flip_returns h.distinguished_order ht
  constructor
  · intro heq
    have hsame : rightCosetTranslate H (rightCosetTranslate H beta z) t =
        rightCosetTranslate H beta t := heq.trans htreturn.symm
    exact (triple_point_cosets_distinct h hbeta).2.1
      (rightCosetTranslate_injective H t hsame)
  · change (rightCosetStabilizer H beta ⊓
        rightCosetStabilizer H (rightCosetTranslate H beta z)).map
        (MulAut.conj t⁻¹).toMonoidHom = _
    rw [Subgroup.map_inf _ _ _ (MulAut.conj t⁻¹).injective]
    change rightConjugate (rightCosetStabilizer H beta) t ⊓
        rightConjugate (rightCosetStabilizer H (rightCosetTranslate H beta z)) t = _
    rw [rightCosetStabilizer_right_translate, rightCosetStabilizer_right_translate, htreturn]
    rfl

theorem normalized_subgroup_le_right_conjugate_overgroup
    (P F : Subgroup G) (t : G) (hPF : P ≤ F)
    (htP : t ∈ Subgroup.normalizer (P : Set G)) : P ≤ rightConjugate F t := by
  have hconj : rightConjugate P t = P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (P : Set G)).inv_mem htP)
  have hmap := Subgroup.map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) hPF
  change rightConjugate P t ≤ rightConjugate F t at hmap
  rwa [hconj] at hmap

theorem full_motion_opposite_pair_flip_contains_triple_sylow [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (p : ℕ) (hp : p.Prime) (P : Subgroup G)
    (hPF : P ≤ oppositePairStabilizer H z beta)
    (hzP : z ∈ Subgroup.normalizer (P : Set G))
    (htP : t ∈ Subgroup.normalizer (P : Set G)) (hP : IsPGroup p P)
    (hmotion : Nat.card (conjugacyWithin P z) =
      p ^ (Nat.card (conjugacyWithin H z)).factorization p) :
    let delta := rightCosetTranslate H (rightCosetTranslate H beta z) t
    delta ≠ rightCosetMk H 1 ∧
      rightConjugate (oppositePairStabilizer H z beta) t = pairPointStabilizer H delta ∧
      ∃ R : Sylow p (pairPointStabilizer H delta),
        P ≤ (R : Subgroup (pairPointStabilizer H delta)).map (pairPointStabilizer H delta).subtype ∧
          (R : Subgroup (pairPointStabilizer H delta)).map (pairPointStabilizer H delta).subtype ≤
            triplePointStabilizer H z delta := by
  obtain ⟨hdelta, hpair⟩ := opposite_pair_flip_transport h hbeta ht
  dsimp only
  refine ⟨hdelta, hpair, ?_⟩
  have hPpair : P ≤ pairPointStabilizer H (rightCosetTranslate H (rightCosetTranslate H beta z) t) := by
    rw [← hpair]
    exact normalized_subgroup_le_right_conjugate_overgroup P _ t hPF htP
  obtain ⟨R, hPR, hRtriple, _⟩ := triple_motion_threshold_contains_pair_sylow
    h S hzS hzcenter _ hdelta p hp P hPpair hP hzP hmotion.ge
  exact ⟨R, hPR, hRtriple⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
