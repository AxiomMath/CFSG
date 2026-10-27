module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNeighbourStandardAniso
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotF6Fix

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (minusIndexEquiv coordinateQuadMinus regular_coordinateQuadMinus)

section Norm

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem card_anisoNormOne {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card {x : K × K // x.1 ^ 2 + b * x.1 * x.2 + c * x.2 ^ 2 = 1} = Nat.card K + 1 := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨N, hNdef⟩ : ∃ N : K × K → K, N = fun x => x.1 ^ 2 + b * x.1 * x.2 + c * x.2 ^ 2 :=
    ⟨_, rfl⟩
  have hNapp : ∀ x : K × K, N x = x.1 ^ 2 + b * x.1 * x.2 + c * x.2 ^ 2 := fun x => by rw [hNdef]
  have hN0 : ∀ x : K × K, N x = 0 → x = 0 := by
    rintro ⟨p, s⟩ hx
    rw [hNapp] at hx
    by_cases hs : s = 0
    · subst hs
      have hp : p = 0 := by
        have : p ^ 2 = 0 := by linear_combination hx
        exact pow_eq_zero_iff two_ne_zero |>.mp this
      rw [hp]
      rfl
    · exfalso
      apply hirr (p / s)
      field_simp
      linear_combination hx
  have hNscale : ∀ (t : K) (x : K × K), N (t • x) = t ^ 2 * N x := by
    rintro t ⟨p, s⟩
    rw [hNapp, hNapp]
    simp only [Prod.smul_mk, smul_eq_mul]
    ring
  have hfib : ∀ t : K, t ≠ 0 →
      (Finset.univ.filter (fun x => N x = t)).card =
        (Finset.univ.filter (fun x => N x = 1)).card := by
    intro t ht
    obtain ⟨r, hr⟩ := isSquare_of_charTwo' t
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hr
      exact ht hr
    refine Finset.card_nbij' (fun x => r⁻¹ • x) (fun x => r • x) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
      rw [hNscale, hx, hr]
      field_simp
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
      rw [hNscale, hx, hr]
      ring
    · intro x _
      simp only [smul_smul, mul_inv_cancel₀ hr0, one_smul]
    · intro x _
      simp only [smul_smul, inv_mul_cancel₀ hr0, one_smul]
  have hsum := Finset.card_eq_sum_card_fiberwise (f := N) (s := Finset.univ)
    (t := Finset.univ) (fun x _ => Finset.mem_univ _)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0)] at hsum
  have h0 : (Finset.univ.filter (fun x => N x = 0)).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨0, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨hN0 x, fun hx => by rw [hx, hNapp]; simp⟩
  rw [h0, Finset.sum_congr rfl fun t ht => hfib t (Finset.ne_of_mem_erase ht), Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, Finset.card_univ,
    Fintype.card_prod, smul_eq_mul] at hsum
  have hcard : Nat.card {x : K × K // x.1 ^ 2 + b * x.1 * x.2 + c * x.2 ^ 2 = 1} =
      (Finset.univ.filter (fun x => N x = 1)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp [hNapp]
  rw [hcard, Nat.card_eq_fintype_card]
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card K = m + 2 := ⟨Fintype.card K - 2, by omega⟩
  rw [hm] at hsum ⊢
  have h1 : (m + 1) * (Finset.univ.filter (fun x => N x = 1)).card = (m + 1) * (m + 2 + 1) := by
    have : m + 2 - 1 = m + 1 := by omega
    rw [this] at hsum
    nlinarith [hsum]
  exact Nat.eq_of_mul_eq_mul_left (by omega) h1

end Norm

section Card

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a a' : Fin d} {b c : K}

theorem IsAnisoCoord.card_anisoRotSub (h : IsAnisoCoord Q a a' b c) :
    Nat.card (anisoRotSub h.ne b c) = Nat.card K + 1 := by
  rw [← card_anisoNormOne h.irr]
  symm
  refine Nat.card_eq_of_bijective
    (fun x => ⟨anisoRotEquiv h.ne b c x.2, anisoRotEquiv_mem_anisoRotSub h.ne x.2⟩) ⟨?_, ?_⟩
  · rintro ⟨⟨p, s⟩, hx⟩ ⟨⟨p', s'⟩, hx'⟩ hxx'
    have h1 := congrArg (fun g : anisoRotSub h.ne b c =>
      (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) (Pi.single a 1)) hxx'
    simp only [anisoRotEquiv_apply, anisoRotLin_single_left h.ne] at h1
    have ha := congrFun h1 a
    have ha' := congrFun h1 a'
    simp [Pi.single_eq_of_ne h.ne, Pi.single_eq_of_ne h.ne.symm] at ha ha'
    apply Subtype.ext
    simp only [Prod.mk.injEq]
    exact ⟨ha, ha'⟩
  · rintro ⟨g, p, s, hN, hg⟩
    refine ⟨⟨(p, s), hN⟩, Subtype.ext (LinearEquiv.ext fun v => ?_)⟩
    rw [hg]
    rfl

theorem IsAnisoCoord.card_anisoTorusOf (h : IsAnisoCoord Q a a' b c)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    Nat.card (anisoTorusOf Q h.ne b c) = Nat.card K + 1 := by
  rw [anisoTorusOf, card_map_of_injective (projHom_injective h.exists_ne_zero),
    ← h.card_anisoRotSub]
  exact Nat.card_congr (subgroupOfEquivOfLe (h.anisoRotSub_le_orthDerived hQ hT)).toEquiv

theorem card_anisoTorus {n : ℕ} (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (anisoTorus (K := K) (by omega : 1 ≤ n) b c) = Nat.card K + 1 := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus n K b c hn hirr
  exact (isAnisoCoord_coordinateQuadMinus (by omega) hirr).card_anisoTorusOf hQ hT

end Card

section Fix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a a' : Fin d} {b c : K}

theorem IsAnisoCoord.fixSpace_comap_anisoTorusOf (h : IsAnisoCoord Q a a' b c)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    fixSpace ((anisoTorusOf Q h.ne b c).comap (projHom Q)) = perpSub K a a' := by
  have hb := h.b_ne_zero
  have hc := h.c_ne_zero
  ext v
  constructor
  · intro hv
    have hN₀ := h.norm_rot_one
    have hmem : (⟨anisoRotEquiv h.ne b c hN₀, h.anisoRotSub_le_orthDerived hQ hT
        (anisoRotEquiv_mem_anisoRotSub h.ne hN₀)⟩ : orthDerived Q) ∈
        (anisoTorusOf Q h.ne b c).comap (projHom Q) :=
      ⟨_, anisoRotEquiv_mem_anisoRotSub h.ne hN₀, rfl⟩
    have h1 := hv _ hmem
    change anisoRotLin a a' b c 1 (b / c) v = v at h1
    have ha := congrFun h1 a
    have ha' := congrFun h1 a'
    rw [anisoRotLin_apply_left] at ha
    rw [anisoRotLin_apply_right h.ne] at ha'
    have hva' : v a' = 0 := by
      have : b * v a' = 0 := by
        have e : c * (b / c) = b := by field_simp
        linear_combination ha - (v a') * e
      exact (mul_eq_zero.mp this).resolve_left hb
    refine ⟨?_, hva'⟩
    rw [hva', mul_zero, add_zero] at ha'
    have : b / c * v a = 0 := by linear_combination ha'
    exact (mul_eq_zero.mp this).resolve_left (div_ne_zero hb hc)
  · intro hv g hg
    obtain ⟨y, hy, hyg⟩ := hg
    rw [projHom_injective h.exists_ne_zero hyg] at hy
    obtain ⟨p, s, -, hgp⟩ := mem_subgroupOf.mp hy
    rw [hgp]
    exact anisoRotLin_apply_of_mem_perpSub p s hv

theorem IsAnisoCoord.card_fixSpace_comap_anisoTorusOf (h : IsAnisoCoord Q a a' b c)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    Nat.card (fixSpace ((anisoTorusOf Q h.ne b c).comap (projHom Q))) = Nat.card K ^ (d - 2) := by
  rw [h.fixSpace_comap_anisoTorusOf hQ hT, card_perpSub h.ne]

theorem fixSpace_comap_anisoTorus {n : ℕ} (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    fixSpace ((anisoTorus (K := K) (by omega : 1 ≤ n) b c).comap
      (projHom (coordinateQuadMinus n K (by omega) b c))) =
      perpSub K (anisoCoordLeft (by omega : 1 ≤ n)) (anisoCoordRight (by omega : 1 ≤ n)) := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus n K b c hn hirr
  exact (isAnisoCoord_coordinateQuadMinus (by omega) hirr).fixSpace_comap_anisoTorusOf hQ hT

end Fix

end CFSG.SeitzReduction.OmegaPilot
