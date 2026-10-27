module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusGen
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotRootCentralizerPerfect

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap
open CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)

section Frame

variable {K : Type} [Field K] {d m : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a b : Fin m → Fin d}

theorem eichler_eq_eichler_neg_of_singular {u w : Fin d → K} (hu : Q u = 0) (hw : Q w = 0)
    (huw : polar Q u w = 0) : eichler Q u w = eichler Q w (-u) := by
  have hwu : polar Q w (-u) = 0 := by rw [polar_neg_right, polar_comm, huw, neg_zero]
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_apply hu huw, eichler_apply hw hwu, hw, QuadraticMap.map_neg, hu, polar_neg_right]
  module

theorem IsHypFrame.eichler_right_left (h : IsHypFrame Q a b) {i j : Fin m} (hij : i ≠ j) (c : K) :
    eichler Q (Pi.single (b j) 1) (c • Pi.single (a i) 1) = frameRootElt Q a b i j (-c) := by
  have hpol : polar Q (Pi.single (b j) 1) (c • Pi.single (a i) 1) = 0 := by
    rw [(h.hyp j).polar_right, Pi.smul_apply,
      Pi.single_eq_of_ne (fun e => hij (h.left_injective e).symm), smul_zero]
  have hQ : Q (c • Pi.single (a i) 1) = 0 := by
    rw [QuadraticMap.map_smul, (h.hyp i).map_left, smul_zero]
  rw [eichler_eq_eichler_neg_of_singular (h.hyp j).map_right hQ hpol, eichler_smul_left,
    frameRootElt, smul_neg, ← neg_smul]

variable [CharP K 2]

theorem IsHypFrame.eichler_flip_apply (h : IsHypFrame Q a b) {z : Fin d → K} (hz : Q z = 1)
    (hza : ∀ k, z (a k) = 0) (hzb : ∀ k, z (b k) = 0) (i : Fin m) :
    Q (coordFrameVec a b i true + coordFrameVec a b i false + z) = 0 ∧
      polar Q (coordFrameVec a b i true + coordFrameVec a b i false + z) z = 0 ∧
      (∀ r, eichler Q (coordFrameVec a b i true + coordFrameVec a b i false + z) z
        (coordFrameVec a b i r) = coordFrameVec a b i (!r)) ∧
      ∀ j, j ≠ i → ∀ r, eichler Q (coordFrameVec a b i true + coordFrameVec a b i false + z) z
        (coordFrameVec a b j r) = coordFrameVec a b j r := by
  have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
  have hneg : ∀ v : Fin d → K, -v = v := fun v => by
    funext j
    simp [CharTwo.neg_eq]
  set e := coordFrameVec (K := K) a b i true with he
  set f := coordFrameVec (K := K) a b i false with hf
  have hef : polar Q e f = 1 := by
    rw [he, hf, h.polar_coordFrameVec]
    simp
  have hez : polar Q e z = 0 := by rw [he, h.polar_coordFrameVec]; exact hzb i
  have hfz : polar Q f z = 0 := by rw [hf, h.polar_coordFrameVec]; exact hza i
  have hQe : Q e = 0 := (h.hyp i).map_left
  have hQf : Q f = 0 := (h.hyp i).map_right
  have hzz : polar Q z z = 0 := by rw [polar_self, hz, two_smul, CharTwo.add_self_eq_zero]
  have hu : Q (e + f + z) = 0 := by
    rw [QuadraticMap.map_add Q, QuadraticMap.map_add Q, hQe, hQf, hz, polar_add_left, hef, hez, hfz]
    linear_combination htwo
  have huz : polar Q (e + f + z) z = 0 := by
    rw [polar_add_left, polar_add_left, hez, hfz, hzz, add_zero, add_zero]
  refine ⟨hu, huz, fun r => ?_, fun j hji r => ?_⟩
  · rw [eichler_apply hu huz, hz]
    cases r
    ·
      have h1 : polar Q f (e + f + z) = 1 := by
        rw [polar_add_right, polar_add_right, polar_comm, hef, polar_self, hQf, smul_zero, hfz,
          add_zero, add_zero]
      change f + polar Q f (e + f + z) • z - (polar Q f z + 1 * polar Q f (e + f + z)) •
        (e + f + z) = e
      rw [h1, hfz, one_smul, zero_add, one_mul, one_smul]
      rw [show f + z - (e + f + z) = -e by abel, hneg]
    ·
      have h1 : polar Q e (e + f + z) = 1 := by
        rw [polar_add_right, polar_add_right, hef, polar_self, hQe, smul_zero, hez, zero_add,
          add_zero]
      change e + polar Q e (e + f + z) • z - (polar Q e z + 1 * polar Q e (e + f + z)) •
        (e + f + z) = f
      rw [h1, hez, one_smul, zero_add, one_mul, one_smul]
      rw [show e + z - (e + f + z) = -f by abel, hneg]
  · have hv := h.coordFrameVec_vanish (k := i) (l := j) (Ne.symm hji)
    refine eichler_apply_of_polar_eq_zero ?_ ?_
    · rw [h.polar_coordFrameVec]
      cases r
      · simp only [Bool.cond_false, Pi.add_apply, he, hf, (hv true).1, (hv false).1, hza j,
          add_zero]
      · simp only [Bool.cond_true, Pi.add_apply, he, hf, (hv true).2, (hv false).2, hzb j,
          add_zero]
    · rw [h.polar_coordFrameVec]
      cases r
      · exact hza j
      · exact hzb j

theorem IsHypFrame.pairSwap_conj_frameRootElt (h : IsHypFrame Q a b) {p p' : Fin m}
    (hpp : p ≠ p') (r s : Fin m) (c : K) :
    pairSwap Q (a p) (b p) (a p') (b p') * frameRootElt Q a b r s c *
        (pairSwap Q (a p) (b p) (a p') (b p'))⁻¹ =
      frameRootElt Q a b (Equiv.swap p p' r) (Equiv.swap p p' s) c := by
  rw [frameRootElt, eichler_conj (show pairSwap Q (a p) (b p) (a p') (b p') ∈
      TauCeti.QuadraticMap.orthogonalGroup Q from eichler_mem_orthogonalGroup Q _ _), map_smul,
    show (Pi.single (a r) 1 : Fin d → K) = coordFrameVec a b r true from rfl,
    show (Pi.single (b s) 1 : Fin d → K) = coordFrameVec a b s false from rfl,
    h.pairSwap_coordFrameVec hpp, h.pairSwap_coordFrameVec hpp]
  rfl

theorem IsHypFrame.elementaryGroup_le_of_rootElt (h : IsHypFrame Q a b) {z : Fin d → K}
    (hz : Q z = 1) (hza : ∀ k, z (a k) = 0) (hzb : ∀ k, z (b k) = 0)
    (hrest : ∀ v : Fin d → K, (∀ k, v (a k) = 0 ∧ v (b k) = 0) → Q v = 0 → v = 0)
    {H : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K))}
    (hroot : ∀ p q : Fin m, p ≠ q → ∀ c : K, frameRootElt Q a b p q c ∈ H) (k₀ : Fin m)
    (hplane : ∀ u w : Fin d → K, (∀ k, k ≠ k₀ → u (a k) = 0 ∧ u (b k) = 0) →
      (∀ k, k ≠ k₀ → w (a k) = 0 ∧ w (b k) = 0) → eichler Q u w ∈ H) :
    elementaryGroup Q ≤ H := by
  have hconj : ∀ g ∈ H, g ∈ TauCeti.QuadraticMap.orthogonalGroup Q → ∀ u w,
      eichler Q u w ∈ H → eichler Q (g u) (g w) ∈ H := fun g hg hgO u w huw => by
    rw [← eichler_conj hgO]
    exact mul_mem (mul_mem hg huw) (inv_mem hg)
  have hswap : ∀ p q : Fin m, p ≠ q → pairSwap Q (a p) (b p) (a q) (b q) ∈ H := fun p q hpq => by
    rw [h.pairSwap_eq_frameRootElt hpq]
    exact mul_mem (mul_mem (hroot q p (Ne.symm hpq) 1) (hroot p q hpq 1))
      (hroot q p (Ne.symm hpq) 1)
  have hswapO : ∀ p q : Fin m, pairSwap Q (a p) (b p) (a q) (b q) ∈
      TauCeti.QuadraticMap.orthogonalGroup Q := fun p q => eichler_mem_orthogonalGroup Q _ _
  have hvan : ∀ r : Bool, ∀ k, k ≠ k₀ →
      coordFrameVec (K := K) a b k₀ r (a k) = 0 ∧ coordFrameVec (K := K) a b k₀ r (b k) = 0 :=
    fun r k hk => h.coordFrameVec_vanish (Ne.symm hk) r
  obtain ⟨-, -, -, -⟩ := h.eichler_flip_apply hz hza hzb k₀
  have hflip : ∀ i : Fin m,
      eichler Q (coordFrameVec a b i true + coordFrameVec a b i false + z) z ∈ H := by
    have h0 : eichler Q (coordFrameVec a b k₀ true + coordFrameVec a b k₀ false + z) z ∈ H := by
      refine hplane _ _ (fun k hk => ?_) (fun k hk => ⟨hza k, hzb k⟩)
      simp only [Pi.add_apply, (hvan true k hk).1, (hvan false k hk).1, (hvan true k hk).2,
        (hvan false k hk).2, hza k, hzb k, add_zero, and_self]
    intro i
    by_cases hi : i = k₀
    · rw [hi]
      exact h0
    have h1 := hconj _ (hswap k₀ i (Ne.symm hi)) (hswapO k₀ i) _ _ h0
    have hz' : pairSwap Q (a k₀) (b k₀) (a i) (b i) z = z :=
      h.pairSwap_apply_of_vanish (hza k₀) (hzb k₀) (hza i) (hzb i)
    rwa [map_add, map_add, h.pairSwap_coordFrameVec (Ne.symm hi),
      h.pairSwap_coordFrameVec (Ne.symm hi), Equiv.swap_apply_left, hz'] at h1
  have hflipO : ∀ i : Fin m, eichler Q (coordFrameVec a b i true + coordFrameVec a b i false + z)
      z ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun i => eichler_mem_orthogonalGroup Q _ _
  set F := h.toHypFrame z (by rw [hz]; exact isUnit_one) hza hzb
  refine F.elementaryGroup_le (fun {i j} hij s t c => ?_) (fun i s v hv => ?_)
    (fun v hv hv0 => hrest v (h.apply_eq_zero_of_polar hv) hv0)
  · simp only [F, IsHypFrame.toHypFrame_vec]
    have hmixed : ∀ t : Bool, ∀ c : K,
        eichler Q (coordFrameVec a b j t) (c • coordFrameVec a b i (!t)) ∈ H := by
      intro t c
      cases t
      · exact (h.eichler_right_left hij c).symm ▸ hroot i j hij (-c)
      · exact hroot j i (Ne.symm hij) c
    by_cases hst : s = !t
    · rw [hst]
      exact hmixed t c
    · have hs : s = t := by
        revert hst
        cases s <;> cases t <;> decide
      obtain ⟨-, -, hwi, hwj⟩ := h.eichler_flip_apply hz hza hzb i
      have h1 := hconj _ (hflip i) (hflipO i) _ _ (hmixed t c)
      rw [hs]
      rwa [map_smul, hwi, Bool.not_not, hwj j (Ne.symm hij)] at h1
  · simp only [F, IsHypFrame.toHypFrame_vec] at hv ⊢
    have hv' := h.apply_eq_zero_of_polar hv
    have h0 : eichler Q (coordFrameVec a b k₀ s) v ∈ H :=
      hplane _ _ (hvan s) (fun k _ => hv' k)
    by_cases hi : i = k₀
    · rw [hi]
      exact h0
    have h1 := hconj _ (hswap k₀ i (Ne.symm hi)) (hswapO k₀ i) _ _ h0
    rwa [h.pairSwap_coordFrameVec (Ne.symm hi), Equiv.swap_apply_left,
      h.pairSwap_apply_of_vanish (hv' k₀).1 (hv' k₀).2 (hv' i).1 (hv' i).2] at h1

end Frame

section Three

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a b : Fin 3 → Fin d}

theorem IsHypFrame.eq_top_of_frameLeviProj_le_three (h : IsHypFrame Q a b)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {z : Fin d → K} (hz : Q z = 1) (hza : ∀ k, z (a k) = 0) (hzb : ∀ k, z (b k) = 0)
    (hrest : ∀ v : Fin d → K, (∀ k, v (a k) = 0 ∧ v (b k) = 0) → Q v = 0 → v = 0)
    {T : Subgroup (matrixProjectiveDerived Q)} (h01 : frameLeviProj Q a b 0 1 ≤ T)
    (h12 : frameLeviProj Q a b 1 2 ≤ T) (hR : stabPairsBar Q (a 0) (b 0) (a 1) (b 1) ≤ T) :
    T = ⊤ := by
  set H : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
    (T.comap (projHom Q)).map (orthDerived Q).subtype with hHdef
  have hmemH : ∀ x (hx : x ∈ orthDerived Q), projHom Q ⟨x, hx⟩ ∈ T → x ∈ H :=
    fun x hx hxT => ⟨⟨x, hx⟩, hxT, rfl⟩
  have hlevi : ∀ p q : Fin 3, frameLeviProj Q a b p q ≤ T → ∀ x : K,
      frameRootElt Q a b p q x ∈ H ∧ frameRootElt Q a b q p x ∈ H := by
    intro p q hpq x
    exact ⟨hmemH _ (eichler_mem_orthDerived hQ hT _ _) (hpq ⟨⟨_, eichler_mem_orthDerived hQ hT _ _⟩,
        mem_subgroupOf.2 (frameRootElt_mem_frameLeviSL_right p q x), rfl⟩),
      hmemH _ (eichler_mem_orthDerived hQ hT _ _) (hpq ⟨⟨_, eichler_mem_orthDerived hQ hT _ _⟩,
        mem_subgroupOf.2 (frameRootElt_mem_frameLeviSL_left p q x), rfl⟩)⟩
  have h12' : (1 : Fin 3) ≠ 2 := by decide
  have hs12 : pairSwap Q (a 1) (b 1) (a 2) (b 2) ∈ H := by
    rw [h.pairSwap_eq_frameRootElt h12']
    exact mul_mem (mul_mem (hlevi 1 2 h12 1).2 (hlevi 1 2 h12 1).1) (hlevi 1 2 h12 1).2
  have hsw0 : Equiv.swap (1 : Fin 3) 2 0 = 0 := by decide
  have h02 : ∀ x : K, frameRootElt Q a b 0 2 x ∈ H ∧ frameRootElt Q a b 2 0 x ∈ H := by
    intro x
    have e1 := h.pairSwap_conj_frameRootElt h12' 0 1 x
    have e2 := h.pairSwap_conj_frameRootElt h12' 1 0 x
    rw [hsw0, Equiv.swap_apply_left] at e1 e2
    exact ⟨e1 ▸ mul_mem (mul_mem hs12 (hlevi 0 1 h01 x).1) (inv_mem hs12),
      e2 ▸ mul_mem (mul_mem hs12 (hlevi 0 1 h01 x).2) (inv_mem hs12)⟩
  have hroot : ∀ p q : Fin 3, p ≠ q → ∀ x : K, frameRootElt Q a b p q x ∈ H := by
    intro p q hpq x
    fin_cases p <;> fin_cases q
    · exact absurd rfl hpq
    · exact (hlevi 0 1 h01 x).1
    · exact (h02 x).1
    · exact (hlevi 0 1 h01 x).2
    · exact absurd rfl hpq
    · exact (hlevi 1 2 h12 x).1
    · exact (h02 x).2
    · exact (hlevi 1 2 h12 x).2
    · exact absurd rfl hpq
  have hplane : ∀ u w : Fin d → K, (∀ k, k ≠ 2 → u (a k) = 0 ∧ u (b k) = 0) →
      (∀ k, k ≠ 2 → w (a k) = 0 ∧ w (b k) = 0) → eichler Q u w ∈ H := by
    intro u w hu hw
    have hu0 := hu 0 (by decide)
    have hu1 := hu 1 (by decide)
    have hw0 := hw 0 (by decide)
    have hw1 := hw 1 (by decide)
    refine hmemH _ (eichler_mem_orthDerived hQ hT u w) (hR ⟨⟨_, eichler_mem_orthDerived hQ hT u w⟩,
      mem_subgroupOf.2 ⟨mem_stabSub.2 ⟨?_, ?_⟩, mem_stabSub.2 ⟨?_, ?_⟩⟩, rfl⟩)
    · exact eichler_apply_of_polar_eq_zero (by rw [(h.hyp 0).polar_left, hu0.2])
        (by rw [(h.hyp 0).polar_left, hw0.2])
    · exact eichler_apply_of_polar_eq_zero (by rw [(h.hyp 0).polar_right, hu0.1])
        (by rw [(h.hyp 0).polar_right, hw0.1])
    · exact eichler_apply_of_polar_eq_zero (by rw [(h.hyp 1).polar_left, hu1.2])
        (by rw [(h.hyp 1).polar_left, hw1.2])
    · exact eichler_apply_of_polar_eq_zero (by rw [(h.hyp 1).polar_right, hu1.1])
        (by rw [(h.hyp 1).polar_right, hw1.1])
  have hEH : elementaryGroup Q ≤ H :=
    h.elementaryGroup_le_of_rootElt hz hza hzb hrest hroot 2 hplane
  have hΩ : orthDerived Q = elementaryGroup Q :=
    (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hQ hT).1
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := projHom_surjective Q x
  have hy : (y : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ elementaryGroup Q := hΩ ▸ y.2
  obtain ⟨y', hy', hyy⟩ := hEH hy
  have : y' = y := Subtype.ext hyy
  rw [← this]
  exact hy'

end Three

section Minus

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (minusIndexEquiv
  coordinateQuadMinus regular_coordinateQuadMinus)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_top_of_frameLeviProj_le_four {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {T : Subgroup (matrixProjectiveDerived (coordinateQuadMinus (2 + 2) K (by omega) b c))}
    (h01 : frameLeviProj (coordinateQuadMinus (2 + 2) K (by omega) b c)
      (minusFrameLeft (by omega)) (minusFrameRight (by omega)) 0 1 ≤ T)
    (h12 : frameLeviProj (coordinateQuadMinus (2 + 2) K (by omega) b c)
      (minusFrameLeft (by omega)) (minusFrameRight (by omega)) 1 2 ≤ T)
    (hR : stabPairsBar (coordinateQuadMinus (2 + 2) K (by omega) b c)
      (minusIndexEquiv (2 + 2) (by omega) (.inl 0))
      (minusIndexEquiv (2 + 2) (by omega) (.inr (.inl 0)))
      (minusIndexEquiv (2 + 2) (by omega) (.inl 1))
      (minusIndexEquiv (2 + 2) (by omega) (.inr (.inl 1))) ≤ T) :
    T = ⊤ := by
  have hn1 : 1 ≤ 2 + 2 := by omega
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus (2 + 2) K b c (by omega) hirr
  exact (isHypFrame_minus K hn1 b c).eq_top_of_frameLeviProj_le_three hQ hT
    (coordinateQuadMinus_minusAnisoVec hn1 b c) (minusAnisoVec_frameLeft hn1)
    (minusAnisoVec_frameRight hn1) (eq_zero_of_frame_vanish_minus hn1 hirr) h01 h12 hR

end Minus

end CFSG.SeitzReduction.OmegaPilot
