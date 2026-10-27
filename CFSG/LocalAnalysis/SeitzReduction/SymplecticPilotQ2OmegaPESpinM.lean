module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Universal.Spin.Twisted.Weyl
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartOne.CTP.SpinCenterEven

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup QuadraticMap Matrix CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

section Rho

variable {n : ℕ} {K : Type} [Field K] [Finite K] {b c : K} (hn : 4 ≤ n)
  (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

@[expose] noncomputable def peRhoM :
    spinGroup (quadMinus n K b c) →* StatedOmega (StatedQuadMinus n K b c) :=
  (spinMatrix (quadMinus n K b c)).codRestrict _
    (spinMatrix_mem_of_range_eq _ (range_spinMatrix_quadMinus hn hirr))

theorem peRhoM_mulVec (x : spinGroup (quadMinus n K b c))
    (w : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    (((peRhoM hn hirr x : StatedOmega (StatedQuadMinus n K b c)) :
      GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
        (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) *ᵥ w = spinAction (quadMinus n K b c) x w :=
  spinMatrix_mulVec _ x w

theorem peRhoM_surjective : Function.Surjective (peRhoM hn hirr) := by
  rintro ⟨A, hA⟩
  rw [← range_spinMatrix_quadMinus hn hirr] at hA
  obtain ⟨x, hx⟩ := hA
  exact ⟨x, Subtype.ext hx⟩

theorem peRhoM_injective [CharP K 2] : Function.Injective (peRhoM hn hirr) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have h1 : x ∈ (spinAction (quadMinus n K b c)).ker := by
    rw [MonoidHom.mem_ker]
    refine LinearEquiv.ext fun w => ?_
    rw [← peRhoM_mulVec hn hirr x w, hx]
    simp
  have h2 := ker_spinAction_le_center (quadMinus n K b c) h1
  rwa [CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot hn hirr] at h2

@[expose] noncomputable def peRhoMEquiv [CharP K 2] :
    spinGroup (quadMinus n K b c) ≃* StatedOmega (StatedQuadMinus n K b c) :=
  MulEquiv.ofBijective (peRhoM hn hirr) ⟨peRhoM_injective hn hirr, peRhoM_surjective hn hirr⟩

theorem peRhoMEquiv_apply [CharP K 2] (x : spinGroup (quadMinus n K b c)) :
    peRhoMEquiv hn hirr x = peRhoM hn hirr x := rfl

end Rho

section Pieces

variable {n : ℕ} {K : Type} [Field K] {b c : K}

variable (K b c) in
@[expose] def peSpinFixM (P : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) → Prop) :
    Subgroup (spinGroup (quadMinus n K b c)) where
  carrier := {x | ∀ w, P w → spinAction (quadMinus n K b c) x w = w}
  one_mem' := fun w _ => by simp
  mul_mem' := fun {x y} hx hy w hw => by
    rw [map_mul, LinearEquiv.mul_apply, hy w hw, hx w hw]
  inv_mem' := fun {x} hx w hw => by
    conv_lhs => rw [← hx w hw]
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl

@[expose] def peSuppM (J : Finset (Fin (n - 1))) : Finset (Fin (n - 1)) :=
  J.biUnion fun j => if h : j.val + 1 < n - 1 then {j, ⟨j.val + 1, h⟩} else {j}

@[expose] def PEMShort (J : Finset (Fin (n - 1))) : Prop := ∃ j ∈ J, ¬ j.val + 1 < n - 1

@[expose] def PEOffM (J : Finset (Fin (n - 1))) (w : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    Prop :=
  (∀ a ∈ peSuppM J, w (.inl a) = 0 ∧ w (.inr (.inl a)) = 0) ∧
    (PEMShort J → w (.inr (.inr 0)) = 0 ∧ w (.inr (.inr 1)) = 0)

theorem polar_minusVec_of_off {w : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K} {a : Fin (n - 1)}
    (h : w (.inl a) = 0 ∧ w (.inr (.inl a)) = 0) (s : Bool) :
    polar (quadMinus n K b c) w (minusVec n a s) = 0 := by
  cases s
  · rw [minusVec_false, fVec, polar_quadMinus_single_inr_inl]
    exact h.1
  · rw [minusVec_true, eVec, polar_quadMinus_single_inl]
    exact h.2

theorem polar_planeVec_of_off {w : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K}
    (h : w (.inr (.inr 0)) = 0 ∧ w (.inr (.inr 1)) = 0) (p : Fin 2 → K) :
    polar (quadMinus n K b c) w (planeVec n p) = 0 := by
  rw [polar_quadMinus]
  simp [planeVec, h.1, h.2]

variable (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

theorem rankOne_le_peSpinFixM (j : Fin (n - 1)) {J : Finset (Fin (n - 1))} (hj : j ∈ J) :
    CFSG.LieType.CurtisTits.rankOne (minusRootGroup n hirr) j ≤
      peSpinFixM K b c (PEOffM J) := by
  by_cases hlt : j.val + 1 < n - 1
  · have hjS : j ∈ peSuppM J := by
      simp only [peSuppM, Finset.mem_biUnion]
      exact ⟨j, hj, by simp [hlt]⟩
    have hj1S : (⟨j.val + 1, hlt⟩ : Fin (n - 1)) ∈ peSuppM J := by
      simp only [peSuppM, Finset.mem_biUnion]
      exact ⟨j, hj, by simp [hlt]⟩
    rw [CFSG.LieType.CurtisTits.rankOne, minusRootGroup_single_of_lt n hirr hlt,
      minusRootGroup_neg_single_of_lt n hirr hlt, sup_le_iff]
    constructor
    · rintro _ ⟨a, rfl⟩ w hw
      have ha : a = Multiplicative.ofAdd (Multiplicative.toAdd a) := rfl
      rw [ha]
      exact (minusFrame n b c).spinAction_longRoot_of_polar _ true false _
        (by rw [minusFrame_vec]; exact polar_minusVec_of_off (hw.1 j hjS) true)
        (by rw [minusFrame_vec]; exact polar_minusVec_of_off (hw.1 _ hj1S) false)
    · rintro _ ⟨a, rfl⟩ w hw
      have ha : a = Multiplicative.ofAdd (Multiplicative.toAdd a) := rfl
      rw [ha]
      exact (minusFrame n b c).spinAction_longRoot_of_polar _ true false _
        (by rw [minusFrame_vec]; exact polar_minusVec_of_off (hw.1 _ hj1S) true)
        (by rw [minusFrame_vec]; exact polar_minusVec_of_off (hw.1 j hjS) false)
  · have hjS : j ∈ peSuppM J := by
      simp only [peSuppM, Finset.mem_biUnion]
      exact ⟨j, hj, by simp [hlt]⟩
    have hsh : PEMShort J := ⟨j, hj, hlt⟩
    rw [rankOne_minusRootGroup_of_not_lt n hirr hlt, sup_le_iff]
    constructor
    · rintro _ ⟨p, rfl⟩ w hw
      have hp : p = Multiplicative.ofAdd (Multiplicative.toAdd p) := rfl
      rw [hp, ← twShortRoot_true]
      exact spinAction_twShortRoot_of_polar n hirr j true _
        (polar_minusVec_of_off (hw.1 j hjS) true) (polar_planeVec_of_off (hw.2 hsh) _)
    · rintro _ ⟨p, rfl⟩ w hw
      have hp : p = Multiplicative.ofAdd (Multiplicative.toAdd p) := rfl
      rw [hp, ← twShortRoot_false]
      exact spinAction_twShortRoot_of_polar n hirr j false _
        (polar_minusVec_of_off (hw.1 j hjS) false) (polar_planeVec_of_off (hw.2 hsh) _)

theorem levi_le_peSpinFixM (J : Finset (Fin (n - 1))) :
    CFSG.LieType.CurtisTits.levi (minusRootGroup n hirr) J ≤ peSpinFixM K b c (PEOffM J) :=
  iSup₂_le fun j hj => rankOne_le_peSpinFixM hirr j hj

theorem spinAction_leviM_of_peOff {J : {J : Finset (Fin (n - 1)) // J.card ≤ 2}}
    (x : (minusDatum n hirr).leviAmalgam J) {w : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K}
    (hw : PEOffM J.1 w) : spinAction (quadMinus n K b c) x w = w :=
  levi_le_peSpinFixM hirr J.1 x.2 w hw

end Pieces

section EichlerG

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] noncomputable def peEichG {u w a : V} (hu : Q u = 0) (huw : polar Q u w = 0)
    (hua : polar Q u a = 0) (hwa : polar Q w a = 0) (ha : IsUnit (Q a)) : spinGroup Q :=
  rootHom Q hu huw (one_add_smul_ι_mul_ι_mem_spinGroup Q hu huw hua hwa ha) (.ofAdd 1)

theorem spinAction_peEichG {u w a : V} (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0)
    (hua : polar Q u a = 0) (hwa : polar Q w a = 0) (ha : IsUnit (Q a)) (z : V) :
    spinAction Q (peEichG hu huw hua hwa ha) z = z + polar Q z u • w - polar Q z w • u := by
  rw [peEichG, spinAction_rootHom, one_smul, hw, zero_mul, zero_smul, sub_zero]

end EichlerG

section Short

variable {n : ℕ} {K : Type} [Field K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

variable (n) in
@[expose] noncomputable def peShortWord (i : Fin (n - 1)) : spinGroup (quadMinus n K b c) :=
  twShortRoot n hirr i true (.ofAdd planeOne) * twShortRoot n hirr i false (.ofAdd planeOne)

theorem peShortWord_mem_levi {i : Fin (n - 1)} (hi : ¬ i.val + 1 < n - 1)
    {J : Finset (Fin (n - 1))} (hJ : i ∈ J) :
    peShortWord n hirr i ∈ CFSG.LieType.CurtisTits.levi (minusRootGroup n hirr) J := by
  have h := CFSG.LieType.CurtisTits.rankOne_le_levi (minusRootGroup n hirr) hJ
  rw [rankOne_minusRootGroup_of_not_lt n hirr hi] at h
  exact mul_mem (h (mem_sup_left ⟨_, rfl⟩)) (h (mem_sup_right ⟨_, rfl⟩))

theorem minusWeyl_mem_levi {k : Fin (n - 1)} {J : Finset (Fin (n - 1))} (hk : k ∈ J) :
    minusWeyl n hirr k ∈ CFSG.LieType.CurtisTits.levi (minusRootGroup n hirr) J :=
  CFSG.LieType.CurtisTits.rankOne_le_levi (minusRootGroup n hirr) hk (minusDatum_n_mem n hirr k)

theorem spinAction_minusWeyl_planeVec {k : Fin (n - 1)} (hk : k.val + 1 < n - 1)
    (p : Fin 2 → K) :
    spinAction (quadMinus n K b c) (minusWeyl n hirr k) (planeVec n p) = planeVec n p := by
  rw [minusWeyl_of_lt n hirr hk]
  exact spinAction_longWeyl_planeVec n _ true false p

theorem spinAction_minusWeyl_minusVec [CharP K 2] {k : Fin (n - 1)} (hk : k.val + 1 < n - 1)
    (m : Fin (n - 1)) (s : Bool) :
    spinAction (quadMinus n K b c) (minusWeyl n hirr k) (minusVec n m s) =
      minusVec n (Equiv.swap k ⟨k.val + 1, hk⟩ m) s := by
  rw [minusWeyl_of_lt n hirr hk]
  have h := (minusFrame n b c).spinAction_longWeyl_vec (succ_ne_of_lt n hk) true false m s
  rw [minusFrame_vec] at h
  rw [h]
  have hsign : (longWeylSign k m : K) = 1 := by
    unfold longWeylSign
    split_ifs
    · exact CharTwo.neg_eq 1
    · rfl
  have hbool : longWeylBool k ⟨k.val + 1, hk⟩ true false m s = s := by
    unfold longWeylBool
    split_ifs <;> simp
  rw [hsign, hbool, one_smul]

end Short

section ShortAction

variable {n : ℕ} {K : Type} [Field K]

theorem pe_planeVec_planeOne :
    planeVec n (planeOne : Fin 2 → K) = Pi.single (.inr (.inr 0)) 1 := by
  funext t
  rcases t with t | t | t
  · simp [planeVec]
  · simp [planeVec]
  · fin_cases t <;> simp [planeVec, planeOne]

theorem pe_planeNorm_planeOne (b c : K) : planeNorm b c (planeOne : Fin 2 → K) = 1 := by
  simp [planeNorm, planeOne]

variable [CharP K 2] (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0)

theorem spinAction_peShortWord (i : Fin (n - 1)) (x : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    spinAction (quadMinus n K 1 1) (peShortWord n hirr i) x =
      x + (x (.inl i) + x (.inr (.inr 1))) •
          (Pi.single (.inl i) 1 + Pi.single (.inr (.inl i)) 1) +
        (x (.inr (.inl i)) + x (.inr (.inr 1))) •
          (Pi.single (.inl i) 1 + Pi.single (.inr (.inr 0)) 1) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [peShortWord, map_mul, LinearEquiv.mul_apply, spinAction_twShortRoot n hirr i false,
    spinAction_twShortRoot n hirr i true]
  simp only [minusVec_true, minusVec_false, eVec, fVec, polar_quadMinus_single_inl,
    polar_quadMinus_single_inr_inl, pe_planeNorm_planeOne, pe_planeVec_planeOne,
    polar_quadMinus_single_inr_inr_zero]
  funext t
  rcases t with t | t | t
  · by_cases hti : t = i
    · subst hti
      simp
      linear_combination (-(x (.inl t) + x (.inr (.inr 1)) + x (.inr (.inl t)))) * h2
    · simp [hti]
  · by_cases hti : t = i
    · subst hti
      simp
      linear_combination (-(x (.inr (.inr 0)) + x (.inr (.inr 1)) + x (.inl t))) * h2
    · simp [hti]
  · fin_cases t
    · simp
      linear_combination (-(x (.inr (.inr 0)) + x (.inr (.inr 1)))) * h2
    · simp

end ShortAction

end CFSG.SeitzReduction.SymplecticPilot
