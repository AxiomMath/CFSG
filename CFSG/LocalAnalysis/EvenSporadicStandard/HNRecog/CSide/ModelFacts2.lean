module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.ModelIota
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.ModelDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.ModelCheckDefs
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

private def cSideOrb0 : Set V0 := {M | M ≠ 0 ∧ det0 M = 0}

private def cSideOrb1 : Set V0 := {M | det0 M = 1}

private def cSideOrbSet (i : Fin 2) : Set V0 :=
  if i = 0 then cSideOrb0 else cSideOrb1

private lemma cSideOrbSet_zero : cSideOrbSet 0 = cSideOrb0 := by
  unfold cSideOrbSet
  rw [if_pos rfl]

private lemma cSideOrbSet_one : cSideOrbSet 1 = cSideOrb1 := by
  unfold cSideOrbSet
  rw [if_neg (by decide)]

private lemma sigma0_symm_apply (X : SL2 × SL2) (M : V0) :
    sigma0 (iota.symm X.1, iota.symm X.2) M = actFun X M := by
  rw [sigma0_apply, show (iota (iota.symm X.1), iota (iota.symm X.2)) = X by
    exact Prod.ext (iota.apply_symm_apply X.1) (iota.apply_symm_apply X.2)]

private lemma cSideOrb0_disjoint_cSideOrb1 : Disjoint cSideOrb0 cSideOrb1 := by
  rw [Set.disjoint_left]
  intro M hM hM1
  have hM' : M ≠ 0 ∧ det0 M = 0 := hM
  have hM1' : det0 M = 1 := hM1
  exact zero_ne_one (hM'.2.symm.trans hM1')

private lemma cSideOrb0_card (h4d : cSideK4d) : Nat.card cSideOrb0 = 75 := by
  have h : Nat.card {M : V0 // M ≠ 0 ∧ det0 M = 0} = 75 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact h4d.1
  exact h

private lemma cSideOrb1_card (h4d : cSideK4d) : Nat.card cSideOrb1 = 60 := by
  have h : Nat.card {M : V0 // det0 M = 1} = 60 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact h4d.2
  exact h

theorem cSideOrbits_sigma0 (h : cSideModelProp) : CSideOrbits q0 sigma0 := by
  classical
  have h4a : cSideK4a := h.2.2.2.1.1
  have h4b : cSideK4b := h.2.2.2.1.2.1
  have h4c : cSideK4c := h.2.2.2.1.2.2.1
  have h4d : cSideK4d := h.2.2.2.1.2.2.2
  refine ⟨cSideOrbSet, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    rw [Fin.exists_fin_two, cSideOrbSet_zero, cSideOrbSet_one]
    change (v ≠ 0 ∧ q0Fun v = 0) ↔ ((v ≠ 0 ∧ det0 v = 0) ∨ det0 v = 1)
    exact h4a v
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | exact cSideOrb0_disjoint_cSideOrb1
        | exact cSideOrb0_disjoint_cSideOrb1.symm
  · intro i g v hv
    fin_cases i
    · change sigma0 g v ≠ 0 ∧ det0 (sigma0 g v) = 0
      have hv' : v ≠ 0 ∧ det0 v = 0 := hv
      refine ⟨?_, ?_⟩
      · intro h0
        exact hv'.1 ((sigma0 g).injective (by rw [h0, map_zero]))
      · rw [sigma0_apply, det0_actFun]
        exact hv'.2
    · change det0 (sigma0 g v) = 1
      rw [sigma0_apply, det0_actFun]
      exact hv
  · intro i v hv w hw
    fin_cases i
    · change v ∈ cSideOrb0 at hv
      change w ∈ cSideOrb0 at hw
      have hv' : v ≠ 0 ∧ det0 v = 0 := hv
      have hw' : w ≠ 0 ∧ det0 w = 0 := hw
      obtain ⟨Gv, hGv⟩ := h4b v hv'.1 hv'.2
      obtain ⟨Gw, hGw⟩ := h4b w hw'.1 hw'.2
      refine ⟨(iota.symm (Gw * Gv⁻¹).1, iota.symm (Gw * Gv⁻¹).2), ?_⟩
      rw [sigma0_symm_apply]
      calc actFun (Gw * Gv⁻¹) v
          = actFun (Gw * Gv⁻¹) (actFun Gv cSideE11) := by rw [hGv]
        _ = actFun ((Gw * Gv⁻¹) * Gv) cSideE11 := by rw [← actFun_mul]
        _ = actFun Gw cSideE11 := by
              rw [show (Gw * Gv⁻¹) * Gv = Gw by
                simp only [mul_assoc, inv_mul_cancel, mul_one]]
        _ = w := hGw
    · change v ∈ cSideOrb1 at hv
      change w ∈ cSideOrb1 at hw
      have hv' : det0 v = 1 := hv
      have hw' : det0 w = 1 := hw
      obtain ⟨Gv, hGv⟩ := h4c v hv'
      obtain ⟨Gw, hGw⟩ := h4c w hw'
      refine ⟨(iota.symm (Gw * Gv⁻¹).1, iota.symm (Gw * Gv⁻¹).2), ?_⟩
      rw [sigma0_symm_apply]
      calc actFun (Gw * Gv⁻¹) v
          = actFun (Gw * Gv⁻¹) (actFun Gv 1) := by rw [hGv]
        _ = actFun ((Gw * Gv⁻¹) * Gv) 1 := by rw [← actFun_mul]
        _ = actFun Gw 1 := by
              rw [show (Gw * Gv⁻¹) * Gv = Gw by
                simp only [mul_assoc, inv_mul_cancel, mul_one]]
        _ = w := hGw
  · change Nat.card cSideOrb0 = 75
    exact cSideOrb0_card h4d
  · change Nat.card cSideOrb1 = 60
    exact cSideOrb1_card h4d

end CFSG.EvenSporadicStandard.HNRecog.CSide
