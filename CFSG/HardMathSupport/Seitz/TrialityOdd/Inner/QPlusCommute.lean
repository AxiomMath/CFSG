module

public import CFSG.LieType.Steinberg.TwistedD4.Weyl
public import CFSG.LieType.Steinberg.TwistedD4.Local
public import CFSG.LieType.Steinberg.TwistedD4.RankOne
public import Certificates.Certificate117

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal CFSG.LieType.Steinberg.TwistedD4

set_option linter.unusedSectionVars false


def thetaRoot : Fin d4.rank → ℤ :=
  twReflectHom (ng 0) (twReflectHom (ng 1) (Pi.single (nd 2) 1))

theorem isRoot_thetaRoot : IsRoot d4 thetaRoot :=
  isRoot_twReflect (ng 0) (isRoot_twReflect (ng 1) (isRoot_single d4 (nd 2)))

theorem not_isRoot_thetaRoot_add_outer (a : Fin d4.rank) (ha : a ≠ nd 2) (s : ℤ)
    (hs : s = 1 ∨ s = -1) : ¬ IsRoot d4 (thetaRoot + s • Pi.single a 1) := by
  rw [← StringData.memDec_iff (Tag.rootCertificate_check d4) (Tag.stringData_check d4)]
  revert a
  rcases hs with rfl | rfl <;> decide +kernel

theorem not_isRoot_neg_thetaRoot_add_outer (a : Fin d4.rank) (ha : a ≠ nd 2) (s : ℤ)
    (hs : s = 1 ∨ s = -1) : ¬ IsRoot d4 (-thetaRoot + s • Pi.single a 1) := by
  rw [← StringData.memDec_iff (Tag.rootCertificate_check d4) (Tag.stringData_check d4)]
  revert a
  rcases hs with rfl | rfl <;> decide +kernel

theorem thetaRoot_ne_outer (a : Fin d4.rank) (ha : a ≠ nd 2) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    thetaRoot ≠ s • Pi.single a 1 ∧ thetaRoot ≠ -(s • Pi.single a 1) ∧
      -thetaRoot ≠ s • Pi.single a 1 ∧ -thetaRoot ≠ -(s • Pi.single a 1) := by
  revert a
  rcases hs with rfl | rfl <;> decide +kernel

section Ambient

variable {K : Type} [Field K]

local notation "𝕏" => rootGroup (rootOperatorFamily d4) K

def outerRankOne : Subgroup (adjointGroup d4 K) :=
  CFSG.LieType.CurtisTits.rankOne (rootGroup (rootOperatorFamily d4) K) (nd 0) ⊔
    CFSG.LieType.CurtisTits.rankOne (rootGroup (rootOperatorFamily d4) K) (nd 1) ⊔
      CFSG.LieType.CurtisTits.rankOne (rootGroup (rootOperatorFamily d4) K) (nd 3)

theorem rankOne_zero_le_outer :
    CFSG.LieType.CurtisTits.rankOne (rootGroup (rootOperatorFamily d4) K) (nd 0) ≤
      (outerRankOne : Subgroup (adjointGroup d4 K)) :=
  le_trans le_sup_left le_sup_left

theorem rankOne_one_le_outer :
    CFSG.LieType.CurtisTits.rankOne (rootGroup (rootOperatorFamily d4) K) (nd 1) ≤
      (outerRankOne : Subgroup (adjointGroup d4 K)) :=
  le_trans le_sup_right le_sup_left

theorem rankOne_three_le_outer :
    CFSG.LieType.CurtisTits.rankOne (rootGroup (rootOperatorFamily d4) K) (nd 3) ≤
      (outerRankOne : Subgroup (adjointGroup d4 K)) :=
  le_sup_right

def thetaGroup : Subgroup (adjointGroup d4 K) := 𝕏 thetaRoot ⊔ 𝕏 (-thetaRoot)

theorem isRoot_neg_thetaRoot : IsRoot d4 (-thetaRoot) := by
  have h := isRoot_twReflect (ng 0) (isRoot_twReflect (ng 1) (isRoot_neg_single d4 (nd 2)))
  have e : -thetaRoot = twReflectHom (ng 0) (twReflectHom (ng 1) (-Pi.single (nd 2) 1)) := by
    simp [thetaRoot]
  rw [e]
  exact h

theorem commute_theta_rootGroup_outer {γ : Fin d4.rank → ℤ} (hγ : γ = thetaRoot ∨ γ = -thetaRoot)
    {y : adjointGroup d4 K} (hy : y ∈ 𝕏 γ) {a : Fin d4.rank} (ha : a ≠ nd 2) {s : ℤ}
    (hs : s = 1 ∨ s = -1) {z : adjointGroup d4 K} (hz : z ∈ 𝕏 (s • Pi.single a 1)) :
    Commute y z := by
  obtain ⟨h1, h2, h3, h4⟩ := thetaRoot_ne_outer a ha s hs
  rcases hγ with rfl | rfl
  · exact commute_of_mem_rootGroup isRoot_thetaRoot (isRoot_smul_single hs a) h1 h2
      (not_isRoot_thetaRoot_add_outer a ha s hs) hy hz
  · exact commute_of_mem_rootGroup isRoot_neg_thetaRoot (isRoot_smul_single hs a) h3 h4
      (not_isRoot_neg_thetaRoot_add_outer a ha s hs) hy hz

theorem outerRankOne_le_centralizer {γ : Fin d4.rank → ℤ} (hγ : γ = thetaRoot ∨ γ = -thetaRoot)
    {y : adjointGroup d4 K} (hy : y ∈ 𝕏 γ) :
    (outerRankOne : Subgroup (adjointGroup d4 K)) ≤ Subgroup.centralizer {y} := by
  have hrk : ∀ a : Fin d4.rank, a ≠ nd 2 →
      CFSG.LieType.CurtisTits.rankOne (rootGroup (rootOperatorFamily d4) K) a ≤
        Subgroup.centralizer {y} := by
    intro a ha
    refine sup_le (fun z hz => ?_) (fun z hz => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have := commute_theta_rootGroup_outer hγ hy ha (s := 1) (Or.inl rfl)
        (by rw [one_smul]; exact hz)
      exact this.eq.symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have := commute_theta_rootGroup_outer hγ hy ha (s := -1) (Or.inr rfl)
        (by rw [neg_one_smul]; exact hz)
      exact this.eq.symm
  exact sup_le (sup_le (hrk (nd 0) (by decide)) (hrk (nd 1) (by decide))) (hrk (nd 3) (by decide))

theorem commute_thetaGroup_outerRankOne {y z : adjointGroup d4 K}
    (hy : y ∈ (thetaGroup : Subgroup (adjointGroup d4 K))) (hz : z ∈ (outerRankOne : Subgroup (adjointGroup d4 K))) :
    Commute y z := by
  have hle : (thetaGroup : Subgroup (adjointGroup d4 K)) ≤ Subgroup.centralizer ((outerRankOne (K := K) : Subgroup (adjointGroup d4 K)) : Set (adjointGroup d4 K)) := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact Subgroup.mem_centralizer_singleton_iff.1
        (outerRankOne_le_centralizer (Or.inl rfl) hy hz)
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact Subgroup.mem_centralizer_singleton_iff.1
        (outerRankOne_le_centralizer (Or.inr rfl) hy hz)
  exact (Subgroup.mem_centralizer_iff.1 (hle hy) z hz).symm

theorem conj_mem_thetaGroup {b : adjointGroup d4 K}
    (hb : b ∈ 𝕏 (Pi.single (nd 2) 1) ⊔ 𝕏 (-Pi.single (nd 2) 1)) :
    (nHatE K (ng 0) * nHatE K (ng 1)) * b * (nHatE K (ng 0) * nHatE K (ng 1))⁻¹ ∈
      (thetaGroup : Subgroup (adjointGroup d4 K)) := by
  have e1 : ∀ x : adjointGroup d4 K,
      (nHatE K (ng 0) * nHatE K (ng 1)) * x * (nHatE K (ng 0) * nHatE K (ng 1))⁻¹ =
        nHatE K (ng 0) * (nHatE K (ng 1) * x * (nHatE K (ng 1))⁻¹) * (nHatE K (ng 0))⁻¹ := by
    intro x
    simp [mul_assoc]
  have hpos : ∀ y ∈ 𝕏 (Pi.single (nd 2) 1 : Fin d4.rank → ℤ),
      nHatE K (ng 0) * (nHatE K (ng 1) * y * (nHatE K (ng 1))⁻¹) * (nHatE K (ng 0))⁻¹ ∈
        𝕏 thetaRoot := fun y hy =>
    nHatE_conj_mem (ng 0) (isRoot_twReflect (ng 1) (isRoot_single d4 (nd 2)))
      (nHatE_conj_mem (ng 1) (isRoot_single d4 (nd 2)) hy)
  have hneg : ∀ z ∈ 𝕏 (-Pi.single (nd 2) 1 : Fin d4.rank → ℤ),
      nHatE K (ng 0) * (nHatE K (ng 1) * z * (nHatE K (ng 1))⁻¹) * (nHatE K (ng 0))⁻¹ ∈
        𝕏 (-thetaRoot) := fun z hz => by
    have e2 : twReflectHom (ng 0) (twReflectHom (ng 1) (-Pi.single (nd 2) 1)) = -thetaRoot := by
      simp [thetaRoot]
    have h := nHatE_conj_mem (ng 0) (isRoot_twReflect (ng 1) (isRoot_neg_single d4 (nd 2)))
      (nHatE_conj_mem (ng 1) (isRoot_neg_single d4 (nd 2)) hz)
    rw [e2] at h
    exact h
  have hle : (𝕏 (Pi.single (nd 2) 1 : Fin d4.rank → ℤ) ⊔ 𝕏 (-Pi.single (nd 2) 1)).map
      (MulAut.conj (nHatE K (ng 0) * nHatE K (ng 1))).toMonoidHom ≤
        (thetaGroup : Subgroup (adjointGroup d4 K)) := by
    unfold thetaGroup
    rw [Subgroup.map_sup]
    refine sup_le_sup (a := Subgroup.map _ (𝕏 (Pi.single (nd 2) 1 : Fin d4.rank → ℤ)))
      (b := 𝕏 thetaRoot) (c := Subgroup.map _ (𝕏 (-Pi.single (nd 2) 1 : Fin d4.rank → ℤ)))
      (d := 𝕏 (-thetaRoot)) ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      intro y hy
      show (nHatE K (ng 0) * nHatE K (ng 1)) * y * (nHatE K (ng 0) * nHatE K (ng 1))⁻¹ ∈
        𝕏 thetaRoot
      rw [e1]
      exact hpos y hy
    · rw [Subgroup.map_le_iff_le_comap]
      intro y hy
      show (nHatE K (ng 0) * nHatE K (ng 1)) * y * (nHatE K (ng 0) * nHatE K (ng 1))⁻¹ ∈
        𝕏 (-thetaRoot)
      rw [e1]
      exact hneg y hy
  exact hle (Subgroup.mem_map_of_mem _ hb)

end Ambient

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
