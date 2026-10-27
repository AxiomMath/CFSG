module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Desc
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Finish
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38ShapeTop
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38WeakChecks
public import Certificates.Certificate9588
public import Certificates.Certificate9589

public section

namespace CFSG.AGLEmbedding.ChevOuter.U38

open CFSG.Quasithin CFSG.AGLEmbedding.ChevOuter CFSG.AGLEmbedding.ChevOuter.GF64
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts
open scoped Matrix

theorem pow_mem_iff {X : Type} [Group X] (K : Subgroup X) {y : X} (hy3 : y ^ 3 = 1) (hyK : y ∉ K)
    {j : ℕ} (hj : j < 3) (h : y ^ j ∈ K) : j = 0 := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
  · rfl
  · exact absurd (by simpa using h) hyK
  · exfalso
    apply hyK
    have : y = (y ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hy3, one_mul, pow_one]
    rw [this]
    exact K.pow_mem h 2

variable {X : Type} [Group X] (K : Subgroup X) [K.Normal]

noncomputable def modelSU (e : K ≃* SU) (y : X) (hy3 : y ^ 3 = 1) (hyK : y ∉ K)
    (hact : actOn K e y = sigSU) : Model X where
  ι := K.subtype.comp e.symm.toMonoidHom
  x := y
  x_cube := hy3
  x_conj g := by
    have h := coe_actOn_symm K e y g
    rw [hact] at h
    exact h.symm
  sc := s1Sc
  sc_ker s hs := by
    have h1 : s = GF64.ofNat' 1 := by simpa [s1Sc] using hs
    have h2 : GF64.ofNat' 1 = (1 : GF64) := rfl
    rw [h1, h2]
    exact ⟨1, by simp, by simp⟩
  inj g j hj h := by
    have hj0 : j = 0 := by
      apply pow_mem_iff K hy3 hyK hj
      have : y ^ j = ((e.symm g : K) : X)⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this]
      exact K.inv_mem (e.symm g).2
    subst hj0
    have hg : g = 1 := by
      have h' : ((e.symm g : K) : X) = 1 := by simpa using h
      apply e.symm.injective
      exact Subtype.ext (by simpa using h')
    refine ⟨rfl, GF64.ofNat' 1, by simp [s1Sc], ?_⟩
    rw [hg]
    simp [show GF64.ofNat' 1 = (1 : GF64) from rfl]

theorem range_modelSU (e : K ≃* SU) (y : X) (hy3 : y ^ 3 = 1) (hyK : y ∉ K)
    (hact : actOn K e y = sigSU) : (modelSU K e y hy3 hyK hact).ι.range = K := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact (e.symm g).2
  · intro k hk
    exact ⟨e ⟨k, hk⟩, by simp [modelSU]⟩

noncomputable def modelPSU (e : K ≃* unitaryPSU hU 3) (y : X) (hy3 : y ^ 3 = 1) (hyK : y ∉ K)
    (hact : actOn K e y = psuField hU sigma2Equiv) : Model X where
  ι := K.subtype.comp (e.symm.toMonoidHom.comp (unitaryProj hU 3))
  x := y
  x_cube := hy3
  x_conj g := by
    have h := coe_actOn_symm K e y (unitaryProj hU 3 g)
    rw [hact] at h
    exact h.symm
  sc := p1Sc
  sc_ker s hs := by
    have hs' : s = GF64.ofNat' 1 ∨ s = GF64.ofNat' 8 ∨ s = GF64.ofNat' 9 := by
      simpa [p1Sc] using hs
    have hc : s ^ 3 = 1 := cube_roots_mem s hs
    refine ⟨scalarSU s hc, coe_scalarGL s hc, ?_⟩
    have : unitaryProj hU 3 (scalarSU s hc) = 1 := by
      rw [← MonoidHom.mem_ker, ker_unitaryProj]
      exact scalarSU_mem s hc
    simp [this]
  inj g j hj h := by
    have hj0 : j = 0 := by
      apply pow_mem_iff K hy3 hyK hj
      have : y ^ j = ((e.symm (unitaryProj hU 3 g) : K) : X)⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this]
      exact K.inv_mem (e.symm (unitaryProj hU 3 g)).2
    subst hj0
    have hg : unitaryProj hU 3 g = 1 := by
      have h' : ((e.symm (unitaryProj hU 3 g) : K) : X) = 1 := by simpa using h
      have := e.symm.injective (Subtype.ext (by simpa using h') :
        e.symm (unitaryProj hU 3 g) = e.symm 1)
      exact this
    have hmem : g ∈ unitaryScalars hU 3 := by
      rw [← ker_unitaryProj]
      exact hg
    obtain ⟨c, hc, hgc⟩ := exists_scalar_of_mem hmem
    exact ⟨rfl, c, by simpa [p1Sc] using hc, hgc⟩

theorem range_modelPSU (e : K ≃* unitaryPSU hU 3) (y : X) (hy3 : y ^ 3 = 1) (hyK : y ∉ K)
    (hact : actOn K e y = psuField hU sigma2Equiv) : (modelPSU K e y hy3 hyK hact).ι.range = K := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact (e.symm (unitaryProj hU 3 g)).2
  · intro k hk
    obtain ⟨g, hg⟩ := unitaryProj_surjective hU 3 (e ⟨k, hk⟩)
    exact ⟨g, by simp [modelPSU, hg]⟩

theorem le_weakCore_of_sigma_su [Finite X] (e : K ≃* SU) (y : X)
    (hy3 : y ^ 3 = 1) (hyK : y ∉ K) (hact : actOn K e y = sigSU) (R : Sylow 3 X) :
    K ≤ CFSG.Open.GLBWeakCore 3 (R : Subgroup X) := by
  have hG : ∀ k < 2, checkG (modelSU K e y hy3 hyK hact).repSys.sc
      (modelSU K e y hy3 hyK hact).repSys.valid s1Data k = true := by
    intro k hk
    interval_cases k
    exacts [checkG_s1_zero, checkG_s1_one]
  obtain ⟨E, hEab, -, hrange⟩ := range_le_weakCore_top (modelSU K e y hy3 hyK hact) s1Data s1Gen
    checkE_s1 hG Certificates.certificate9588 rfl
    (by intro k hk; interval_cases k <;> rfl) (by intro k hk; interval_cases k <;> rfl)
  rw [range_modelSU] at hrange
  exact normal_le_weakCore_sylow K E hEab hrange R

theorem le_weakCore_of_sigma_psu [Finite X]
    (e : K ≃* unitaryPSU hU 3) (y : X) (hy3 : y ^ 3 = 1) (hyK : y ∉ K)
    (hact : actOn K e y = psuField hU sigma2Equiv) (R : Sylow 3 X) :
    K ≤ CFSG.Open.GLBWeakCore 3 (R : Subgroup X) := by
  have hG : ∀ k < 2, checkG (modelPSU K e y hy3 hyK hact).repSys.sc
      (modelPSU K e y hy3 hyK hact).repSys.valid p1Data k = true := by
    intro k hk
    interval_cases k
    exacts [checkG_p1_zero, checkG_p1_one]
  obtain ⟨E, hEab, -, hrange⟩ := range_le_weakCore_top (modelPSU K e y hy3 hyK hact) p1Data
    p1Gen checkE_p1 hG Certificates.certificate9589 rfl
    (by intro k hk; interval_cases k <;> rfl) (by intro k hk; interval_cases k <;> rfl)
  rw [range_modelPSU] at hrange
  exact normal_le_weakCore_sylow K E hEab hrange R

end CFSG.AGLEmbedding.ChevOuter.U38
