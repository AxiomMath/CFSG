module

public import CFSG.GH74.Uniqueness.Section7Prop74Def
public import CFSG.GH74.Uniqueness.Section6Basic
public import CFSG.GH74.Uniqueness.Setup

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.prop74_of_centralizer_le (S : ZDSetup X Z M) (hL73 : Lemma73Stmt Z M) {z : X}
    {p : ℕ} {W : Subgroup X} (hW : T4Max Z M z p W)
    (hC : centralizer (CFSG.OddInversion.invertedSet W z : Set X) ≤ M) :
    Prop74Spec Z M z W (omegaFix M (W : Set X)) := by
  have hZ := S.invariant
  have h := S.prodDisc
  have hcand := hW.cand
  have hz := hcand.mem_Z
  have hzM := hcand.mem_M
  have hzMN : z ∈ normalizer (M : Set X) := by
    rw [h.normalizer_eq_self]
    exact hzM
  have hz'MN : z⁻¹ ∈ normalizer (M : Set X) := (normalizer (M : Set X)).inv_mem hzMN
  refine ⟨le_rfl, hcand.self_mem_omegaFix, ?_, fun β hβ => hcand.conjugate_z_mem_omegaFix hβ, ?_,
    ?_⟩
  · have := hcand.two_le
    omega
  · intro β _ γ _ _ x hx
    exact hC hx.1.1
  · intro β hβ hβM
    have hWβ : W ≤ β := (h.mem_omegaFix_iff.mp hβ).2
    have hβz : conjugate β z ∈ omegaFix M (W : Set X) := hcand.conjugate_z_mem_omegaFix hβ
    have hWβz : W ≤ conjugate β z := (h.mem_omegaFix_iff.mp hβz).2
    have hWE : W ≤ M ⊓ β ⊓ conjugate β z := le_inf (le_inf hcand.le_M hWβ) hWβz
    obtain ⟨hL1, hL2⟩ := hL73 z p W hW β hβ hβM
    obtain ⟨P, hP, hWP, hzP⟩ := hL1 W hcand.pgroup hWE hcand.normalizes
    obtain ⟨t, htZ, htP, htβ⟩ := hL2 P hP hzP
    have htt : t * t = 1 := hZ.mul_self_eq_one htZ
    set u : X := z⁻¹ * t * z with hu
    have huu : u * u = 1 := by
      have : u * u = z⁻¹ * (t * t) * z := by rw [hu]; group
      rw [this, htt]
      group
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
    have huP : u ∈ normalizer (P : Set X) :=
      (normalizer (P : Set X)).mul_mem
        ((normalizer (P : Set X)).mul_mem ((normalizer (P : Set X)).inv_mem hzP) htP) hzP
    have hu'P : u⁻¹ ∈ normalizer (P : Set X) := (normalizer (P : Set X)).inv_mem huP
    have h2 : conjSet (CFSG.OddInversion.invertedSet W z) u ⊆
        ((M ⊓ β ⊓ conjugate β z : Subgroup X) : Set X) := by
      rintro x ⟨k, hk, rfl⟩
      have hkP : k ∈ P := hWP hk.1
      have := (Subgroup.mem_normalizer_iff.mp hu'P k).mp hkP
      rw [inv_inv] at this
      exact hP.le this
    have hzMinv : conjugate M z⁻¹ = M := conjugate_eq_iff_mem_normalizer.mpr hz'MN
    have hMu : conjugate M u = conjugate β z := by
      rw [hu, conjugate_mul_mul, hzMinv, htβ]
    refine ⟨t, htZ, htβ, h2, ?_, u, ?_, ?_⟩
    ·
      rintro x ⟨⟨hxC, hxM⟩, hxβ⟩
      have hxu : u * x * u⁻¹ ∈ centralizer (CFSG.OddInversion.invertedSet W z : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        have hcomm : (u⁻¹ * k * u) * x = x * (u⁻¹ * k * u) :=
          Subgroup.mem_centralizer_iff.mp hxC _ ⟨k, hk, rfl⟩
        calc k * (u * x * u⁻¹) = u * ((u⁻¹ * k * u) * x) * u⁻¹ := by group
          _ = u * (x * (u⁻¹ * k * u)) * u⁻¹ := by rw [hcomm]
          _ = (u * x * u⁻¹) * k := by group
      have hxMu : x ∈ conjugate M u := mem_conjugate_iff.mpr (hC hxu)
      rw [hMu] at hxMu
      exact ⟨⟨hxM, hxβ⟩, hxMu⟩
    ·
      have hβt : conjugate β t = M := by
        rw [← htβ, conjugate_conjugate, htt, conjugate_one]
      have e : z * u = t * z := by rw [hu]; group
      have hzM' : conjugate M z = M := conjugate_eq_iff_mem_normalizer.mpr hzMN
      rw [conjugate_conjugate, e, ← conjugate_conjugate, hβt, hzM']
    ·
      refine h.mem_omegaFix_iff.mpr ⟨conjugate_mem_omega hβ.1 u, ?_⟩
      have hKβ : CFSG.OddInversion.invertedSet W z ⊆ (conjugate β u : Set X) := by
        intro k hk
        have h1 := h2 ⟨k, hk, rfl⟩
        have h3 : u⁻¹ * k * u ∈ β := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp h1).1).2
        rw [huinv] at h3
        rw [SetLike.mem_coe, mem_conjugate_iff, huinv]
        exact h3
      calc W = Subgroup.closure (CFSG.OddInversion.invertedSet W z) :=
            (hcand.closure_invertedSet hZ).symm
        _ ≤ conjugate β u := (Subgroup.closure_le _).mpr hKβ

end CFSG.GH74.Uniqueness
