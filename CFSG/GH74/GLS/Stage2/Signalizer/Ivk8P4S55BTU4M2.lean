module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTU4M
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTU4B2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTU4N2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTU4N3

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BU4

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open BS4 BL4
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K]

theorem false_of_lagr_u4 [Finite K] (h : UnitaryFieldData p f K) (h2 : (2 : K) ≠ 0)
    {W I : Subgroup (hypPSU h 2 0)} (hI : ⁅I, I⁆ = I) (hIne : I ≠ ⊥)
    {U : Subgroup (MulAut (hypPSU h 2 0))} (hU : IVK.IsFourSubgroup U)
    (hUW : ∀ u ∈ U, ∀ w ∈ W, u w ∈ W) (hUI : ∀ u ∈ U, ∀ x ∈ I, u x = x)
    (hS : ∀ u ∈ U, u ≠ 1 → u * u = 1 → SurvU4Orth h u)
    {N : Submodule K (HypIndex 2 0 → K)} {g : hypSU h 2 0} (hg : g • hypFlag h 2 0 2 = N)
    (hIN : ∀ s ∈ I.comap (hypProj h 2 0), ∀ v ∈ N,
      (((s : hypSU h 2 0) : GL (HypIndex 2 0) K) : MH K) *ᵥ v ∈ N)
    (hNlin : ∀ A : GL (HypIndex 2 0) K, A ∈ normalizer ((preGL h W :
        Subgroup (GL (HypIndex 2 0) K)) : Set (GL (HypIndex 2 0) K)) →
      ∀ v ∈ N, (A : MH K) *ᵥ v ∈ N)
    (hNsemi : ∀ (A : GL (HypIndex 2 0) K) (σ : K ≃+* K), (∀ c, σ c = h.bar c) →
      ∀ hx : (⟨A, σ⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0,
      (∀ w ∈ W, semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩ w ∈ W) →
      (A : MH K) * (A : MH K).map h.bar = 1 → ∀ v ∈ N, (A : MH K) *ᵥ barV h v ∈ N) :
    False := by
  set G := (g : GL (HypIndex 2 0) K) with hGdef
  set H' := (Hu h I).map (ψU h G) with hH'
  have hgU : G ∈ hypUnitary h 2 0 := mem_hypUnitary.mpr (mem_hypSU.mp g.2).1
  have hHle : Hu h I ≤ I.comap (hypProj h 2 0) := Subgroup.commutator_le_self _
  have hH21 : ∀ x ∈ H', (x : MB K).toBlocks₂₁ = 0 := by
    rintro _ ⟨s, hs, rfl⟩
    rw [coe_ψU]
    exact cv_bl hg (hIN s (hHle hs))
  have hHu : ∀ x ∈ H', ((x : MB K).map h.bar)ᵀ * jU * (x : MB K) = jU := by
    rintro _ ⟨s, -, rfl⟩
    rw [coe_ψU]
    exact cv_herm G hgU (mem_hypSU.mp s.2).1
  have hfin := false_of_commU hI hIne (ψU_injective (h := h) G)
  have hlin : ∀ (B : GL (HypIndex 2 0) K)
      (hx : (⟨B, RingEquiv.refl K⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0),
      semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩ ∈ U →
      semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩ ≠ 1 → B ∈ hypUnitary h 2 0 →
      (∃ s : K, (B : MH K) * B = s • 1) →
      IsLinB h.bar (cv G B) ∧ ∀ x ∈ H', cv G B * (x : MB K) = (x : MB K) * cv G B := by
    intro B hx hBU hB1 hBu ⟨s, hs⟩
    refine ⟨⟨cv_bl hg (hNlin B (mem_normalizer_preGL_of_lin hx (hUW _ hBU))),
      cv_herm G hgU (mem_hypUnitary.mp hBu), ⟨s, cv_sq G hs⟩, cv_ns G (ne_smul_of_ne_one hB1)⟩,
      ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    rw [coe_ψU, ← cv_mul, ← cv_mul, ← Units.val_mul, ← Units.val_mul,
      comm_of_lin hx (hUI _ hBU) t ht]
  have hG : ∀ (B A : GL (HypIndex 2 0) K) (σ : K ≃+* K)
      (hxB : (⟨B, RingEquiv.refl K⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0)
      (hxA : (⟨A, σ⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0),
      semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hxB⟩ ∈ U →
      semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hxB⟩ ≠ 1 → B ∈ hypUnitary h 2 0 →
      (∃ s : K, (B : MH K) * B = s • 1) →
      semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hxA⟩ ∈ U → A ∈ hypUnitary h 2 0 →
      (∀ c, σ c = h.bar c) → (A : MH K) * (A : MH K).map h.bar = 1 →
      SurvU4Orth h (semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hxB⟩ *
        semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hxA⟩) → False := by
    intro B A σ hxB hxA hBU hB1 hBu hBs hAU hAu hσ hAA hS3
    obtain ⟨hBL, hBH⟩ := hlin B hxB hBU hB1 hBu hBs
    rcases lin_or_semi hS3 with ⟨B₃, hx₃, -, -, he⟩ | ⟨A₃, σ₃, hx₃, hA₃u, -, hAA₃, he⟩
    · obtain ⟨hr, -⟩ := eq_of_eq_mul hxB hxA hx₃ he.symm
      obtain ⟨c, hc⟩ := h.exists_bar_ne
      exact hc (by rw [← hσ, ← hr]; rfl)
    · obtain ⟨-, μ, hμ⟩ := eq_of_eq_mul hxB hxA hx₃ he.symm
      have hrel := semi_rel (mem_hypUnitary.mp hBu) (mem_hypUnitary.mp hAu)
        (mem_hypUnitary.mp hA₃u) (by rw [hμ, coe_scalar_mul_hyp, Units.val_mul]) hAA hAA₃
      exact hfin (caseGU h2 hH21 hHu hBL hBH (sv_bl hg (hNsemi A σ hσ hxA (hUW _ hAU) hAA))
        (det_sv G h A) (by rw [cv_sv, hrel]))
  obtain ⟨u₁, hu₁, u₂, hu₂, h1, h2', h12, hsq1, hsq2, hsq12⟩ := exists_pair_four hU
  have hcomm : u₁ * u₂ = u₂ * u₁ := by
    have := hU.1.toIsMulCommutative
    exact congrArg Subtype.val (mul_comm' (⟨u₁, hu₁⟩ : ↥U) ⟨u₂, hu₂⟩)
  have hu12 : u₁ * u₂ ∈ U := mul_mem hu₁ hu₂
  have hS12 := hS _ hu12 h12 hsq12
  rcases lin_or_semi (hS u₁ hu₁ h1 hsq1) with
    ⟨B₁, hx₁, hB₁u, hB₁s, rfl⟩ | ⟨A₁, σ₁, hx₁, hA₁u, hσ₁, hAA₁, rfl⟩ <;>
    rcases lin_or_semi (hS u₂ hu₂ h2' hsq2) with
      ⟨B₂, hx₂, hB₂u, hB₂s, rfl⟩ | ⟨A₂, σ₂, hx₂, hA₂u, hσ₂, hAA₂, rfl⟩
  · obtain ⟨hL₁, hH₁⟩ := hlin B₁ hx₁ hu₁ h1 hB₁u hB₁s
    obtain ⟨hL₂, hH₂⟩ := hlin B₂ hx₂ hu₂ h2' hB₂u hB₂s
    rcases lin_or_semi hS12 with ⟨B₃, hx₃, hB₃u, hB₃s, he⟩ | ⟨A₃, σ₃, hx₃, -, hσ₃, -, he⟩
    · obtain ⟨-, μ, hμ⟩ := eq_of_eq_mul hx₁ hx₂ hx₃ he.symm
      obtain ⟨hL₃, -⟩ := hlin B₃ hx₃ (he ▸ hu12) (he ▸ h12) hB₃u hB₃s
      have e3 : cv G (B₃ : MH K) = (μ : K) • (cv G B₁ * cv G B₂) := by
        rw [hμ, coe_scalar_mul_hyp, Units.val_mul, cv_smul, cv_mul]
      rw [e3] at hL₃
      exact hfin (caseLU h2 hH21 hHu hL₁ hL₂ hL₃ hH₁ hH₂)
    · obtain ⟨hr, -⟩ := eq_of_eq_mul hx₁ hx₂ hx₃ he.symm
      obtain ⟨c, hc⟩ := h.exists_bar_ne
      exact hc (by rw [← hσ₃, hr]; rfl)
  · exact hG B₁ A₂ σ₂ hx₁ hx₂ hu₁ h1 hB₁u hB₁s hu₂ hA₂u hσ₂ hAA₂ hS12
  · exact hG B₂ A₁ σ₁ hx₂ hx₁ hu₂ h2' hB₂u hB₂s hu₁ hA₁u hσ₁ hAA₁ (by rw [← hcomm]; exact hS12)
  · rcases lin_or_semi hS12 with ⟨B₃, hx₃, hB₃u, hB₃s, he⟩ | ⟨A₃, σ₃, hx₃, -, hσ₃, -, he⟩
    · have hv : semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx₃⟩ *
          semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx₁⟩ =
            semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx₂⟩ := by
        rw [← he, hcomm, mul_assoc, hsq1, mul_one]
      exact hG B₃ A₁ σ₁ hx₃ hx₁ (he ▸ hu12) (he ▸ h12) hB₃u hB₃s hu₁ hA₁u hσ₁ hAA₁
        (by rw [hv]; exact hS _ hu₂ h2' hsq2)
    · exact semi_mul_semi hσ₁ hσ₂ hσ₃ hx₁ hx₂ hx₃ he.symm

end BU4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
